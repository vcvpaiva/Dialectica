module DC where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import CatLib using (Category;module Finitely; module BinaryProducts; module Cartesian; module Pullback; module ObjectProduct)
open import Cubical.Core.Everything using (_≡_)

-- Assuming a Category 𝒞... 
module _ {o ℓ : Level}(𝒞 : Category o ℓ)where 
    open Category 𝒞
    open Finitely 𝒞 using (FinitelyComplete)
    -- ... that is Finitely Complete
    module foo {fin : FinitelyComplete} where 
        open FinitelyComplete fin using (cartesian; pullback)
        open Cartesian 𝒞 using (CartesianT)
        open Pullback 𝒞 using (PullbackT ; IsPullback)
        open PullbackT
        open CartesianT cartesian using (products)
        open BinaryProducts 𝒞 using(BinaryProductsT)
        open BinaryProductsT products using (_×_; product)
        open ObjectProduct 𝒞 using (module Morphisms; Product)
  
        -- Definition of Objects in DC
        record Obj : Set (o ⊔ ℓ) where 
            field 
                {A} {U} {X} : Ob    
                α : A ⇒ (U × X)
                is-monic : ∀ {C} → (g₁ g₂ : C ⇒ A) → α ∘ g₁ ≡ α ∘ g₂ → g₁ ≡ g₂

        open Morphisms
        open Product

        -- Definition of morphisms in DC...
        record Hom (A B : Obj) : Set (o ⊔ ℓ) where 
            open Obj A
            open Obj B renaming (A to B; U to V; X to Y; α to β)
            -- .. Consist of two maps f, F
            field
                f : U ⇒ V 
                F : (U × Y) ⇒ X
           
            π₁×F : (U × Y) ⇒ (U × X)
            π₁×F = [ product ]⟨ π₁ product , F ⟩

            f×Y : (U × Y) ⇒ (V × Y)
            f×Y = [ product ⇒ product ] f × id

            -- taking the pullback of a and π₁×F 
            open PullbackT (pullback α π₁×F) renaming (P to A'; p₂ to α')
            -- taking the pullback of f×Y and β
            open PullbackT (pullback f×Y β) renaming (P to B'; p₁ to β')
            -- α' and β' should be monic

            -- Diagram on page 3 of Valeria's Thesis
            field   
                -- k should be unique, missing this condition
                k : A' ⇒ B'
                k-cond : β' ∘ k ≡ α'

        open Hom
        
        -- f : U ⇒ U
        -- F : U × X ⇒ X
        DCid : {X : Obj} → Hom X X
        DCid .f = id
        DCid .F = π₂ product
        DCid .k = {! id  !}
            where 
                _  = [ {!   !} ⇒ {!   !} ] {!   !} × id
        DCid .k-cond = {!   !}
        {- id object diagram
                       A'  ---->  A
                       |          |
                       |          |
                       |          |
            A' ----> U x X ----> U × X
            |          |
            |          |
            |          |
            A  ----> U × X
        -}

        _×ₚ_ : (A B : Ob) → Product A B 
        A ×ₚ B = product

        Δ : ∀ (X : Ob) → X ⇒ (X × X)
        Δ X = [ X ×ₚ X ]⟨ id , id ⟩

        -- Something about using the context of the metalanguage here.. 
        swap : ∀ {X Y : Ob} → (X × Y) ⇒ (Y × X)
        swap {X} {Y} = [ p ]⟨ π₂ p , π₁ p ⟩
        --([ p ⇒ p ] π₂ p × π₁ p) ∘ Δ (X × Y)
            where
                p = product
        --([ ((X × Y) ×ₚ (X × Y)) ⇒ (Y ×ₚ X) ] π₂ (X ×ₚ Y) × π₁ (X ×ₚ Y)) ∘ Δ (X × Y)

        -- This is a bit of trickery
        -- Since 𝒞 has aribitrary products, we can form products from any objects of 𝒞
        -- here p is infered to be different product objects.. the projection maps just guide the typing
        shuffle : ∀ {X Y Z : Ob} → (( X × Y) × Z) ⇒ (X × (Y × Z))
        shuffle {X} {Y} {Z} = [ p ]⟨ π₁ p ∘ π₁ p , [ p ]⟨ π₂ p ∘ π₁ p , π₂ p ⟩ ⟩
            where 
                p = product


        _∘DC_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C 
        _∘DC_ g f .f = Hom.f g ∘ Hom.f f
        _∘DC_ {A}{B}{C} g f .F = ((Hom.F f ∘ U×G) ∘ U×f×Z) ∘ Δ×Z
            where
                open Obj A using (U; X)
                open Obj B renaming (U to V; X to Y)
                open Obj C renaming (U to W; X to Z) 
                p = product 

                Δ×Z : (U × Z) ⇒ ((U × U) × Z)
                Δ×Z = [ p ⇒ p ] Δ U × id

                U×f×Z : (( U × U) × Z) ⇒ (U × (V × Z))
                U×f×Z = ([ p ⇒ p ] id × ([ p ⇒ p ] Hom.f f × id)) ∘ shuffle
                
                U×G : (U × (V × Z)) ⇒ (U × Y)
                U×G = [ p ⇒ p ] id × Hom.F g
                
        _∘DC_ g f .k = {!   !}
        _∘DC_ g f .k-cond = {!   !}
    
        -- now try to make a category out of this...
        open import Cubical.Foundations.Isomorphism using (isoToPath; iso ; Iso)
        open import Cubical.Foundations.Prelude using (_≡⟨_⟩_;≡⟨⟩-syntax;_∎;cong;cong₂;refl; transport; sym)

        module HomEq where
            Hom≡ : ∀{A B : Obj}{m₁ m₂ : Hom A B} → f m₁ ≡ f m₂ → F m₁ ≡ F m₂ → {!   !}
            Hom≡ = {!   !}

        DC : Category (o ⊔ ℓ) (o ⊔ ℓ) 
        DC .Ob = Obj
        DC ._⇒_ = Hom 
        DC .id = DCid
        DC ._∘_ = _∘DC_
        DC .idr = {!   !}
        DC .idl = {!   !}
        DC .assoc = {!   !}






{-
kruft. old start to the proofs required to show DC is a category

        open Hom
        open import Cubical.Foundations.Isomorphism using (isoToPath; iso ; Iso)
        open import Cubical.Foundations.Prelude using (_≡⟨_⟩_;≡⟨⟩-syntax;_∎;cong;cong₂;refl; transport; sym)
        open Iso
        open IsPullback

        module lemmas where 


            ispbsym : {P X Y Z : Ob} → (p₁ : P ⇒ X) → (p₂ : P ⇒ Y) → (f : X ⇒ Z) → (g : Y ⇒ Z) → 
                IsPullback p₁ p₂ f g ≡ IsPullback p₂ p₁ g f 
            ispbsym p₁ p₂ f g = isoToPath prf
                where prf : Iso (IsPullback p₁ p₂ f g) (IsPullback p₂ p₁ g f)
                      prf .fun ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = λ x → (ispb  .universal) (sym x)
                                        ; unique = λ x y → ispb .unique y x
                                        {- 
                                        {h₂.A : Ob} {h₁ : h₂.A ⇒ X} {h₂ : h₂.A ⇒ Y} {eq : f ∘ h₁ ≡ g ∘ h₂} →
                                        p₁ ∘ Pullback.IsPullback.universal ispb eq ≡ h₁

                                        {h₂.A : Ob} {h₁ : h₂.A ⇒ Y} {h₂ : h₂.A ⇒ X}{eq : g ∘ h₁ ≡ f ∘ h₂} →
                                        p₂ ∘ ispb .Pullback.IsPullback.universal (λ i → eq (Cubical.Foundations.Prelude.~ i)) ≡ h₁
                                        
                                        -}
                                        ; p₁∘universal≈h₁ = {! refl!}
                                        ; p₂∘universal≈h₂ = {!   !}
                                        }
                      prf .inv ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = λ x → (ispb  .universal) (sym x)
                                        ; unique = λ x y → ispb .unique y x
                                        ; p₁∘universal≈h₁ = {!   !}
                                        ; p₂∘universal≈h₂ = {!   !}
                                        }
                      prf .rightInv = λ b → {!   !}
                      prf .leftInv = λ b → {!   !}

            -- correct notion of equality... probably not
            pbsym : {X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g ≡ PullbackT g f
            pbsym f g = isoToPath isoprf 
                where isoprf : Iso (PullbackT f g) (PullbackT g f)
                      isoprf .fun pb₁ = record { p₁ = pb₁ .p₂ ; p₂ = pb₁ .p₁ ; isPullback = 
                                         record
                                            { commute = sym ((pb₁ .isPullback) .commute)
                                            ; universal = λ x → {!   !}
                                            ; unique = {!   !}
                                            ; p₁∘universal≈h₁ = {!   !}
                                            ; p₂∘universal≈h₂ = {!   !}
                                            } }
                      isoprf .inv pb₂ = record { p₁ = pb₂ .p₂ ; p₂ = pb₂ .p₁ ; isPullback = {!   !} }
                      isoprf .rightInv = {!   !}
                      isoprf .leftInv = {!   !}
-}




            
            

        

    

   