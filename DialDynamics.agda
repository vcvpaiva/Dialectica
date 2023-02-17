module DialDynamics where



module TwoSystems where 
    open import LDDialSet
    open import Two
    open LD renaming(LDepDialSet to LDD ; LDepDialSetMap to LDD[_,_])

    record Sys (S : Set)(p : LDD) : Set where
        constructor Syˢ⇒_
        field                        -- arbitrary choice here... why ⊤? 
                                     -- if S had some structure.. could maybe say something more interestin
            system : LDD[  ⟨ S , (λ _ → S) , (λ s s' → ⊤) ⟩ , p ]
    open Sys    


    open import Data.Bool
    open import Data.Nat 
    open import Data.Product

    -- ℕ × ℕ → Bool
    ldd : LDD                         -- arbitrary choice again
    ldd = ⟨ Bool , (λ _ → ℕ × ℕ) , (λ{ false (n1 , n2) → ⊥
                                     ; true (n1 , n2) → ⊤}) ⟩

    data Pos₃ : Set where 
        P₁ P₂ P₃ : Pos₃                                

    sys : Sys Pos₃ ldd 
    sys = Syˢ⇒ ((λ{P₁ → true
                 ; P₂ → true
                 ; P₃ → false}) ∧ (λ{ P₁ d → P₁
                                    ; P₂ d → P₁
                                    ; P₃ d → P₁}) st λ { P₁ (fst , snd) → tt
                                                       ; P₂ d → tt
                                                       ; P₃ d → {!   !}})





open import Level
open import LDDialSet
open LD renaming(LDepDialSet to LDD ; LDepDialSetMap to LDD[_,_])
open import Lineale
open MonProset
module GeneralSystems {ℓ : Level}{L : Set ℓ}
        {{pl : Proset L}}
        {{mp : MonProset L}}
        {{lin : Lineale L}} where

    record Sys (S : Set ℓ)(p : LDD) : Set ℓ where
        constructor Syˢ⇒_
        field                        -- what goes here... S → S → L
            system : LDD[  ⟨ S , (λ _ → S) , (λ s s' → unit mp) ⟩ , p ]
    open Sys

    data Pos₄ : Set ℓ where 
        P₁ P₂ P₃ P₄ : Pos₄

    data Bool : Set ℓ where 
        TT FF : Bool
    
    data ℕ : Set ℓ where 
        z : ℕ 
        s : ℕ → ℕ

    open import Data.Product

    -- ℕ × ℕ → Bool
    ldd : LDD 
    ldd = ⟨ Bool , (λ _ → ℕ × ℕ) , (λ{ b (n1 , n2) → {!   !}}) ⟩

    _ : Sys Pos₄ {!   !}
    _ = {!   !}