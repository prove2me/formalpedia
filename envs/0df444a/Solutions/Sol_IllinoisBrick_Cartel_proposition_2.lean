-- Prove2me | solution 1 for IllinoisBrick.Cartel.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:13:07.032083+00:00
-- url     : https://prove2.me/submissions/af0d7a09-00ff-413a-9545-4b7de2159a7c

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model
import Theorems.Thm_IllinoisBrick_Cartel_proposition_1
import Theorems.Thm_IllinoisBrick_Cartel_proposition_2a
import Theorems.Thm_IllinoisBrick_Cartel_proposition_2b

open IllinoisBrick.Cartel

theorem solution (a b c : ℝ) (h : Standing a b c) :
    (∀ k : Contract,
      ∃ qC : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC) ∧
    (∀ k : Contract, k ≠ Contract.WPFF →
      ∀ qC : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC →
      ∀ v : Fin 2 → Terms, (∀ j, Admissible c k (v j)) →
      ∀ q : Fin 2 → ℝ, IsRetailerEq a b c k v q →
        ¬ IsCartel a b c k v q qC) ∧
    (∃ v : Fin 2 → Terms, (∀ j, Admissible c Contract.WPFF (v j)) ∧
      (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
      ∀ q qC : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
        IsRetailerEq a b c Contract.WPFF (fun _ => competitiveTerms a b c Contract.WPFF) qC →
        IsCartel a b c Contract.WPFF v q qC) :=
  ⟨fun k => (proposition_1 a b c h k).1,
   fun k hk qC hqC v hadm q hq => proposition_2a a b c h k hk qC hqC v hadm q hq,
   proposition_2b a b c h⟩

