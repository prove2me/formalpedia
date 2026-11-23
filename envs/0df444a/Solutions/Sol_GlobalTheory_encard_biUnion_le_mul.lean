-- Prove2me | solution 1 for GlobalTheory.encard_biUnion_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:41.399827+00:00
-- url     : https://prove2.me/submissions/e7f036b2-70c9-40e9-bd70-263f72e57abc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {α β : Type*} (s : Set α) (t : α → Set β) (a b : ℕ)
    (hs : s.encard ≤ a) (ht : ∀ i ∈ s, (t i).encard ≤ b) :
    (⋃ i ∈ s, t i).encard ≤ ((a * b : ℕ) : ℕ∞) := by
  have hfin : s.Finite := Set.finite_of_encard_le_coe hs
  have key : (⋃ i ∈ s, t i).encard ≤ s.encard * b := by
    clear hs
    induction s, hfin using Set.Finite.induction_on with
    | empty => simp
    | @insert i s hi _ ih =>
      rw [Set.biUnion_insert, Set.encard_insert_of_notMem hi, add_mul, one_mul, add_comm]
      exact (Set.encard_union_le _ _).trans (add_le_add (ht i (Set.mem_insert _ _))
        (ih fun j hj => ht j (Set.mem_insert_of_mem _ hj)))
  refine key.trans ?_
  push_cast
  gcongr
end GlobalTheory
