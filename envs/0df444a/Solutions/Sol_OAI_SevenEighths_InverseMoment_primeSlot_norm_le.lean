-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeSlot_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:42.789199+00:00
-- url     : https://prove2.me/submissions/57252712-8b4d-489c-a828-e9538a32bf65

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_empty
attribute [local simp] OAI.SevenEighths.InverseMoment.primeMark_empty

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp
end OAI.SevenEighths.InverseMoment
