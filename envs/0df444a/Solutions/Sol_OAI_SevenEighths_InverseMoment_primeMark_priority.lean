-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeMark_priority
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:04.717542+00:00
-- url     : https://prove2.me/submissions/00d9b3b7-f18c-4f62-b9fc-2a5516b72c7d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeSlot_priority

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I
end OAI.SevenEighths.InverseMoment
