-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeMark_residual_lists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:05.619868+00:00
-- url     : https://prove2.me/submissions/0bf5ec6d-f802-4a03-ae27-c5d837953b36

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeSlot_residual_list

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
omit [DecidableEq σ]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _
end OAI.SevenEighths.InverseMoment
