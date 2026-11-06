-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeSlot_residual_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:36.163785+00:00
-- url     : https://prove2.me/submissions/872fd8f7-2731-4410-8dd1-d261193c6d98

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
theorem _root_.solution (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto
end OAI.SevenEighths.InverseMoment
