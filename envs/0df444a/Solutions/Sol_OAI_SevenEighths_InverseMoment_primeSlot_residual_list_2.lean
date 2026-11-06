-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.primeSlot_residual_list
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:40.498779+00:00
-- url     : https://prove2.me/submissions/47c29f92-87ac-4783-b5ec-b6e792a3d345

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
theorem solution (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  unfold primeSlot
  simp only [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto
