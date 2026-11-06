-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.bounded_finset_coefficient_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:15.751296+00:00
-- url     : https://prove2.me/submissions/5b7a8b73-1a7d-4968-ab2d-9d1b83f0757c

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
import Theorems.Thm_OAI_SevenEighths_InverseMoment_finite_expansion_energy


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h
end OAI.SevenEighths.InverseMoment
