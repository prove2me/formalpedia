-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.normForm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:56.652984+00:00
-- url     : https://prove2.me/submissions/ed1e23fe-6a55-4722-9b67-4bf92a47fd9b

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta

theorem solution (x y : ℝ) : normForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold normForm at h
    have hy : y = 0 := by
      nlinarith [sq_nonneg (2 * x - y), sq_nonneg y]
    have hx : x = 0 := by
      nlinarith [sq_nonneg (2 * x - y), sq_nonneg y]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [normForm]
