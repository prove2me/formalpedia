-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.normForm_ge_half_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:10.036225+00:00
-- url     : https://prove2.me/submissions/0dffda77-6067-42e1-9dd6-1600468422b2

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta
namespace OAI.SevenEighths.LatticeSummability
theorem _root_.solution (n : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖n‖ ^ 2 ≤ normForm n.1 n.2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  unfold normForm
  rcases le_total |(n.1 : ℝ)| |(n.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.2 : ℝ)]
end OAI.SevenEighths.LatticeSummability
