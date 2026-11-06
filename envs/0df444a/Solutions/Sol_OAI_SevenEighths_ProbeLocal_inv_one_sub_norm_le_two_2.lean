-- Prove2me | solution 2 for OAI.SevenEighths.ProbeLocal.inv_one_sub_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:24.243124+00:00
-- url     : https://prove2.me/submissions/1b8071c1-8e8f-4f00-a241-10ee722cd237

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Local
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeLocal
namespace OAI.SevenEighths.ProbeLocal
theorem _root_.solution (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith
end OAI.SevenEighths.ProbeLocal
