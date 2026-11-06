-- Prove2me | solution 3 for OAI.SevenEighths.ProbeLocal.inv_one_sub_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:16.279654+00:00
-- url     : https://prove2.me/submissions/a990ed97-fec2-47ee-83f7-6df1c2a75ac4

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Local
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeLocal
theorem solution (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have h1 : (1 : ℝ) / 2 ≤ ‖1 - a‖ := by
    have := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  have hpos : (0 : ℝ) < ‖1 - a‖ := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith
