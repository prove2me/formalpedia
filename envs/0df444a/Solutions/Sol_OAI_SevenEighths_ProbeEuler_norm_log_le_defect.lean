-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.norm_log_le_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:12.002514+00:00
-- url     : https://prove2.me/submissions/dcc9abfe-8728-49cf-8e71-c6d36b3e4dfe

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) :
    ‖Complex.log a‖ ≤ (3/2:ℝ)*‖a-1‖ := by
  simpa only [add_sub_cancel] using Complex.norm_log_one_add_half_le_self ha
end OAI.SevenEighths.ProbeEuler
