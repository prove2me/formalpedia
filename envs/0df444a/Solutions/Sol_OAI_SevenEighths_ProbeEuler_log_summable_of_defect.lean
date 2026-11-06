-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.log_summable_of_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:22:27.904202+00:00
-- url     : https://prove2.me/submissions/70d66359-0679-4b8d-a798-8e8a1bc1b686

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_norm_log_le_defect

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    Summable (fun i => ‖Complex.log (F i)‖) := by
  apply (hb.mul_left (3/2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  exact (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
    (mul_le_mul_of_nonneg_left (hF i) (by norm_num))
end OAI.SevenEighths.ProbeEuler
