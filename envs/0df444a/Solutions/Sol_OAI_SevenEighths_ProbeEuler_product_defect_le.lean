-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.product_defect_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:03.590004+00:00
-- url     : https://prove2.me/submissions/2ec1b447-981b-4c7a-8c79-ec07ad68d6ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_product_eq_exp_log
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_norm_log_sum_le

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2)
    (hsmall : (∑' i, b i) ≤ 1/6) : ‖(∏' i, F i)-1‖ ≤ 1/2 := by
  have hlog := norm_log_sum_le F b hb hF hhalf
  have hlog1 : ‖∑' i, Complex.log (F i)‖ ≤ 1 := by linarith
  rw [product_eq_exp_log F b hb hF hhalf]
  exact (Complex.norm_exp_sub_one_le hlog1).trans (by linarith)
end OAI.SevenEighths.ProbeEuler
