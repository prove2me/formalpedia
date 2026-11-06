-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.normalProduct_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:04.241787+00:00
-- url     : https://prove2.me/submissions/71f4767b-72e6-4fdc-ad6a-3f7058a041d2

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_norm_log_le_defect
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_product_eq_exp_log

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution {ι : Type*} (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : Summable b)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i s, s ∈ U → ‖F i s-1‖ ≤ b i)
    (hhalf : ∀ i, b i ≤ 1/2) :
    AnalyticOnNhd ℂ (fun s => ∏' i, F i s) U := by
  have hlogs : ∀ i, DifferentiableOn ℂ (fun s => Complex.log (F i s)) U := by
    intro i
    apply (hF i).differentiableOn.clog
    intro s hs
    have hsmall : ‖F i s-1‖ < 1 := lt_of_le_of_lt ((hbound i s hs).trans (hhalf i)) (by norm_num)
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hb.mul_left (3/2)) hlogs hU
    (fun i s hs => (norm_log_le_defect _ ((hbound i s hs).trans (hhalf i))).trans
      (mul_le_mul_of_nonneg_left (hbound i s hs) (by norm_num)))
  apply DifferentiableOn.analyticOnNhd _ hU
  apply hd.cexp.congr
  intro s hs
  exact product_eq_exp_log (fun i => F i s) b hb (fun i => hbound i s hs) hhalf
end OAI.SevenEighths.ProbeEuler
