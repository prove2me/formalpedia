-- Prove2me | solution 1 for GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:44.916837+00:00
-- url     : https://prove2.me/submissions/cb6bff15-e738-4925-b889-cd0567f2b93f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegrableExpNegAbs
open MeasureTheory Set
namespace GlobalTheory.IntegrableExpNegAbs
theorem _root_.solution {c : ℝ} (hc : (0 : ℝ) < c) :
    MeasureTheory.Integrable (fun (s : ℝ) ↦ Real.exp (-(c * |s|))) MeasureTheory.MeasureSpace.volume := by
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp only [abs_of_pos hx', neg_mul]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only [abs_of_nonpos hx', mul_neg, neg_neg]
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h
end GlobalTheory.IntegrableExpNegAbs
