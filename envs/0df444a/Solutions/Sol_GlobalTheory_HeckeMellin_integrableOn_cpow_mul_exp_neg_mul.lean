-- Prove2me | solution 1 for GlobalTheory.HeckeMellin.integrableOn_cpow_mul_exp_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:27.418375+00:00
-- url     : https://prove2.me/submissions/889f3750-21eb-487c-863d-d80f1f73ede9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
open Set
namespace GlobalTheory.HeckeMellin
theorem _root_.solution {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent hw
  rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at h
  refine (IntegrableOn.congr_fun (h.const_mul (1 / (c : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le, Complex.ofReal_exp]
  push_cast
  have hne : (c : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hc.ne')
  field_simp
end GlobalTheory.HeckeMellin
