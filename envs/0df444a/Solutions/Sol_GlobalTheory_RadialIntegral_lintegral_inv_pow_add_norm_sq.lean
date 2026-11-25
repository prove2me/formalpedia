-- Prove2me | solution 1 for GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:44.985902+00:00
-- url     : https://prove2.me/submissions/f9ecc55f-9015-4228-b480-fa14f4238142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralComplexInvPowAddNormSq
import Theorems.Thm_GlobalTheory_RadialIntegral_radial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.RadialIntegral
namespace GlobalTheory.RadialIntegral
theorem _root_.solution (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring
end GlobalTheory.RadialIntegral
