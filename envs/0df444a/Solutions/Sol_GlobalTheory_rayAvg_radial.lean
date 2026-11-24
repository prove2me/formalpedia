-- Prove2me | solution 1 for GlobalTheory.rayAvg_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:24.287633+00:00
-- url     : https://prove2.me/submissions/f93d958d-68cd-4cb2-825a-c86a93c51848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0; simp
  set g : ℝ → ℝ := fun t => r ^ (m + 1) / t ^ (m + 2) with hgdef
  have hrpow : ∀ t : ℝ, 0 < t → (t ^ (-(m:ℝ) - 2)) = (t ^ (m + 2))⁻¹ := by
    intro t ht
    rw [show (-(m:ℝ) - 2) = -(((m + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
      Real.rpow_natCast]
  have hcongr : EqOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) g (Ioi r) := by
    intro t ht
    simp only [hgdef, hrpow t (hpos.trans ht), div_eq_mul_inv]
  have hint : IntegrableOn g (Ioi r) :=
    (show IntegrableOn (fun t : ℝ => r ^ (m + 1) * t ^ (-(m:ℝ) - 2)) (Ioi r) volume from
      (integrableOn_Ioi_rpow_of_lt (a := -(m:ℝ) - 2)
        (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos).const_mul (r ^ (m + 1))).congr_fun
      hcongr measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := hpos.trans ht
    simp only [Pi.zero_apply, hgdef]; positivity
  have hval : ∫ t in Ioi r, g t = 1 / ((m:ℝ) + 1) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(m:ℝ) - 2) (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hpos]
    rw [show (-(m:ℝ) - 2 + 1) = -(((m + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    have : 0 < r ^ (m + 1) := pow_pos hpos _
    field_simp
    push_cast; ring
  have hgm : Measurable fun t : ℝ => ENNReal.ofReal (g t) :=
    ENNReal.measurable_ofReal.comp (by simp only [hgdef]; fun_prop)
  calc ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t * a := by
        refine le_trans (setLIntegral_le_lintegral _ _) (le_of_eq ?_)
        congr 1; ext t
        simp only [indicator, mem_Ici, hgdef]
        split_ifs <;> simp
    _ = (∫⁻ t, (Ici r).indicator (fun t => ENNReal.ofReal (g t)) t) * a :=
        lintegral_mul_const _ (hgm.indicator measurableSet_Ici)
    _ = (∫⁻ t in Ioi r, ENNReal.ofReal (g t)) * a := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]
end GlobalTheory
