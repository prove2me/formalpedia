-- Prove2me | solution 1 for GlobalTheory.FlagVolume.lintegral_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:50.967536+00:00
-- url     : https://prove2.me/submissions/a41656cf-8799-4e84-b03e-1578aacbaa10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume
namespace GlobalTheory.FlagVolume
theorem _root_.solution {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹)
      (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r := by
    intro r _
    have hp : 0 < A + r ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add A
    have h2 := ((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv
      (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)
    refine h2.fun_neg.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹ := fun r hr ↦ by
    have : 0 < r := hr
    positivity
  have hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]
  simp
end GlobalTheory.FlagVolume
