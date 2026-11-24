-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:58.644861+00:00
-- url     : https://prove2.me/submissions/b01f1d96-ce76-4690-9f49-716072a347a9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman
namespace GlobalTheory.CompanionTheory.Casselman
theorem _root_.solution {X : Type} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ) (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (Function.onFun Disjoint E))
    (c D B r : ℝ) (hc : 0 < c) (hB : 0 < B) (hr : 0 ≤ r)
    (hμ : ∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j))
    (hlow : ∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) : D * r ^ p < 1 := by
  by_contra hcon
  have hq : 1 ≤ D * r ^ p := not_lt.1 hcon
  have hrp : 0 ≤ r ^ p := Real.rpow_nonneg hr p
  have hD : 0 ≤ D := by
    by_contra hD
    have : D * r ^ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.1 hD).le hrp
    linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hI := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top).1
    hf.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal hp.le] at hI
  have ha : 0 < c * B ^ p := mul_pos hc (Real.rpow_pos_of_pos hB p)
  have hterm : ∀ j : ℕ, ENNReal.ofReal (c * B ^ p) ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
    intro j
    have hBr : 0 ≤ B * r ^ j := mul_nonneg hB.le (pow_nonneg hr j)
    have h1 : ∫⁻ _ in E j, ENNReal.ofReal ((B * r ^ j) ^ p) ∂μ ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
      refine setLIntegral_mono' (hE j) fun x hx => ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg hBr hp.le, Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hlow j x hx)) hp.le
    rw [setLIntegral_const] at h1
    refine le_trans ?_ h1
    refine le_trans ?_ (mul_le_mul_right (hμ j) _)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBr p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (B * r ^ j) ^ p * (c * D ^ j) = c * B ^ p * (D * r ^ p) ^ j := by
      rw [Real.mul_rpow hB.le (pow_nonneg hr j), mul_pow, ← Real.rpow_natCast r j,
        ← Real.rpow_natCast (r ^ p) j, ← Real.rpow_mul hr, ← Real.rpow_mul hr, mul_comm (j : ℝ) p]
      ring
    rw [e]
    exact le_mul_of_one_le_right ha.le (one_le_pow₀ hq)
  have htop : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ)
      (ENNReal.ofReal_pos.2 ha).ne']
    exact ENNReal.tsum_le_tsum hterm
  have hle : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [← lintegral_iUnion hE hdisj]
    exact setLIntegral_le_lintegral _ _
  rw [htop] at hle
  exact absurd (lt_of_le_of_lt hle hI) (lt_irrefl _)
end GlobalTheory.CompanionTheory.Casselman
