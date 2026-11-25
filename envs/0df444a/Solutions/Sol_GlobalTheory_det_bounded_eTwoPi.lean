-- Prove2me | solution 1 for GlobalTheory.det_bounded_eTwoPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:30.921929+00:00
-- url     : https://prove2.me/submissions/cd02b4ea-faad-4262-8052-410ea8666eab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPi
import Theorems.Thm_GlobalTheory_tendsto_tsum_coeff_mul_pow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open Filter Topology
namespace GlobalTheory
theorem _root_.solution : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith
end GlobalTheory
