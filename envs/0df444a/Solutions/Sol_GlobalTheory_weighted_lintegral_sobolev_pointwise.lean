-- Prove2me | solution 1 for GlobalTheory.weighted_lintegral_sobolev_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:22.8018+00:00
-- url     : https://prove2.me/submissions/92a469b6-6b55-4fbb-b487-9bb2b0b24117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwise
import Theorems.Thm_GlobalTheory_T_lintegral_unit_ball_ray_average_le
import Theorems.Thm_P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453


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
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  intro E _ _ _ _ _ μ _ m hdim
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set B : Set E := Metric.closedBall (0:E) 1 with hB
  set β : ℝ≥0∞ := μ B with hβ
  have hβ0 : β ≠ 0 := (Metric.measure_closedBall_pos μ (0:E) one_pos).ne'
  have hβtop : β ≠ ∞ := (measure_closedBall_lt_top).ne
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (m.factorial : ℝ)) * ENNReal.ofReal (1 / ((m : ℝ) + 1)) with hc
  refine ⟨2 * c / β, ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hβ0, ?_⟩
  intro F _ _ _ G hG hdec k x
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ x
  set S : Set E := B ∩ {v | 0 ≤ φ v} with hS
  have hSmeas : MeasurableSet S :=
    Metric.isClosed_closedBall.measurableSet.inter (measurableSet_le measurable_const φ.continuous.measurable)
  have hβS : β ≤ 2 * μ S := by
    have hsub : B ⊆ S ∪ -S := by
      intro v hv
      by_cases h : 0 ≤ φ v
      · exact Or.inl ⟨hv, h⟩
      · right
        refine ⟨?_, ?_⟩
        · simpa [hB, Metric.mem_closedBall, norm_neg] using hv
        · show 0 ≤ φ (-v)
          rw [map_neg]
          linarith [not_le.mp h]
    calc β ≤ μ (S ∪ -S) := measure_mono hsub
      _ ≤ μ S + μ (-S) := measure_union_le _ _
      _ = 2 * μ S := by rw [Measure.measure_neg, two_mul]
  have hDc : Continuous (fun z => ‖iteratedFDeriv ℝ (m + 1) G z‖) :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((m+1 : ℕ) : ℕ∞) ≤ ⊤))).norm
  set Ψ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x + y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + y)‖) with hΨ
  have hΨm : Measurable Ψ := by
    apply ENNReal.measurable_ofReal.comp
    exact (((continuous_const.add continuous_id).norm.pow k).mul
      (hDc.comp (continuous_const.add continuous_id))).measurable
  set a : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) with ha
  set H : E → ℝ≥0∞ := fun v => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) with hH
  have hpt : ∀ v ∈ S, v ≠ 0 → a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    intro v hvS hv0
    have hray : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0) := by
      intro j hj
      refine (hdec j hj).comp ?_
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have h1 : Tendsto (fun t : ℝ => t * ‖v‖ + -‖x‖) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hvpos)
      refine tendsto_atTop_mono (fun t => ?_) h1
      have e1 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
        simpa using norm_sub_le (x + t • v) x
      have e2 : t * ‖v‖ ≤ ‖t • v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)
      show t * ‖v‖ + -‖x‖ ≤ ‖x + t • v‖
      linarith
    have hR := GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' G m x v hG hray
    have hxk : (0:ℝ) ≤ ‖x‖ ^ k := by positivity
    calc a = ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal ‖G x‖ := by rw [ha, ENNReal.ofReal_mul hxk]
      _ ≤ ENNReal.ofReal (‖x‖ ^ k) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by gcongr
      _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (m.factorial : ℝ)) *
            (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v)) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
          have ht0 : (0:ℝ) ≤ t := le_of_lt ht
          have hmono : ‖x‖ ≤ ‖x + t • v‖ := by
            have h1 : φ x ≤ φ (x + t • v) := by
              rw [map_add, map_smul, smul_eq_mul]
              have : 0 ≤ φ v := hvS.2
              nlinarith
            have h2 : φ (x + t • v) ≤ ‖x + t • v‖ := by
              calc φ (x + t • v) ≤ |φ (x + t • v)| := le_abs_self _
                _ = ‖φ (x + t • v)‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖φ‖ * ‖x + t • v‖ := φ.le_opNorm _
                _ ≤ 1 * ‖x + t • v‖ := mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
                _ = ‖x + t • v‖ := one_mul _
            have h0 : φ x = ‖x‖ := by simpa using hφx
            linarith
          have hpow : ‖x‖ ^ k ≤ ‖x + t • v‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hmono k
          have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
          have hP : 0 ≤ t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖) := by positivity
          have hA : 0 ≤ t ^ m * ‖v‖ ^ (m + 1) := by positivity
          have hf : 0 ≤ 1 / (m.factorial : ℝ) := by positivity
          show ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) ≤
            ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) *
              ENNReal.ofReal (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖))
          rw [← ENNReal.ofReal_mul hxk, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hf]
          apply ENNReal.ofReal_le_ofReal
          have e : 1 / (m.factorial : ℝ) * (t ^ m * ‖v‖ ^ (m + 1) * (‖x + t • v‖ ^ k *
              ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) = ‖x + t • v‖ ^ k * (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hpow hP
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ v ∂(μ.restrict S), a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    rw [ae_restrict_iff' hSmeas]
    have h0 : ∀ᵐ v ∂μ, v ≠ (0:E) := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [h0] with v hv0 hvS
    exact hpt v hvS hv0
  have hI : ∫⁻ y, Ψ y ∂μ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ :=
    lintegral_add_left_eq_self (μ := μ) (fun z => ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖)) x
  have hmain : μ S * a ≤ c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
    calc μ S * a = ∫⁻ _ in S, a ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ v in S, ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v ∂μ := lintegral_mono_ae hae
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in S, H v ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in B, H v ∂μ := by
          gcongr
          exact inter_subset_left
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ) := by
          gcongr
          exact GlobalTheory.T.lintegral_unit_ball_ray_average_le μ Ψ m hΨm hdim
      _ = c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
          rw [hI, hc, mul_assoc]
  have h2 : a * β ≤ 2 * (c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ) := by
    calc a * β ≤ a * (2 * μ S) := by gcongr
      _ = 2 * (μ S * a) := by ring
      _ ≤ _ := by gcongr
  have h3 := (ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)).mpr h2
  calc a ≤ _ := h3
    _ = 2 * c / β * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
end GlobalTheory
