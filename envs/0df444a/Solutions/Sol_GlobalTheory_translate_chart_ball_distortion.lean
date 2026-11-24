-- Prove2me | solution 1 for GlobalTheory.translate_chart_ball_distortion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:47.16123+00:00
-- url     : https://prove2.me/submissions/ed3aff94-29e2-43b9-960e-df406266febf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TranslateChartBallDistortion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : V → G)
    (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e) (he0 : e 0 = 1)
    (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h))
    (hopen : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ,
      (fun g => e x * g) '' (e '' ball 0 r) ⊆ e '' ball x (κ * r) ∧
      e '' ball x r ⊆ (fun g => e x * g) '' (e '' ball 0 (κ * r)) := by
  set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  have hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2 := by
    have h3 : ε * (3 + 2 * κ) = (κ - 1) / 2 := by
      rw [hε]
      field_simp
    nlinarith [mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η →
      ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro a b ha hb
    have h := @hη (a, b) (by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt ha hb)
    simpa using h
  have hLc : ContinuousAt (fun x => L (e x)) 0 := hL.comp_of_eq he.continuousAt he0
  obtain ⟨η2, hη20, hη2⟩ := Metric.continuousAt_iff.mp hLc ε hε0
  have hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖ := by
    intro x hx v
    have h1 := hη2 (by rwa [dist_zero_right] : dist x 0 < η2)
    simp only [he0, hL1, dist_eq_norm] at h1
    have h2 := (L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))
  have hU : e '' ball 0 η ∈ 𝓝 (1 : G) := hopen η hη0
  have hφ : Continuous (fun p : V × V => e p.1 * e p.2) :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  have hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2) :=
    (he.comp continuous_fst).inv.mul (he.comp continuous_snd)
  have hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V)) :=
    hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  have hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈
      𝓝 ((0 : V), (0 : V)) :=
    hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  obtain ⟨η3, hη30, hη3⟩ := Metric.mem_nhds_iff.mp hφU
  obtain ⟨η4, hη40, hη4⟩ := Metric.mem_nhds_iff.mp hψU
  have hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη3 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη4 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have h0η : ‖(0 : V)‖ < η := by simpa using hη0
  refine ⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))),
    lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩
  intro x hx r hr
  rw [mem_ball_zero_iff] at hx
  obtain ⟨hr0, hrδ⟩ := hr
  have b1 : ‖x‖ < η / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have b2 : ‖x‖ < η2 := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : ‖x‖ < η3 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : ‖x‖ < η4 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have r1 : r < η / 2 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have r3 : r < η3 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 : r < η4 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0)) := by
    intro y
    rw [map_sub, he0, ← hm, ← hm, mul_one]
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨z, hz, hze⟩ := hφ' x y (by linarith) (by linarith)
    refine ⟨z, ?_, hze⟩
    rw [mem_ball, dist_eq_norm]
    have e1 := hD z x hz (by linarith)
    have e2 := hD y 0 (by linarith) h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hze, hmx y] at e1
    have nι : ‖ι (z - x)‖ = ‖z - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖ := by
      have h := norm_sub_norm_le (ι (z - x)) (L (e x) v)
      have h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖ := norm_sub_rev _ _
      linarith
    have t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖ := by
      have h := norm_sub_norm_le (L (e x) v) v
      linarith
    have t3 : ‖v‖ ≤ (1 + ε) * ‖y‖ := by
      have h := norm_sub_norm_le v (ι y)
      linarith
    have k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖ := by
      have := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith only [t1, t2, this]
    have k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r := mul_lt_mul_of_pos_left hy (by positivity)
    have k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r := by
      have h1 : (1 - ε) ^ 2 ≤ 1 - ε := by
        rw [sq]
        exact mul_le_of_le_one_left (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le
    have k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r) := by linarith only [k1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (by linarith)
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    have hwx := norm_sub_norm_le w x
    obtain ⟨y, hyη, hye⟩ := hψ' x w (by linarith) (by linarith)
    have hexy : e w = e x * e y := by rw [hye, mul_inv_cancel_left]
    refine ⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩
    rw [mem_ball_zero_iff]
    have e1 := hD w x (by linarith) (by linarith)
    have e2 := hD y 0 hyη h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hexy, hmx y] at e1
    have nι : ‖ι (w - x)‖ = ‖w - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖ := by
      have h := norm_sub_norm_le (L (e x) v) (ι (w - x))
      linarith
    have s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖ := by
      have h := norm_sub_norm_le v (L (e x) v)
      have h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖ := norm_sub_rev _ _
      linarith
    have s3 : (1 - ε) * ‖y‖ ≤ ‖v‖ := by
      have h := norm_sub_norm_le (ι y) v
      have h' : ‖ι y - v‖ = ‖v - ι y‖ := norm_sub_rev _ _
      linarith
    have k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)
      linarith only [this]
    have k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r := mul_lt_mul_of_pos_left hw (by linarith)
    have k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r := by
      linarith only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r) := by
      linarith only [k1, s2, s1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le
end GlobalTheory
