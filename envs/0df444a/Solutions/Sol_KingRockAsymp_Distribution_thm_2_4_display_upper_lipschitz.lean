-- Prove2me | solution 1 for KingRockAsymp.Distribution.thm_2_4_display_upper_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:29:36.666093+00:00
-- url     : https://prove2.me/submissions/a181d5b5-482e-4d9e-8256-b8381373b2eb

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution

theorem solution {n m : ℕ} (F : Rn n → Set (Rn m)) (x₀ : Rn n)
    (h0 : (0 : Rn m) ∈ F x₀)
    (hD : contingentDeriv (svInv F) 0 x₀ 0 = {0}) :
    ∃ U ∈ 𝓝 x₀, ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ᶠ y in 𝓝 (0 : Rn m), U ∩ svInv F y ⊆ closedBall x₀ (lam * ‖y‖) := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, ∃ y : Rn m, ∃ x : Rn n, ‖y‖ < 1 / ((k : ℝ) + 1) ∧
      ‖x - x₀‖ < 1 / ((k : ℝ) + 1) ∧ y ∈ F x ∧ ((k : ℝ) + 1) * ‖y‖ < ‖x - x₀‖ := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h := hcon (ball x₀ (1 / ((k : ℝ) + 1))) (ball_mem_nhds _ hk) ((k : ℝ) + 1)
      (by positivity)
    obtain ⟨y, hy, hyb⟩ := (h.and_eventually (ball_mem_nhds (0 : Rn m) hk)).exists
    rw [not_subset] at hy
    obtain ⟨x, ⟨hxU, hxF⟩, hxn⟩ := hy
    refine ⟨y, x, by simpa using hyb, by simpa [dist_eq_norm] using hxU, hxF, ?_⟩
    simpa [dist_eq_norm, not_le] using hxn
  choose y x hy hx hF hlt using key
  set t : ℕ → ℝ := fun k => ‖x k - x₀‖ with ht_def
  have tpos : ∀ k, 0 < t k := fun k => lt_of_le_of_lt (by positivity) (hlt k)
  set u : ℕ → Rn n := fun k => (t k)⁻¹ • (x k - x₀) with hu_def
  have hu : ∀ k, u k ∈ sphere (0 : Rn n) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, hu_def]
    simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (tpos k)]
    exact inv_mul_cancel₀ (tpos k).ne'
  obtain ⟨u0, hu0, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Rn n) 1).tendsto_subseq hu
  have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero (fun k => (tpos k).le) (fun k => (hx k).le) h1
  have htw : Tendsto (fun k => t (φ k)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0.comp hφ.tendsto_atTop,
      Eventually.of_forall fun k => tpos (φ k)⟩
  set v : ℕ → Rn m := fun k => (t k)⁻¹ • y k with hv_def
  have hv0 : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h1
    rw [hv_def]; simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (tpos k)]
    have := hlt k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [inv_mul_le_iff₀ (tpos k)]
    rw [div_eq_mul_inv, one_mul]
    rw [le_mul_inv_iff₀ hk]
    linarith [mul_comm ((k : ℝ) + 1) ‖y k‖]
  have hpair : Tendsto (fun k => (v (φ k), u (φ k))) atTop (𝓝 ((0 : Rn m), u0)) :=
    (hv0.comp hφ.tendsto_atTop).prodMk_nhds hlim
  have hmem : u0 ∈ contingentDeriv (svInv F) 0 x₀ 0 := by
    intro ε hε
    apply htw.frequently
    apply Eventually.frequently
    filter_upwards [hpair (ball_mem_nhds _ hε)] with k hk
    refine ⟨(v (φ k), u (φ k)), ?_, hk⟩
    refine ⟨(y (φ k), x (φ k)), hF (φ k), ?_⟩
    simp [hv_def, hu_def, smul_sub]
  rw [hD] at hmem
  have hn : ‖u0‖ = 1 := by simpa using hu0
  rw [mem_singleton_iff] at hmem
  rw [hmem, norm_zero] at hn
  exact zero_ne_one hn
