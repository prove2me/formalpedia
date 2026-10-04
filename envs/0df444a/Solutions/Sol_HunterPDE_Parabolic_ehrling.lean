-- Prove2me | solution 1 for HunterPDE.Parabolic.ehrling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:46:16.015928+00:00
-- url     : https://prove2.me/submissions/59038316-12b8-4132-9d14-eb2d6c8fc240

import Mathlib

set_option autoImplicit false

open Filter Topology in
theorem HunterPDE_Parabolic_ehrling_aux {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (i : X →L[ℝ] Y) (j : Y →L[ℝ] Z) (hj : Function.Injective j)
    (hcpt : IsCompactOperator i) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ u : X, ‖i u‖ ≤ ε * ‖u‖ + Cε * ‖j (i u)‖ := by
  by_contra h
  push_neg at h
  choose u hu using h
  set w : ℕ → X := fun n => u (n : ℝ) with hw
  have hwpos : ∀ n, 0 < ‖w n‖ := by
    intro n
    rw [norm_pos_iff]
    intro h0
    have := hu (n : ℝ)
    simp only [hw] at h0
    rw [h0] at this
    simp at this
  set v : ℕ → X := fun n => ‖w n‖⁻¹ • w n with hv
  have hvnorm : ∀ n, ‖v n‖ = 1 := by
    intro n
    simp only [hv, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hwpos n).ne'
  have hvineq : ∀ n : ℕ, ε + (n : ℝ) * ‖j (i (v n))‖ < ‖i (v n)‖ := by
    intro n
    have h1 := hu (n : ℝ)
    have hp := hwpos n
    have e1 : ‖i (v n)‖ = ‖w n‖⁻¹ * ‖i (w n)‖ := by
      simp only [hv, map_smul, norm_smul, norm_inv, norm_norm]
    have e2 : ‖j (i (v n))‖ = ‖w n‖⁻¹ * ‖j (i (w n))‖ := by
      simp only [hv, map_smul, norm_smul, norm_inv, norm_norm]
    rw [e1, e2]
    have h1' : ε * ‖w n‖ + (n : ℝ) * ‖j (i (w n))‖ < ‖i (w n)‖ := h1
    have hinv : 0 < ‖w n‖⁻¹ := inv_pos.mpr hp
    have := mul_lt_mul_of_pos_left h1' hinv
    have hc : ‖w n‖⁻¹ * ‖w n‖ = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith [this, hc]
  have hbound : ∀ n, ‖i (v n)‖ ≤ ‖i‖ := by
    intro n
    have := i.le_opNorm (v n)
    rw [hvnorm n, mul_one] at this
    exact this
  obtain ⟨K, hK, hsub⟩ := hcpt.image_closedBall_subset_compact (f := (i : X →ₗ[ℝ] Y)) 1
  have hmem : ∀ n, i (v n) ∈ K := by
    intro n
    apply hsub
    refine ⟨v n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hvnorm n]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  -- j (i (v n)) → 0
  have hj0 : Tendsto (fun n => j (i (v n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat ‖i‖)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    have := hvineq n
    have := hbound n
    nlinarith
  have hja : Tendsto (fun n => j (i (v (φ n)))) atTop (𝓝 (j a)) :=
    (j.continuous.tendsto a).comp hlim
  have hj0' : Tendsto (fun n => j (i (v (φ n)))) atTop (𝓝 0) :=
    hj0.comp hφ.tendsto_atTop
  have hja0 : j a = 0 := tendsto_nhds_unique hja hj0'
  have ha : a = 0 := hj (by rw [hja0, map_zero])
  have hnorm : Tendsto (fun n => ‖i (v (φ n))‖) atTop (𝓝 ‖a‖) := hlim.norm
  have hge : ε ≤ ‖a‖ := by
    refine ge_of_tendsto hnorm (Eventually.of_forall fun n => ?_)
    have := hvineq (φ n)
    have : 0 ≤ ((φ n : ℕ) : ℝ) * ‖j (i (v (φ n)))‖ := by positivity
    show ε ≤ ‖i (v (φ n))‖
    linarith
  rw [ha, norm_zero] at hge
  linarith

open Filter Topology in
theorem solution {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (i : X →L[ℝ] Y) (j : Y →L[ℝ] Z) (hi : Function.Injective i) (hj : Function.Injective j)
    (hcpt : IsCompactOperator i) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ u : X, ‖i u‖ ≤ ε * ‖u‖ + Cε * ‖j (i u)‖ := by
  exact HunterPDE_Parabolic_ehrling_aux i j hj hcpt ε hε
