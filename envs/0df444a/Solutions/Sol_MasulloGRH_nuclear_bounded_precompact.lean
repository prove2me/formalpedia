-- Prove2me | solution 1 for MasulloGRH.nuclear_bounded_precompact
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:00:35.241977+00:00
-- url     : https://prove2.me/submissions/3744df69-4766-4cb3-9820-543bb26f8a14

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH Set Filter Topology

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ V ∈ 𝓝 (0 : E), ∃ t : Finset E, B ⊆ ⋃ x ∈ t, {y : E | y - x ∈ V} := by
  classical
  intro V hV
  obtain ⟨ι, _, P, hP⟩ := hE.1.1
  have hadd : IsTopologicalAddGroup E := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hP.continuousSMul
  -- `V` contains the open ball of radius `r` of a continuous seminorm `p`
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hV
  have hr : 0 < r := hr
  obtain ⟨p, hp⟩ : ∃ p : Seminorm ℂ E, p = s.sup P := ⟨_, rfl⟩
  have hsub : p.ball 0 r ⊆ V := by rw [hp]; exact hsub
  have hpc : Continuous p := by
    rw [hp]
    exact Seminorm.continuous (r := r) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, r)) hr)
  -- quasinuclear domination of `p`
  obtain ⟨q, f, c, hqc, hc0, hcs, hfq, hdom⟩ := nuclear_quasinuclear_domination E hE p hpc
  -- `q` is bounded on `B`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
    have hq1 : {x : E | q x < 1} ∈ 𝓝 (0 : E) :=
      (isOpen_lt hqc continuous_const).mem_nhds (by simp)
    obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
    refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
    have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
    obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
    have hy' : q y < 1 := hy
    change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
    rw [map_smul_eq_mul, hnorm]
    nlinarith [le_max_right ρ 1, apply_nonneg q y]
  -- summability of the dominating series
  have hsum : ∀ x : E, Summable fun n => c n * ‖f n x‖ := fun x =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hfq n x) (hc0 n)) (hcs.mul_right (q x))
  have hCtot : 0 ≤ ∑' n, c n := tsum_nonneg hc0
  -- choose the cut-off `N` making the tail of `c` small
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' k, c (k + N) < r / (4 * M) := by
    have ht : Tendsto (fun i => ∑' k, c (k + i)) atTop (𝓝 0) := tendsto_sum_nat_add c
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / (4 * M)))).exists
  -- the finite-dimensional head
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ∑' n, c n ≤ r / 2 := by
    refine ⟨r / (2 * (∑' n, c n + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  let Φ : E → (Fin N → ℂ) := fun x n => f n x
  have hbdd : TotallyBounded (Φ '' B) := by
    refine (isCompact_closedBall (0 : Fin N → ℂ) M).totallyBounded.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hM0.le]
    exact fun n => (hfq n x).trans (hM x hx)
  obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.1 hbdd (δ / 2) (by positivity)
  -- representatives in `B` of the centres
  let rep : (Fin N → ℂ) → E := fun y =>
    if h : ∃ x ∈ B, Φ x ∈ Metric.ball y (δ / 2) then h.choose else 0
  refine ⟨htfin.toFinset.image rep, fun z hz => ?_⟩
  obtain ⟨y, hyt, hzy⟩ : ∃ y ∈ t, Φ z ∈ Metric.ball y (δ / 2) := by
    simpa using htcov (mem_image_of_mem Φ hz)
  have hex : ∃ x ∈ B, Φ x ∈ Metric.ball y (δ / 2) := ⟨z, hz, hzy⟩
  have hrep : rep y = hex.choose := dif_pos hex
  obtain ⟨hxB, hxy⟩ := hex.choose_spec
  rw [← hrep] at hxB hxy
  have hmemT : rep y ∈ htfin.toFinset.image rep :=
    Finset.mem_image_of_mem rep (htfin.mem_toFinset.2 hyt)
  simp only [mem_iUnion, exists_prop]
  refine ⟨rep y, hmemT, hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  -- estimates for `w = z - rep y`
  have hdist : dist (Φ z) (Φ (rep y)) < δ := by
    have h1 := Metric.mem_ball.1 hzy
    have h2 := Metric.mem_ball.1 hxy
    calc dist (Φ z) (Φ (rep y)) ≤ dist (Φ z) y + dist (Φ (rep y)) y := dist_triangle_right _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 h2
      _ = δ := by ring
  have hhead : ∀ n, n < N → ‖f n (z - rep y)‖ ≤ δ := by
    intro n hn
    have h1 : ‖(Φ z - Φ (rep y)) ⟨n, hn⟩‖ ≤ ‖Φ z - Φ (rep y)‖ := norm_le_pi_norm _ _
    have h2 : (Φ z - Φ (rep y)) ⟨n, hn⟩ = f n (z - rep y) := by
      simp [Φ, map_sub]
    rw [h2, ← dist_eq_norm] at h1
    exact h1.trans hdist.le
  have hqw : q (z - rep y) ≤ 2 * M := by
    have h1 : q (z - rep y) ≤ q z + q (rep y) := map_sub_le_add q z (rep y)
    linarith [hM z hz, hM _ hxB]
  have hsplit := (hsum (z - rep y)).sum_add_tsum_nat_add N
  have h1 : ∑ n ∈ Finset.range N, c n * ‖f n (z - rep y)‖ ≤ δ * ∑' n, c n := by
    calc ∑ n ∈ Finset.range N, c n * ‖f n (z - rep y)‖
        ≤ ∑ n ∈ Finset.range N, c n * δ :=
          Finset.sum_le_sum fun n hn =>
            mul_le_mul_of_nonneg_left (hhead n (Finset.mem_range.1 hn)) (hc0 n)
      _ = δ * ∑ n ∈ Finset.range N, c n := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ δ * ∑' n, c n :=
          mul_le_mul_of_nonneg_left (hcs.sum_le_tsum _ fun n _ => hc0 n) hδ0.le
  have hcsN : Summable fun k => c (k + N) := (summable_nat_add_iff N).2 hcs
  have h2 : ∑' k, c (k + N) * ‖f (k + N) (z - rep y)‖ ≤ (∑' k, c (k + N)) * (2 * M) := by
    rw [← tsum_mul_right]
    refine ((summable_nat_add_iff N).2 (hsum (z - rep y))).tsum_le_tsum (fun k => ?_)
      (hcsN.mul_right _)
    exact mul_le_mul_of_nonneg_left ((hfq _ _).trans hqw) (hc0 _)
  have h3 : (∑' k, c (k + N)) * (2 * M) < r / 2 := by
    have := mul_lt_mul_of_pos_right hN (by positivity : (0 : ℝ) < 2 * M)
    calc (∑' k, c (k + N)) * (2 * M) < r / (4 * M) * (2 * M) := this
      _ = r / 2 := by field_simp; ring
  calc p (z - rep y) ≤ ∑' n, c n * ‖f n (z - rep y)‖ := hdom _
    _ = ∑ n ∈ Finset.range N, c n * ‖f n (z - rep y)‖
          + ∑' k, c (k + N) * ‖f (k + N) (z - rep y)‖ := hsplit.symm
    _ < r := by linarith
