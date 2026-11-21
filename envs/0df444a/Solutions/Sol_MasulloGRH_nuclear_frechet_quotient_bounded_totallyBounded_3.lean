-- Prove2me | solution 3 for MasulloGRH.nuclear_frechet_quotient_bounded_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:04:30.413042+00:00
-- url     : https://prove2.me/submissions/55145535-4ff5-4212-a527-6653f9922db2

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH Set Filter Topology

open scoped Pointwise

-- Finite-coordinate net and tail estimate adapted from marozols’s Prove2Me submission
-- 3744df69-4766-4cb3-9820-543bb26f8a14 for nuclear_bounded_precompact.
private theorem finite_net_of_domination {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (p q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ)
    (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) (hfq : ∀ n x, ‖f n x‖ ≤ q x)
    (hdom : ∀ x, p x ≤ ∑' n, c n * ‖f n x‖)
    (B : Set E) (M : ℝ) (hM0 : 0 < M) (hM : ∀ x ∈ B, q x ≤ M) (r : ℝ) (hr : 0 < r) :
    ∃ t : Finset E, ∀ z ∈ B, ∃ x ∈ t, p (z - x) < r := by
  classical
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
  refine ⟨rep y, hmemT, ?_⟩
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

theorem solution (X : Type*) [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X)
    (W : Submodule ℂ X) (hW : IsClosed (W : Set X)) (B : Set (X ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U := by
  classical
  intro U hU
  obtain ⟨ι, _, P, hP⟩ := hN.1.1
  have hadd := hP.topologicalAddGroup
  have hsmul := hP.continuousSMul
  have hpre : W.mkQ ⁻¹' U ∈ 𝓝 0 :=
    W.continuous_mkQ.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨⟨s,r⟩,hr,hsub⟩ := hP.hasBasis_zero_ball.mem_iff.mp hpre
  let p := s.sup P
  have hr : 0 < r := hr
  have hball : p.ball 0 r ⊆ W.mkQ ⁻¹' U := hsub
  have hpc : Continuous p := Seminorm.continuous (r := r)
    (hP.hasBasis_zero_ball.mem_of_mem (i := (s,r)) hr)
  obtain ⟨q,f,c,hqc,hc0,hcs,hfq,hdom⟩ := nuclear_quasinuclear_domination X hN p hpc
  let D := {x : X | q x < 1}
  have hD : D ∈ 𝓝 0 := (isOpen_lt hqc continuous_const).mem_nhds (by simp)
  have hqD : W.mkQ '' D ∈ 𝓝 0 := by simpa using W.isOpenMap_mkQ.image_mem_nhds hD
  obtain ⟨ρ,hρ⟩ := absorbs_iff_norm.mp (hB hqD)
  let M := max ρ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnorm : ‖(M : ℂ)‖ = M := by rw [Complex.norm_real, Real.norm_of_nonneg hM.le]
  obtain ⟨t,ht⟩ := finite_net_of_domination p q f c hc0 hcs hfq hdom
    {x | q x ≤ M} M hM (fun _ h => h) r hr
  refine ⟨t.image W.mkQ, ?_⟩
  intro y hy
  obtain ⟨_, ⟨z,hz,rfl⟩, he⟩ := hρ (M : ℂ) (by rw [hnorm]; exact le_max_left _ _) hy
  let x := (M : ℂ) • z
  have hx : q x ≤ M := by
    have hz1 : q z < 1 := hz
    change q ((M : ℂ) • z) ≤ M
    rw [map_smul_eq_mul, hnorm]
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hz1.le)]
  have hxy : W.mkQ x = y := (W.mkQ.map_smul _ _).trans he
  obtain ⟨a,ha,hd⟩ := ht x hx
  have hu : W.mkQ (x - a) ∈ U := by
    apply hball
    rwa [Seminorm.mem_ball_zero]
  exact ⟨W.mkQ a, Finset.mem_image_of_mem _ ha, W.mkQ (x - a), hu,
    by rw [map_sub, hxy]; exact add_sub_cancel _ _⟩
