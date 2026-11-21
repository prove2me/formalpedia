-- Prove2me | solution 1 for MasulloGRH.compact_sot_tendsto_norm
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:42:25.211174+00:00
-- url     : https://prove2.me/submissions/beaa4f0f-b041-4bc3-b539-c76e514515bd

import Mathlib

set_option autoImplicit false

open Filter Topology Metric

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A Q : H →L[ℂ] H) (hA : IsCompactOperator A) (Qm : ℕ → H →L[ℂ] H)
    (hQ : ∀ u : H, Filter.Tendsto (fun m => Qm m u) Filter.atTop (nhds (Q u))) :
    Filter.Tendsto (fun m => Qm m ∘L A) Filter.atTop (nhds (Q ∘L A)) := by
  -- the differences `D m = Qm m - Q` tend to zero pointwise
  let D : ℕ → H →L[ℂ] H := fun m => Qm m - Q
  have hD : ∀ u : H, Tendsto (fun m => D m u) atTop (𝓝 0) := by
    intro u
    have h := (hQ u).sub_const (Q u)
    simpa [D] using h
  -- uniform boundedness
  obtain ⟨C, hC⟩ : ∃ C, ∀ m, ‖D m‖ ≤ C := by
    apply banach_steinhaus
    intro u
    have hb := Metric.isBounded_range_of_tendsto _ (hD u)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
    exact ⟨C, fun m => hC _ ⟨m, rfl⟩⟩
  set L : ℝ := max C 0 + 1 with hL
  have hL0 : 0 < L := by
    have := le_max_right C 0
    linarith
  have hDL : ∀ m, ‖D m‖ ≤ L := fun m => (hC m).trans (by
    have := le_max_left C 0
    linarith)
  -- the image of the unit ball is relatively compact
  have hK : IsCompact (closure (A '' closedBall (0 : H) 1)) :=
    hA.isCompact_closure_image_closedBall 1
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * L) := by positivity
  obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / (3 * L)) hδ
  have hev : ∀ᶠ m in atTop, ∀ y ∈ t, ‖D m y‖ < ε / 3 := by
    rw [Filter.eventually_all_finite htfin]
    intro y _
    have h := (hD y).eventually (Metric.ball_mem_nhds (0 : H) (by positivity : 0 < ε / 3))
    filter_upwards [h] with m hm
    simpa using hm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
  change ‖D m ∘L A‖ < ε
  have hunit : ∀ x : H, ‖x‖ ≤ 1 → ‖D m (A x)‖ ≤ 2 * ε / 3 := by
    intro x hx
    have hxK : A x ∈ closure (A '' closedBall (0 : H) 1) :=
      subset_closure ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩
    obtain ⟨y, hyt, hy⟩ : ∃ y ∈ t, A x ∈ ball y (ε / (3 * L)) := by
      simpa using htcov hxK
    have h1 : ‖D m (A x - y)‖ ≤ L * (ε / (3 * L)) := by
      refine ((D m).le_opNorm _).trans ?_
      have h2 : ‖A x - y‖ ≤ ε / (3 * L) := by
        rw [← dist_eq_norm]
        exact (mem_ball.1 hy).le
      exact mul_le_mul (hDL m) h2 (norm_nonneg _) hL0.le
    have h3 : L * (ε / (3 * L)) = ε / 3 := by
      field_simp
    have h4 := hN m hm y hyt
    have h5 : D m (A x) = D m (A x - y) + D m y := by
      rw [← map_add, sub_add_cancel]
    rw [h5]
    refine (norm_add_le _ _).trans ?_
    rw [h3] at h1
    linarith
  have hbound : ‖D m ∘L A‖ ≤ 2 * ε / 3 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    by_cases hx : x = 0
    · subst hx
      simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := hunit (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hxn.le),
          inv_mul_cancel₀ hxn.ne'])
      rw [map_smul, map_smul, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 hxn.le), inv_mul_le_iff₀ hxn] at h1
      rw [ContinuousLinearMap.comp_apply]
      linarith
  linarith
