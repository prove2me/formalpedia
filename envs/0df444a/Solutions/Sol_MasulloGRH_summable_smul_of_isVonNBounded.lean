-- Prove2me | solution 1 for MasulloGRH.summable_smul_of_isVonNBounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:31:26.831428+00:00
-- url     : https://prove2.me/submissions/00cb17d9-fab2-4376-aafb-343e68edfea5

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hL : IsHLCS G)
    (w : ℕ → G) (hw : Bornology.IsVonNBounded ℂ (Set.range w))
    (d : ℕ → ℂ) (hd : Summable (fun n => ‖d n‖)) :
    Summable (fun n => d n • w n) := by
  obtain ⟨⟨ι, _, p, hp⟩, _⟩ := hL
  have := hp.topologicalAddGroup
  set S : Finset ℕ → G := fun s => ∑ n ∈ s, d n • w n with hS
  -- seminorm estimate on finite sums
  have hsum_le : ∀ (q : Seminorm ℂ G) (t : Finset ℕ),
      q (∑ n ∈ t, d n • w n) ≤ ∑ n ∈ t, ‖d n‖ * q (w n) := by
    intro q t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine (map_add_le_add q _ _).trans ?_
      rw [map_smul_eq_mul]
      linarith
  have hcauchy : IsCauchyFilter (map S atTop) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    obtain ⟨I, ε, hε, hball⟩ := (hp.mem_nhds_iff 0 U).1 hU
    obtain ⟨M, hM, hMw⟩ := (hp.isVonNBounded_iff_finset_seminorm_bounded).1 hw I
    have hδ : 0 < ε / (4 * M) := by positivity
    obtain ⟨s0, hs0⟩ := hd.vanishing (Metric.ball_mem_nhds (0 : ℝ) hδ)
    have htail : ∀ t : Finset ℕ, Disjoint t s0 →
        (I.sup p) (∑ n ∈ t, d n • w n) ≤ M * (ε / (4 * M)) := by
      intro t ht
      have h1 := hs0 t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero,
        abs_of_nonneg (Finset.sum_nonneg fun n _ => norm_nonneg _)] at h1
      refine (hsum_le _ t).trans ?_
      calc ∑ n ∈ t, ‖d n‖ * (I.sup p) (w n) ≤ ∑ n ∈ t, ‖d n‖ * M :=
            Finset.sum_le_sum fun n _ =>
              mul_le_mul_of_nonneg_left (hMw _ (Set.mem_range_self n)).le (norm_nonneg _)
        _ = M * ∑ n ∈ t, ‖d n‖ := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ M * (ε / (4 * M)) := mul_le_mul_of_nonneg_left h1.le hM.le
    refine ⟨S '' {s | s0 ⊆ s}, image_mem_map (mem_atTop s0), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    apply hball
    rw [Seminorm.mem_ball, sub_zero]
    simp only [hS]
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    have h1 := htail (s \ s') (Finset.disjoint_of_subset_right hs' Finset.sdiff_disjoint)
    have h2 := htail (s' \ s) (Finset.disjoint_of_subset_right hs Finset.sdiff_disjoint)
    have hMe : M * (ε / (4 * M)) = ε / 4 := by field_simp
    calc (I.sup p) (∑ n ∈ s \ s', d n • w n - ∑ n ∈ s' \ s, d n • w n)
        ≤ (I.sup p) (∑ n ∈ s \ s', d n • w n) + (I.sup p) (∑ n ∈ s' \ s, d n • w n) :=
          map_sub_le_add _ _ _
      _ ≤ ε / 4 + ε / 4 := by rw [hMe] at h1 h2; linarith
      _ < ε := by linarith
  obtain ⟨x, hx⟩ := hC.2 _ hcauchy
  exact ⟨x, hx⟩
