-- Prove2me | solution 1 for ModernOnlineLearning.OMD.theorem_6_9
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:09:39.66998+00:00
-- url     : https://prove2.me/submissions/e68848f3-5c81-4be0-a21b-715ff36f7909

import Definitions.Def_ModernOnlineLearning_OMD_Defs

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.OMD

private lemma strong_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (f : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn D lam f)
    (y x : E) (hy : y ∈ D) (hx : x ∈ D) (g : E →L[ℝ] ℝ)
    (hg : IsSubgradientOn D f y g) :
    f y + g (x - y) + lam / 2 * ‖y - x‖ ^ 2 ≤ f x := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖y - x‖ ^ 2) ≤ f x - f y - g (x - y) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv := hstrong.1 hy hx ha ht.le hab
    have hm := hg _ hv
    have hs := hstrong.2 hy hx ha ht.le hab
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hm hs ⊢
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖y - x‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : lam / 2 * ‖y - x‖ ^ 2 ≤ f x - f y - g (x - y) := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hsegment t ht ht1
  linarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (D : Set E) (f : E → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hclosed : IsClosedOnDomain D f)
    (hstrong : StrongConvexOn D lam f)
    (hsub : ∃ y ∈ D, ∃ g : E →L[ℝ] ℝ, IsSubgradientOn D f y g) :
    ∃! x : E, x ∈ D ∧ ∀ z ∈ D, f x ≤ f z := by
  obtain ⟨y, hy, g, hg⟩ := hsub
  have hlevel : ∀ b : ℝ, IsClosed {z : E | z ∈ D ∧ f z ≤ b} := by
    intro b
    exact hclosed.preimage (continuous_id.prodMk continuous_const)
  let K : Set E := {z | z ∈ D ∧ f z ≤ f y}
  have hKclosed : IsClosed K := hlevel (f y)
  have hKy : y ∈ K := ⟨hy, le_rfl⟩
  have hKbound : K ⊆ Metric.closedBall y (2 * ‖g‖ / lam) := by
    intro z hz
    have hq := strong_support D f lam hstrong y z hy hz.1 g hg
    rw [norm_sub_rev y z] at hq
    have ho : |g (z - y)| ≤ ‖g‖ * ‖z - y‖ := by
      simpa only [Real.norm_eq_abs] using g.le_opNorm (z - y)
    have hlo := (abs_le.mp ho).1
    have hr : ‖z - y‖ ≤ 2 * ‖g‖ / lam := by
      apply (le_div_iff₀ hlam).mpr
      by_cases heq : ‖z - y‖ = 0
      · simpa [heq] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg g))
      · have hp : 0 < ‖z - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm heq)
        have hf : f z ≤ f y := hz.2
        nlinarith
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hr
  have hKcompact : IsCompact K :=
    (isCompact_closedBall y (2 * ‖g‖ / lam)).of_isClosed_subset hKclosed hKbound
  have hls : LowerSemicontinuousOn f K := by
    apply lowerSemicontinuousOn_iff_preimage_Iic.mpr
    intro b
    refine ⟨{z | z ∈ D ∧ f z ≤ b}, hlevel b, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hb⟩
      exact ⟨hz, hz.1, hb⟩
    · rintro ⟨hz, _, hb⟩
      exact ⟨hz, hb⟩
  obtain ⟨x, hx, hmin⟩ := hls.exists_isMinOn ⟨y, hKy⟩ hKcompact
  have hglobal : ∀ z ∈ D, f x ≤ f z := by
    intro z hz
    by_cases hb : f z ≤ f y
    · exact hmin ⟨hz, hb⟩
    · exact hx.2.trans (le_of_lt (lt_of_not_ge hb))
  refine ⟨x, ⟨hx.1, hglobal⟩, ?_⟩
  intro z hz
  by_contra hne
  have hp : 0 < ‖z - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hv : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • x ∈ D :=
    hstrong.1 hz.1 hx.1 (by norm_num) (by norm_num) (by norm_num)
  have hmid := hstrong.2 hz.1 hx.1
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have hmx := hglobal _ hv
  have hzx := hz.2 x hx.1
  nlinarith [mul_pos hlam hp]

