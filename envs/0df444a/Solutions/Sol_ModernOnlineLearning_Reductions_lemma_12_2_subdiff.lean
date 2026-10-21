-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.lemma_12_2_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:33:47.875179+00:00
-- url     : https://prove2.me/submissions/3777f6b7-a0c1-4406-acf5-c2f1026b55fc

import Definitions.Def_ModernOnlineLearning_Reductions_Setting

set_option autoImplicit false
open ModernOnlineLearning.Reductions

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V)
    (x y : E) (hx : x ∉ V) (hy : IsProjection V x y) :
    ∀ g : E →L[ℝ] ℝ,
      IsSubgradient (distance V) x g ↔
        ‖g‖ = 1 ∧ g (x - y) = ‖x - y‖ ∧ ∀ u ∈ V, g (u - y) ≤ 0  := by
  intro g
  have hy0 : distance V y = 0 := Metric.infDist_zero_of_mem hy.1
  have hxy : 0 < ‖x-y‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    exact hx (heq ▸ hy.1)
  have hnorm (v : E) : g v ≤ ‖g‖ * ‖v‖ :=
    (le_abs_self (g v)).trans (by simpa only [Real.norm_eq_abs] using g.le_opNorm v)
  constructor
  · intro hg
    have hup (v : E) : g v ≤ ‖v‖ := by
      have hs := hg (x+v)
      have hd := Metric.infDist_le_infDist_add_dist (x := x+v) (y := x) (s := V)
      simp only [add_sub_cancel_left] at hs
      rw [dist_eq_norm, add_sub_cancel_left] at hd
      change distance V (x+v) ≤ distance V x + ‖v‖ at hd
      linarith
    have hle : ‖g‖ ≤ 1 := by
      apply g.opNorm_le_bound zero_le_one
      intro v
      rw [one_mul, Real.norm_eq_abs, abs_le]
      constructor
      · have h := hup (-v)
        simp only [map_neg, norm_neg] at h
        linarith
      · exact hup v
    have hs := hg y
    rw [hy0, ← hy.2] at hs
    have hval : g (x-y) = ‖x-y‖ := by
      have hn := hnorm (x-y)
      have hc := mul_le_mul_of_nonneg_right hle (norm_nonneg (x-y))
      simp only [map_sub] at hs hn ⊢
      nlinarith
    have hge : 1 ≤ ‖g‖ := by
      have hn := hnorm (x-y)
      rw [hval] at hn
      nlinarith
    refine ⟨hle.antisymm hge, hval, ?_⟩
    intro u hu
    have hs := hg u
    have hu0 : distance V u = 0 := Metric.infDist_zero_of_mem hu
    rw [hu0, ← hy.2] at hs
    simp only [map_sub] at hval hs ⊢
    linarith
  · rintro ⟨hgn, hval, hnormal⟩ z
    change distance V x + g (z-x) ≤ Metric.infDist z V
    apply (Metric.le_infDist hV).mpr
    intro u hu
    have hn := hnorm (z-u)
    rw [hgn, one_mul] at hn
    have hc := hnormal u hu
    rw [dist_eq_norm, ← hy.2]
    simp only [map_sub] at hn hc hval ⊢
    linarith

