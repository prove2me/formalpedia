-- Prove2me | solution 1 for NoHair.Weyl.kerr_weyl_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:32:55.984271+00:00
-- url     : https://prove2.me/submissions/836aecb9-94a2-429d-bdf6-2f1e826c97c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_Weyl_kerr_chart_reconstruction
import Theorems.Thm_NoHair_Weyl_kerr_reduced_field_equations

open NoHair NoHair.Weyl Set Filter Topology

private theorem prolate_gt_abs (ℓ : ℝ) (p : OrbitPoint) : |p.2| < prolateRadius ℓ p := by
  have side (x : ℝ) : |x| < Real.sqrt (Real.exp (2*p.1)+x^2) := by
    rw [← Real.sqrt_sq_eq_abs x]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith [Real.exp_pos (2*p.1)])
  have h := abs_add_le (p.2-ℓ) (p.2+ℓ)
  rw [show p.2-ℓ+(p.2+ℓ) = 2*p.2 by ring, abs_mul, abs_of_pos (by norm_num : 0 < (2:ℝ))] at h
  unfold prolateRadius
  linarith [side (p.2-ℓ), side (p.2+ℓ)]

private theorem regular_kerr_ernst (m a : ℝ) (hm : 0 < m) :
    ContDiff ℝ 2 (kerrErnst m a).normSq ∧ ContDiff ℝ 2 (kerrErnst m a).twist ∧
    ∀ p, 0 < (kerrErnst m a).normSq p := by
  let ℓ := Real.sqrt (m^2-a^2)
  let R := prolateRadius ℓ
  let r := fun p => m+R p
  let c := fun p : OrbitPoint => p.2/R p
  have hRpos (p : OrbitPoint) : 0 < R p := (abs_nonneg _).trans_lt (prolate_gt_abs ℓ p)
  have hrpos (p : OrbitPoint) : 0 < r p := add_pos hm (hRpos p)
  have hR : ContDiff ℝ 2 R := by
    change ContDiff ℝ 2 (fun p : OrbitPoint =>
      (Real.sqrt (Real.exp (2*p.1)+(p.2-ℓ)^2)+Real.sqrt (Real.exp (2*p.1)+(p.2+ℓ)^2))/2)
    fun_prop (disch := first | positivity | intro q; positivity)
  have hr : ContDiff ℝ 2 r := contDiff_const.add hR
  have hc : ContDiff ℝ 2 c := contDiff_snd.div hR (fun p => (hRpos p).ne')
  have hden (p : OrbitPoint) : r p ^ 2 + a^2 * c p ^ 2 ≠ 0 := by
    have := hrpos p
    positivity
  refine ⟨?_,?_,?_⟩
  · change ContDiff ℝ 2 (fun p => kerrAxialNorm m a (r p) (c p))
    unfold kerrAxialNorm
    fun_prop (disch := apply hden)
  · change ContDiff ℝ 2 (fun p => kerrAxialTwist m a (r p) (c p))
    unfold kerrAxialTwist
    fun_prop (disch := apply hden)
  · intro p
    have hcos : |c p| < 1 := by
      change |p.2 / R p| < 1
      rw [abs_div, abs_of_pos (hRpos p), div_lt_iff₀ (hRpos p), one_mul]
      exact prolate_gt_abs ℓ p
    have hb := abs_lt.mp hcos
    have hS : 0 < 1-c p^2 := by
      nlinarith [mul_pos (show 0 < 1-c p by linarith [hb.2])
        (show 0 < 1+c p by linarith [hb.1])]
    have := hrpos p
    change 0 < kerrAxialNorm m a (r p) (c p)
    unfold kerrAxialNorm
    positivity

private theorem dense_off_axis (m a : ℝ) : kerrNewmanDOC m a 0 ⊆ closure (offAxisExterior m a) := by
  intro y hy
  by_cases h : y 1 ≠ 0 ∨ y 2 ≠ 0
  · exact subset_closure (show y ∈ offAxisExterior m a from ⟨hy,h⟩)
  push_neg at h
  let γ := fun t : ℝ => y + t • coordBasis 1
  have hopen : IsOpen (kerrNewmanDOC m a 0) := isOpen_lt continuous_const (continuous_ksRadius a)
  have hc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have h0 : γ 0 = y := by simp [γ]
  have ht₀ : Tendsto γ (𝓝[>] 0) (𝓝 (γ 0)) := hc.continuousAt.continuousWithinAt
  have ht : Tendsto γ (𝓝[>] 0) (𝓝 y) := h0 ▸ ht₀
  apply mem_closure_of_tendsto ht
  filter_upwards [ht (hopen.mem_nhds hy), self_mem_nhdsWithin] with t hD (htp : 0 < t)
  refine ⟨hD,Or.inl ?_⟩
  simpa [γ, coordBasis, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, h.1] using htp.ne'

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    (kerrErnst m a).IsSolution ∧
    IsWeylRepresentation m a (kerrNewmanMetric m a 0) (kerrErnst m a) ∧
    kerrNewmanDOC m a 0 ⊆ closure (offAxisExterior m a) ∧
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  obtain ⟨hX,hY,hpos⟩ := regular_kerr_ernst m a hm.1
  obtain ⟨hrep,hcharts⟩ := kerr_chart_reconstruction m a hm
  exact ⟨⟨hX,hY,fun p => ⟨hpos p,kerr_reduced_field_equations m a hm p⟩⟩,
    hrep,dense_off_axis m a,hcharts⟩
