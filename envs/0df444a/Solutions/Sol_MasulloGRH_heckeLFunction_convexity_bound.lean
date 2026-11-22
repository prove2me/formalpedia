-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_convexity_bound
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T19:36:28.060285+00:00
-- url     : https://prove2.me/submissions/e92ca21a-4a54-4487-9d99-15447a48c862

import Theorems.Thm_MasulloGRH_halfStrip_convexity
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_bounded_right_of_one
import Theorems.Thm_MasulloGRH_heckeLFunction_left_edge_bound
import Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips

set_option autoImplicit false

open MasulloGRH

open Filter Topology

namespace ConvexityAux

/-- A meromorphic function in normal form which is bounded near a point is analytic there
(argument as in the accepted proof of `heckeLFunction_inv_polynomial_growth_on_one_line`). -/
theorem analyticAt_of_bdd {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f x) {B : ℝ}
    (hB : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ B) : AnalyticAt ℂ f x := by
  rw [← hf.meromorphicOrderAt_nonneg_iff_analyticAt]
  by_contra hneg
  push Not at hneg
  have ht := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  rw [← tendsto_norm_atTop_iff_cobounded] at ht
  obtain ⟨z, hz1, hz2⟩ := ((ht.eventually_gt_atTop B).and (hB.filter_mono nhdsWithin_le_nhds)).exists
  linarith

/-- On a fixed vertical strip, `L_f(s, χ)` is holomorphic at all points of large height. -/
theorem heckeLFunction_differentiableAt_strip
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (a b : ℝ) :
    ∃ T : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      DifferentiableAt ℂ (heckeLFunction χ) s := by
  set lo := min a b - 1
  set hi := max a b + 1
  obtain ⟨M, hM, C, T0, hgrow⟩ :=
    heckeLFunction_polynomial_growth_on_vertical_strips F χ lo hi
      (by simp only [lo, hi]; linarith [min_le_max (a := a) (b := b)])
  have hNF : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
    have hex := heckeLFunction_exists_meromorphic_continuation F χ
    unfold heckeLFunction
    rw [dif_pos hex]
    exact hex.choose_spec.1
  refine ⟨max T0 0 + 1, fun s hsa hsb hsT => ?_⟩
  refine (analyticAt_of_bdd (hNF (Set.mem_univ s)) (B := |C| * (|s.im| + 1) ^ M) ?_).differentiableAt
  filter_upwards [Metric.ball_mem_nhds s (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have hre : |z.re - s.re| < 1 / 2 := by
    have := Complex.abs_re_le_norm (z - s); rw [Complex.sub_re] at this; linarith
  have him : |z.im - s.im| < 1 / 2 := by
    have := Complex.abs_im_le_norm (z - s); rw [Complex.sub_im] at this; linarith
  have hzlo : lo ≤ z.re := by
    simp only [lo]; have := abs_lt.1 hre; linarith [min_le_left a b]
  have hzhi : z.re ≤ hi := by
    simp only [hi]; have := abs_lt.1 hre; linarith [le_max_right a b]
  have himz1 : |s.im| - 1 / 2 ≤ |z.im| := by
    have := abs_sub_abs_le_abs_sub s.im z.im; rw [abs_sub_comm] at this; linarith
  have himz2 : |z.im| ≤ |s.im| + 1 := by
    have := abs_sub_abs_le_abs_sub z.im s.im; linarith
  have hT0 : T0 ≤ |z.im| := by linarith [le_max_left T0 0]
  calc ‖heckeLFunction χ z‖ ≤ C * |z.im| ^ M := hgrow z hzlo hzhi hT0
    _ ≤ |C| * |z.im| ^ M :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ |C| * (|s.im| + 1) ^ M :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) himz2 hM.le) (abs_nonneg C)

end ConvexityAux

open ConvexityAux

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖heckeLFunction χ s‖ ≤
        C * |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε) := by
  set n : ℝ := (Module.finrank ℚ F : ℝ) with hn_def
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set δ : ℝ := ε / (n + 1) with hδ_def
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨T1, hT1⟩ := heckeLFunction_differentiableAt_strip F χ (-δ) (1 + δ)
  obtain ⟨M, -, C0, T0, hgrow⟩ :=
    heckeLFunction_polynomial_growth_on_vertical_strips F χ (-δ) (1 + δ) (by linarith)
  obtain ⟨Ca, Ta, hla⟩ := heckeLFunction_left_edge_bound F χ δ hδ
  obtain ⟨Cb, hrb⟩ := heckeLFunction_bounded_right_of_one F χ δ hδ
  set T : ℝ := max (max 1 T1) (max T0 Ta) with hT_def
  set A : ℝ := max (max C0 Ca) (max Cb 0) with hA_def
  have hT1T : T1 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT0T : T0 ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTaT : Ta ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have h1T : 1 ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC0A : C0 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCaA : Ca ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCbA : Cb ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨C, T', hconv⟩ := halfStrip_convexity (heckeLFunction χ) (-δ) (1 + δ)
    (n * (1 / 2 + δ)) 0 M A T (by linarith) h1T
    (fun s h1 h2 hs => hT1 s h1 h2 (le_trans hT1T hs))
    (fun s h1 h2 hs => (hgrow s h1 h2 (le_trans hT0T hs)).trans
      (mul_le_mul_of_nonneg_right hC0A (Real.rpow_nonneg (abs_nonneg _) _)))
    (fun t ht => (hla t (le_trans hTaT ht)).trans
      (mul_le_mul_of_nonneg_right hCaA (Real.rpow_nonneg (abs_nonneg _) _)))
    (fun t _ => by rw [Real.rpow_zero, mul_one]; exact (hrb t).trans hCbA)
  refine ⟨max C 0, max T' 1, fun s hs0 hs1 hsT => ?_⟩
  have hx : 1 ≤ |s.im| := le_trans (le_max_right _ _) hsT
  have h := hconv s (by linarith) (by linarith) (le_trans (le_max_left _ _) hsT)
  have hexp : n * (1 / 2 + δ) * (1 + δ - s.re) / (1 + δ - -δ) +
      0 * (s.re - -δ) / (1 + δ - -δ) ≤ n * ((1 - s.re) / 2) + ε := by
    have hden : (1 + δ - -δ) ≠ 0 := by linarith
    have heq : n * (1 / 2 + δ) * (1 + δ - s.re) / (1 + δ - -δ) +
        0 * (s.re - -δ) / (1 + δ - -δ) = n * ((1 - s.re) / 2) + n * δ / 2 := by
      field_simp
      ring
    rw [heq]
    have : n * δ ≤ ε := by
      rw [hδ_def, mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  calc ‖heckeLFunction χ s‖
      ≤ C * |s.im| ^ (n * (1 / 2 + δ) * (1 + δ - s.re) / (1 + δ - -δ) +
          0 * (s.re - -δ) / (1 + δ - -δ)) := h
    _ ≤ max C 0 * |s.im| ^ (n * (1 / 2 + δ) * (1 + δ - s.re) / (1 + δ - -δ) +
          0 * (s.re - -δ) / (1 + δ - -δ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ max C 0 * |s.im| ^ (n * ((1 - s.re) / 2) + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hexp) (le_max_right _ _)
