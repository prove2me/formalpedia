-- Prove2me | solution 1 for MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right
-- status  : ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T13:34:55.699597+00:00
-- url     : https://prove2.me/submissions/f47a0e94-4cda-427d-85e1-a4a23491cda8

import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloRH_riemannZeta_analyticOrderNatAt_one_sub
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

set_option autoImplicit false

namespace MasulloRH_EvenSymm

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff

private lemma ofReal_cpow_conj (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (star s) = star ((x : ℂ) ^ s) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0]
  simp only [RCLike.star_def, ← exp_conj, map_mul, conj_ofReal, ← ofReal_log (le_of_lt hx)]

private lemma hasDerivAt_star_comp_star {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' (star z)) :
    HasDerivAt (fun w => star (f (star w))) (star f') z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hf ⊢
  have hstar_nhds : Tendsto (star : ℂ → ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (continuous_star.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun w hw => by simpa using star_ne_zero.mpr hw)
  have hcomp := (continuous_star.tendsto f').comp (hf.comp hstar_nhds)
  refine hcomp.congr (fun t => ?_)
  dsimp [Function.comp]
  simp only [map_mul, map_inv₀, map_sub, map_add, conj_conj]

private lemma differentiableAt_star_comp_star {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (star z)) :
    DifferentiableAt ℂ (fun w => star (f (star w))) z :=
  (hasDerivAt_star_comp_star hf.hasDerivAt).differentiableAt

private lemma analyticAt_star_comp_star {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (star z)) :
    AnalyticAt ℂ (fun w => star (f (star w))) z := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have h1 : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f (star w) :=
    (continuous_star.tendsto z).eventually hf
  exact h1.mono (fun _ hw => differentiableAt_star_comp_star hw)

private lemma riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have hs_star : 1 < (star s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs_star, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hterm : ∀ n : ℕ, 1 / (n + 1 : ℂ) ^ (star s) = star (1 / (n + 1 : ℂ) ^ s) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ofReal_cpow_conj ((n : ℝ) + 1) hn s, star_div₀, star_one]
  simp_rw [hterm, RCLike.star_def]
  exact (conjCLE.map_tsum).symm

private lemma riemannZeta_conj_of_im_pos {s : ℂ} (hs : 0 < s.im) :
    riemannZeta (star s) = star (riemannZeta s) := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU_conn : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hU_ne_one : ∀ z ∈ U, z ≠ 1 := by
    intro z hz h1
    rw [h1] at hz
    change (0 : ℝ) < (1 : ℂ).im at hz
    norm_num at hz
  have hU_star_ne_one : ∀ z ∈ U, star z ≠ 1 := by
    intro z hz h1
    apply hU_ne_one z hz
    simpa using congrArg star h1
  have hAnalytic1 : AnalyticOnNhd ℂ riemannZeta U := by
    intro z hz
    exact DifferentiableOn.analyticAt
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds (hU_ne_one z hz))
  have hAnalytic2 : AnalyticOnNhd ℂ (fun z => star (riemannZeta (star z))) U := by
    intro z hz
    have hAt : AnalyticAt ℂ riemannZeta (star z) :=
      DifferentiableOn.analyticAt
        (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
        (isOpen_compl_singleton.mem_nhds (hU_star_ne_one z hz))
    exact analyticAt_star_comp_star hAt
  let z₀ : ℂ := 2 + Complex.I
  have hz₀U : z₀ ∈ U := by
    show 0 < (2 + Complex.I).im
    simp
  have hEv : riemannZeta =ᶠ[𝓝 z₀] (fun z => star (riemannZeta (star z))) := by
    have hOpenRe : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz₀Re : z₀ ∈ {z : ℂ | 1 < z.re} := by
      show (1 : ℝ) < (2 + Complex.I).re
      norm_num
    filter_upwards [hOpenRe.mem_nhds hz₀Re] with z hz
    rw [riemannZeta_conj_of_one_lt_re hz, star_star]
  have hEqOn := hAnalytic1.eqOn_of_preconnected_of_eventuallyEq hAnalytic2 hU_conn hz₀U hEv
  have hval := congrArg star (hEqOn hs)
  simp only [star_star] at hval
  exact hval.symm

private lemma riemannZeta_conj_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta (star s) = star (riemannZeta s) := by
  rcases lt_trichotomy 0 s.im with hpos | hzero | hneg
  · exact riemannZeta_conj_of_im_pos hpos
  · exact (hs hzero.symm).elim
  · have hstar_pos : 0 < (star s).im := by
      simp only [RCLike.star_def, conj_im]
      linarith
    have h := riemannZeta_conj_of_im_pos hstar_pos
    rw [star_star] at h
    have h2 := congrArg star h.symm
    simp only [star_star] at h2
    exact h2

private lemma analyticOrderAt_star_comp_star (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z => star (f (star z))) z₀ = analyticOrderAt f (star z₀) := by
  let f_star : ℂ → ℂ := fun z => star (f (star z))
  by_cases hf : AnalyticAt ℂ f (star z₀)
  · have hf_star : AnalyticAt ℂ f_star z₀ := analyticAt_star_comp_star hf
    rcases eq_or_ne (analyticOrderAt f (star z₀)) ⊤ with htop | hne_top
    · rw [htop, analyticOrderAt_eq_top]
      rw [analyticOrderAt_eq_top] at htop
      have h1 : ∀ᶠ z in 𝓝 z₀, f (star z) = 0 := (continuous_star.tendsto z₀).eventually htop
      exact h1.mono (fun z hz => by simp only [hz, star_zero])
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
      rw [← hn]
      have hord : analyticOrderAt f (star z₀) = (n : ℕ∞) := hn.symm
      rw [hf.analyticOrderAt_eq_natCast] at hord
      rcases hord with ⟨g, hg_an, hg_ne, hg_eq⟩
      rw [hf_star.analyticOrderAt_eq_natCast]
      refine ⟨fun z => star (g (star z)), analyticAt_star_comp_star hg_an, ?_, ?_⟩
      · simpa using hg_ne
      · have h1 : ∀ᶠ z in 𝓝 z₀,
            f (star z) = (star z - star z₀) ^ n • g (star z) :=
          (continuous_star.tendsto z₀).eventually hg_eq
        refine h1.mono (fun z hz => ?_)
        dsimp [f_star]
        simp only [RCLike.star_def] at hz ⊢
        rw [hz]
        simp [smul_eq_mul]
  · have hf_star : ¬ AnalyticAt ℂ f_star z₀ := by
      intro h
      apply hf
      have h1 : AnalyticAt ℂ f_star (star (star z₀)) := by simpa [star_star] using h
      simpa [f_star, star_star] using analyticAt_star_comp_star h1
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf_star]

private lemma riemannZeta_analyticOrderNatAt_conj_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    analyticOrderNatAt riemannZeta (star s) = analyticOrderNatAt riemannZeta s := by
  unfold analyticOrderNatAt
  congr 1
  rw [← analyticOrderAt_star_comp_star riemannZeta s]
  refine analyticOrderAt_congr ?_
  have hOpen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  filter_upwards [hOpen.mem_nhds hs] with z hz
  dsimp
  have h := riemannZeta_conj_of_im_ne_zero hz
  have h2 := congrArg star h
  simp only [star_star] at h2
  exact h2

private lemma im_ne_zero_of_riemannZeta_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.im ≠ 0 := by
  have h6 : 6 < |ρ.im| := by
    by_contra hle
    push Not at hle
    exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six h0 h1 hle hζ
  intro him
  rw [him, abs_zero] at h6
  linarith

private lemma mellin_neg_of_even (φ : ℝ → ℂ) (heven : ∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) (w : ℂ) :
    mellin φ (-w) = mellin φ w := by
  rw [← mellin_comp_inv]
  simp only [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  dsimp
  rw [heven t ht]

private lemma mellin_ofReal_conj (ψ : ℝ → ℝ) (w : ℂ) :
    mellin (fun t => (ψ t : ℂ)) (star w) = star (mellin (fun t => (ψ t : ℂ)) w) := by
  simp only [mellin, smul_eq_mul]
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ (star w - 1) * (ψ t : ℂ))
      (fun t : ℝ => star ((t : ℂ) ^ (w - 1) * (ψ t : ℂ))) (Ioi 0) := by
    intro t ht
    dsimp
    have h1 : (starRingEnd ℂ) w - 1 = star (w - 1) := by simp [RCLike.star_def]
    rw [h1, ofReal_cpow_conj t ht (w - 1)]
    simp only [RCLike.star_def, map_mul, conj_ofReal]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  exact integral_conj

private abbrev UpperRightZeros (α : ℝ) :=
  {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}

private abbrev RemainderZeros (α : ℝ) :=
  {ρ : MasulloRH.ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}

private lemma riemannZeta_one_sub_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : riemannZeta (1 - ρ) = 0 := by
  have hs : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
    intro n h
    have hre : ρ.re = -(n : ℝ) := by simpa using congrArg Complex.re h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs' : ρ ≠ 1 := by
    intro h
    have hre : ρ.re = 1 := by simpa using congrArg Complex.re h
    linarith
  rw [riemannZeta_one_sub hs hs', hζ, mul_zero]

private def upperRightToRemQ1 {α : ℝ} (hα : 0 < α) (ρ : UpperRightZeros α) : RemainderZeros α :=
  ⟨⟨ρ.1, ρ.2.1, by linarith [ρ.2.2.1], ρ.2.2.2.1, by
    rw [abs_lt]
    constructor <;> linarith [ρ.2.2.1, ρ.2.2.2.1]⟩,
   by
    show α ≤ |ρ.1.re - 1 / 2|
    rw [abs_of_nonneg (by linarith [ρ.2.2.1])]
    linarith [ρ.2.2.1]⟩

private def upperRightToRemQ2 {α : ℝ} (hα : 0 < α) (ρ : UpperRightZeros α) : RemainderZeros α :=
  have hζ_star : riemannZeta (star ρ.1) = 0 := by
    rw [riemannZeta_conj_of_im_ne_zero (ne_of_gt ρ.2.2.2.2), ρ.2.1, star_zero]
  have hζ_1 : riemannZeta (1 - star ρ.1) = 0 :=
    riemannZeta_one_sub_eq_zero hζ_star (by simpa using by linarith [ρ.2.2.1]) (by simpa using ρ.2.2.2.1)
  ⟨⟨1 - star ρ.1, hζ_1, by
    simp only [sub_re, one_re, RCLike.star_def, conj_re]; linarith [ρ.2.2.2.1], by
    simp only [sub_re, one_re, RCLike.star_def, conj_re]; linarith [ρ.2.2.1], by
    simp only [sub_re, one_re, RCLike.star_def, conj_re]; rw [abs_lt]
    constructor <;> linarith [ρ.2.2.1, ρ.2.2.2.1]⟩,
   by
    show α ≤ |(1 - star ρ.1).re - 1 / 2|
    simp only [sub_re, one_re, RCLike.star_def, conj_re]
    rw [abs_of_nonpos (by linarith [ρ.2.2.1])]
    linarith [ρ.2.2.1]⟩

private def upperRightToRemQ4 {α : ℝ} (hα : 0 < α) (ρ : UpperRightZeros α) : RemainderZeros α :=
  have hζ_star : riemannZeta (star ρ.1) = 0 := by
    rw [riemannZeta_conj_of_im_ne_zero (ne_of_gt ρ.2.2.2.2), ρ.2.1, star_zero]
  ⟨⟨star ρ.1, hζ_star, by
    simp only [RCLike.star_def, conj_re]; linarith [ρ.2.2.1], by
    simp only [RCLike.star_def, conj_re]; exact ρ.2.2.2.1, by
    simp only [RCLike.star_def, conj_re]; rw [abs_lt]
    constructor <;> linarith [ρ.2.2.1, ρ.2.2.2.1]⟩,
   by
    show α ≤ |(star ρ.1).re - 1 / 2|
    simp only [RCLike.star_def, conj_re]
    rw [abs_of_nonneg (by linarith [ρ.2.2.1])]
    linarith [ρ.2.2.1]⟩

private def upperRightToRemQ3 {α : ℝ} (hα : 0 < α) (ρ : UpperRightZeros α) : RemainderZeros α :=
  have hζ_1 : riemannZeta (1 - ρ.1) = 0 :=
    riemannZeta_one_sub_eq_zero ρ.2.1 (by linarith [ρ.2.2.1]) ρ.2.2.2.1
  ⟨⟨1 - ρ.1, hζ_1, by
    simp only [sub_re, one_re]; linarith [ρ.2.2.2.1], by
    simp only [sub_re, one_re]; linarith [ρ.2.2.1], by
    simp only [sub_re, one_re]; rw [abs_lt]
    constructor <;> linarith [ρ.2.2.1, ρ.2.2.2.1]⟩,
   by
    show α ≤ |(1 - ρ.1).re - 1 / 2|
    simp only [sub_re, one_re]
    rw [abs_of_nonpos (by linarith [ρ.2.2.1])]
    linarith [ρ.2.2.1]⟩

private noncomputable def remainderEquiv {α : ℝ} (hα : 0 < α) :
    (UpperRightZeros α ⊕ UpperRightZeros α) ⊕ (UpperRightZeros α ⊕ UpperRightZeros α) ≃
      RemainderZeros α where
  toFun
    | Sum.inl (Sum.inl ρ) => upperRightToRemQ1 hα ρ
    | Sum.inl (Sum.inr ρ) => upperRightToRemQ2 hα ρ
    | Sum.inr (Sum.inl ρ) => upperRightToRemQ4 hα ρ
    | Sum.inr (Sum.inr ρ) => upperRightToRemQ3 hα ρ
  invFun z :=
    let c : ℂ := z.1.1
    have hζ : riemannZeta c = 0 := z.1.2.1
    have h0 : 0 < c.re := z.1.2.2.1
    have h1 : c.re < 1 := z.1.2.2.2.1
    have hα_abs : α ≤ |c.re - 1 / 2| := z.2
    have him_ne : c.im ≠ 0 := im_ne_zero_of_riemannZeta_eq_zero hζ h0 h1
    if him : 0 ≤ c.im then
      have him_pos : 0 < c.im := lt_of_le_of_ne him him_ne.symm
      if hre : 1 / 2 ≤ c.re then
        Sum.inl (Sum.inl ⟨c, hζ, by
          rw [abs_of_nonneg (by linarith)] at hα_abs; linarith, h1, him_pos⟩)
      else
        Sum.inl (Sum.inr ⟨1 - star c,
          riemannZeta_one_sub_eq_zero
            (by rw [riemannZeta_conj_of_im_ne_zero him_ne, hζ, star_zero])
            (by simpa using h0) (by simpa using h1),
          by
            push Not at hre
            rw [abs_of_neg (by linarith)] at hα_abs
            simp only [sub_re, one_re, RCLike.star_def, conj_re]; linarith,
          by simp only [sub_re, one_re, RCLike.star_def, conj_re]; linarith,
          by simp only [sub_im, one_im, RCLike.star_def, conj_im]; linarith⟩)
    else
      have him_neg : c.im < 0 := lt_of_not_ge him
      if hre : 1 / 2 ≤ c.re then
        Sum.inr (Sum.inl ⟨star c,
          by rw [riemannZeta_conj_of_im_ne_zero him_ne, hζ, star_zero],
          by
            rw [abs_of_nonneg (by linarith)] at hα_abs
            simp only [RCLike.star_def, conj_re]; linarith,
          by simp only [RCLike.star_def, conj_re]; exact h1,
          by simp only [RCLike.star_def, conj_im]; linarith⟩)
      else
        Sum.inr (Sum.inr ⟨1 - c,
          riemannZeta_one_sub_eq_zero hζ h0 h1,
          by
            push Not at hre
            rw [abs_of_neg (by linarith)] at hα_abs
            simp only [sub_re, one_re]; linarith,
          by simp only [sub_re, one_re]; linarith,
          by simp only [sub_im, one_im]; linarith⟩)
  left_inv x := by
    rcases x with (ρ | ρ) | (ρ | ρ) <;>
    · dsimp [upperRightToRemQ1, upperRightToRemQ2, upperRightToRemQ3, upperRightToRemQ4]
      split_ifs <;>
      first
      | (exfalso; linarith [ρ.2.2.1, ρ.2.2.2.2])
      | rfl
      | (congr 2; apply Subtype.ext; simp)
  right_inv z := by
    dsimp
    split_ifs <;>
    · dsimp [upperRightToRemQ1, upperRightToRemQ2, upperRightToRemQ3, upperRightToRemQ4]
      apply Subtype.ext; apply Subtype.ext
      simp

private lemma zetaTraceTerm_quadrants (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ)
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) (ρ : UpperRightZeros α) :
    let φ : ℝ → ℂ := fun t => (ψ t : ℂ)
    let c : ℂ := (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * mellin φ (ρ.1 - 1 / 2)
    MasulloRH.zetaTraceTerm φ (1 / 2) (upperRightToRemQ1 hα ρ).1 = c ∧
    MasulloRH.zetaTraceTerm φ (1 / 2) (upperRightToRemQ2 hα ρ).1 = star c ∧
    MasulloRH.zetaTraceTerm φ (1 / 2) (upperRightToRemQ4 hα ρ).1 = star c ∧
    MasulloRH.zetaTraceTerm φ (1 / 2) (upperRightToRemQ3 hα ρ).1 = c := by
  intro φ c
  have h0 : 0 < ρ.1.re := by linarith [ρ.2.2.1]
  have h1 : ρ.1.re < 1 := ρ.2.2.2.1
  have him_ne : ρ.1.im ≠ 0 := ne_of_gt ρ.2.2.2.2
  have heven_φ : ∀ t : ℝ, 0 < t → φ t⁻¹ = φ t := fun t ht => by
    dsimp [φ]; rw [heven t ht]
  have hord_conj : analyticOrderNatAt riemannZeta (star ρ.1) = analyticOrderNatAt riemannZeta ρ.1 :=
    riemannZeta_analyticOrderNatAt_conj_of_im_ne_zero him_ne
  have hord_sub : analyticOrderNatAt riemannZeta (1 - ρ.1) = analyticOrderNatAt riemannZeta ρ.1 :=
    MasulloRH.riemannZeta_analyticOrderNatAt_one_sub ρ.1 h0 h1
  have hord_sub_conj :
      analyticOrderNatAt riemannZeta (1 - star ρ.1) = analyticOrderNatAt riemannZeta ρ.1 := by
    rw [MasulloRH.riemannZeta_analyticOrderNatAt_one_sub (star ρ.1) (by simpa using h0) (by simpa using h1),
        hord_conj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- Quadrant II: 1 - star ρ
    dsimp [MasulloRH.zetaTraceTerm, upperRightToRemQ2, c]
    simp only [← RCLike.star_def] at *
    rw [hord_sub_conj]
    have harg : 1 - star ρ.1 - 1 / 2 = -(star (ρ.1 - 1 / 2)) := by
      simp; ring
    rw [harg, mellin_neg_of_even φ heven_φ, mellin_ofReal_conj ψ, star_mul, star_natCast, mul_comm]
  · -- Quadrant IV: star ρ
    dsimp [MasulloRH.zetaTraceTerm, upperRightToRemQ4, c]
    simp only [← RCLike.star_def] at *
    rw [hord_conj]
    have harg : star ρ.1 - 1 / 2 = star (ρ.1 - 1 / 2) := by
      simp
    rw [harg, mellin_ofReal_conj ψ, star_mul, star_natCast, mul_comm]
  · -- Quadrant III: 1 - ρ
    dsimp [MasulloRH.zetaTraceTerm, upperRightToRemQ3, c]
    rw [hord_sub]
    have harg : 1 - ρ.1 - 1 / 2 = -(ρ.1 - 1 / 2) := by ring
    rw [harg, mellin_neg_of_even φ heven_φ]

private lemma tsum_four_quadrants {U R : Type*} (e : (U ⊕ U) ⊕ (U ⊕ U) ≃ R)
    (F : R → ℂ) (c : U → ℂ) (hF : Summable F)
    (h1 : ∀ u, F (e (Sum.inl (Sum.inl u))) = c u)
    (h2 : ∀ u, F (e (Sum.inl (Sum.inr u))) = star (c u))
    (h3 : ∀ u, F (e (Sum.inr (Sum.inl u))) = star (c u))
    (h4 : ∀ u, F (e (Sum.inr (Sum.inr u))) = c u) :
    Summable (fun u => (c u).re) ∧
    (∑' r, F r) = 4 * ((∑' u, (c u).re : ℝ) : ℂ) := by
  have hSum_e : Summable (F ∘ e) := e.summable_iff.mpr hF
  have hSum_L : Summable ((F ∘ e) ∘ Sum.inl) := hSum_e.comp_injective Sum.inl_injective
  have hSum_R : Summable ((F ∘ e) ∘ Sum.inr) := hSum_e.comp_injective Sum.inr_injective
  have hSum_Q1 : Summable (((F ∘ e) ∘ Sum.inl) ∘ Sum.inl) := hSum_L.comp_injective Sum.inl_injective
  have hSum_Q2 : Summable (((F ∘ e) ∘ Sum.inl) ∘ Sum.inr) := hSum_L.comp_injective Sum.inr_injective
  have hSum_Q3 : Summable (((F ∘ e) ∘ Sum.inr) ∘ Sum.inl) := hSum_R.comp_injective Sum.inl_injective
  have hSum_Q4 : Summable (((F ∘ e) ∘ Sum.inr) ∘ Sum.inr) := hSum_R.comp_injective Sum.inr_injective
  have hQ1 : (((F ∘ e) ∘ Sum.inl) ∘ Sum.inl) = c := funext h1
  have hQ2 : (((F ∘ e) ∘ Sum.inl) ∘ Sum.inr) = (fun u => star (c u)) := funext h2
  have hQ3 : (((F ∘ e) ∘ Sum.inr) ∘ Sum.inl) = (fun u => star (c u)) := funext h3
  have hQ4 : (((F ∘ e) ∘ Sum.inr) ∘ Sum.inr) = c := funext h4
  have hSum_c : Summable c := hQ1 ▸ hSum_Q1
  have hSum_star_c : Summable (fun u => star (c u)) := hQ2 ▸ hSum_Q2
  have hSum_re : Summable (fun u => (c u).re) := Complex.reCLM.summable hSum_c
  refine ⟨hSum_re, ?_⟩
  have h_e_tsum : (∑' r, F r) = ∑' x, (F ∘ e) x := (e.tsum_eq F).symm
  have h12 : (∑' i, (F ∘ e) (Sum.inl i)) = (∑' u, c u) + (∑' u, star (c u)) := by
    simpa only [Function.comp_apply, h1, h2] using (hSum_Q1.tsum_sum hSum_Q2)
  have h34 : (∑' i, (F ∘ e) (Sum.inr i)) = (∑' u, star (c u)) + (∑' u, c u) := by
    simpa only [Function.comp_apply, h3, h4] using (hSum_Q3.tsum_sum hSum_Q4)
  rw [h_e_tsum, hSum_L.tsum_sum hSum_R, h12, h34]
  have h_add1 : (∑' u, c u) + (∑' u, star (c u)) = ∑' u, (c u + star (c u)) :=
    (hSum_c.tsum_add hSum_star_c).symm
  have h_add2 : (∑' u, star (c u)) + (∑' u, c u) = ∑' u, (star (c u) + c u) :=
    (hSum_star_c.tsum_add hSum_c).symm
  rw [h_add1, h_add2, ← (hSum_c.add hSum_star_c).tsum_add (hSum_star_c.add hSum_c)]
  have h_four : (fun u => (c u + star (c u)) + (star (c u) + c u)) =
      (fun u => (4 : ℂ) * ((c u).re : ℂ)) := by
    funext u
    rw [RCLike.star_def, add_comm ((starRingEnd ℂ) (c u)) (c u), Complex.add_conj]
    push_cast
    ring
  rw [h_four, tsum_mul_left, Complex.ofReal_tsum]

end MasulloRH_EvenSymm

open MasulloRH MeasureTheory Set

theorem solution
    (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ)
    (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    let φ : ℝ → ℂ := fun t => (ψ t : ℂ)
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    let upperRight := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
    Summable (fun ρ : upperRight =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (mellin φ ((ρ : ℂ) - 1 / 2)).re) ∧
    ∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ =
      4 * ((∑' ρ : upperRight,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (mellin φ ((ρ : ℂ) - 1 / 2)).re : ℝ) : ℂ) := by
  intro φ remainder upperRight
  have hWin := MasulloAudit.trace_formula_window_with_remainder α φ hψ
  have hSumRem : Summable (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) := hWin.2.2.2.1
  let c : upperRight → ℂ := fun ρ =>
    (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * mellin φ ((ρ : ℂ) - 1 / 2)
  have hc_re : ∀ ρ : upperRight,
      (c ρ).re = (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (mellin φ ((ρ : ℂ) - 1 / 2)).re := by
    intro ρ
    dsimp [c]
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hQuad := MasulloRH_EvenSymm.tsum_four_quadrants
    (MasulloRH_EvenSymm.remainderEquiv hα)
    (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) c hSumRem
    (fun u => (MasulloRH_EvenSymm.zetaTraceTerm_quadrants α hα ψ heven u).1)
    (fun u => (MasulloRH_EvenSymm.zetaTraceTerm_quadrants α hα ψ heven u).2.1)
    (fun u => (MasulloRH_EvenSymm.zetaTraceTerm_quadrants α hα ψ heven u).2.2.1)
    (fun u => (MasulloRH_EvenSymm.zetaTraceTerm_quadrants α hα ψ heven u).2.2.2)
  simpa only [hc_re] using hQuad
