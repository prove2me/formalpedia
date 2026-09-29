-- Prove2me | solution 1 for Martingale.expectation_prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:45:58.936815+00:00
-- url     : https://prove2.me/submissions/8033fb66-fa7a-4557-b79c-1b3ac5db1289

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (Z k))
    (hadapt : ∀ k, Measurable[ℱ k] (Z k))
    (hint : ∀ k, Integrable (Z k) P)
    (hmds : ∀ k, P[Z (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∫ ω, Z 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ k ω, |Z k ω| ≤ C) (θ : ℝ) (n : ℕ) :
    ∫ ω, (∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))) ∂P = 1 := by
  -- (1) real orthogonality: an `ℱ m`-measurable bounded factor annihilates `Z (m+1)`
  have key : ∀ (m : ℕ) (g : Ω → ℝ), StronglyMeasurable[ℱ m] g → ∀ B : ℝ, (∀ ω, |g ω| ≤ B) →
      ∫ ω, g ω * Z (m + 1) ω ∂P = 0 := by
    intro m g hg B hgb
    have hgm : Measurable g := (hg.mono (ℱ.le m)).measurable
    have hprod : Integrable (fun ω => g ω * Z (m + 1) ω) P := by
      refine Integrable.bdd_mul (c := B) (hint (m + 1)) hgm.aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]; exact hgb ω
    calc ∫ ω, g ω * Z (m + 1) ω ∂P
        = ∫ ω, (P[fun ω' => g ω' * Z (m + 1) ω' | ℱ m]) ω ∂P :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, g ω * (P[Z (m + 1) | ℱ m]) ω ∂P := by
          refine integral_congr_ae ?_
          exact condExp_mul_of_stronglyMeasurable_left hg hprod (hint (m + 1))
      _ = 0 := by
          refine (integral_congr_ae ?_).trans (integral_zero _ _)
          filter_upwards [hmds m] with ω hω
          simp [hω]
  -- (2) complex version, by splitting into real and imaginary parts
  have keyC : ∀ (m : ℕ) (G : Ω → ℂ), Measurable[ℱ m] G → ∀ B : ℝ, (∀ ω, ‖G ω‖ ≤ B) →
      ∫ ω, G ω * (Z (m + 1) ω : ℂ) ∂P = 0 := by
    intro m G hG B hGb
    have hGm : Measurable G := hG.mono (ℱ.le m) le_rfl
    have hre : StronglyMeasurable[ℱ m] (fun ω => (G ω).re) :=
      (Complex.measurable_re.comp hG).stronglyMeasurable
    have him : StronglyMeasurable[ℱ m] (fun ω => (G ω).im) :=
      (Complex.measurable_im.comp hG).stronglyMeasurable
    have hreb : ∀ ω, |(G ω).re| ≤ B := fun ω =>
      le_trans (Complex.abs_re_le_norm (G ω)) (hGb ω)
    have himb : ∀ ω, |(G ω).im| ≤ B := fun ω =>
      le_trans (Complex.abs_im_le_norm (G ω)) (hGb ω)
    have hIint : Integrable (fun ω => G ω * (Z (m + 1) ω : ℂ)) P := by
      refine Integrable.bdd_mul (c := B) ?_ hGm.aestronglyMeasurable ?_
      · exact (hint (m + 1)).ofReal
      · filter_upwards with ω; exact hGb ω
    have hreI : Integrable (fun ω => (G ω).re * Z (m + 1) ω) P := by
      refine Integrable.bdd_mul (c := B) (hint (m + 1))
        ((Complex.measurable_re.comp hGm)).aestronglyMeasurable ?_
      filter_upwards with ω; rw [Real.norm_eq_abs]; exact hreb ω
    have himI : Integrable (fun ω => (G ω).im * Z (m + 1) ω) P := by
      refine Integrable.bdd_mul (c := B) (hint (m + 1))
        ((Complex.measurable_im.comp hGm)).aestronglyMeasurable ?_
      filter_upwards with ω; rw [Real.norm_eq_abs]; exact himb ω
    have hsplit : ∀ ω, G ω * (Z (m + 1) ω : ℂ)
        = (((G ω).re * Z (m + 1) ω : ℝ) : ℂ)
          + Complex.I * (((G ω).im * Z (m + 1) ω : ℝ) : ℂ) := by
      intro ω
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add hreI.ofReal (himI.ofReal.const_mul _),
      integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      key m (fun ω => (G ω).re) hre B hreb, key m (fun ω => (G ω).im) him B himb]
    simp
  -- (3) the induction
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hbdd 0 (Classical.arbitrary Ω))
  set Bc : ℝ := 1 + |θ| * C with hbdef
  have hb0 : (0:ℝ) ≤ Bc := by positivity
  have hfac : ∀ k ω, ‖(1 : ℂ) + Complex.I * θ * (Z k ω : ℂ)‖ ≤ Bc := by
    intro k ω
    refine le_trans (norm_add_le _ _) ?_
    have : ‖Complex.I * (θ : ℂ) * (Z k ω : ℂ)‖ = |θ| * |Z k ω| := by
      simp [norm_mul, Complex.norm_real]
    rw [norm_one, this, hbdef]
    have := hbdd k ω
    nlinarith [abs_nonneg θ, abs_nonneg (Z k ω)]
  have hPibnd : ∀ (j : ℕ) ω, ‖∏ k ∈ Finset.range j, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ≤ Bc ^ j := by
    intro j ω
    rw [norm_prod]
    calc ∏ k ∈ Finset.range j, ‖(1 : ℂ) + Complex.I * θ * (Z k ω : ℂ)‖
        ≤ ∏ _k ∈ Finset.range j, Bc :=
          Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hfac k ω)
      _ = Bc ^ j := by simp
  have hPimeas : ∀ j : ℕ, Measurable (fun ω => ∏ k ∈ Finset.range j,
      (1 + Complex.I * θ * (Z k ω : ℂ))) := by
    intro j
    refine Finset.measurable_prod _ (fun k _ => ?_)
    have := hmeas k
    fun_prop
  have hPiint : ∀ j : ℕ, Integrable (fun ω => ∏ k ∈ Finset.range j,
      (1 + Complex.I * θ * (Z k ω : ℂ))) P := by
    intro j
    refine ⟨(hPimeas j).aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (Bc ^ j)).mono ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg hb0] using hPibnd j ω
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Finset.prod_range_succ]
    have hZint : Integrable (fun ω => (Z m ω : ℂ)) P := (hint m).ofReal
    have hmulint : Integrable (fun ω => (∏ k ∈ Finset.range m,
        (1 + Complex.I * θ * (Z k ω : ℂ))) * (Z m ω : ℂ)) P := by
      refine Integrable.bdd_mul (c := Bc ^ m) hZint (hPimeas m).aestronglyMeasurable ?_
      filter_upwards with ω; exact hPibnd m ω
    have hzero : ∫ ω, (∏ k ∈ Finset.range m,
        (1 + Complex.I * θ * (Z k ω : ℂ))) * (Z m ω : ℂ) ∂P = 0 := by
      cases m with
      | zero =>
        simp only [Finset.range_zero, Finset.prod_empty, one_mul]
        rw [integral_complex_ofReal, hcent]
        simp
      | succ m' =>
        refine keyC m' _ ?_ (Bc ^ (m' + 1)) (fun ω => hPibnd (m' + 1) ω)
        refine Finset.measurable_prod _ (fun k hk => ?_)
        have hk' : Measurable[ℱ m'] (Z k) :=
          (hadapt k).mono (ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) le_rfl
        fun_prop
    have hrw : ∀ ω, (∏ k ∈ Finset.range m, (1 + Complex.I * θ * (Z k ω : ℂ)))
          * (1 + Complex.I * θ * (Z m ω : ℂ))
        = (∏ k ∈ Finset.range m, (1 + Complex.I * θ * (Z k ω : ℂ)))
          + Complex.I * θ * ((∏ k ∈ Finset.range m,
              (1 + Complex.I * θ * (Z k ω : ℂ))) * (Z m ω : ℂ)) := by
      intro ω; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
      integral_add (hPiint m) (hmulint.const_mul _), integral_const_mul, hzero, ih]
    simp
