-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_exponent_quadratic_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:37:07.388043+00:00
-- url     : https://prove2.me/submissions/80ced78a-952e-409b-ab29-739d0468740a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Theorems.Thm_ConsistentSubmodular_exp_neg_le_quadratic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem compensated_exp_upper (β y : ℝ) (hβ : 0 ≤ β) (hy : y < 0) :
    Real.exp (β * y) - 1 - (if -1 < y then β * y else 0) ≤
      (β ^ 2 / 2) * min 1 (y ^ 2) := by
  have hprod : β * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hy.le
  by_cases hsmall : -1 < y
  · have hsq : y ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ y + 1 by linarith) (show 0 ≤ 1 - y by linarith)]
    have h := ConsistentSubmodular.exp_neg_le_quadratic (neg_nonneg.mpr hprod)
    rw [neg_neg] at h
    rw [if_pos hsmall, min_eq_right hsq]
    calc
      Real.exp (β * y) - 1 - β * y ≤ (-(β * y)) ^ 2 / 2 := by linarith
      _ = _ := by ring
  · rw [if_neg hsmall, sub_zero]
    have he : Real.exp (β * y) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hprod
    exact (sub_nonpos.mpr he).trans (mul_nonneg (by positivity)
      (le_min zero_le_one (sq_nonneg y)))

private theorem triplet_laplace_quadratic_upper
    (T : LevyKhintchineTriple) (hneg : T.levyMeasure (Ici 0) = 0) (σ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, 1 ≤ β →
      tripletLaplace (-T.drift) σ T.levyMeasure β ≤ K * β ^ 2 := by
  let ν := T.levyMeasure
  let g : ℝ → ℝ := fun y => min 1 (y ^ 2)
  have hg0 (y : ℝ) : 0 ≤ g y := le_min zero_le_one (sq_nonneg y)
  have hg_meas : Measurable g := by
    dsimp [g]
    fun_prop
  have hg : Integrable g ν :=
    ⟨hg_meas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)).2
      T.levyMeasure_isLevyMeasure.2⟩
  let J := ∫ y, g y ∂ν
  have hJ : 0 ≤ J := integral_nonneg hg0
  refine ⟨|T.drift| + σ ^ 2 / 2 + J / 2, by positivity, ?_⟩
  intro β hβ
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  let F : ℝ → ℝ := fun y => Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)
  have hbound : (∫ y, F y ∂ν) ≤ (β ^ 2 / 2) * J := by
    by_cases hF : Integrable F ν
    · have hs : ∀ᵐ y ∂ν, y < 0 := by
        rw [ae_iff]
        simp only [not_lt]
        change T.levyMeasure (Ici (0 : ℝ)) = 0
        exact hneg
      change (∫ y, F y ∂ν) ≤ (β ^ 2 / 2) * ∫ y, g y ∂ν
      rw [← integral_const_mul]
      exact integral_mono_ae hF (hg.const_mul _) (hs.mono (fun y hy => compensated_exp_upper β y hβ0 hy))
    · rw [integral_undef hF]
      positivity
  have hlinear : T.drift * β ≤ |T.drift| * β ^ 2 := by
    have hsq : β ≤ β ^ 2 := by nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hβ)]
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) hβ0).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
  calc
    tripletLaplace (-T.drift) σ ν β =
      T.drift * β + σ ^ 2 * β ^ 2 / 2 +
        (∫ y, F y ∂ν) := by rw [tripletLaplace, neg_neg]
    _ ≤ |T.drift| * β ^ 2 + σ ^ 2 * β ^ 2 / 2 +
        (β ^ 2 / 2) * J := add_le_add (add_le_add hlinear le_rfl) hbound
    _ = _ := by ring

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, 1 ≤ β → ψ β ≤ K * β ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := triplet_laplace_quadratic_upper
    D.triplet D.negativeJumps D.gaussianCoefficient
  refine ⟨K, hK0, ?_⟩
  intro β hβ
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hψ1 := (hψ β 1 hβ0 zero_lt_one).2
  change ψ β = Real.log (∫ ω, Real.exp (β * D.X 1 ω) ∂P) / ((1 : ℝ≥0) : ℝ) at hψ1
  rw [(source_result81_law_positive_mgf Ω P D 1 β hβ0).2] at hψ1
  simp only [NNReal.coe_one, one_mul, Real.log_exp, div_one] at hψ1
  rw [hψ1]
  exact hK β hβ
