-- Prove2me | solution 1 for OAI.GaussianPropeller.Translation.translation_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:54:20.14634+00:00
-- url     : https://prove2.me/submissions/30dc25d9-c6b2-498d-8172-4cd14f6043e5

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Translation.lean:L168-L198
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Translation.translation_derivative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Theorems.Thm_OAI_GaussianPropeller_Translation_stdGaussian_map_add

-- ---- from OAI.Probability.GaussianPropeller.Translation ----
namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

lemma translated_integral {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-v)).real A =
      ∫ x in A, Real.exp (-⟪v,x⟫-‖v‖^2/2) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  simp_rw [sub_eq_add_neg]
  rw [stdGaussian_map_add]
  simp only [inner_neg_left, norm_neg]
  rw [measureReal_def, withDensity_apply _ hA,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _
      (fun x => (Real.exp_pos (-⟪v,x⟫-‖v‖^2/2)).le)) (by fun_prop)]
  simp only [sub_eq_add_neg]

lemma integrable_exp_inner {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (t : ℝ) : Integrable (fun x => Real.exp (t*⟪h,x⟫)) (stdGaussian E) := by
  let L : StrongDual ℝ E := innerSL ℝ h
  have hi : Integrable (fun x : ℝ => Real.exp (t*x)) ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal L]
    exact integrable_exp_mul_gaussianReal t
  exact hi.comp_aemeasurable L.continuous.aemeasurable

lemma integrableExpSet_neg_inner_restrict {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (A : Set E) :
    integrableExpSet (fun x => -⟪h,x⟫) ((stdGaussian E).restrict A) = univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  change Integrable (fun x => Real.exp (t * -⟪h,x⟫)) ((stdGaussian E).restrict A)
  simpa only [inner_neg_left] using (integrable_exp_inner (-h) t).restrict (s := A)

lemma translation_derivative {ι : Type uι} [Fintype ι]
    (h : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    HasDerivAt (fun u : ℝ =>
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-u•h)).real A)
      (-⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫) 0 := by
  have hd := hasDerivAt_mgf (X := fun x => -⟪h,x⟫)
    (μ := (stdGaussian (EuclideanSpace ℝ ι)).restrict A) (t := 0) (by
      rw [integrableExpSet_neg_inner_restrict, interior_univ]; trivial)
  simp only [zero_mul, Real.exp_zero, mul_one, integral_neg] at hd
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u^2*‖h‖^2/2)) 0 0 := by
    convert (((hasDerivAt_pow 2 (0:ℝ)).neg.mul_const (‖h‖^2)).div_const 2).exp using 1 <;> simp
  have hp := he.mul hd
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul, zero_div,
    Real.exp_zero, one_mul, zero_add] at hp
  have hinner : (∫ x in A, ⟪h,x⟫ ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫ :=
    integral_inner (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ ι))).restrict h
  rw [hinner] at hp
  apply hp.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro u
  dsimp only [Pi.mul_apply]
  rw [translated_integral (u•h) A hA]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    starRingEnd_apply, star_trivial, mgf]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.exp_add]
  congr 1
  ring

end GaussianPropeller.Translation

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Translation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.Translation.translation_derivative.{uι} := @_root_.OAI.GaussianPropeller.Translation.translation_derivative.{uι}
