-- Prove2me | solution 1 for OAI.IndependentProducts.main_gaussian_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:58:57.069244+00:00
-- url     : https://prove2.me/submissions/4210083e-a83c-49d6-8834-3c34b5d164fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianBounds.lean:L121-L138
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.IndependentProducts.main_gaussian_12.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_IndependentProducts_main_gaussian_12) verbatim and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Theorems.Thm_OAI_IndependentProducts_averaged_midpoint_from_scalar
import Theorems.Thm_OAI_IndependentProducts_gaussian_bilinear_excess
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_OAI_IndependentProducts_integral_excess_independent_copy
import Theorems.Thm_OAI_IndependentProducts_measurePreserving_gaussianRotate

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma gaussianTail_nonneg (r : ℝ) : 0 ≤ gaussianTail r := ENNReal.toReal_nonneg

lemma gaussianTail_pos (r : ℝ) : 0 < gaussianTail r := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
  apply lt_of_lt_of_le (b := gaussianReal 0 1 (Ioo (|r| + 1) (|r| + 2)))
  · apply pos_iff_ne_zero.mpr
    intro hzero
    have hz := (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num)) hzero
    have hp : (0 : ℝ≥0∞) < volume (Ioo (|r| + 1) (|r| + 2)) := by simp
    exact hp.ne' hz
  · apply measure_mono
    intro x hx
    exact le_trans (le_abs_self r) (le_trans (by linarith [hx.1]) (le_abs_self x))

lemma gaussian_integral_sq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable] at h
  simpa using h

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

lemma gaussian_polarization (z : ℝ × ℝ) :
    z.1 ^ 2 - z.2 ^ 2 = 2 * (gaussianRotate z).1 * (gaussianRotate z).2 := by
  have h : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hh : Real.sqrt 2 ≠ 0 := by positivity
  dsimp [gaussianRotate]
  field_simp
  nlinarith

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.GaussianMoments ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

lemma gaussian_square_memLp : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert h using 1
  funext x
  change (x ^ 2) ^ 2 = |x| ^ 4
  rw [← pow_mul]
  norm_num
  rw [← abs_pow, abs_of_nonneg (by positivity)]

end GaussianVector
end IndependentProducts

namespace IndependentProducts

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

lemma measurePreserving_gaussianVectorRotate : MeasurePreserving (gaussianVectorRotate (ι := ι))
    (gaussianVector.prod gaussianVector) (gaussianVector.prod gaussianVector) := by
  let PP := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hp := measurePreserving_pi (fun _ : ι => PP) (fun _ : ι => PP)
    (fun _ : ι => measurePreserving_gaussianRotate)
  have hs := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  exact hs.comp (hp.comp hs.symm)

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.GaussianExcess ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section GaussianScalar
variable {ι : Type uι} [Fintype ι]

lemma integrable_gaussian_quadratic (a : ι → ℝ) (b : ℝ) :
    Integrable (fun x : ι → ℝ => b + ∑ i, a i * x i ^ 2) gaussianVector := by
  apply (integrable_const b).add
  apply integrable_finsetSum
  intro i _
  exact ((gaussian_square_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ => gaussianReal 0 1) i)).integrable (by norm_num)).const_mul _

lemma gaussian_quadratic_difference (a : ι → ℝ) (b : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    ((b + ∑ i, a i * z.1 i ^ 2) - (b + ∑ i, a i * z.2 i ^ 2)) / 2 =
      ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
  have he : ∀ i, a i * z.1 i ^ 2 - a i * z.2 i ^ 2 =
      2 * (a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i) := by
    intro i
    rw [← mul_sub, gaussian_polarization (z.1 i, z.2 i)]
    dsimp [gaussianVectorRotate]
    ring
  have hh : (∑ i, a i * z.1 i ^ 2) - (∑ i, a i * z.2 i ^ 2) =
      2 * ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [he, ← Finset.mul_sum]
  linarith

lemma gaussian_quadratic_scalar_excess (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      (t * K * Real.sqrt (∑ i, a i ^ 2) - r) ≤
      ∫ x : ι → ℝ, excess t r (b + ∑ i, a i * x i ^ 2) ∂gaussianVector := by
  have hpartial := gaussian_bilinear_excess a K t r hK ht hr
  have hsym := integral_excess_independent_copy (integrable_gaussian_quadratic a b) ht r
  have he : (∫ z : (ι → ℝ) × (ι → ℝ),
      excess t r (((b + ∑ i, a i * z.1 i ^ 2) - (b + ∑ i, a i * z.2 i ^ 2)) / 2)
      ∂gaussianVector.prod gaussianVector) =
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by
    simp_rw [gaussian_quadratic_difference a b]
    exact measurePreserving_gaussianVectorRotate.hasLaw.integral_comp (f := fun z : (ι → ℝ) × (ι → ℝ) =>
      excess t r (∑ i, a i * z.1 i * z.2 i)) (by unfold excess; fun_prop)
  rw [he] at hsym
  calc
    _ ≤ (gaussianTail (Real.sqrt 2 * K) / 12) * excess t r (K * Real.sqrt (∑ i, a i ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (gaussianTail_nonneg _) (by norm_num))
      unfold excess
      rw [abs_of_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))]
      simpa only [mul_assoc] using le_max_left (t * (K * Real.sqrt (∑ i, a i ^ 2)) - r) 0
    _ ≤ _ := hpartial.trans hsym

lemma gaussian_square_scalar_excess (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      (t * K * Real.sqrt (∑ i, a i ^ 2) - r) ≤
      ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i)
        ∂Measure.pi (fun _ => gaussianSquareLaw) := by
  have hp : MeasurePreserving (fun x : ι → ℝ => fun i => x i ^ 2) gaussianVector
      (Measure.pi (fun _ => gaussianSquareLaw)) := by
    unfold gaussianVector
    apply measurePreserving_pi (fun _ : ι => gaussianReal 0 1) (fun _ : ι => gaussianSquareLaw)
      (f := fun _ x => x ^ 2)
    intro i
    exact ⟨by fun_prop, rfl⟩
  have he := hp.hasLaw.integral_comp (f := fun w : ι → ℝ => excess t r (b + ∑ i, a i * w i))
    ((by unfold excess; fun_prop : Continuous (fun w : ι → ℝ => excess t r (b + ∑ i, a i * w i))).aestronglyMeasurable)
  exact he ▸ gaussian_quadratic_scalar_excess a b K t r hK ht hr

end GaussianScalar
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.GaussianBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
namespace FiniteHead

end FiniteHead

lemma gaussianSquareLaw_memLp : MemLp (fun w : ℝ => w) 2 gaussianSquareLaw := by
  unfold gaussianSquareLaw
  exact (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr gaussian_square_memLp

lemma gaussianSquareLaw_mean : (∫ w : ℝ, w ∂gaussianSquareLaw) = 1 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  exact gaussian_integral_sq

lemma gaussianSquareLaw_second : (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) = 3 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  simpa only [← pow_mul, Nat.reduceMul] using gaussian_integral_fourth

lemma gaussianSquareLaw_hypotheses : MultiplierHypotheses gaussianSquareLaw := by
  refine ⟨inferInstance, ?_, ?_, gaussianSquareLaw_mean, gaussianSquareLaw_memLp⟩
  · unfold gaussianSquareLaw
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    filter_upwards [(gaussianReal 0 1).ae_ne 0] with w hw
    exact sq_pos_of_ne_zero hw
  · intro c hc
    have h1 : (1 : ℝ) = c := by
      calc
        1 = ∫ w : ℝ, w ∂gaussianSquareLaw := gaussianSquareLaw_mean.symm
        _ = ∫ _ : ℝ, c ∂gaussianSquareLaw := integral_congr_ae hc
        _ = c := by simp
    have h2 : (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) = c ^ 2 := by
      calc
        _ = ∫ _ : ℝ, c ^ 2 ∂gaussianSquareLaw := integral_congr_ae (hc.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw))
        _ = _ := by simp
    rw [gaussianSquareLaw_second, ← h1] at h2
    norm_num at h2

lemma gaussian_midpoint_parameter (t K : ℝ) (ht : 0 < t) (hK : 0 ≤ K) :
    (gaussianTail (Real.sqrt 2 * K) / 12) * (t * K / (2 * Real.sqrt 3) - 1) ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t := by
  let q := gaussianTail (Real.sqrt 2 * K) / 12
  have hq : 0 ≤ q := div_nonneg (gaussianTail_nonneg _) (by norm_num)
  have hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) := by
    rw [gaussianSquareLaw_second]
    positivity
  have hb := averaged_midpoint_from_scalar gaussianSquareLaw gaussianSquareLaw_hypotheses
    t (q * (t * K)) q ht.le (mul_nonneg hq (mul_nonneg ht.le hK)) hq hC
    (fun ι _ a b r hr => by
      have h := gaussian_square_scalar_excess a b K t r hK ht.le hr
      change q * (t * K * euclidSize a - r) ≤ _ at h
      nlinarith)
  rw [gaussianSquareLaw_second] at hb
  convert hb using 1
  ring

end IndependentProducts

namespace IndependentProducts

theorem main_gaussian_12 (t : ℝ) (ht : 0 < t) :
    gaussianTail (8 * Real.sqrt 6 / t) / 4 ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t ∧
    0 < gaussianTail (8 * Real.sqrt 6 / t) / 4 := by
  constructor
  · have h := gaussian_midpoint_parameter t (8 * Real.sqrt 3 / t) ht (by positivity)
    have he : Real.sqrt 2 * (8 * Real.sqrt 3 / t) = 8 * Real.sqrt 6 / t := by
      rw [mul_div_assoc', ← mul_assoc, mul_comm (Real.sqrt 2) 8, mul_assoc,
        ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hr : t * (8 * Real.sqrt 3 / t) / (2 * Real.sqrt 3) - 1 = 3 := by
      field_simp
      ring
    rw [he, hr] at h
    convert h using 1
    ring
  · exact div_pos (gaussianTail_pos _) (by norm_num)

end IndependentProducts

end

end OAI

-- ---- mission target ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (t : ℝ) (ht : 0 < t) :
    gaussianTail (8 * Real.sqrt 6 / t) / 4 ≤
      averagedMidpointModulus (productSpan gaussianSquareLaw)
        (normSeminorm ℝ (productSpan gaussianSquareLaw)) t ∧
    0 < gaussianTail (8 * Real.sqrt 6 / t) / 4 := by
  first
    | exact OAI.IndependentProducts.main_gaussian_12 t ht
    | exact OAI.IndependentProducts.main_gaussian_12 X t ht
    | exact OAI.IndependentProducts.main_gaussian_12
    | (apply OAI.IndependentProducts.main_gaussian_12 <;> assumption)
    | (intros; apply OAI.IndependentProducts.main_gaussian_12 <;> assumption)
