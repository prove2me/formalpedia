-- Prove2me | solution 1 for OAI.IndependentProducts.exponential_scalar_excess
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:46:47.203756+00:00
-- url     : https://prove2.me/submissions/f31e0e57-7a65-4897-ac2e-e40fe2f3b199

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ExponentialExcess.lean:L176-L203
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.exponential_scalar_excess. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
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
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialMixture
import Theorems.Thm_OAI_IndependentProducts_excessConstant_pos
import Theorems.Thm_OAI_IndependentProducts_integral_complex_exp_exponentialLaw
import Theorems.Thm_OAI_IndependentProducts_integral_excess_independent_copy
import Theorems.Thm_OAI_IndependentProducts_weighted_sum_tail

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma integrable_gaussian_abs_excess (K : ℝ) :
    Integrable (fun x : ℝ => max (|x| - 2 * K) 0) (gaussianReal 0 1) := by
  exact (((memLp_id_gaussianReal 1).integrable (by norm_num)).abs.sub (integrable_const _)).sup
    (integrable_const 0)

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

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

lemma weighted_sum_memLp_two [IsProbabilityMeasure P] (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) :
    MemLp (fun ω => ∑ i, a i ^ 2 * U i ω) 2 P := by
  exact memLp_finsetSum _ (fun i _ => (hU i).const_mul _)

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

end GaussianVector
end IndependentProducts

namespace IndependentProducts

lemma excess_nonneg (t r z : ℝ) : 0 ≤ excess t r z := le_max_right _ _

lemma integrable_excess {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P) (t r : ℝ) :
    Integrable (fun ω => excess t r (X ω)) P :=
  ((hX.abs.const_mul t).sub (integrable_const r)).sup (integrable_const 0)

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.ExponentialLaw ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uE

namespace IndependentProducts

lemma exponentialLaw_density : exponentialLaw =
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
  change volume.withDensity (exponentialPDF 1) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [hp.le, hp]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [not_le.mpr hn, hp]

lemma exponentialLaw_positive : ∀ᵐ x ∂exponentialLaw, 0 < x := by
  rw [exponentialLaw_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (self_mem_ae_restrict measurableSet_Ioi)

lemma integral_exponentialLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (∫ x, f x ∂exponentialLaw) = ∫ x in Ioi 0, Real.exp (-x) • f x := by
  rw [exponentialLaw_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma integrable_exponentialLaw_iff {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Integrable f exponentialLaw ↔
      Integrable (fun x => Real.exp (-x) • f x) (volume.restrict (Ioi 0)) := by
  rw [exponentialLaw_density, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma exponentialLaw_integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) exponentialLaw := by
  rw [integrable_exponentialLaw_iff]
  simpa only [IntegrableOn, add_sub_cancel_right, Real.rpow_natCast, smul_eq_mul]
    using Real.GammaIntegral_convergent (s := n + 1) (by positivity)

lemma exponentialLaw_pow_integral (n : ℕ) : (∫ x : ℝ, x ^ n ∂exponentialLaw) = n.factorial := by
  rw [integral_exponentialLaw]
  have h := Real.Gamma_eq_integral (s := n + 1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  exact h.symm

lemma exponentialLaw_mean : (∫ x : ℝ, x ∂exponentialLaw) = 1 := by
  simpa using exponentialLaw_pow_integral 1

lemma exponentialLaw_second : (∫ x : ℝ, x ^ 2 ∂exponentialLaw) = 2 := by
  simpa using exponentialLaw_pow_integral 2

lemma exponentialLaw_memLp : MemLp (fun x : ℝ => x) 2 exponentialLaw :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (exponentialLaw_integrable_pow 2)

end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.ExponentialMixture ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section ExponentialFinite
variable {ι : Type uι} [Fintype ι]

lemma exponential_eval_hasLaw (i : ι) :
    HasLaw (fun x : ι → ℝ => x i) exponentialLaw exponentialVector :=
  (measurePreserving_eval (fun _ => exponentialLaw) i).hasLaw

lemma exponentialVector_positive : ∀ᵐ x : ι → ℝ ∂exponentialVector, ∀ i, 0 < x i := by
  apply ae_all_iff.mpr
  intro i
  exact ((exponential_eval_hasLaw i).ae_iff (by measurability)).mpr exponentialLaw_positive

lemma exponential_vector_complexMGF (z : ι → ℂ) (hz : ∀ i, (z i).re < 1) :
    (∫ x : ι → ℝ, Complex.exp (∑ i, z i * x i) ∂exponentialVector) =
      ∏ i, 1 / (1 - z i) := by
  simp only [Complex.exp_sum]
  unfold exponentialVector
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp (z i * x))]
  apply Finset.prod_congr rfl
  intro i hi
  exact integral_complex_exp_exponentialLaw _ (hz i)

lemma exponential_vector_characteristic (a : ι → ℝ) (q : ℝ) :
    (∫ x : ι → ℝ, Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I) ∂exponentialVector) =
      ∏ i, 1 / (1 - (q * a i : ℝ) * Complex.I) := by
  have he : (fun x : ι → ℝ => Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I)) =
      (fun x => Complex.exp (∑ i, ((q * a i : ℝ) : ℂ) * Complex.I * x i)) := by
    funext x
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  exact exponential_vector_complexMGF _ (fun i => by simp)

lemma exponential_difference_charFun (a : ι → ℝ) (q : ℝ) :
    charFun ((exponentialVector.prod exponentialVector).map (exponentialDifference a)) q =
      ∏ i, 1 / (1 + ((q * a i : ℝ) : ℂ) ^ 2) := by
  rw [charFun_apply_real, integral_map (by unfold exponentialDifference; fun_prop) (by fun_prop)]
  have he : (fun z : (ι → ℝ) × (ι → ℝ) =>
      Complex.exp ((q : ℂ) * exponentialDifference a z * Complex.I)) =
      (fun z => Complex.exp ((q : ℂ) * (∑ i, a i * z.1 i) * Complex.I) *
        Complex.exp ((-(q) : ℝ) * (∑ i, a i * z.2 i) * Complex.I)) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    simp only [exponentialDifference, mul_sub, Finset.sum_sub_distrib,
      Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  rw [he, integral_prod_mul
      (fun x : ι → ℝ => Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I))
      (fun x : ι → ℝ => Complex.exp ((-(q) : ℝ) * (∑ i, a i * x i) * Complex.I)),
    exponential_vector_characteristic, exponential_vector_characteristic,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [div_mul_div_comm, one_mul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma exponentialVariance_nonneg (a : ι → ℝ) (u : ι → ℝ) : 0 ≤ exponentialVariance a u := by
  unfold exponentialVariance
  positivity

lemma measurable_exponentialVariance (a : ι → ℝ) : Measurable (exponentialVariance a) := by
  unfold exponentialVariance
  fun_prop

lemma measurable_exponentialMixture (a : ι → ℝ) : Measurable (exponentialMixture a) :=
  (((measurable_exponentialVariance a).comp measurable_fst).sqrt).mul measurable_snd

lemma gaussian_scaled_characteristic (v q : ℝ) (hv : 0 ≤ v) :
    (∫ g : ℝ, Complex.exp ((q : ℂ) * ((Real.sqrt v * g : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (-((v * q ^ 2 / 2 : ℝ) : ℂ)) := by
  have he : (fun g : ℝ => Complex.exp ((q : ℂ) * ((Real.sqrt v * g : ℝ) : ℂ) * Complex.I)) =
      (fun g : ℝ => Complex.exp (((q * Real.sqrt v : ℝ) : ℂ) * g * Complex.I)) := by
    funext g
    congr 1
    push_cast
    ring
  rw [he, ← charFun_apply_real, charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, NNReal.coe_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  have hs : ((Real.sqrt v : ℝ) : ℂ) ^ 2 = (v : ℂ) := by exact_mod_cast Real.sq_sqrt hv
  rw [mul_pow, hs]
  ring

lemma exponential_mixture_charFun (a : ι → ℝ) (q : ℝ) :
    charFun ((exponentialVector.prod (gaussianReal 0 1)).map (exponentialMixture a)) q =
      ∏ i, 1 / (1 + ((q * a i : ℝ) : ℂ) ^ 2) := by
  rw [charFun_apply_real, integral_map (measurable_exponentialMixture a).aemeasurable (by fun_prop)]
  have hint : Integrable (fun z : (ι → ℝ) × ℝ =>
      Complex.exp ((q : ℂ) * exponentialMixture a z * Complex.I))
      (exponentialVector.prod (gaussianReal 0 1)) := by
    apply Integrable.of_bound (by exact ((by fun_prop : Measurable (fun x : ℝ =>
      Complex.exp ((q : ℂ) * x * Complex.I))).comp (measurable_exponentialMixture a)).aestronglyMeasurable) 1
    filter_upwards [] with z
    simp [Complex.norm_exp]
  rw [integral_prod _ hint]
  have he : (fun u : ι → ℝ => ∫ g : ℝ,
      Complex.exp ((q : ℂ) * exponentialMixture a (u, g) * Complex.I) ∂gaussianReal 0 1) =ᵐ[exponentialVector]
      (fun u => Complex.exp (∑ i, -(((q * a i : ℝ) : ℂ) ^ 2) * u i)) := by
    filter_upwards [exponentialVector_positive (ι := ι)] with u hu
    change (∫ g : ℝ, Complex.exp ((q : ℂ) * ((Real.sqrt (exponentialVariance a u) * g : ℝ) : ℂ) * Complex.I)
      ∂gaussianReal 0 1) = _
    rw [gaussian_scaled_characteristic _ _ (exponentialVariance_nonneg a u)]
    have hv : exponentialVariance a u * q ^ 2 / 2 = ∑ i, (q * a i) ^ 2 * u i := by
      have hmax : ∀ i, max (u i) 0 = u i := fun i => max_eq_left (hu i).le
      simp only [exponentialVariance, hmax]
      calc
        2 * (∑ i, a i ^ 2 * u i) * q ^ 2 / 2 = (∑ i, a i ^ 2 * u i) * q ^ 2 := by ring
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    rw [hv]
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Finset.sum_neg_distrib, neg_mul]

  rw [integral_congr_ae he, exponential_vector_complexMGF _ (fun i => by
    simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    nlinarith [sq_nonneg (q * a i)])]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [sub_neg_eq_add]

lemma exponential_difference_mixture (a : ι → ℝ) :
    (exponentialVector.prod exponentialVector).map (exponentialDifference a) =
      (exponentialVector.prod (gaussianReal 0 1)).map (exponentialMixture a) := by
  apply Measure.ext_of_charFun
  funext q
  rw [exponential_difference_charFun, exponential_mixture_charFun]

end ExponentialFinite
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.ExponentialExcess ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section ExponentialExcess
variable {ι : Type uι} [Fintype ι]

lemma exponential_eval_memLp (i : ι) : MemLp (fun u : ι → ℝ => u i) 2 exponentialVector :=
  exponentialLaw_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ => exponentialLaw) i)

lemma exponential_positive_eval_memLp (i : ι) : MemLp (fun u : ι → ℝ => max (u i) 0) 2 exponentialVector := by
  apply MemLp.ae_eq (f := fun u : ι → ℝ => u i) ?_ (exponential_eval_memLp i)
  filter_upwards [exponentialVector_positive (ι := ι)] with u hu
  exact (max_eq_left (hu i).le).symm

lemma exponential_positive_eval_mean (i : ι) :
    (∫ u : ι → ℝ, max (u i) 0 ∂exponentialVector) = 1 := by
  calc
    _ = ∫ u : ι → ℝ, u i ∂exponentialVector := by
      apply integral_congr_ae
      filter_upwards [exponentialVector_positive (ι := ι)] with u hu
      exact max_eq_left (hu i).le
    _ = 1 := (exponential_eval_hasLaw i).integral_comp (by fun_prop) |>.trans exponentialLaw_mean

lemma exponential_positive_eval_second (i : ι) :
    (∫ u : ι → ℝ, (max (u i) 0) ^ 2 ∂exponentialVector) = 2 := by
  calc
    _ = ∫ u : ι → ℝ, (u i) ^ 2 ∂exponentialVector := by
      apply integral_congr_ae
      filter_upwards [exponentialVector_positive (ι := ι)] with u hu
      rw [max_eq_left (hu i).le]
    _ = 2 := (exponential_eval_hasLaw i).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop) |>.trans exponentialLaw_second

lemma exponentialVariance_tail (a : ι → ℝ) (ha : 0 < ∑ i, a i ^ 2) :
    1 / 8 ≤ (exponentialVector (ι := ι)).real {u | (∑ i, a i ^ 2) ≤ exponentialVariance a u} := by
  have h := weighted_sum_tail a (fun i (u : ι → ℝ) => max (u i) 0)
    exponential_positive_eval_memLp (fun _ => by fun_prop) (fun _ _ => le_max_right _ _)
    exponential_positive_eval_mean 2 (by norm_num)
    (fun i => (exponential_positive_eval_second i).le) ha
  have he : {u : ι → ℝ | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * max (u i) 0} =
      {u : ι → ℝ | (∑ i, a i ^ 2) ≤ exponentialVariance a u} := by
    ext u
    simp only [Set.mem_ofPred_eq, exponentialVariance]
    constructor <;> intro hh <;> linarith
  norm_num only [show (4 * (2 : ℝ)) = 8 by norm_num] at h
  rwa [he] at h

lemma integrable_exponentialVariance (a : ι → ℝ) : Integrable (exponentialVariance a) exponentialVector :=
  ((weighted_sum_memLp_two a (fun i (u : ι → ℝ) => max (u i) 0)
    exponential_positive_eval_memLp).integrable (by norm_num)).const_mul 2

lemma integrable_exponentialMixture (a : ι → ℝ) :
    Integrable (exponentialMixture a) (exponentialVector.prod (gaussianReal 0 1)) := by
  have hs : Integrable (fun u => Real.sqrt (exponentialVariance a u)) exponentialVector := by
    apply ((integrable_exponentialVariance a).add (integrable_const 1)).mono'
      (measurable_exponentialVariance a).sqrt.aestronglyMeasurable
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (exponentialVariance a u) ≤ exponentialVariance a u + 1
    have hv := exponentialVariance_nonneg a u
    have hsq := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg (exponentialVariance a u)
    nlinarith [sq_nonneg (Real.sqrt (exponentialVariance a u) - 1)]
  exact hs.mul_prod ((memLp_id_gaussianReal 1).integrable (by norm_num))

lemma excess_scaled_lower (K s v x : ℝ) (hs : 0 ≤ s) (hsv : s ≤ v) :
    s * max (|x| - 2 * K) 0 ≤ excess 1 (2 * K * s) (v * x) := by
  unfold excess
  rw [abs_mul, abs_of_nonneg (hs.trans hsv), one_mul, mul_max_of_nonneg _ _ hs, mul_zero]
  apply max_le_max_right
  have h := mul_le_mul_of_nonneg_right hsv (abs_nonneg x)
  nlinarith

lemma exponential_mixture_excess (a : ι → ℝ) (K : ℝ) :
    (1 / 8 : ℝ) * Real.sqrt (∑ i, a i ^ 2) *
      (∫ g : ℝ, max (|g| - 2 * K) 0 ∂gaussianReal 0 1) ≤
      ∫ z : (ι → ℝ) × ℝ, excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2))
        (exponentialMixture a z) ∂exponentialVector.prod (gaussianReal 0 1) := by
  let S := ∑ i, a i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hS0 : S = 0
  · change (1 / 8 : ℝ) * Real.sqrt S * _ ≤ _
    rw [hS0, Real.sqrt_zero, mul_zero, zero_mul]
    exact integral_nonneg (fun _ => excess_nonneg _ _ _)
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  let A : Set (ι → ℝ) := {u | S ≤ exponentialVariance a u}
  have hAm : MeasurableSet A := measurableSet_le measurable_const (measurable_exponentialVariance a)
  let c := Real.sqrt S * (∫ g : ℝ, max (|g| - 2 * K) 0 ∂gaussianReal 0 1)
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun _ => le_max_right _ _)
  have hint := integrable_excess (integrable_exponentialMixture a) 1 (2 * K * Real.sqrt S)
  rw [integral_prod _ hint]
  calc
    _ = (1 / 8 : ℝ) * c := by dsimp [c, S]; ring
    _ ≤ exponentialVector.real A * c :=
      mul_le_mul_of_nonneg_right (exponentialVariance_tail a hSp) hc
    _ = ∫ u : ι → ℝ, A.indicator (fun _ => c) u ∂exponentialVector := by
      simp [integral_indicator hAm, mul_comm]
    _ ≤ ∫ u : ι → ℝ, ∫ g : ℝ, excess 1 (2 * K * Real.sqrt S)
        (exponentialMixture a (u, g)) ∂gaussianReal 0 1 ∂exponentialVector := by
      apply integral_mono ((integrable_const _).indicator hAm) hint.integral_prod_left
      intro u
      by_cases hu : u ∈ A
      · rw [Set.indicator_of_mem hu]
        change Real.sqrt S * (∫ g, max (|g| - 2 * K) 0 ∂gaussianReal 0 1) ≤ _
        rw [← integral_const_mul]
        simp only [exponentialMixture]
        apply integral_mono ((integrable_gaussian_abs_excess K).const_mul _)
          (integrable_excess (((memLp_id_gaussianReal 1).integrable (by norm_num)).const_mul _) _ _)
        intro g
        exact excess_scaled_lower K (Real.sqrt S) (Real.sqrt (exponentialVariance a u)) g
          (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hu)
      · rw [Set.indicator_of_notMem hu]
        exact integral_nonneg fun _ => excess_nonneg _ _ _

lemma integrable_exponential_linear (a : ι → ℝ) (b : ℝ) :
    Integrable (fun u : ι → ℝ => b + ∑ i, a i * u i) exponentialVector := by
  apply (integrable_const b).add
  exact integrable_finsetSum _ (fun i _ => ((exponential_eval_memLp i).integrable (by norm_num)).const_mul _)

lemma exponential_scalar_excess_unit (a : ι → ℝ) (b K : ℝ) :
    excessConstant K * Real.sqrt (∑ i, a i ^ 2) ≤
      ∫ u : ι → ℝ, excess 1 (K * Real.sqrt (∑ i, a i ^ 2)) (b + ∑ i, a i * u i) ∂exponentialVector := by
  have hcopy := integral_excess_independent_copy (integrable_exponential_linear a b)
    (by norm_num : (0 : ℝ) ≤ 1) (K * Real.sqrt (∑ i, a i ^ 2))
  have hd : ∀ z : (ι → ℝ) × (ι → ℝ),
      excess 1 (K * Real.sqrt (∑ i, a i ^ 2))
      (((b + ∑ i, a i * z.1 i) - (b + ∑ i, a i * z.2 i)) / 2) =
      excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2)) (exponentialDifference a z) / 2 := by
    intro z
    have he : (b + ∑ i, a i * z.1 i) - (b + ∑ i, a i * z.2 i) = exponentialDifference a z := by
      simp only [exponentialDifference, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he]
    unfold excess
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul, one_mul,
      ← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  simp_rw [hd] at hcopy
  rw [integral_div] at hcopy
  have hm : (∫ z : (ι → ℝ) × (ι → ℝ),
      excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2)) (exponentialDifference a z)
      ∂exponentialVector.prod exponentialVector) =
      ∫ z : (ι → ℝ) × ℝ, excess 1 (2 * K * Real.sqrt (∑ i, a i ^ 2))
        (exponentialMixture a z) ∂exponentialVector.prod (gaussianReal 0 1) := by
    have h := exponential_difference_mixture a
    have hm : Measurable (exponentialDifference a) := by unfold exponentialDifference; fun_prop
    rw [← integral_map hm.aemeasurable (by unfold excess; fun_prop), h,
      integral_map (measurable_exponentialMixture a).aemeasurable (by unfold excess; fun_prop)]
  rw [hm] at hcopy
  have hlow := exponential_mixture_excess a K
  unfold excessConstant
  nlinarith

end ExponentialExcess
end IndependentProducts

namespace IndependentProducts

lemma excess_threshold_scale (t K s r x : ℝ) (ht : 0 ≤ t) (hr : r ≤ t * K * s) :
    t * excess 1 (K * s) x ≤ excess t r x := by
  unfold excess
  rw [one_mul, mul_max_of_nonneg _ _ ht, mul_zero]
  apply max_le_max_right
  nlinarith

lemma exponential_scalar_excess {ι : Type uι} [Fintype ι] (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 < K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (t * excessConstant K) * Real.sqrt (∑ i, a i ^ 2) - (excessConstant K / K) * r ≤
      ∫ u : ι → ℝ, excess t r (b + ∑ i, a i * u i) ∂exponentialVector := by
  let s := Real.sqrt (∑ i, a i ^ 2)
  have hc : 0 ≤ excessConstant K := (excessConstant_pos K).le
  by_cases hgood : r ≤ t * K * s
  · calc
      _ ≤ t * (excessConstant K * s) := by
        have hh := mul_nonneg (div_nonneg hc hK.le) hr
        dsimp [s]
        nlinarith
      _ ≤ t * (∫ u : ι → ℝ, excess 1 (K * s) (b + ∑ i, a i * u i) ∂exponentialVector) :=
        mul_le_mul_of_nonneg_left (exponential_scalar_excess_unit a b K) ht
      _ = ∫ u : ι → ℝ, t * excess 1 (K * s) (b + ∑ i, a i * u i) ∂exponentialVector :=
        (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono
        ((integrable_excess (integrable_exponential_linear a b) 1 (K * s)).const_mul t)
        (integrable_excess (integrable_exponential_linear a b) t r)
        (fun u => excess_threshold_scale t K s r (b + ∑ i, a i * u i) ht hgood)
  · have hbad : t * K * s ≤ r := (lt_of_not_ge hgood).le
    have hd : t * s ≤ r / K := (le_div_iff₀ hK).mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hd hc
    have hn : (t * excessConstant K) * s - (excessConstant K / K) * r ≤ 0 := by
      calc
        _ = excessConstant K * (t * s) - excessConstant K * (r / K) := by ring
        _ ≤ 0 := sub_nonpos.mpr hh
    exact hn.trans (integral_nonneg (fun _ => excess_nonneg _ _ _))

end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι

theorem solution {ι : Type uι} [Fintype ι] (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 < K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (t * excessConstant K) * Real.sqrt (∑ i, a i ^ 2) - (excessConstant K / K) * r ≤
      ∫ u : ι → ℝ, excess t r (b + ∑ i, a i * u i) ∂exponentialVector := by
  first
    | exact OAI.IndependentProducts.exponential_scalar_excess a b K t r hK ht hr
    | exact OAI.IndependentProducts.exponential_scalar_excess
    | (apply OAI.IndependentProducts.exponential_scalar_excess <;> assumption)
    | (intros; apply OAI.IndependentProducts.exponential_scalar_excess <;> assumption)
