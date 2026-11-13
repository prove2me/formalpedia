-- Prove2me | solution 1 for OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:10:35.352673+00:00
-- url     : https://prove2.me/submissions/845bf7db-bf71-4f62-9ba7-fccd979fb0b9

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_spectralCanonical_identification
import Theorems.Thm_OAI_InvariantIsing_spinPriorContactObjective_exists_minimum
import Theorems.Thm_OAI_InvariantIsing_spinPriorContact_limit_tail_order
import Theorems.Thm_OAI_InvariantIsing_spinPriorPerturbation_arrayResidual_bound
import Theorems.Thm_OAI_InvariantIsing_spinPriorPerturbation_minimizers_constantDiagonal
import Theorems.Thm_OAI_InvariantIsing_spinPriorPerturbedArrayLaw_ward_limits
import Theorems.Thm_OAI_InvariantIsing_spinPriorRestrictedContactPressure_field_le
import Theorems.Thm_OAI_InvariantIsing_spinPriorRestrictedContact_zero_cost

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

lemma integrable_spectral_composition (R : ℝ → ℝ) (hR : Continuous R)
    (p : OverlapPath) : Integrable (fun r => R (deficit p r)) pathMeasure := by
  change IntegrableOn (fun r => R (deficit p r)) (Set.Ioo (0 : ℝ) 1)
  exact ((hR.comp (continuous_deficit p)).continuousOn.integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

lemma gaussian_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin n => g i)
      gaussianCoordinates (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have he := hs.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

lemma cylinderField_eq_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) (g : ℕ → ℝ) :
    cylinderField a g = ∑ i : Fin n, a i*g i := by
  classical
  rw [cylinderField, a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*g i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

lemma cylinderField_law (a : ℕ →₀ ℝ) :
    gaussianCoordinates.map (cylinderField a) =
      gaussianReal 0 ((a.sum (fun _ c => c^2)).toNNReal) := by
  classical
  let n := a.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he : cylinderField a = (fun g : Fin n → ℝ => ∑ i : Fin n, a i*g i) ∘
      (fun g : ℕ → ℝ => fun i : Fin n => g i) := by
    funext g
    exact cylinderField_eq_prefix a ha g
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    (gaussian_prefix_measurePreserving n).map_eq,(gaussian_weighted_sum_law (fun i : Fin n => a i)).map_eq]
  congr 2
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => a i^2) n

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

lemma partition_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp ((p:ℝ)*H x)) ν) :
    (∫ x, Real.exp (H x) ∂ν)^p ≤ ∫ x, Real.exp ((p:ℝ)*H x) ∂ν := by
  simpa only [Function.comp_def, Real.exp_nat_mul] using
    (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (H x)).le)) h1
      (by simpa only [Function.comp_def, Real.exp_nat_mul] using hp)

lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp

 

lemma gaussian_field_exp_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (t : ℝ) :
    Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) ∧
      (∫ ω, ∫ x, Real.exp (t*H (ω,x)) ∂ν ∂μ) ≤ Real.exp (t^2*K/2) := by
  have he : Measurable (fun z => Real.exp (t*H z)) := hm.const_mul t |>.exp
  have hsec : ∀ x, Integrable (fun ω => Real.exp (t*H (ω,x))) μ := by
    intro x
    have hx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
    apply (integrable_map_measure (g := fun y : ℝ => Real.exp (t*y)) (μ := μ) (by fun_prop) hx.aemeasurable).mp
    rw [hg x]
    exact integrable_exp_mul_gaussianReal t
  have hb (x : X) : (∫ ω, Real.exp (t*H (ω,x)) ∂μ) ≤ Real.exp (t^2*K/2) := by
    have h := mgf_gaussianReal (X := fun ω => H (ω, x))
      (hg x) t
    simp only [mgf, zero_mul, zero_add] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hv x) (sq_nonneg t)]
  have hi : Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) := by
    apply (integrable_prod_iff' he.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    apply Integrable.of_bound he.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      (Real.exp (t^2*K/2))
    refine Filter.Eventually.of_forall fun x => ?_
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (integral_nonneg (μ := μ) (f := fun ω : Ω => Real.exp (t*H (ω,x))) (fun ω => (Real.exp_pos _).le))] using hb x
  refine ⟨hi, ?_⟩
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _ : X, Real.exp (t^2*K/2) ∂ν :=
      integral_mono hi.integral_prod_right (integrable_const _) hb
    _ = _ := by simp

lemma abs_le_exp_add_exp_neg (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.add_one_le_exp (-x), Real.exp_pos x]

lemma gaussian_field_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) : Integrable H (μ.prod ν) := by
  have hp := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  have hn := (gaussian_field_exp_integrable (ν := ν) hm hg hv (-1:ℝ)).1
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, one_mul, neg_one_mul] using abs_le_exp_add_exp_neg (H z)

 

lemma gaussian_partition_moments {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (p : ℕ) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧
      (∫ ω, Z ω^p ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) ∧
      (∫ ω, (Z ω^p)⁻¹ ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  change Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧ _
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have h1 := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  simp only [one_mul] at h1
  obtain ⟨hip, hbp⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (p:ℝ)
  obtain ⟨hin, hbn⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (-(p:ℝ))
  have hp : ∀ᵐ ω ∂μ, Z ω^p ≤ ∫ x, Real.exp ((p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [h1.prod_right_ae, hip.prod_right_ae] with ω hω hωp
    exact partition_pow_le p hω hωp
  have hn : ∀ᵐ ω ∂μ, (Z ω^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [hH.prod_right_ae, h1.prod_right_ae, hin.prod_right_ae] with ω hω hω1 hωn
    exact partition_inv_pow_le p hω hω1 hωn
  have hz (ω) : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hpint : Integrable (fun ω => Z ω^p) μ := by
    apply hip.integral_prod_left.mono' (hmZ.pow_const p).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hz _) _)] using hp
  have hnint : Integrable (fun ω => (Z ω^p)⁻¹) μ := by
    apply hin.integral_prod_left.mono' ((hmZ.pow_const p).inv).aestronglyMeasurable
    simpa only [Pi.inv_apply, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hz _) _))] using hn
  refine ⟨hpint, hnint, (integral_mono_ae hpint hip.integral_prod_left hp).trans hbp, ?_⟩
  simpa only [neg_sq] using (integral_mono_ae hnint hin.integral_prod_left hn).trans hbn

lemma log_square_le_partition_moments {x : ℝ} (hx : 0 < x) :
    (Real.log x)^2 ≤ 2*(x^2+(x^2)⁻¹) := by
  have hp := Real.log_le_sub_one_of_pos hx
  have hn := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hn
  have hB : |Real.log x| ≤ x+x⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [inv_pos.mpr hx]
  have hs := pow_le_pow_left₀ (abs_nonneg (Real.log x)) hB 2
  rw [sq_abs] at hs
  rw [← inv_pow]
  nlinarith [sq_nonneg (x-x⁻¹)]

 

lemma gaussian_log_partition_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => (Real.log (Z ω))^2) μ ∧
    (∫ ω, (Real.log (Z ω))^2 ∂μ) ≤ 4*Real.exp (2*K) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hip,hin,hbp,hbn⟩ := gaussian_partition_moments (ν := ν) hm hg hv 2
  change Integrable (fun ω => Z ω^2) μ at hip
  change Integrable (fun ω => (Z ω^2)⁻¹) μ at hin
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have he := (gaussian_field_exp_integrable (ν := ν) hm hg hv 1).1
  simp only [one_mul] at he
  have hb : ∀ᵐ ω ∂μ, (Real.log (Z ω))^2 ≤ 2*(Z ω^2+(Z ω^2)⁻¹) := by
    filter_upwards [hH.prod_right_ae, he.prod_right_ae] with ω hω hωe
    apply log_square_le_partition_moments
    exact (Real.exp_pos _).trans_le (exp_integral_le_partition hω hωe)
  have hi : Integrable (fun ω => (Real.log (Z ω))^2) μ := by
    apply ((hip.add hin).const_mul 2).mono' (hmZ.log.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (Z ω)))] using hω
  refine ⟨hi, (integral_mono_ae hi ((hip.add hin).const_mul 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hip hin]
  have hx : (2:ℝ)^2*K/2 = 2*K := by ring
  simp only [Nat.cast_ofNat] at hbp hbn
  rw [hx] at hbp hbn
  linarith



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma joint_integrable_square_of_uniform_conditionals {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] {P : Measure Ω} {Q : Measure Γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {F : Ω × Γ → ℝ}
    (hm : Measurable F) {C : ℝ}
    (hi : ∀ ω, Integrable (fun g => F (ω,g)^2) Q)
    (hb : ∀ ω, (∫ g, F (ω,g)^2 ∂Q) ≤ C) :
    Integrable (fun z => F z^2) (P.prod Q) := by
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  apply integrable_of_measurable_abs_le
    ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact hb ω

lemma integrable_exp_of_integer_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (hm : Measurable Y)
    (he : ∀ n : ℤ, Integrable (fun x => Real.exp ((n:ℝ)*Y x)) ν) (t : ℝ) :
    Integrable (fun x => Real.exp (t*Y x)) ν := by
  obtain ⟨n,hn⟩ := exists_nat_gt |t|
  have hp := he (n:ℤ)
  have hm' := he (-(n:ℤ))
  apply (hp.add hm').mono' (hm.const_mul t |>.exp.aestronglyMeasurable)
  refine ae_of_all _ fun x => ?_
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Int.cast_natCast,Int.cast_neg]
  by_cases hy : 0 ≤ Y x
  · have h : t*Y x ≤ (n:ℝ)*Y x := mul_le_mul_of_nonneg_right ((le_abs_self t).trans hn.le) hy
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have h : t*Y x ≤ -(n:ℝ)*Y x := mul_le_mul_of_nonpos_right (by linarith [neg_abs_le t]) (le_of_not_ge hy)
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

lemma cylinder_cgf_second {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun g => (cgf (fun x => cylinderField (a x) g) ν t)^2) gaussianCoordinates ∧
      (∫ g, (cgf (fun x => cylinderField (a x) g) ν t)^2 ∂gaussianCoordinates) ≤
        4*Real.exp (2*(t^2*K)) := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (a z.2) z.1) :=
    (measurable_cylinderFields a).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((a x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((a x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
  exact gaussian_log_partition_second (ν := ν) hm (fun x => cylinder_scaled_law a x t) hv

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

open ProbabilityTheory Filter

lemma mem_interior_integrableExpSet_of_all {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν)
    (t : ℝ) : t ∈ interior (integrableExpSet Y ν) := by
  have h : integrableExpSet Y ν = univ := Set.eq_univ_of_forall he
  simp [h]

lemma contDiff_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ContDiff ℝ 2 (cgf Y ν) :=
  contDiff_iff_contDiffAt.mpr (fun t =>
    (analyticAt_cgf (mem_interior_integrableExpSet_of_all he t)).contDiffAt)

lemma convexOn_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ConvexOn ℝ univ (cgf Y ν) := by
  have hd := contDiff_cgf_of_all_exp he
  apply convexOn_univ_of_deriv2_nonneg (hd.differentiable (by norm_num)) hd.differentiable_deriv_two
  intro t
  have hv := variance_nonneg Y (ν.tilted (t*Y ·))
  rw [variance_tilted_mul (mem_interior_integrableExpSet_of_all he t)] at hv
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, Function.iterate_succ_apply'] using hv

end IsingPerceptron

namespace IsingPerceptron

lemma integral_tilted_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) :
    (∫ x, F x ∂ν.tilted H) = (∫ x, Real.exp (H x)*F x ∂ν)/(∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

lemma measurable_random_tilted_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H F : Ω × X → ℝ} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun ω => ∫ x, F (ω,x) ∂(ν ω).tilted (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  simp_rw [integral_tilted_ratio]
  exact ((hH.exp.mul hF).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((hH.exp).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := _root_.MeasureTheory.integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

end IsingPerceptron

namespace IsingPerceptron

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false, if_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma featureCoefficients_variance {I : Type*} [Fintype I]
    (t : I → ℕ) (ht : Function.Injective t) (a : I → ℝ) :
    (featureCoefficients t a).sum (fun _ c => c^2) = ∑ i, (a i)^2 := by
  rw [← cylinderCross_self,featureCoefficients_diagonal t t (fun _ _ h => ht h)]
  simp [pow_two]

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true, if_true,ih]

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true, if_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma treeFeatureTag_injective {J : Type*} [Encodable J] (n : ℕ) (v : LabeledLeaf n) :
    Function.Injective (treeFeatureTag (J := J) n v) := by
  intro i j h
  exact ((treeFeatureTag_cross n v v i j).mp h).1

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

lemma logMean_bounds (μ : Measure A) [IsProbabilityMeasure μ]
    {F : A → ℝ} (hF : Measurable F) {b K : ℝ} (hb : 0 < b)
    (hbound : ∀ a, |F a| ≤ K) : |logMean b μ F| ≤ K := by
  have hi : Integrable (fun a => Real.exp (b*F a)) μ := by
    apply Integrable.of_bound ((measurable_const.mul hF).exp).aestronglyMeasurable (Real.exp (b*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le)
  have hlow : Real.exp (-b*K) ≤ ∫ a, Real.exp (b*F a) ∂μ := by
    calc
      _ = ∫ _, Real.exp (-b*K) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro a
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp (hbound a)).1
        nlinarith
  have hhigh : (∫ a, Real.exp (b*F a) ∂μ) ≤ Real.exp (b*K) := by
    calc
      _ ≤ ∫ _, Real.exp (b*K) ∂μ := integral_mono hi (integrable_const _) (fun a =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le))
      _ = _ := by simp
  have hM := integral_exp_pos μ F hi
  rw [abs_le, logMean]
  constructor
  · apply (le_div_iff₀ hb).mpr
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have := Real.log_le_log hM hhigh
    rw [Real.log_exp] at this
    nlinarith

end IsingPerceptron

namespace IsingPerceptron

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma cgf_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H Y : X → ℝ) (t : ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (het : Integrable (fun x => Real.exp (H x+t*Y x)) ν) :
    cgf Y (gibbsProbability ν H) t =
      Real.log (referencePartition ν (fun x => H x+t*Y x)) - Real.log (referencePartition ν H) := by
  rw [gibbsProbability_eq_tilted _ _ he]
  unfold cgf mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (ne_of_gt (_root_.MeasureTheory.integral_exp_pos het))
    (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))]
  rfl

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma hasDerivAt_mean_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} (ν : Ω → Measure X) (Y : Ω → X → ℝ)
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) P)
    (hd : ∀ t, Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)) P)
    (v : ℝ) :
    HasDerivAt (fun t => ∫ ω, cgf (Y ω) (ν ω) t ∂P)
      (∫ ω, ∫ x, Y ω x ∂(ν ω).tilted (fun x => v*Y ω x) ∂P) v := by
  let D : ℝ → Ω → ℝ := fun t ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)
  let B : Ω → ℝ := fun ω => |D (v-1) ω|+|D (v+1) ω|
  have hderiv : ∀ᵐ ω ∂P, ∀ t : ℝ, HasDerivAt (cgf (Y ω) (ν ω)) (D t ω) t := by
    filter_upwards [he] with ω hω
    intro t
    dsimp [D]
    rw [integral_tilted_mul_self (mem_interior_integrableExpSet_of_all hω t)]
    exact (analyticAt_cgf (mem_interior_integrableExpSet_of_all hω t)).differentiableAt.hasDerivAt
  have hB : Integrable B P := (hd (v-1)).abs.add (hd (v+1)).abs
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (v-1) (v+1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) (hi v)
    (hd v).aestronglyMeasurable (bound := B) ?_ hB ?_).2
  · filter_upwards [he,hderiv] with ω hω hdω
    intro t ht
    have hmono := (convexOn_cgf_of_all_exp hω).monotoneOn_deriv
      (fun x _ => (hdω x).differentiableAt)
    have hlo := hmono (mem_univ _) (mem_univ _) ht.1.le
    have hhi := hmono (mem_univ _) (mem_univ _) ht.2.le
    rw [(hdω (v-1)).deriv,(hdω t).deriv] at hlo
    rw [(hdω t).deriv,(hdω (v+1)).deriv] at hhi
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by dsimp [B] <;> linarith [neg_abs_le (D (v-1) ω),abs_nonneg (D (v+1) ω)],
      by dsimp [B] <;> linarith [le_abs_self (D (v+1) ω),abs_nonneg (D (v-1) ω)]⟩
  · filter_upwards [hderiv] with ω hω
    exact fun t _ => hω t

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron


lemma matrix_sum_le_of_offDiagonal {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j ≤ -ε) :
    ∑ i, ∑ j, B i j ≤ (n : ℝ) * (D - (n - 1 : ℝ) * ε) := by
  classical
  have hrow : ∀ i, ∑ j, B i j ≤ D - (n - 1 : ℝ) * ε := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag i]
    have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
    have h := Finset.sum_le_sum (s := Finset.univ.erase i) (f := fun j => B i j)
      (g := fun _ => -ε) (fun j hj => hoff i j (Ne.symm (Finset.mem_erase.mp hj).1))
    have hcard : (Finset.univ.erase i).card = n - 1 := by simp
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
    linarith
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)

lemma posSemidef_sum_nonneg {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) : 0 ≤ ∑ i, ∑ j, B i j := by
  simpa [dotProduct, Matrix.mulVec] using hB.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))

lemma no_large_negative_block {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hn : 0 < n) (hsize : D < (n - 1 : ℝ) * ε)
    (hB : B.PosSemidef) (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j < -ε) : False := by
  have hs := matrix_sum_le_of_offDiagonal hdiag (fun i j h => (hoff i j h).le)
  have hp := posSemidef_sum_nonneg hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma measurableSet_negative_finite (n : ℕ) (ε : ℝ) :
    MeasurableSet {b : Fin n → Fin n → ℝ | ∀ i j, i ≠ j → b i j < -ε} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => ?_)))
  exact measurableSet_lt
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

lemma mem_negativeBlock_succ {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) {ω : Ω} {ε : ℝ} {n : ℕ} :
    ω ∈ negativeBlock B ε (n + 1) ↔
      ω ∈ negativeBlock B ε n ∧ ∀ i : Fin n, B ω i n < -ε := by
  constructor
  · intro h
    constructor
    · intro i j hij
      exact h i.castSucc j.castSucc (fun he => hij (Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) he)))
    · intro i
      exact h i.castSucc (Fin.last n) (by intro he; have := congrArg Fin.val he; simp at this; omega)
  · rintro ⟨h, ht⟩ i j hij
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · exact h ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun he => hij (Fin.ext (congrArg (fun t : Fin n => t.val) he)))
      · have hjn : j.val = n := by omega
        change B ω i.val j.val < -ε
        rw [hjn]
        exact ht ⟨i.val, hi⟩
    · have hin : i.val = n := by omega
      by_cases hj : j.val < n
      · change B ω i.val j.val < -ε
        rw [hin, hsym]
        exact ht ⟨j.val, hj⟩
      · have hjn : j.val = n := by omega
        exact (hij (Fin.ext (hin.trans hjn.symm))).elim

lemma negativeBlock_two {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) (ε : ℝ) :
    negativeBlock B ε 2 = {ω | B ω 0 1 < -ε} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h
    · change B ω 1 0 < -ε
      rw [hsym]
      exact h
    · exact (hij rfl).elim

lemma negativeBlock_next_probability {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (ε : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    μ.real (negativeBlock B ε n) * μ.real {ω | B ω 0 1 < -ε} ≤
      μ.real (negativeBlock B ε (n + 1)) := by
  classical
  let A := negativeBlock B ε n
  let Bad := fun i : Fin n => A ∩ {ω | -ε ≤ B ω i n}
  have hbase : μ.real {ω | -ε ≤ B ω 0 1} = 1 - μ.real {ω | B ω 0 1 < -ε} := by
    have hset : {ω | -ε ≤ B ω 0 1} = {ω | B ω 0 1 < -ε}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_lt (hm 0 1) measurable_const), probReal_univ]
  have hbad : ∀ i : Fin n, μ.real (Bad i) =
      μ.real A * (1 - μ.real {ω | B ω 0 1 < -ε}) / n := by
    intro i
    have h := hGG n hn i {b | ∀ i j, i ≠ j → b i j < -ε}
      (measurableSet_negative_finite n ε) (Set.Ici (-ε)) measurableSet_Ici
    have hp : arrayBlock B n ⁻¹' {b | ∀ i j, i ≠ j → b i j < -ε} = A := rfl
    rw [hp] at h
    have hz : ∀ j ∈ Finset.univ.erase i,
        A ∩ {ω | B ω i j ∈ Set.Ici (-ε)} = ∅ := by
      intro j hj
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hω, hω'⟩
      exact (not_le_of_gt (hω i j (Ne.symm (Finset.mem_erase.mp hj).1))) hω'
    have hzero : (∑ j ∈ Finset.univ.erase i,
        μ.real (A ∩ {ω | B ω i j ∈ Set.Ici (-ε)})) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j hj, measureReal_empty]
    rw [hzero] at h
    simp only [zero_div, add_zero, Set.mem_Ici] at h
    simpa only [Bad, hbase] using h
  have hsub : A ⊆ negativeBlock B ε (n + 1) ∪ ⋃ i : Fin n, Bad i := by
    intro ω hω
    by_cases ht : ∀ i : Fin n, B ω i n < -ε
    · exact Or.inl ((mem_negativeBlock_succ hsym).mpr ⟨hω, ht⟩)
    · right
      push Not at ht
      obtain ⟨i, hi⟩ := ht
      exact Set.mem_iUnion.mpr ⟨i, hω, hi⟩
  have hbound := (measureReal_mono (μ := μ) hsub).trans
    (measureReal_union_le (negativeBlock B ε (n + 1)) (⋃ i : Fin n, Bad i))
  have hsum := measureReal_iUnion_fintype_le Bad (μ := μ)
  simp_rw [hbad] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mul_div_left_comm, div_self hn', mul_one] at hsum
  nlinarith

lemma gg_negative_probability_zero {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | B ω 0 1 < -ε} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  by_contra hbne
  have hb : 0 < μ.real {ω | B ω 0 1 < -ε} :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hbne)
  have hblocks : ∀ k : ℕ, 0 < μ.real (negativeBlock B ε (k + 2)) := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add, negativeBlock_two hsym] using hb
    | succ k ih =>
      have h := negativeBlock_next_probability hm hsym hGG ε (k + 2) (by omega)
      exact (mul_pos ih hb).trans_le (by simpa only [Nat.succ_add] using h)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (D / ε)
  have hsize : D < ((m + 2 : ℕ) - 1 : ℝ) * ε := by
    have h := (div_lt_iff₀ hε).mp hmgt
    simp only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hnull : μ (negativeBlock B ε (m + 2)) = 0 := by
    have ha : ∀ᵐ ω ∂μ, ω ∉ negativeBlock B ε (m + 2) := by
      filter_upwards [hGram, hdiag] with ω hg hd
      intro hn
      exact no_large_negative_block (by omega : 0 < m + 2) hsize (hg (m + 2))
        (fun i => hd i) hn
    simpa using ae_iff.mp ha
  have hpos := hblocks m
  rw [Measure.real, hnull, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

 

theorem gg_pair_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  have ha : ∀ k : ℕ, ∀ᵐ ω ∂μ, -(1 / (k + 1 : ℝ)) ≤ B ω 0 1 := by
    intro k
    rw [ae_iff]
    simp only [not_le]
    exact gg_negative_probability_zero hm hsym hGG hGram hdiag (by positivity)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  simp only [neg_zero] at hlim
  exact le_of_tendsto' hlim hω



lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm


lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma replica_injective_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {r : ℕ} (ι : Fin r → ℕ) (hi : Function.Injective ι) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ (ι i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  have h0 : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have h := h0.precomp hi
  have he := h.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbationWeight_pos (j : ℕ) : 0 < perturbationWeight j := by
  unfold perturbationWeight
  positivity

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma contactGGRate_eq {N : ℕ} (hN : 0 < N) (j : ℕ) (L B : ℝ) :
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(N:ℝ)^(-3/8:ℝ) +
      (2*B/perturbationWeight j)*(N:ℝ)^(-1/8:ℝ) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(N:ℝ)^(-1/8:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hw := perturbationWeight_pos j
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  have he2 : (perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    unfold perturbationScale
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    norm_num
  have h1 : 1/(Real.sqrt N*(perturbationScale N)^2) = (N:ℝ)^(-3/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  have h2 : contactStep N/(perturbationScale N)^2 = (N:ℝ)^(-1/8:ℝ) := by
    rw [he2]
    unfold contactStep
    rw [← Real.rpow_sub hn]
    norm_num
  have h3 : 1/(Real.sqrt N*(perturbationScale N)^2*contactStep N) = (N:ℝ)^(-1/8:ℝ) := by
    rw [Real.sqrt_eq_rpow,he2]
    unfold contactStep
    rw [← Real.rpow_add hn,← Real.rpow_add hn,one_div,← Real.rpow_neg hn.le]
    norm_num
  calc
    contactGGRate N j L B =
      (B*(2/perturbationWeight j+1)/perturbationWeight j)*(1/(Real.sqrt N*(perturbationScale N)^2)) +
      (2*B/perturbationWeight j)*(contactStep N/(perturbationScale N)^2) +
      (16*B*Real.sqrt L/(perturbationWeight j)^2)*(1/(Real.sqrt N*(perturbationScale N)^2*contactStep N)) := by
        unfold contactGGRate perturbationAmplitude
        rw [Real.sqrt_div' L hn.le]
        have hn' : (N:ℝ) = (Real.sqrt N)^2 := (Real.sq_sqrt hn.le).symm
        conv_lhs => rw [hn']
        simp only [Real.sqrt_sq hr.le]
        field_simp
        ring
    _ = _ := by rw [h1,h2,h3]

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

lemma contactStep_tendsto : Tendsto contactStep atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/4:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/4) (by norm_num)

lemma contactGGRate_tendsto (j : ℕ) (L B : ℝ) :
    Tendsto (fun N => contactGGRate N j L B) atTop (𝓝 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 3/8) (by norm_num)).const_mul
    (B*(2/perturbationWeight j+1)/perturbationWeight j)
  have h2 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul (2*B/perturbationWeight j)
  have h3 := (tendsto_nat_rpow_neg (c := 1/8) (by norm_num)).const_mul
    (16*B*Real.sqrt L/(perturbationWeight j)^2)
  apply Tendsto.congr' _ (show Tendsto _ _ (𝓝 (0:ℝ)) from by simpa using (h1.add h2).add h3)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div,one_div] using (contactGGRate_eq hN j L B).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma labeledCommonDepth_sum (n : ℕ) (x y : LabeledLeaf n) :
    (∑ d ∈ Finset.range n, if (labeledAddress n x).take (d+1) =
      (labeledAddress n y).take (d+1) then (1:ℝ) else 0) = labeledCommonDepth n x y := by
  have hc := labeledCommonDepth_le n x y
  calc
    _ = ∑ d ∈ Finset.range n, if d < labeledCommonDepth n x y then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [labeled_prefix_eq_iff n x y (d := d+1) (by have := Finset.mem_range.mp hd; omega), Nat.add_one_le_iff]
    _ = labeledCommonDepth n x y := by
      simp only [Finset.sum_boole]
      congr 1
      have he : (Finset.range n).filter (fun d => d < labeledCommonDepth n x y) =
          Finset.range (labeledCommonDepth n x y) := by
        ext d
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
      rw [he,Finset.card_range]

lemma treeOverlap_posSemidef (n : ℕ) {m : ℕ} (x : Fin m → LabeledLeaf n) :
    Matrix.PosSemidef (fun i j => treeOverlap n (x i) (x j)) := by
  classical
  let A : ℕ → Matrix (Fin m) (Fin m) ℝ := fun d =>
    Matrix.submatrix (1 : Matrix (List ChildLabel) (List ChildLabel) ℝ)
      (fun i => (labeledAddress n (x i)).take (d+1)) (fun i => (labeledAddress n (x i)).take (d+1))
  have hp (d : ℕ) : (A d).PosSemidef := Matrix.PosSemidef.one.submatrix _
  have hs := (Matrix.posSemidef_sum (Finset.range n) (fun d _ => hp d)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
  have he : (fun i j => treeOverlap n (x i) (x j)) =
      ((n+1:ℕ):ℝ)⁻¹ • (∑ d ∈ Finset.range n, A d) := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,A,Matrix.submatrix_apply,Matrix.one_apply]
    rw [labeledCommonDepth_sum]
    simp only [treeOverlap,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hs

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma HasGhirlandaGuerra.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {B C : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (he : B =ᵐ[μ] C) :
    HasGhirlandaGuerra C μ := by
  have hm (P : RealArray → Prop) : μ.real {ω | P (C ω)} = μ.real {ω | P (B ω)} := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    change P (C ω) = P (B ω)
    rw [hω]
  intro n hn i A hA t ht
  change μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i n ∈ t} =
    (μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A} * μ.real {ω | C ω 0 1 ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) / n
  rw [hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i n ∈ t),
    hm (fun b => (fun j k : Fin n => b j k) ∈ A), hm (fun b => b 0 1 ∈ t)]
  have hs : (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) =
      ∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A ∧ B ω i j ∈ t} := by
    apply Finset.sum_congr rfl
    intro j _
    exact hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i j ∈ t)
  rw [hs]
  exact h n hn i A hA t ht

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

lemma GramDiagonal.default {D : ℝ} (hD : 0 ≤ D) :
    GramDiagonal D (fun i j => if i=j then D else 0) := by
  constructor
  · intro n
    have he : (fun i j : Fin n => if (i:ℕ)=(j:ℕ) then D else 0) =
        Matrix.diagonal (fun _ : Fin n => D) := by
      ext i j
      simp only [Matrix.diagonal_apply,Fin.val_inj]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun _ => hD)
  · intro i
    simp



lemma gg_pair_nonnegative_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have ht := gg_pair_nonnegative (fun i j => by fun_prop) (fun ω => (hCG ω).symm)
    (hgg.congr_ae he) (ae_of_all _ (fun ω => (hCG ω).1)) (ae_of_all _ (fun ω => (hCG ω).2))
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma gaussianTransform_const_add {U : ℝ → ℝ} (hU : Measurable U) (hG : HasLinearGrowth U)
    (s d c : ℝ) :
    gaussianTransform s d (fun x => c+U x) = fun x => c+gaussianTransform s d U x := by
  ext x
  by_cases hd : d=0
  · simp only [gaussianTransform,hd,ite_true, if_true]
    have hi : Integrable (fun z : ℝ => U (x+Real.sqrt s*z)) (gaussianReal 0 1) :=
      gaussian_linearGrowth_integrable
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) _ _
    rw [integral_add (integrable_const c) hi]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [gaussianTransform,hd,ite_false, if_false]
    exact logMean_const_add (gaussianReal 0 1) hd
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d) c

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_BoundedTiltAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Tilt Average. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exp_mul_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) (d : ℝ) :
    Integrable (fun x => Real.exp (d*U x)) P := by
  apply Integrable.of_bound ((measurable_const.mul hU).exp).aestronglyMeasurable (Real.exp (|d| * K))
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    change |d * U x| ≤ |d| * K
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)))

lemma bounded_tilted_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {U A : Ω → ℝ} (hU : Measurable U)
    {K C : ℝ} (hK : ∀ x, |U x| ≤ K) (hA : Measurable A) (hC : ∀ x, |A x| ≤ C) (d : ℝ) :
    |∫ x, A x ∂P.tilted (fun x => d*U x)| ≤ C := by
  let := isProbabilityMeasure_tilted (exp_mul_integrable_of_bound P hU hK d)
  exact abs_integral_le_integral_abs.trans (by
    calc
      (∫ x, |A x| ∂P.tilted (fun x => d*U x)) ≤ ∫ _ : Ω, C ∂P.tilted (fun x => d*U x) :=
        integral_mono (Integrable.of_bound hA.abs.aestronglyMeasurable C
          (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hC x)))
          (integrable_const _) hC
      _ = C := by simp)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_last {n : ℕ} (a : Fin (n+1) → ℝ) : finiteFieldPath a n = ∑ j, a j := by
  simp only [finiteFieldPath,show ∀ j : Fin (n+1), j.val ≤ n from fun j => by omega,ite_true, if_true]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TimeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma right_derivative_nonneg_of_min {F : ℝ → ℝ} {D : ℝ}
    (hD : HasDerivWithinAt F D (Ici 0) 0)
    (hmin : ∀ᶠ a in 𝓝[>] (0:ℝ), F 0 ≤ F a) : 0 ≤ D := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
    (hD.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto ht
  filter_upwards [hmin,self_mem_nhdsWithin] with a ha ha'
  simpa only [slope_def_field,sub_zero] using div_nonneg (sub_nonneg.mpr ha) ha'.le

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma measurable_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) :
    Measurable (finiteStepFunction ζ v) := by
  unfold finiteStepFunction
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

lemma integral_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u ∂pathMeasure) = ∑ i, (ζ i.succ-ζ i.castSucc)*v i := by
  classical
  let : IsFiniteMeasure pathMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs (i : Fin k) : Ioo (ζ i.castSucc) (ζ i.succ) ⊆ Ioo (0:ℝ) 1 := by
    intro u hu
    have h0 : 0≤ζ i.castSucc := by rw [← hz0]; exact hz.monotone (Fin.zero_le _)
    have h1 : ζ i.succ≤1 := by rw [← hz1]; exact hz.monotone (Fin.le_last _)
    exact ⟨h0.trans_lt hu.1,hu.2.trans_le h1⟩
  have hind (i : Fin k) : (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) =
      (Ioo (ζ i.castSucc) (ζ i.succ)).indicator (fun _ : ℝ => v i) := by
    ext u
    simp only [Set.indicator_apply,Set.mem_Ioo]
  have hi (i : Fin k) : Integrable (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) pathMeasure := by
    rw [hind]
    exact (integrable_const (v i)).indicator measurableSet_Ioo
  unfold finiteStepFunction
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hind]
  rw [integral_indicator measurableSet_Ioo]
  have he : pathMeasure.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) = volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (hs i)]
  rw [he,integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hz.monotone (Fin.castSucc_le_succ i))),smul_eq_mul]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_linearGrowth : HasLinearGrowth (fun x : ℝ => |x|) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun x => ?_⟩
  simp only [abs_abs,zero_add,one_mul,Real.norm_eq_abs,le_refl]

lemma gaussian_abs_exp_bound (a x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ z, Real.exp (d*|x+a*z|) ∂gaussianReal 0 1) ≤
      2*Real.exp (d*|x|+(d*a)^2/2) := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+a*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument a) d
  have hj : Integrable (fun z : ℝ => Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z))) (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal (d*a)).add (integrable_exp_mul_gaussianReal (-d*a))).const_mul _
  have hp (z : ℝ) : Real.exp (d*|x+a*z|) ≤ Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) := by
    calc
      _ ≤ Real.exp (d*(|x|+|a*z|)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le _ _) hd)
      _ = Real.exp (d*|x|)*Real.exp (d*|a*z|) := by rw [mul_add,Real.exp_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        by_cases h : 0 ≤ a*z
        · rw [abs_of_nonneg h]
          have he : d*(a*z) = (d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_neg (lt_of_not_ge h)]
          have he : d*-(a*z) = (-d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ ∫ z, Real.exp (d*|x|)*(Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) ∂gaussianReal 0 1 :=
      integral_mono hi hj hp
    _ = _ := by
      rw [integral_const_mul,integral_add (integrable_exp_mul_gaussianReal _) (integrable_exp_mul_gaussianReal _)]
      have hmgf (t : ℝ) : (∫ z : ℝ, Real.exp (t*z) ∂gaussianReal 0 1) = Real.exp (t^2/2) := by
        simpa [mgf] using mgf_gaussianReal (p := gaussianReal 0 1) (μ := 0) (v := 1) (X := fun z : ℝ => z) (by simp) t
      rw [hmgf,hmgf]
      have hs : (-d*a)^2 = (d*a)^2 := by ring
      rw [hs,Real.exp_add]
      ring

lemma gaussianTransform_abs_bound {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (x : ℝ) :
    gaussianTransform s d (fun y => |y|) x ≤ |x|+d*s/2+Real.log 2/d := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+Real.sqrt s*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument (Real.sqrt s)) d
  change (if d=0 then _ else _/d) ≤ _
  rw [ite_eq_right hd.ne']
  apply (div_le_iff₀ hd).2
  have H := Real.log_le_log (integral_exp_pos (gaussianReal 0 1) _ hi)
    (gaussian_abs_exp_bound (Real.sqrt s) x hd.le)
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at H
  have hsq := Real.sq_sqrt hs
  apply H.trans_eq
  rw [mul_pow,hsq]
  field_simp
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

lemma rotatedEnergy_constant {N : ℕ} (a : ℝ) (U : Rotation N) (σ : Spin N) :
    rotatedEnergy (fun _ => a) U σ = a * N / 2 := by
  rw [rotatedEnergy, ← Finset.mul_sum, rotated_spin_sq_sum]
  ring

/-- Pointwise operator comparison in spectral coordinates. -/
lemma abs_rotatedEnergy_sub_le {N : ℕ} (eig κ : Fin N → ℝ) (U : Rotation N)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) (σ : Spin N) :
    |rotatedEnergy eig U σ - rotatedEnergy κ U σ| ≤ δ * N / 2 := by
  have he : rotatedEnergy eig U σ - rotatedEnergy κ U σ =
      (1 / 2 : ℝ) * ∑ i, (eig i - κ i) * (U (spinVector σ) i) ^ 2 := by
    simp only [rotatedEnergy, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ i, |(eig i - κ i) * (U (spinVector σ) i) ^ 2| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, |eig i - κ i| * (U (spinVector σ) i) ^ 2 := by
      simp only [abs_mul, abs_sq]
    _ ≤ (1 / 2 : ℝ) * ∑ i, δ * (U (spinVector σ) i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hδ i) (sq_nonneg _)
    _ = δ * N / 2 := by rw [← Finset.mul_sum, rotated_spin_sq_sum]; ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_Overlaps
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap geometry

The finite projected overlaps are Gram matrices. Panchenko's ultrametricity
theorem applies to their limit arrays satisfying the Ghirlanda–Guerra identities.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Each spectral overlap component is a positive semidefinite Gram kernel. -/
lemma projectedOverlap_posSemidef {N m : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Fin m → Spin N) :
    Matrix.PosSemidef (fun i j => projectedOverlap U I (σ i) (σ j)) := by
  classical
  let A : Matrix (Fin m) (Fin N) ℝ := fun i k =>
    if k ∈ I then U (spinVector (σ i)) k else 0
  have hp := (Matrix.posSemidef_self_mul_conjTranspose A).smul
    (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
  have he : (fun i j : Fin m => projectedOverlap U I (σ i) (σ j)) =
      (N : ℝ)⁻¹ • (A * Aᴴ) := by
    ext i j
    change (N : ℝ)⁻¹ * (∑ k ∈ I, U (spinVector (σ i)) k * U (spinVector (σ j)) k) =
      (N : ℝ)⁻¹ * ∑ k, (if k ∈ I then U (spinVector (σ i)) k else 0) *
        (if k ∈ I then U (spinVector (σ j)) k else 0)
    congr 1
    simp only [ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self]
  rw [he]
  exact hp

/-- Full spectral overlap agrees with the ordinary spin overlap, because an
orthogonal rotation preserves the inner product. -/
lemma projectedOverlap_univ {N : ℕ} (U : Rotation N) (σ τ : Spin N) :
    projectedOverlap U Finset.univ σ τ =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  simp only [projectedOverlap]
  congr 1
  have h := U.inner_map_map (spinVector σ) (spinVector τ)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    spinVector_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor features for spectral-overlap GG perturbations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma spectralSpinFeature_cross {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ τ : Spin N) :
    (∑ i : I, spectralSpinFeature U I σ i * spectralSpinFeature U I τ i) =
      projectedOverlap U I σ τ := by
  simp only [spectralSpinFeature, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm]
  unfold projectedOverlap
  congr 1
  exact Finset.sum_coe_sort I (fun i => U (spinVector σ) i * U (spinVector τ) i)

/-- The Gaussian tensor coefficient covariance is exactly the required
monomial in the individual spectral overlaps. -/
theorem spectralMonomialFeature_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    (∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature U I d σ v * spectralMonomialFeature U I d τ v) =
      ∏ a, projectedOverlap U (I a) σ τ ^ d a := by
  simp only [spectralMonomialFeature, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (v : Fin (d a) → I a) =>
    IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) v *
      IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) τ) v)]
  simp_rw [IsingPerceptron.tensorFeature_cross, spectralSpinFeature_cross]

theorem spectralMonomial_abs_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    |∏ a, projectedOverlap U (I a) σ τ ^ d a| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro a _
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one U (I a) σ τ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The concrete Gaussian covariance is the linear spin-field kernel plus
the required finite sum of spectral-overlap monomials. -/
theorem spinTensorFeature_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude τ i) =
      (site : ℝ) * (∑ i, spinValue (σ i) * spinValue (τ i)) +
        ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
          ∏ a, projectedOverlap U (I a) σ τ ^ degree j a := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (monomial j : ℝ) * amplitude j ^ 2 *
          ∑ v : SpectralTensorIndex I (degree j),
            spectralMonomialFeature U I (degree j) σ v * spectralMonomialFeature U I (degree j) τ v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spectralMonomialFeature_cross]

theorem spinTensorFeature_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) ≤
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  have he : (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) =
      ∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
        spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude σ i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, spinTensorFeature_covariance]
  simp only [← sq, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have hp : (∏ a, projectedOverlap U (I a) σ σ ^ degree j a) ≤ 1 :=
    (le_abs_self _).trans (spectralMonomial_abs_le_one U I (degree j) σ σ)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat Gaussian coefficients for root and finite-depth tensor marks. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorLeafCoefficients_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amplitude n v x)
      (tensorLeafCoefficients V I degree amplitude n v y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        ∑ j : SpinTensorIndex I degree, (v i j : ℝ) *
          spinTensorFeature U I degree amplitude x.1 j * spinTensorFeature V I degree amplitude y.1 j
        else 0 := by
  classical
  rw [tensorLeafCoefficients, tensorLeafCoefficients, featureCoefficients_diagonal
    (treeFeatureTag n x.2) (treeFeatureTag n y.2)
    (fun i j h => ((treeFeatureTag_cross n x.2 y.2 i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
  · simp only [hi, ite_true, if_true]
    apply Finset.sum_congr rfl
    intro j _
    have hs : (NNReal.sqrt (v i j) : ℝ) ^ 2 = (v i j : ℝ) :=
      by exact_mod_cast NNReal.sq_sqrt (v i j)
    calc
      _ = (NNReal.sqrt (v i j) : ℝ) ^ 2 *
          spinTensorFeature U I degree amplitude x.1 j *
            spinTensorFeature V I degree amplitude y.1 j := by ring
      _ = _ := by rw [hs]
  · simp only [hi, ite_false, if_false, Finset.sum_const_zero]

lemma tensorLeafCoefficients_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) x).sum (fun _ c => c ^ 2) ≤
      ∑ i, ((site i : ℝ) * N + ∑ j, (monomial i j : ℝ) * amplitude j ^ 2) := by
  rw [← cylinderCross_self, tensorLeafCoefficients_cross]
  simp only [labeledCommonDepth_self,
    show ∀ i : Fin (n + 1), i.1 ≤ n from fun i => Nat.le_of_lt_succ i.isLt, ite_true, if_true]
  apply Finset.sum_le_sum
  intro i _
  simpa only [pow_two, mul_assoc] using
    spinTensorFeature_variance_le U I degree amplitude (site i) (monomial i) x.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BaseGaussianVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian variance for the countable spin/leaf partition with base energy. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

/-- Splitting off a fixed integrable base energy is an almost-everywhere
identity for the actual countable Gaussian partition, including nonuniform
and cascade-leaf weights. -/
lemma cylinder_log_partition_base {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    (fun g : ℕ → ℝ => Real.log (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν))
      =ᵐ[gaussianCoordinates]
    (fun g => Real.log (∫ x, Real.exp (H x) ∂ν) +
      cgf (fun x => cylinderField (A x) g) (ν.tilted H) t) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have hVar (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  have he := (gaussian_field_exp_integrable (ν := ν.tilted H)
    (measurable_cylinderFields A) (fun x => cylinderField_law (A x)) hVar t).1.prod_right_ae
  filter_upwards [he] with g hg
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := integral_exp_pos hH
  have hz' : 0 < ∫ x, Real.exp (t * cylinderField (A x) g) ∂ν.tilted H := integral_exp_pos hg
  have hi := integral_exp_tilted (μ := ν) H (fun x => t * cylinderField (A x) g)
  have hid : (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν) =
      (∫ x, Real.exp (H x) ∂ν) *
        (∫ x, Real.exp (t * cylinderField (A x) g) ∂ν.tilted H) := by
    rw [hi]
    simp only [Pi.add_apply]
    field_simp
  rw [hid, Real.log_mul hz.ne' hz'.ne']
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite perturbation sums for the manuscript's geometric weights. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Nat.succ_le_of_lt hN)
  · norm_num

lemma perturbationScale_sq_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ^ 2 ≤ 1 := by
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [perturbationScale_le_one hN]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGaussianMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean rotation comparison on the concrete countable tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma finite_spin_base_exp_integrable {N n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] (H : Spin N → ℝ) :
    Integrable (fun x : Spin N × LabeledLeaf n => Real.exp (H x.1)) ν := by
  classical
  apply (integrable_const (∑ σ : Spin N, Real.exp (H σ))).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Finset.single_le_sum (fun σ _ => (Real.exp_pos (H σ)).le) (Finset.mem_univ x.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's linear enrichment and monomial tree variance increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma varianceIncrement_coe {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    (varianceIncrement q i : ℝ) = pathIncrement q i :=
  Real.coe_toNNReal _ (pathIncrement_nonneg hq h0 i)

lemma varianceIncrement_sum {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (n : ℕ) :
    (∑ i : Fin (n + 1), (varianceIncrement q i : ℝ)) = q n := by
  simp_rw [varianceIncrement_coe hq h0]
  rw [Fin.sum_univ_eq_sum_range, pathIncrement_sum]

lemma monomialVarianceIncrement_sum_le (n : ℕ) (r : ℕ) :
    (∑ i : Fin (n + 1), (varianceIncrement (monomialPath n r) i : ℝ)) ≤ 1 := by
  rw [varianceIncrement_sum (monomialPath_monotone n r) (monomialPath_nonneg n r 0)]
  exact monomialPath_diag_le_one n r

lemma tensorPathProfile_variance_cap {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) :
    (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x).sum (fun _ c => c ^ 2) ≤
      h n * N + ∑ j, amplitude j ^ 2 := by
  have hc := tensorLeafCoefficients_variance_le U I degree amplitude n
    (fun i => varianceIncrement h i)
    (fun i j => varianceIncrement (monomialPath n (treeDegree j)) i) x
  refine hc.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, varianceIncrement_sum hh h0,
    Finset.sum_comm]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (treeDegree j))
    (sq_nonneg (amplitude j))).trans_eq (one_mul _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalPerturbation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic spectral-diagonal perturbation as an exact eigenvalue shift. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- This is the first term of the manuscript's perturbation, including
its coefficient `N e_N`, in the actual rotated Ising Hamiltonian. -/
theorem rotatedEnergy_diagonalPerturbation {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ =
      t * rotatedEnergy eig U σ + N * perturbationScale N * ∑ a, v a * projectedOverlap U (I a) σ σ := by
  classical
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold rotatedEnergy diagonalPerturbedEigenvalues projectedOverlap
  simp_rw [add_mul, Finset.sum_add_distrib]
  have he : (∑ i, (2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0) *
      U (spinVector σ) i ^ 2) =
      2 * perturbationScale N * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    calc
      _ = (2 * perturbationScale N) *
          ∑ i, ∑ a, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = (2 * perturbationScale N) *
          ∑ a, ∑ i, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [he]
  simp_rw [← pow_two]
  have hl : (∑ i, t * eig i * U (spinVector σ) i ^ 2) =
      t * ∑ i, eig i * U (spinVector σ) i ^ 2 := by
    simp only [Finset.mul_sum, mul_assoc]
  have hs : (∑ a, v a * ((N : ℝ)⁻¹ * ∑ i ∈ I a, U (spinVector σ) i ^ 2)) =
      (N : ℝ)⁻¹ * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hl, hs]
  field_simp [hn]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_FullPerturbationCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vanishing cost of both terms of the manuscript perturbation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fullPerturbationCost_tendsto (m : ℕ) :
    Filter.Tendsto (fun N => 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
  simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
    (perturbationScale_tendsto.const_mul (2 * (m : ℝ))).add
      ((perturbationScale_tendsto.pow 2).const_mul 8)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_MonomialEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete complete enumeration of the spectral/tree monomials with linear degree cap. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma multidegreeDecode_encode (m : ℕ) (d : Fin m → ℕ) :
    multidegreeDecode m (multidegreeEncode m d) = d := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    funext i
    induction i using Fin.cases with
    | zero => simp only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_zero]
    | succ i =>
      simpa only [multidegreeDecode, multidegreeEncode, Nat.unpair_pair, Fin.cases_succ,
        Fin.tail] using congrFun (ih (Fin.tail d)) i

lemma multidegreeDecode_sum_le (m j : ℕ) :
    (∑ i, multidegreeDecode m j i) ≤ j := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [multidegreeDecode, Fin.cases_zero, Fin.cases_succ]
    exact (Nat.add_le_add_left (ih (Nat.unpair j).2) _).trans (Nat.unpair_add_le j)

/-- Every nonconstant joint spectral/tree monomial occurs at a fixed
finite index, hence eventually occurs in the truncation through `N`. -/
theorem enumeratedMonomial_surjective (m : ℕ) (d : Fin m → ℕ) (r : ℕ)
    (h : 1 ≤ (∑ a, d a) + r) :
    ∃ j, (∀ a, enumeratedSpectralDegree m j a = d a) ∧ enumeratedTreeDegree m j = r := by
  let v : Fin (m + 1) → ℕ := Fin.lastCases r d
  let c := multidegreeEncode (m + 1) v
  have hc : 1 ≤ c := by
    have hs := multidegreeDecode_sum_le (m + 1) c
    rw [multidegreeDecode_encode] at hs
    rw [Fin.sum_univ_castSucc] at hs
    simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last] at hs
    exact h.trans hs
  refine ⟨c - 1, ?_, ?_⟩
  · intro a
    have he := congrFun (multidegreeDecode_encode (m + 1) v) a.castSucc
    simpa only [enumeratedSpectralDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_castSucc] using he
  · have he := congrFun (multidegreeDecode_encode (m + 1) v) (Fin.last m)
    simpa only [enumeratedTreeDegree, Nat.sub_add_cancel hc, v, Fin.lastCases_last] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespaceTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : Function.Injective (tensorNamespaceTag I degree) := by
  rintro ⟨i, p, a⟩ ⟨j, q, b⟩ h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      cases he
      rfl
    | inr b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨a, s⟩
      rcases b with ⟨b, t⟩
      have hp := Nat.pair_eq_pair.mp h
      have hab : a = b := Fin.ext (Nat.add_right_cancel hp.1)
      subst b
      have he := Encodable.encode_inj.mp hp.2
      cases he
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomCoefficientIBP
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian insertion when the finite coefficient vectors depend on external
disorder. This permits the Haar-dependent spectral-overlap tensor features.
The Gaussian coordinates remain independent of the external disorder.
-/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

omit [IsProbabilityMeasure P] in
/-- All exponential tilts are integrable for almost every joint disorder.
Only integer tilts are intersected before extending to every real parameter. -/
lemma randomCoefficient_all_exp_ae (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1, hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t * cylinderField (A p.1.1 p.2) p.1.2)) := (hA.const_mul t).exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((A ω x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (A ω x).sum (fun _ c => c ^ 2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha ω x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields (A ω))
      (fun x => cylinderField_law (A ω x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n : ℝ) * cylinderField (A z.1 x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n : ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

omit [Countable X] [MeasurableSingletonClass X] in
lemma measurable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hA.const_mul t)).log

/-- The external-disorder-dependent log partition is integrable, by the
uniform pointwise Gaussian second-moment estimate. -/
lemma integrable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) (P.prod gaussianCoordinates) := by
  have hm := measurable_randomCoefficient_cgf hν A hA t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).1)
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen exponential integrability and selected-field log partition identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespacedCoefficients_variance_eq {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) =
      (tensorLeafCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) := by
  have hi : Function.Injective (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
      tensorNamespaceTag I degree (i.1.1, (labeledAddress n x.2).take i.1, i.2)) := by
    intro i j hij
    apply treeFeatureTag_injective n x.2
    exact congrArg Encodable.encode ((tensorNamespaceTag_injective I degree) hij)
  rw [tensorNamespacedCoefficients, featureCoefficients_variance _ hi,
    tensorLeafCoefficients, featureCoefficients_variance _ (treeFeatureTag_injective n x.2)]

lemma tensorNamespacedPath_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x).sum (fun _ c => c ^ 2) ≤
      h n * N + ∑ j, amplitude j ^ 2 := by
  rw [tensorNamespacedCoefficients_variance_eq]
  exact tensorPathProfile_variance_cap U I degree amplitude n treeDegree h hh h0 x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMinimumRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing rates for diagonal perturbation energies at parameter minima. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma diagonalContactRate_eq {N : ℕ} (hN : 0 < N) (L : ℝ) :
    diagonalContactRate N L = (3 / 2) * (N : ℝ) ^ (-7 / 16 : ℝ) +
      (1 + 8 * Real.sqrt L) * (N : ℝ) ^ (-3 / 16 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have he : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have h1 : 1 / (Real.sqrt N * perturbationScale N) = (N : ℝ) ^ (-7 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, ← Real.rpow_add hn,
      one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  have h2 : contactStep N / perturbationScale N = (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [contactStep, perturbationScale, ← Real.rpow_sub hn]
    congr 1
    norm_num
  have h3 : 1 / (Real.sqrt N * perturbationScale N * contactStep N) =
      (N : ℝ) ^ (-3 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, perturbationScale, contactStep,
      ← Real.rpow_add hn, ← Real.rpow_add hn, one_div, ← Real.rpow_neg hn.le]
    congr 1
    norm_num
  calc
    _ = (3 / 2) * (1 / (Real.sqrt N * perturbationScale N)) +
        contactStep N / perturbationScale N +
        8 * Real.sqrt L * (1 / (Real.sqrt N * perturbationScale N * contactStep N)) := by
      unfold diagonalContactRate
      rw [Real.sqrt_div' L hn.le]
      have hn' : (N : ℝ) = (Real.sqrt N) ^ 2 := (Real.sq_sqrt hn.le).symm
      conv_lhs => rw [hn']
      simp only [Real.sqrt_sq hr.le]
      field_simp
      ring
    _ = _ := by rw [h1, h2, h3]; ring

lemma diagonalContactRate_tendsto (L : ℝ) :
    Tendsto (fun N => diagonalContactRate N L) atTop (nhds 0) := by
  have h1 := (tendsto_nat_rpow_neg (c := 7 / 16) (by norm_num)).const_mul (3 / 2 : ℝ)
  have h2 := (tendsto_nat_rpow_neg (c := 3 / 16) (by norm_num)).const_mul (1 + 8 * Real.sqrt L)
  apply Tendsto.congr' _ (show Tendsto _ _ (nhds (0 : ℝ)) from by simpa using h1.add h2)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simpa only [neg_div] using (diagonalContactRate_eq hN L).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_BoundedObservableMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic spectral-diagonal perturbation estimate at a parameter minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_bounded_random_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω × X → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : ∀ ω x, |Y (ω, x)| ≤ B) (t : ℝ) :
    Integrable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) P := by
  have hm : Measurable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) := by
    simpa only [cgf, mgf, referencePartition] using
      (measurable_random_referencePartition hν (hY.const_mul t)).log
  apply Integrable.of_bound hm.aestronglyMeasurable (|t| * B)
  exact ae_of_all _ fun ω => by
    have hYm : Measurable (fun x => t * Y (ω, x)) :=
      (hY.comp (measurable_const.prodMk measurable_id)).const_mul t
    have hb : ∀ x, |t * Y (ω, x)| ≤ |t| * B := fun x => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ω x) (abs_nonneg _)
    have h := logMean_bounds (ν ω) hYm (b := 1) (by norm_num) hb
    simpa only [cgf, mgf, logMean, one_mul, div_one, Real.norm_eq_abs] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorReplicaAverageLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite replica averages under the tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma referenceReplicaMean_zero {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {q : ℕ} (D : (Fin q → X) → ℝ) :
    referenceReplicaMean ν (fun _ => 0) D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin q => ν) := by
  rw [referenceReplicaMean_eq_tilted ν (fun _ => 0) (by simp) D]
  simp only [show (fun _ : X => (0 : ℝ)) = 0 from rfl, tilted_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine compact parameter region for the finite upper comparison.
Field covariance increments are nonnegative and their sum is capped. -/

noncomputable section
open Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContactRegion_bounds {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (hp : p ∈ tensorContactRegion N m n H) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ (∀ j, 0 ≤ p.2.1 j) ∧ (∑ j, p.2.1 j) ≤ H ∧
      (∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2) ∧ (∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) := by
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.1.1.2.1, hp.2,
    fun j => ⟨hp.1.1.2.2.1 j, hp.1.2.2.2.1 j⟩,
    fun a => ⟨hp.1.1.2.2.2 a, hp.1.2.2.2.2 a⟩⟩

lemma tensorContactRegion_mem {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (ht : p.1 ∈ Icc (0 : ℝ) 1)
    (ha : ∀ j, 0 ≤ p.2.1 j) (hcap : (∑ j, p.2.1 j) ≤ H)
    (hu : ∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2)
    (hv : ∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) : p ∈ tensorContactRegion N m n H := by
  refine ⟨⟨⟨ht.1, ha, (fun j => (hu j).1), (fun a => (hv a).1)⟩,
    ht.2, ?_, (fun j => (hu j).2), (fun a => (hv a).2)⟩, hcap⟩
  intro j
  exact (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)).trans hcap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_mono {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFG : IsingPerceptron.HasLinearGrowth F) (hGG : IsingPerceptron.HasLinearGrowth G)
    (h : ∀ z, F z ≤ G z) {a : ℝ} (ha : 0 ≤ a) (v z : ℝ) :
    gaussianOperator a v F z ≤ gaussianOperator a v G z := by
  by_cases ha0 : a = 0
  · simp only [gaussianOperator, ha0, ite_true, if_true]
    apply integral_mono
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) _ _)
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) _ _)
    exact fun y => h _
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_transform, gaussianOperator_eq_transform]
    simp only [IsingPerceptron.gaussianTransform, ha0, ite_false, if_false]
    exact IsingPerceptron.logMean_mono (gaussianReal 0 1) hap
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) a)
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) a)
      (fun y => h _)

lemma linearGrowth_const_add {F : ℝ → ℝ} (hF : IsingPerceptron.HasLinearGrowth F)
    (c : ℝ) : IsingPerceptron.HasLinearGrowth (fun z => c + F z) := by
  obtain ⟨C, L, hC, hL, h⟩ := hF
  refine ⟨|c| + C, L, add_nonneg (abs_nonneg _) hC, hL, fun z => ?_⟩
  exact (abs_add_le _ _).trans (by linarith [h z])

lemma gaussianOperator_const_add {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) (c a v z : ℝ) :
    gaussianOperator a v (fun x => c + F x) z = c + gaussianOperator a v F z := by
  simp only [gaussianOperator_eq_transform]
  exact congrFun (IsingPerceptron.gaussianTransform_const_add hF hFG v a c) z

lemma gaussianOperator_fold_growth (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) :
    Measurable (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) ∧
      IsingPerceptron.HasLinearGrowth
        (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) := by
  induction L with
  | nil => exact ⟨hF, hFG⟩
  | cons av L ih =>
    have ht := ih (fun bv hb => hL bv (List.mem_cons_of_mem _ hb))
    exact gaussianOperator_positive_growth ht.1 ht.2 (hL av (List.mem_cons_self)) av.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDomain
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma measurable_fieldFunction (h : FieldStep) : Measurable (fieldFunction h) :=
  IsingPerceptron.measurable_finiteStepFunction h.cut h.height

lemma fieldFunction_le_last (h : FieldStep) (s : ℝ) :
    fieldFunction h s ≤ h.height (Fin.last h.depth) := by
  classical
  by_cases hex : ∃ i : Fin (h.depth + 1), h.cut i.castSucc < s ∧ s < h.cut i.succ
  · obtain ⟨i, hi⟩ := hex
    have he := IsingPerceptron.finiteStepFunction_on_cell h.ordered_cut h.height hi
    change IsingPerceptron.finiteStepFunction h.cut h.height s ≤ _
    rw [he]
    exact h.ordered_height (Fin.le_last _)
  · have he : fieldFunction h s = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hex ⟨i, hi⟩)
    rw [he]
    exact h.nonneg _

lemma integrable_fieldFunction (h : FieldStep) : Integrable (fieldFunction h) pathMeasure := by
  apply (integrable_const (h.height (Fin.last h.depth))).mono'
    (measurable_fieldFunction h).aestronglyMeasurable
  filter_upwards [] with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fieldFunction_nonneg h s)] using
    fieldFunction_le_last h s

lemma integrable_path_mul_field (p : OverlapPath) (h : FieldStep) :
    Integrable (fun s => p s * fieldFunction h s) pathMeasure := by
  apply (integrable_fieldFunction h).mono'
    (p.measurable.mul (measurable_fieldFunction h)).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (p.nonneg s),
    abs_of_nonneg (fieldFunction_nonneg h s)]
  exact mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)

lemma integral_fieldFunction (h : FieldStep) :
    (∫ s, fieldFunction h s ∂pathMeasure) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * h.height i :=
  IsingPerceptron.integral_finiteStepFunction h.cut h.ordered_cut h.first h.last h.height

/-- Summation by parts for the finite height increments. -/
lemma sum_finite_height_difference (n : ℕ) (H F : ℕ → ℝ) :
    (∑ i : Fin (n + 1), (H i - if i.val = 0 then 0 else H (i.val - 1)) * F i) =
      H n * F n + ∑ i : Fin n, H i * (F i - F (i.val + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_ne_zero, ite_false, if_false,
      Nat.add_sub_cancel]
    rw [ih]
    ring

lemma fieldIncrement_eq_heightSequence (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 = heightSequence h i -
      if i.val = 0 then 0 else heightSequence h (i.val - 1) := by
  rw [heightSequence_eq h _ (by omega)]
  unfold fieldIncrement
  split_ifs with hi
  · rfl
  · rw [heightSequence_eq h _ (by omega)]

lemma fieldCutSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth + 1) :
    fieldCutSequence h i = h.cut ⟨i, by omega⟩ := by
  simp only [fieldCutSequence, min_eq_left hi]

lemma fieldIncrement_weighted_sum (h : FieldStep) (F : ℝ → ℝ) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2 * F (h.cut i.castSucc)) =
      h.height (Fin.last h.depth) * F (h.cut (Fin.last h.depth).castSucc) +
        ∑ i : Fin h.depth, h.height i.castSucc *
          (F (h.cut i.castSucc.castSucc) - F (h.cut i.succ.castSucc)) := by
  have hs := sum_finite_height_difference h.depth (heightSequence h)
    (fun i => F (fieldCutSequence h i))
  convert (config := {transparency := .instances, preTransparency := .instances}) hs using 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [fieldIncrement_eq_heightSequence, fieldCutSequence_eq h _ (by omega)]
    rfl
  · congr 1
    · rw [heightSequence_eq h _ le_rfl, fieldCutSequence_eq h _ (by omega)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      rw [heightSequence_eq h _ (by omega), fieldCutSequence_eq h _ (by omega),
        fieldCutSequence_eq h _ (by omega)]
      rfl

lemma integral_fieldFunction_eq_increment_sum (h : FieldStep) :
    (∫ s, fieldFunction h s ∂pathMeasure) =
      ∑ i : Fin (h.depth + 1), (1 - h.cut i.castSucc) * (fieldIncrement h i).2 := by
  rw [integral_fieldFunction]
  have hs := fieldIncrement_weighted_sum h (fun x => 1 - x)
  rw [Fin.sum_univ_castSucc] at ⊢
  rw [show h.cut (Fin.last h.depth).succ = 1 from h.last]
  rw [show (∑ i : Fin (h.depth + 1),
      (1 - h.cut i.castSucc) * (fieldIncrement h i).2) =
      ∑ i : Fin (h.depth + 1), (fieldIncrement h i).2 * (1 - h.cut i.castSucc) by
        apply Finset.sum_congr rfl; intro i _; ring, hs]
  have heq :
      (∑ i : Fin h.depth,
        (h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) * h.height i.castSucc) =
      ∑ i : Fin h.depth, h.height i.castSucc *
        ((1 - h.cut i.castSucc.castSucc) - (1 - h.cut i.succ.castSucc)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    rw [hi]
    ring
  rw [heq]
  ring

lemma fieldIncrement_sum (h : FieldStep) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2) =
      h.height (Fin.last h.depth) := by
  simpa using fieldIncrement_weighted_sum h (fun _ => 1)

lemma fieldPairing_le_const_integral (p : OverlapPath) (h : FieldStep) (m : ℝ)
    (hp : ∀ᵐ s ∂pathMeasure, p s ≤ m) :
    fieldPairing p h ≤ m * ∫ s, fieldFunction h s ∂pathMeasure := by
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_path_mul_field p h)
    ((integrable_fieldFunction h).const_mul m)
  filter_upwards [hp] with s hs
  exact mul_le_mul_of_nonneg_right hs (fieldFunction_nonneg h s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCapEstimate
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rough field cap estimate used in the finite-dimensional upper comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianAbsoluteMean_nonneg : 0 ≤ gaussianAbsoluteMean :=
  integral_nonneg (fun _ => abs_nonneg _)

lemma gaussianOperator_fold_abs (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) (z : ℝ) :
    (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
      (fun x => Real.log (Real.cosh x))) z ≤ |z| +
        (L.map (fun av => av.1 * av.2 / 2 + Real.log 2 / av.1)).sum := by
  induction L generalizing z with
  | nil =>
    simpa using (le_abs_self (Real.log (Real.cosh z))).trans
      (IsingPerceptron.abs_log_cosh_le z)
  | cons av L ih =>
    have htail : ∀ bv ∈ L, 0 < bv.1 ∧ 0 ≤ bv.2 :=
      fun bv hb => hL bv (List.mem_cons_of_mem _ hb)
    have hav := hL av (List.mem_cons_self)
    have hT := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1)
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
    let c := (L.map (fun bv => bv.1 * bv.2 / 2 + Real.log 2 / bv.1)).sum
    have hm : gaussianOperator av.1 av.2
        (L.foldr (fun bv f => gaussianOperator bv.1 bv.2 f)
          (fun x => Real.log (Real.cosh x))) z ≤
        gaussianOperator av.1 av.2 (fun x => c + |x|) z := by
      apply gaussianOperator_mono hT.1 (measurable_const.add measurable_id.abs)
        hT.2 (linearGrowth_const_add IsingPerceptron.abs_linearGrowth c) _ hav.1.le
      intro x
      simpa only [c, Pi.add_apply, id_eq, add_comm] using ih htail x
    rw [gaussianOperator_const_add (F := fun x : ℝ => |x|) measurable_id.abs IsingPerceptron.abs_linearGrowth] at hm
    have hc : gaussianOperator av.1 av.2 (fun x : ℝ => |x|) z ≤
        |z| + av.1 * av.2 / 2 + Real.log 2 / av.1 := by
      rw [gaussianOperator_eq_transform]
      exact IsingPerceptron.gaussianTransform_abs_bound hav.2 hav.1 z
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    dsimp only [c] at hm
    linarith

lemma gaussianOperator_zero_abs (v : ℝ) :
    gaussianOperator 0 v (fun x : ℝ => |x|) 0 = Real.sqrt v * gaussianAbsoluteMean := by
  simp only [gaussianOperator, ite_true, if_true, zero_add, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg v), integral_const_mul, gaussianAbsoluteMean]

lemma fieldValue_abs_sum (h : FieldStep) :
    fieldValue h 0 ≤ Real.sqrt (h.height 0) * gaussianAbsoluteMean +
      (∑ i : Fin h.depth,
        ((fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2 +
          Real.log 2 / (fieldIncrement h i.succ).1)) - h.height (Fin.last h.depth) / 2 := by
  let L := List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)
  have hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2 := by
    intro av hav
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
    exact ⟨fieldIncrement_tail_positive h i, fieldIncrement_nonneg h i.succ⟩
  have hT := gaussianOperator_fold_growth L (fun av hav => (hL av hav).1)
    IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
  let c := (L.map (fun av => av.1 * av.2 / 2 + Real.log 2 / av.1)).sum
  have hm := gaussianOperator_mono hT.1 (measurable_const.add measurable_id.abs)
    hT.2 (linearGrowth_const_add IsingPerceptron.abs_linearGrowth c)
    (fun x => by simpa only [c, Pi.add_apply, id_eq, add_comm] using gaussianOperator_fold_abs L hL x)
    (show 0 ≤ (0 : ℝ) from le_rfl) (h.height 0) 0
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) 0 ≤
    gaussianOperator 0 (h.height 0) (fun x : ℝ => c + |x|) 0 at hm
  rw [gaussianOperator_const_add (F := fun x : ℝ => |x|) measurable_id.abs IsingPerceptron.abs_linearGrowth,
    gaussianOperator_zero_abs] at hm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    simp [fieldIncrement, h.first]
  simp only [fieldValue, List.ofFn_succ, List.foldr_cons, hroot]
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) 0 - h.height (Fin.last h.depth) / 2 ≤ _
  have hc : c = ∑ i : Fin h.depth,
      ((fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2 +
        Real.log 2 / (fieldIncrement h i.succ).1) := by
    simp only [c, L, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [hc] at hm
  linarith

/-- The field value has a linear negative cost in its integrated height and
only a square-root positive cost at the root.  This is sufficient to make
the upper-comparison field cap inactive for a fixed trial partition. -/
lemma fieldValue_cap_estimate (h : FieldStep) :
    fieldValue h 0 ≤ -(∫ s, fieldFunction h s ∂pathMeasure) / 2 +
      Real.sqrt (h.height 0) * gaussianAbsoluteMean + fieldPartitionConstant h := by
  have harea := integral_fieldFunction_eq_increment_sum h
  have hs := fieldIncrement_sum h
  have hz : (fieldIncrement h 0).1 = 0 := by simp [fieldIncrement, h.first]
  have hcut : (∑ i : Fin (h.depth + 1),
      (fieldIncrement h i).1 * (fieldIncrement h i).2) =
      h.height (Fin.last h.depth) - ∫ s, fieldFunction h s ∂pathMeasure := by
    rw [harea, ← hs, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change h.cut i.castSucc * (fieldIncrement h i).2 = _
    ring
  rw [Fin.sum_univ_succ, hz, zero_mul, zero_add] at hcut
  have hv := fieldValue_abs_sum h
  rw [Finset.sum_add_distrib] at hv
  have hc : (∑ i : Fin h.depth,
      (fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2) =
      (h.height (Fin.last h.depth) - ∫ s, fieldFunction h s ∂pathMeasure) / 2 := by
    rw [← Finset.sum_div, hcut]
  rw [hc] at hv
  change fieldValue h 0 ≤ _ + (_ + fieldPartitionConstant h) - _ at hv
  linarith

lemma integral_fieldFunction_ge_last (h : FieldStep) :
    (1 - h.cut (Fin.last h.depth).castSucc) * h.height (Fin.last h.depth) ≤
      ∫ s, fieldFunction h s ∂pathMeasure := by
  rw [integral_fieldFunction]
  have hm : h.cut (Fin.last h.depth).succ = 1 := h.last
  rw [← hm]
  apply Finset.single_le_sum (f := fun i : Fin (h.depth + 1) =>
    (h.cut i.succ - h.cut i.castSucc) * h.height i) _ (Finset.mem_univ (Fin.last h.depth))
  intro i _
  exact mul_nonneg (sub_nonneg.mpr (h.ordered_cut.monotone (Fin.castSucc_le_succ i)))
    (h.nonneg i)

/-- With a trial uniformly below one, the negative last-height term dominates
all fields on that fixed partition. -/
lemma fieldValue_add_pairing_cap (p : OverlapPath) {d : ℝ} (hd : 0 ≤ d)
    (hp : ∀ᵐ s ∂pathMeasure, p s ≤ 1 - d) (h : FieldStep) :
    fieldValue h 0 + fieldPairing p h / 2 ≤
      -(d * (1 - h.cut (Fin.last h.depth).castSucc) / 2) *
          h.height (Fin.last h.depth) +
        gaussianAbsoluteMean * Real.sqrt (h.height (Fin.last h.depth)) +
        fieldPartitionConstant h := by
  have hv := fieldValue_cap_estimate h
  have hq := fieldPairing_le_const_integral p h (1 - d) hp
  have ha := integral_fieldFunction_ge_last h
  have hn := mul_le_mul_of_nonneg_left ha hd
  have hr := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (h.ordered_height (Fin.zero_le (Fin.last h.depth)))) gaussianAbsoluteMean_nonneg
  nlinarith

/-- The elementary square-root-versus-linear estimate needed to choose the
field cap. -/
lemma exists_linear_sqrt_cap {e : ℝ} (he : 0 < e) (C K B : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x : ℝ, H ≤ x → -e * x + C * Real.sqrt x + K ≤ B := by
  let A := C ^ 2 / (2 * e) + |K| + |B| + 1
  let H := 2 * A / e
  have hA : 0 < A := by
    have ht : 0 ≤ C ^ 2 / (2 * e) := div_nonneg (sq_nonneg _) (by positivity)
    dsimp only [A]
    linarith [abs_nonneg K, abs_nonneg B]
  have hH : 0 < H := div_pos (mul_pos (by norm_num) hA) he
  refine ⟨H, hH, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := hH.le.trans hx
  have hsq := sq_nonneg (e * Real.sqrt x - C)
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  rw [sub_sq, mul_pow, hs] at hsq
  have hroot : C * Real.sqrt x ≤ e * x / 2 + C ^ 2 / (2 * e) := by
    calc
      _ ≤ (e ^ 2 * x + C ^ 2) / (2 * e) :=
        (le_div_iff₀ (show 0 < 2 * e by positivity)).2 (by nlinarith)
      _ = _ := by field_simp
  have hxe : 2 * A ≤ e * x := by
    change 2 * A / e ≤ x at hx
    have hh := (div_le_iff₀ he).1 hx
    nlinarith
  dsimp only [A] at hxe
  nlinarith [le_abs_self K, neg_le_abs B]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactStep
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact increment coordinates represent the same fixed-partition
fields and pairings as the one-site variational functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldPairing_of_step_trial (p : OverlapPath) (h : FieldStep)
    (v : Fin (h.depth + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ) → p s = v i) :
    fieldPairing p h = ∑ i, (h.cut i.succ - h.cut i.castSucc) * v i * h.height i := by
  unfold fieldPairing
  calc
    _ = ∫ s, finiteStepFunction h.cut (fun i => v i * h.height i) s ∂pathMeasure := by
      apply integral_congr_ae
      refine ae_of_all _ fun s => ?_
      simp only [fieldFunction, finiteStepFunction, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · rw [hv i s hi]
      · simp
    _ = ∑ i, (h.cut i.succ - h.cut i.castSucc) * (v i * h.height i) :=
      integral_finiteStepFunction h.cut h.ordered_cut h.first h.last _
    _ = _ := by simp only [mul_assoc]

lemma fieldPairing_contactFieldStep {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → p s = v i) :
    fieldPairing p (contactFieldStep cut hc hfirst hlast a ha) =
      ∑ i, ((cut i.succ - cut i.castSucc) * v i) * finiteFieldPath a i :=
  fieldPairing_of_step_trial p (contactFieldStep cut hc hfirst hlast a ha) v hv


lemma fieldPartitionConstant_contactFieldStep {n : ℕ}
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) :
    fieldPartitionConstant (contactFieldStep cut hc hfirst hlast a ha) =
      ∑ i : Fin n, Real.log 2 / cut i.succ.castSucc := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the tensor pressure before varying its
linear field. Gaussian CGF bounds suffice; no concentration input is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma randomCoefficient_log_partition_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω → X → ℝ) (hH : Measurable (Function.uncurry H))
    (he : ∀ ω, Integrable (fun x => Real.exp (H ω x)) (ν ω))
    (hi : Integrable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) P)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hcap : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) :
    Integrable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1))
      (P.prod gaussianCoordinates) := by
  let η := fun ω => (ν ω).tilted (H ω)
  have : ∀ ω, IsProbabilityMeasure (η ω) := fun ω => isProbabilityMeasure_tilted (he ω)
  have hη : Measurable η := measurable_random_tilted_measure
    (ν := ν) (H := Function.uncurry H) hν hH
  let G := fun p : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A p.1 x) p.2) (η p.1) 1
  have hmG : Measurable G := measurable_randomCoefficient_cgf hη A hA 1
  have hiG : Integrable G (P.prod gaussianCoordinates) := integrable_randomCoefficient_cgf hη A hA hcap 1
  have hmC : Measurable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) :=
    (measurable_random_referencePartition hν hH).log
  have : ∀ p : Ω × (ℕ → ℝ), IsProbabilityMeasure ((ν ∘ Prod.fst) p) := fun p => by
    change IsProbabilityMeasure (ν p.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hHm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => H p.1.1 p.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hmF : Measurable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) :=
    (measurable_random_referencePartition (hν.comp measurable_fst) (hHm.add hA)).log
  have hfold : (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) =ᵐ[P.prod gaussianCoordinates]
      (fun p => Real.log (∫ x, Real.exp (H p.1 x) ∂ν p.1) + G p) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmF ((hmC.comp measurable_fst).add hmG))).mpr
    exact ae_of_all _ fun ω => by
      have ht := cylinder_log_partition_base (ν ω) (H ω) (he ω) (A ω) (hcap ω) 1
      filter_upwards [ht] with z hz
      simpa only [one_mul, G, η, Pi.add_apply, Function.comp_apply] using hz
  exact ((hi.comp_fst gaussianCoordinates).add hiG).congr hfold.symm

lemma measurable_tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (Function.uncurry (tensorDeterministicEnergy eig c n)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add_const (fieldEnergy c x.1)

lemma measurable_tensorNamespacedPathFields {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
        (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amp n
        (fun a => tensorPathProfile I degree n treeDegree h a) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → NNReal :=
    fun a => tensorPathProfile I degree n treeDegree h a
  have hm : Measurable (fun p : TensorFlatDisorder N n => (p.1.1, p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amp n v x).comp hm
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGGRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete tensor GG rate tends to zero for every fixed monomial. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma tensorContactGGRate_tendsto (j m : ℕ) (L B : ℝ) :
    Tendsto (fun N => tensorContactGGRate N j m L B) atTop (nhds 0) := by
  have h := (contactGGRate_tendsto j L B).add
    ((diagonalContactRate_tendsto L).const_mul (2 * B * ∑ a, (enumeratedSpectralDegree m j a : ℝ)))
  simpa only [tensorContactGGRate, mul_zero, add_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) :
    Continuous (spectralEntryMonomial d) := by
  exact continuous_finsetProd _ fun a _ => ((continuous_apply a).subtype_val).pow _

lemma continuous_spectralBlockView (m n : ℕ) : Continuous (spectralBlockView m n) := by
  unfold spectralBlockView
  fun_prop

lemma continuous_spectralBlockLink (m n i j : ℕ) : Continuous (spectralBlockLink m n i j) :=
  (continuous_spectralBlockView m n).prodMk (continuous_apply _)

private lemma continuous_spectralBlockPairCoordinate (m n : ℕ)
    (i : ((Fin n × Fin n) × Fin m) ⊕ Fin m) :
    Continuous (spectralBlockPairCoordinate m n i) := by
  cases i <;> unfold spectralBlockPairCoordinate <;> fun_prop

private lemma spectralBlockPairCoordinate_ext (m n : ℕ)
    (x y : SpectralBlock m n × SpectralEntry m)
    (h : ∀ i, spectralBlockPairCoordinate m n i x = spectralBlockPairCoordinate m n i y) : x = y := by
  apply Prod.ext
  · funext i j a
    exact Subtype.ext (h (.inl ((i, j), a)))
  · funext a
    exact Subtype.ext (h (.inr a))

/-- Polynomial moments in the new link, with arbitrary continuous tests
of the old block, determine its full joint law. -/
theorem spectralBlock_pair_monomials_unique (m n : ℕ)
    (P Q : Measure (SpectralBlock m n × SpectralEntry m)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (∫ x, D x.1 * spectralEntryMonomial d x.2 ∂P) =
        ∫ x, D x.1 * spectralEntryMonomial d x.2 ∂Q) : P = Q := by
  classical
  have : TopologicalSpace.SeparableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (SpectralBlock m n × SpectralEntry m) := inferInstance
  let I := ((Fin n × Fin n) × Fin m) ⊕ Fin m
  let g : I → ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨spectralBlockPairCoordinate m n i, continuous_spectralBlockPairCoordinate m n i⟩
  let ev : MvPolynomial I ℝ →ₐ[ℝ] ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((SpectralBlock m n × SpectralEntry m) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : I) (x : SpectralBlock m n × SpectralEntry m) :
      g i x = spectralBlockPairCoordinate m n i x := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i : I, spectralBlockPairCoordinate m n i x ≠
        spectralBlockPairCoordinate m n i y := by
      by_contra! hno
      exact hxy (spectralBlockPairCoordinate_ext m n x y hno)
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using hi
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    let D : SpectralBlock m n → ℝ := fun b =>
      ∏ i : (Fin n × Fin n) × Fin m, (b i.1.1 i.1.2 i.2 : ℝ) ^ k (.inl i)
    have hD : Continuous D := by
      apply continuous_finsetProd
      intro i _
      exact (by fun_prop : Continuous (fun b : SpectralBlock m n => (b i.1.1 i.1.2 i.2 : ℝ))).pow _
    have he (x : SpectralBlock m n × SpectralEntry m) :
        ev (MvPolynomial.monomial k c) x = c * (D x.1 * spectralEntryMonomial (fun a => k (.inr a)) x.2) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_pow]
      simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply,
        BoundedContinuousFunction.coe_prod, BoundedContinuousFunction.coe_pow,
        BoundedContinuousFunction.algebraMap_apply, Finset.prod_apply, Pi.pow_apply, smul_eq_mul, mul_one]
      change c * (∏ i : I, g i x ^ k i) = _
      rw [Fintype.prod_sum_type]
      rfl
    change (∫ x, ev (MvPolynomial.monomial k c) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k c) x ∂Q
    simp only [he, integral_const_mul]
    exact congrArg (c * ·) (h D hD _)

theorem spectral_monomial_measure_identity (m : ℕ) (μ : Measure (SpectralArray m))
    [IsProbabilityMeasure μ] (n : ℕ) (i : Fin n)
    (h : ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    (n : ℝ≥0∞) • μ.map (spectralBlockLink m n i n) =
      (μ.map (spectralBlockView m n)).prod (μ.map (fun x => x (0, 1))) +
        ∑ j ∈ Finset.univ.erase i, μ.map (spectralBlockLink m n i j) := by
  classical
  let block := μ.map (spectralBlockView m n)
  let pair := μ.map (fun x => x (0, 1))
  let link := fun j : ℕ => μ.map (spectralBlockLink m n i j)
  have : IsProbabilityMeasure block := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockView m n).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure pair := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply (0, 1)).aemeasurable).mpr inferInstance
  have (j : ℕ) : IsProbabilityMeasure (link j) := (Measure.isProbabilityMeasure_map_iff
    (continuous_spectralBlockLink m n i j).measurable.aemeasurable).mpr inferInstance
  change (n : ℝ≥0∞) • link n = block.prod pair + ∑ j ∈ Finset.univ.erase i, link j
  have : IsFiniteMeasure ((n : ℝ≥0∞) • link n) := (link n).smul_finite (by simp)
  apply spectralBlock_pair_monomials_unique m n
  intro D hD d
  let F : SpectralBlock m n × SpectralEntry m → ℝ := fun x => D x.1 * spectralEntryMonomial d x.2
  have hF : Continuous F := (hD.comp continuous_fst).mul
    ((continuous_spectralEntryMonomial d).comp continuous_snd)
  have hi (j : ℕ) : (∫ x, F x ∂link j) =
      ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ :=
    integral_map (continuous_spectralBlockLink m n i j).measurable.aemeasurable hF.aestronglyMeasurable
  change (∫ x, F x ∂(n : ℝ≥0∞) • link n) = ∫ x, F x ∂(block.prod pair + ∑ j ∈ Finset.univ.erase i, link j)
  rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    integral_add_measure (compact_integrable hF) (compact_integrable hF),
    integral_finsetSum_measure (fun j _ => compact_integrable hF), hi]
  simp_rw [hi]
  rw [h D hD d]
  congr 1
  have hp := continuous_spectralEntryMonomial d
  have he : (∫ x, F x ∂block.prod pair) =
      (∫ b, D b ∂block) * (∫ x, spectralEntryMonomial d x ∂pair) :=
    integral_prod_mul D (spectralEntryMonomial d)
  rw [he, integral_map (continuous_spectralBlockView m n).measurable.aemeasurable hD.aestronglyMeasurable,
    integral_map (measurable_pi_apply (0, 1)).aemeasurable hp.aestronglyMeasurable]

theorem spectral_monomialGG_measurable (m : ℕ) (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (h : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) =
        (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) μ := by
  classical
  intro n hn i A hA t ht
  have he := congrArg (fun ν : Measure (SpectralBlock m n × SpectralEntry m) => (ν (A ×ˢ t)).toReal)
    (spectral_monomial_measure_identity m μ n i (h n hn i))
  have hmap : ∀ j : ℕ, Measurable (spectralBlockLink m n i j) := fun j =>
    (continuous_spectralBlockLink m n i j).measurable
  have hblock := (continuous_spectralBlockView m n).measurable
  have hpair : Measurable (fun x : SpectralArray m => x (0, 1)) := measurable_pi_apply _
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    Measure.add_apply, Measure.prod_prod, Measure.finsetSum_apply,
    Measure.map_apply (hmap _) (hA.prod ht), Measure.map_apply hblock hA, Measure.map_apply hpair ht] at he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at he
  change (n : ℝ) * μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t} +
    ∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t}) at he
  change μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, n) ∈ t}) =
    (μ.real {x | spectralBlockView m n x ∈ A} * μ.real {x | x (0, 1) ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real ({x | spectralBlockView m n x ∈ A} ∩ {x | x (i, j) ∈ t})) / n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]
  nlinarith [he]

lemma spectralMonomialResidual_zero {m : ℕ} (μ : Measure (SpectralArray m)) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) :
    spectralMonomialResidual μ n i D 0 = 0 := by
  classical
  have hn : 1 ≤ n := by have hi := i.isLt; omega
  simp only [spectralMonomialResidual, spectralEntryMonomial, Pi.zero_apply, pow_zero,
    Finset.prod_const_one, mul_one, integral_const, probReal_univ, one_smul,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
  ring

lemma spectralMonomialResidual_weak_limit {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (n : ℕ) (i : Fin n) (D : SpectralBlock m n → ℝ) (hD : Continuous D) (d : Fin m → ℕ) :
    Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop
      (𝓝 (spectralMonomialResidual μ n i D d)) := by
  have hI : ∀ F : SpectralArray m → ℝ, Continuous F →
      Tendsto (fun N => ∫ x, F x ∂(L N : Measure (SpectralArray m))) atTop
        (𝓝 (∫ x, F x ∂(μ : Measure (SpectralArray m)))) := by
    intro F hF
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hcD := hD.comp (continuous_spectralBlockView m n)
  have ht (j : ℕ) := hI (fun x => D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)))
    (hcD.mul ((continuous_spectralEntryMonomial d).comp (continuous_apply _)))
  exact (((ht n).const_mul (n : ℝ)).sub ((hI _ hcD).mul
    (hI _ ((continuous_spectralEntryMonomial d).comp (continuous_apply _))))).sub
      (tendsto_finsetSum _ fun j _ => ht j)

/-- Vanishing monomial residuals imply the Ghirlanda–Guerra identities
for the weak limit of the spectral overlap arrays. -/
theorem spectralGG_of_weak_monomial_residuals {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {μ : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D → ∀ d : Fin m → ℕ,
      Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectral_monomialGG_measurable
  intro n hn i D hD d
  have he := tendsto_nhds_unique (spectralMonomialResidual_weak_limit hL n i D hD d)
    (hg n hn i D hD d)
  dsimp only [spectralMonomialResidual] at he
  linarith

theorem spectralGG_of_weak_nonconstant_monomial_residuals {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray m)} {μ : ProbabilityMeasure (SpectralArray m)}
    (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : SpectralBlock m n → ℝ, Continuous D →
      ∀ d : Fin m → ℕ, d ≠ 0 →
        Tendsto (fun N => spectralMonomialResidual (L N) n i D d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (μ : Measure (SpectralArray m)) := by
  apply spectralGG_of_weak_monomial_residuals hL
  intro n hn i D hD d
  by_cases hd : d = 0
  · subst d
    simpa only [spectralMonomialResidual_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact hg n hn i D hD d hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

lemma spectralJointEntry_spectral {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) (a : Fin m) :
    (spectralJointEntry U I n x y a.castSucc : ℝ) = projectedOverlap U (I a) x.1 y.1 := by
  simp only [spectralJointEntry, Fin.lastCases_castSucc]

lemma spectralJointEntry_tree {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) :
    (spectralJointEntry U I n x y (Fin.last m) : ℝ) = treeOverlap n x.2 y.2 := by
  simp only [spectralJointEntry, Fin.lastCases_last]

theorem spectralArrayLaw_integral {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)]
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1)))) =
      ∫ ω, ∫ σ, F (spectralReplicaArray U I n (ω, σ))
        ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hm := measurable_spectralReplicaArray U hU I n
  have hi : Integrable (F ∘ spectralReplicaArray U I n) (disorderReplicaLaw P ν hν) := by
    exact (MeasureTheory.integrable_map_measure hF.aestronglyMeasurable hm.aemeasurable).mp
      (compact_integrable hF)
  change (∫ x, F x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)) = _
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact Measure.integral_compProd hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every weak spectral-array limit of actual finite perturbation minimizers
satisfies the full vector Ghirlanda–Guerra identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma enumeratedJointMonomial_surjective (m : ℕ) (d : Fin (m + 1) → ℕ) (hd : d ≠ 0) :
    ∃ j, (fun a => Fin.lastCases (enumeratedTreeDegree m j) (enumeratedSpectralDegree m j) a) = d := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, d a ≠ 0 := by
    by_contra! h
    exact hd (funext h)
  have hs : 1 ≤ ∑ a, d a :=
    (Nat.one_le_iff_ne_zero.mpr ha).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  rw [Fin.sum_univ_castSucc] at hs
  obtain ⟨j, hj, hr⟩ := enumeratedMonomial_surjective m (fun a => d a.castSucc) (d (Fin.last m)) hs
  refine ⟨j, ?_⟩
  funext a
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [Fin.lastCases_last] using hr
  · simpa only [Fin.lastCases_castSucc] using hj b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorSingleObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-replica and direct-observable conventions agree in the actual
countable spin/leaf Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma referenceReplicaMean_zero_one {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν] (D : X → ℝ) :
    referenceReplicaMean ν (fun _ => 0) (fun σ : Fin 1 → X => D (σ 0)) =
      ∫ x, D x ∂ν := by
  rw [referenceReplicaMean_zero]
  exact (measurePreserving_eval (fun _ : Fin 1 => ν) 0).hasLaw.integral_comp
    (measurable_of_countable D).aestronglyMeasurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomBoundedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded random observable has a differentiable disorder-averaged CGF.
This applies to the actual temperature observable retaining common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_bounded_random_tilted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω → X → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB : ∀ ω x, |Y ω x| ≤ B) (t : ℝ) :
    Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t * Y ω x)) P := by
  have hm := measurable_random_tilted_integral hν (hY.const_mul t) hY
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry_apply_pair, id_eq] using bounded_tilted_integral_abs (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) t

theorem hasDerivAt_bounded_random_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω → X → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB : ∀ ω x, |Y ω x| ≤ B) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, cgf (Y ω) (ν ω) s ∂P)
      (∫ ω, ∫ x, Y ω x ∂(ν ω).tilted (fun x => t * Y ω x) ∂P) t := by
  apply hasDerivAt_mean_cgf ν Y
  · exact ae_of_all _ fun ω s => exp_mul_integrable_of_bound (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) s
  · exact fun s => integrable_bounded_random_cgf P ν hν (Function.uncurry Y) hY B hB s
  · exact fun s => integrable_bounded_random_tilted_mean P ν hν Y hY B hB s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTemperatureCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature is a bounded deterministic tilt of the actual enriched
Gibbs reference, with all Gaussian and cascade variables retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma tensorTemperatureHamiltonian_affine {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) (t : ℝ) :
    tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p =
      fun x => tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0)
        c I degree amp n r h p x + t * rotatedEnergy eig (specialRotation p.1.1) x.1 := by
  funext x
  unfold tensorNamespacedHamiltonian
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN]
  ring

lemma measurable_tensorTemperatureObservable {N n : ℕ} (eig : Fin N → ℝ) :
    Measurable (fun p : TensorFlatDisorder N n × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1.1) p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  unfold rotatedEnergy
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_specialRotation_eval (spinVector x.1) i).comp measurable_fst.fst).pow_const 2
      |>.const_mul (eig i)).const_mul _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TailOrder
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper-tail order used in the finite-spectrum upper comparison. -/

noncomputable section

open MeasureTheory Set

namespace InvariantIsing

lemma posPart_integral_eq_interval (p : OverlapPath) (r : ℝ) :
    (∫ u, max (p u - r) 0 ∂pathMeasure) = ∫ u in 0..1, max (p u - r) 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

lemma pathTail_sub_le_posPart (p : OverlapPath) (r : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathTail p s - (1 - s) * r ≤ ∫ u, max (p u - r) 0 ∂pathMeasure := by
  let g : ℝ → ℝ := fun u => max (p u - r) 0
  have hg : Monotone g := fun _ _ huv =>
    max_le_max (sub_le_sub_right (p.monotone huv) r) le_rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := 0) (b := s))
    (hg.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have hlo : 0 ≤ ∫ u in 0..s, g u :=
    intervalIntegral.integral_nonneg_of_forall hs.1 (fun _ => le_max_right _ _)
  have hhi : (∫ u in s..1, p u - r) ≤ ∫ u in s..1, g u :=
    intervalIntegral.integral_mono hs.2
      (p.monotone.intervalIntegrable.sub intervalIntegrable_const) hg.intervalIntegrable
      (fun _ => le_max_left _ _)
  rw [intervalIntegral.integral_sub p.monotone.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hhi
  rw [posPart_integral_eq_interval]
  change (∫ u in s..1, p u) - (1 - s) * r ≤ ∫ u in 0..1, g u
  linarith

/-- A monotone quantile crosses any horizontal level at a cutoff, allowing a
jump or a nontrivial atom at that level. Endpoint values play no role. -/
lemma exists_path_level_cutoff (p : OverlapPath) (r : ℝ) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∀ u ∈ Ioo 0 s, p u ≤ r) ∧ (∀ u ∈ Ioo s 1, r ≤ p u) := by
  let A : Set ℝ := {u | u ∈ Icc (0 : ℝ) 1 ∧ r < p u} ∪ {1}
  have hne : A.Nonempty := ⟨1, Or.inr rfl⟩
  have hb : BddBelow A := by
    refine ⟨0, ?_⟩
    intro u hu
    rcases hu with hu | hu
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.mp hu]; norm_num
  have hs0 : 0 ≤ sInf A := le_csInf hne (by
    intro u hu
    rcases hu with hu | hu
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.mp hu]; norm_num)
  have hs1 : sInf A ≤ 1 := csInf_le hb (Or.inr rfl)
  refine ⟨sInf A, ⟨hs0, hs1⟩, ?_, ?_⟩
  · intro u hu
    by_contra h
    have humem : u ∈ A := Or.inl ⟨⟨hu.1.le, hu.2.le.trans hs1⟩, lt_of_not_ge h⟩
    exact (not_le_of_gt hu.2) (csInf_le hb humem)
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := exists_lt_of_csInf_lt hne hu.1
    rcases hv with hv | hv
    · exact (hv.2.trans_le (p.monotone hvu.le)).le
    · rw [Set.mem_singleton_iff.mp hv] at hvu
      exact False.elim ((not_lt_of_ge hu.2.le) hvu)

/-- The positive-part integral is attained by a tail of the quantile. -/
lemma exists_posPart_eq_pathTail (p : OverlapPath) (r : ℝ) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∫ u, max (p u - r) 0 ∂pathMeasure) = pathTail p s - (1 - s) * r := by
  obtain ⟨s, hs, hlo, hhi⟩ := exists_path_level_cutoff p r
  let g : ℝ → ℝ := fun u => max (p u - r) 0
  have hg : Monotone g := fun _ _ huv =>
    max_le_max (sub_le_sub_right (p.monotone huv) r) le_rfl
  have hlow : (∫ u in 0..s, g u) = 0 := by
    calc
      _ = ∫ _ in 0..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro u hu
        exact max_eq_right (sub_nonpos.mpr (hlo u hu))
      _ = 0 := by simp
  have hhigh : (∫ u in s..1, g u) = pathTail p s - (1 - s) * r := by
    calc
      _ = ∫ u in s..1, p u - r := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.2
        intro u hu
        exact max_eq_left (sub_nonneg.mpr (hhi u hu))
      _ = _ := by
        rw [intervalIntegral.integral_sub p.monotone.intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := 0) (b := s))
    (hg.intervalIntegrable (μ := volume) (a := s) (b := 1))
  refine ⟨s, hs, ?_⟩
  rw [posPart_integral_eq_interval]
  simpa only [hlow, hhigh, zero_add] using hsum.symm

/-- Manuscript `up:tail-order`: ordering every upper tail reverses the entire
deficit function, including at jumps and atoms of either overlap quantile. -/
theorem deficit_le_of_pathTail_le (p q : OverlapPath)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) (r : ℝ) :
    deficit p r ≤ deficit q r := by
  obtain ⟨s, hs, he⟩ := exists_posPart_eq_pathTail q r
  have hpos : (∫ u, max (q u - r) 0 ∂pathMeasure) ≤
      ∫ u, max (p u - r) 0 ∂pathMeasure := by
    rw [he]
    exact (sub_le_sub_right (htail s hs) _).trans (pathTail_sub_le_posPart p r hs)
  unfold deficit
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature differentiation for the actual finite Ising pressure. -/

noncomputable section

open IsingPerceptron MeasureTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma abs_rotatedEnergy_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig U σ| ≤ K * N / 2 := by
  simpa only [rotatedEnergy_constant, zero_mul, zero_div, sub_zero] using
    abs_rotatedEnergy_sub_le eig (fun _ => 0) U K (fun i => by simpa using heig i) σ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorCascadePressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cascade-enriched pressure for a deterministic spin prior.
Normalized magnetization slices are allowed, while the cascade remains
quenched and is averaged only after taking the logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinPriorDeterministicLog_abs_le {N n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    |Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
      (tensorDeterministicEnergy eig c n ω x) ∂labeledSpinReference n π ω.2)| ≤
      (∑ i, |eig i|)*N/2+∑ i, |c i| := by
  let ν := labeledSpinReference n π ω.2
  let H := tensorDeterministicEnergy eig c n ω
  have hH : Integrable (fun x => Real.exp (H x)) ν := finite_spin_base_exp_integrable ν
    (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ)
  have hbound (x : Spin N × LabeledLeaf n) : |H x| ≤ (∑ i, |eig i|)*N/2+∑ i, |c i| := by
    have he := abs_rotatedEnergy_le eig (specialRotation ω.1) (∑ i, |eig i|)
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i)) x.1
    have hf : |fieldEnergy c x.1| ≤ ∑ i, |c i| := by
      simpa only [fieldEnergy,zero_mul,Finset.sum_const_zero,sub_zero] using
        abs_fieldEnergy_sub_le c (fun _ => 0) x.1
    exact (abs_add_le _ _).trans (add_le_add he hf)
  have hb := logMean_abs_sub_le ν (F := H) (G := fun _ => 0) (b := 1) (by norm_num)
    (by simpa only [one_mul] using hH)
    (by simpa only [mul_zero,Real.exp_zero] using (integrable_const (1 : ℝ)))
    (fun x => by simpa only [sub_zero] using hbound x)
  simpa only [logMean,one_mul,div_one,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero] using hb

lemma spinPriorDeterministicLog_integrable {N n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (b : ℕ → ℝ) :
    Integrable (fun ω : SpecialOrthogonal N × LabeledTree n => Real.log
      (∫ x, Real.exp (tensorDeterministicEnergy eig c n ω x) ∂labeledSpinReference n π ω.2))
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) := by
  have hν : Measurable (fun ω : SpecialOrthogonal N × LabeledTree n => labeledSpinReference n π ω.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  apply integrable_of_measurable_abs_le
    (c := (∑ i, |eig i|)*N/2+∑ i, |c i|)
    ((measurable_random_referencePartition hν (measurable_tensorDeterministicEnergy eig c n)).log)
  exact spinPriorDeterministicLog_abs_le π eig c

theorem spinPriorNamespacedLog_integrable {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (spinPriorNamespacedLog (n := n) π eig c I degree amp r h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  have hν : Measurable (fun ω : SpecialOrthogonal N × LabeledTree n => labeledSpinReference n π ω.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  exact randomCoefficient_log_partition_integrable hν (tensorDeterministicEnergy eig c n)
    (measurable_tensorDeterministicEnergy eig c n)
    (fun ω => finite_spin_base_exp_integrable (labeledSpinReference n π ω.2)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ))
    (spinPriorDeterministicLog_integrable μ π eig c b)
    (fun ω => tensorNamespacedCoefficients (specialRotation ω.1) I degree amp n
      (fun i => tensorPathProfile I degree n r h i))
    (measurable_tensorNamespacedPathFields I degree amp n r h)
    (fun ω x => tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amp n r h hh h0 x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorExponential
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential integrability of the actual cascade-enriched Hamiltonian
for a normalized deterministic spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n π p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n π ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n π ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) :=
    finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ)
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorDeterministicEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_tensorNamespacedPathFields I degree amplitude n treeDegree h
  have hA (ω : Ω) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amplitude n treeDegree h hh h0 x
  have he := randomCoefficient_all_exp_ae
    (P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) htilt A hAm hA
  filter_upwards [he] with p hp
  have hi := hp 1
  rw [integrable_tilted_iff (hbase p.1)] at hi
  simpa only [H, A, ν, one_mul, smul_eq_mul, ← Real.exp_add] using hi


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

/-- Injection into the infinite replica sequence gives the exact actual
finite-replica mean, while retaining its common rotation. -/
theorem spinPriorArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(spinPriorArrayLaw μ π eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h D := by
  rw [spinPriorArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold spinPriorReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h p
  have ht := integral_map hm.aemeasurable (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [replica_injective_map ν ι hi] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ σ, D p.1.1 σ ∂Measure.pi (fun _ : Fin z => ν)
  simp_rw [he]
  exact ht.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) :
    Continuous (permuteSpectralArray (m := m) e) := by
  unfold permuteSpectralArray
  fun_prop

lemma disorderReplicaLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (disorderReplicaLaw P ν hν).map (Prod.map id (fun σ i => σ (e i))) =
      disorderReplicaLaw P ν hν := by
  unfold disorderReplicaLaw
  rw [← Measure.compProd_map (by fun_prop)]
  congr 1
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (by fun_prop)]
  change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => σ (e i)) =
    Measure.infinitePi (fun _ : ℕ => ν ω)
  exact Measure.map_infinitePi_infinitePi_of_inj he

lemma spectralArrayLaw_map_reindex {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (e : ℕ → ℕ) (he : Function.Injective e) :
    (spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = spectralArrayLaw P U hU I n ν hν := by
  change ((disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)).map _ = _
  rw [Measure.map_map (continuous_permuteSpectralArray e).measurable
    (measurable_spectralReplicaArray U hU I n)]
  have heq : permuteSpectralArray e ∘ spectralReplicaArray U I n =
      spectralReplicaArray U I n ∘ Prod.map id (fun σ i => σ (e i)) := rfl
  rw [heq, ← Measure.map_map (measurable_spectralReplicaArray U hU I n) (by fun_prop),
    disorderReplicaLaw_map_reindex P ν hν e he]
  rfl

lemma spectralArray_limit_reindex {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (e : ℕ → ℕ)
    (hE : ∀ k, (L k : Measure (SpectralArray m)).map (permuteSpectralArray e) = L k) :
    (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_permuteSpectralArray e)).tendsto Q
  have he : (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = L := by
    funext k
    exact Subtype.ext (hE k)
  have ht := hc.comp hL
  change Tendsto (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) _ _ at ht
  rw [he] at ht
  have heq : Q.map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = Q := tendsto_nhds_unique ht hL
  exact congrArg Subtype.val heq

lemma continuous_spectralCoordinateArray {m : ℕ} (a : Fin m) :
    Continuous (spectralCoordinateArray a) := by
  unfold spectralCoordinateArray
  fun_prop

lemma isClosed_spectralGram (m : ℕ) : IsClosed {x : SpectralArray m | SpectralGram x} := by
  unfold SpectralGram
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun n =>
    (isClosed_setOf_posSemidef n).preimage (by unfold spectralCoordinateArray; fun_prop)

lemma spectralReplicaArray_gram {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralGram (spectralReplicaArray U I n p) := by
  intro a z
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_tree] using
      treeOverlap_posSemidef n (fun i : Fin z => (p.2 i).2)
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (specialRotation (U p.1)) (I j) (fun i : Fin z => (p.2 i).1)

lemma spectralArrayLaw_gram {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))), SpectralGram x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n), SpectralGram x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralGram (m + 1)).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_gram U I n)

lemma spectralArray_limit_gram {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray m)), SpectralGram x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x :=
  ae_closed_of_weak_limit hL (isClosed_spectralGram m) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGGGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma spectralGram_diagonal {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a) (a : Fin m) :
    GramDiagonal (q a) (spectralCoordinateArray a x) :=
  ⟨hG a, fun i => hd i a⟩

lemma spectralGG_coordinate_nonnegative {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ a, 0 ≤ (x (0,1) a : ℝ) := by
  apply ae_all_iff.mpr
  intro a
  exact gg_pair_nonnegative_ae (continuous_spectralCoordinateArray a).measurable
    (hgg.real_map (f := fun x => (x a : ℝ)) (by fun_prop)) (hq a)
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_diagonal hx q hdx a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma projectedOverlap_partition {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ τ) = projectedOverlap U Finset.univ σ τ := by
  classical
  unfold projectedOverlap
  rw [← Finset.mul_sum]
  congr 1
  have hs := Finset.sum_biUnion (f := fun i => U (spinVector σ) i * U (spinVector τ) i)
    (show Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis)
  rw [hcover] at hs
  exact hs.symm

lemma projectedOverlap_partition_self {N m : ℕ} (hN : 0 < N) (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ σ) = 1 := by
  rw [projectedOverlap_partition U I hdis hcover, projectedOverlap_univ]
  simp only [← pow_two, spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')

lemma isClosed_spectralPartitionGeometry (m : ℕ) :
    IsClosed {x : SpectralArray (m + 1) | SpectralPartitionGeometry m x} := by
  unfold SpectralPartitionGeometry
  apply IsClosed.inter
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i j, |spectralSpinArray x i j| ≤ 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le
      (by unfold spectralSpinArray; fun_prop) continuous_const
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i, spectralSpinArray x i i = 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by unfold spectralSpinArray; fun_prop) continuous_const

lemma spectralReplicaArray_partition {Ω : Type*} {N m : ℕ} (hN : 0 < N)
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) :
    SpectralPartitionGeometry m (spectralReplicaArray U I n p) := by
  have he (i j : ℕ) : spectralSpinArray (spectralReplicaArray U I n p) i j =
      projectedOverlap (specialRotation (U p.1)) Finset.univ (p.2 i).1 (p.2 j).1 := by
    simp only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral]
    exact projectedOverlap_partition _ I hdis hcover _ _
  constructor
  · intro i j
    rw [he]
    exact projectedOverlap_abs_le_one _ _ _ _
  · intro i
    simpa only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_partition_self hN (specialRotation (U p.1)) I hdis hcover (p.2 i).1

lemma spectralArrayLaw_partition {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ} (hN : 0 < N)
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))),
      SpectralPartitionGeometry m x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    SpectralPartitionGeometry m x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralPartitionGeometry m).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_partition hN U I hdis hcover n)

lemma spectralArray_limit_partition {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x :=
  ae_closed_of_weak_limit hL (isClosed_spectralPartitionGeometry m) hG


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite spectral resolvents

The finite-alphabet arguments in Sections 3 and 5 of the manuscript use
the unique solution of `∑ a, ρ a / (b - eig a) = x` above all eigenvalues.
The solution is unique and satisfies deterministic bounds.
The weights may vanish; their sum being one is the only normalization.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The transform of a point mass is the constant equal to its atom. -/
theorem finiteResolvent_constant {ρ : ι → ℝ} (hρsum : ∑ a, ρ a = 1)
    (b c : ℝ) :
    finiteResolvent ρ (fun _ => c) b = 1 / (b - c) := by
  unfold finiteResolvent
  rw [← Finset.sum_div, hρsum]

theorem constant_spectrum_solution {ρ : ι → ℝ}
    (hρsum : ∑ a, ρ a = 1) {x c : ℝ} (hx : 0 < x) :
    finiteResolvent ρ (fun _ => c) (c + 1 / x) = x := by
  rw [finiteResolvent_constant hρsum]
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Differentiation of the finite spectral inverse. The inverse function
theorem is applied to the already constructed inverse; no regularity of
that inverse is assumed.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The Cauchy–Schwarz inequality used for convexity of `x ↦ x R(t x)`. -/
theorem finiteSecondResolvent_sq_le_first_mul_third {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hb : ∀ a, eig a < b) :
    finiteSecondResolvent ρ eig b ^ 2 ≤
      finiteResolvent ρ eig b * finiteThirdResolvent ρ eig b := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _
    exact div_nonneg (hρ a) (sub_pos.mpr (hb a)).le
  · intro a _
    exact div_nonneg (hρ a) (pow_nonneg (sub_pos.mpr (hb a)).le 3)
  · intro a _
    apply le_of_eq
    field_simp [ne_of_gt (sub_pos.mpr (hb a))]

theorem hasStrictDerivAt_finiteInverseDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt
      (fun y => -1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum y))
      (2 * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hm := (hasStrictDerivAt_finiteSecondResolvent ρ eig hs.1).comp x hb
  convert (hasStrictDerivAt_const x (-1 : ℝ)).fun_div hm hpos.ne' using 1
  all_goals first | rfl | (simp only [Function.comp_apply]; field_simp [hpos.ne']; ring) | (field_simp [hpos.ne']; ring)

theorem hasStrictDerivAt_mul_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteEnergyDerivative ρ eig hρ hρsum x) x := by
  have hr := hasStrictDerivAt_finiteR ρ eig hρ hρsum hx
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  convert (hasStrictDerivAt_id x).fun_mul hr using 1
  all_goals first | rfl | (simp only [id_eq, finiteR, ite_eq_left hx, finiteEnergyDerivative]; field_simp [ne_of_gt hx, hpos.ne']; ring)

/-- The second derivative used in manuscript `up:energy`. -/
theorem hasStrictDerivAt_finiteEnergyDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteEnergyDerivative ρ eig hρ hρsum)
      (2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3) x := by
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hbp := hasStrictDerivAt_finiteInverseDerivative ρ eig hρ hρsum hx
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  convert hb.fun_add ((hasStrictDerivAt_id x).fun_mul hbp) using 1
  all_goals first | rfl | (simp only [id_eq]; field_simp [hpos.ne']; ring)

theorem finiteEnergy_secondDerivative_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ 2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
      finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
      finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3 := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hcs := finiteSecondResolvent_sq_le_first_mul_third (fun a => (hρ a).le) hs.1
  rw [hs.2] at hcs
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hcs)) (pow_nonneg hm.le 3)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and positive scaling of the finite spectral transform. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteInverse_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) (c : ℝ) :
    finiteInverse ρ (fun _ => c) hρ hρsum x = c + 1 / x := by
  have hs := finiteInverse_spec ρ (fun _ => c) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs.1
    (fun _ => by linarith [one_div_pos.mpr hx]) hs.2
  exact constant_spectrum_solution hρsum hx

theorem finiteR_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x c : ℝ) :
    finiteR ρ (fun _ => c) hρ hρsum x = c := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx, finiteInverse_constant ρ hρ hρsum hx c]
    ring
  · simp only [finiteR, ite_eq_right hx]
    rw [← Finset.sum_mul, hρsum, one_mul]

theorem finiteResolvent_scale (ρ eig : ι → ℝ) (b t : ℝ) :
    finiteResolvent ρ (fun a => t * eig a) (t * b) =
      (1 / t) * finiteResolvent ρ eig b := by
  unfold finiteResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_sub, div_mul_eq_div_div]
  ring

theorem finiteInverse_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    finiteInverse ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteInverse ρ eig hρ hρsum (t * x) := by
  have hs := finiteInverse_spec ρ eig hρ hρsum (mul_pos ht hx)
  have hs' := finiteInverse_spec ρ (fun a => t * eig a) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs'.1
    (fun a => mul_lt_mul_of_pos_left (hs.1 a) ht) hs'.2
  rw [finiteResolvent_scale ρ eig _ t, hs.2]
  field_simp

theorem finiteR_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    finiteR ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [finiteR, mul_zero, lt_self_iff_false, ite_false, if_false]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [finiteR, ite_eq_left h, ite_eq_left (mul_pos ht h),
      finiteInverse_scale ρ eig hρ hρsum h ht]
    field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the spectral energy primitive, including zero. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuousAt_mul_finiteR_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    ContinuousAt (fun x => x * finiteR ρ eig hρ hρsum x) 0 := by
  let K := ∑ a, |eig a|
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    change |eig a| ≤ ∑ a, |eig a|
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hR : ∀ x, |finiteR ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have ht : Tendsto (fun x : ℝ => |x| * K) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const K
  have ht' : Tendsto (fun x => x * finiteR ρ eig hρ hρsum x) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hR x) (abs_nonneg x)
  simpa only [ContinuousAt, zero_mul] using ht'

theorem convexOn_mul_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {c : ℝ} :
    ConvexOn ℝ (Icc 0 c) (fun x => x * finiteR ρ eig hρ hρsum x) := by
  have hcont : ContinuousOn (fun x => x * finiteR ρ eig hρ hρsum x) (Icc 0 c) := by
    intro x hx
    rcases hx.1.eq_or_lt with h | h
    · subst x
      exact (continuousAt_mul_finiteR_zero ρ eig hρ hρsum).continuousWithinAt
    · exact (hasStrictDerivAt_mul_finiteR ρ eig hρ hρsum h).hasDerivAt.continuousAt.continuousWithinAt
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 c) hcont
    (f' := finiteEnergyDerivative ρ eig hρ hρsum)
    (f'' := fun x =>
      2 * (x * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) -
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 2) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3)
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact (hasStrictDerivAt_mul_finiteR ρ eig hρ hρsum hx').hasDerivAt.hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact (hasStrictDerivAt_finiteEnergyDerivative ρ eig hρ hρsum hx').hasDerivAt.hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := (show x ∈ Ioo 0 c by simpa only [interior_Icc] using hx).1
    exact finiteEnergy_secondDerivative_nonneg ρ eig hρ hρsum hx'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
    all_goals try with_reducible_and_instances rfl
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, sub_zero]
  field_simp [hx'.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint contact minima for the actual cascade-enriched spin prior.
The pressure averages the logarithm over the quenched cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spinPriorContactObjective_eq_perturbation {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) :
    spinPriorContactObjective μ π eig c I b w S V p =
      spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 +
        finiteFieldPath p.2.1 n/2 - (∑ i, w i*finiteFieldPath p.2.1 i)/2+S+V p.1 := by
  unfold spinPriorContactObjective spinPriorContactPressure spinPriorPerturbationObjective spinPriorPerturbationPressureMean
  ring

theorem spinPriorContact_minimum_perturbations {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : TensorContactParameter N m n) (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q) :
    ∀ u v, (∀ j, u j ∈ Icc (1 : ℝ) 2) → (∀ a, v a ∈ Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 ≤
        spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) u v := by
  intro u v hu hv
  let q : TensorContactParameter N m n := (p.1,p.2.1,u,v)
  obtain ⟨ht,ha,hcap,_,_⟩ := tensorContactRegion_bounds hp
  have hq : q ∈ tensorContactRegion N m n H := tensorContactRegion_mem ht ha hcap hu hv
  have h := hmin q hq
  rw [spinPriorContactObjective_eq_perturbation μ π eig c I b w S V p,
    spinPriorContactObjective_eq_perturbation μ π eig c I b w S V q] at h
  dsimp only [q] at h
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayDiagonalLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact array/center subsequences and constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma spectralArray_center_subsequence (m : ℕ) (L : ℕ → ProbabilityMeasure (SpectralArray m))
    (c : ℕ → Fin m → Set.Icc (0 : ℝ) 1) :
    ∃ Q : ProbabilityMeasure (SpectralArray m), ∃ q : Fin m → Set.Icc (0 : ℝ) 1,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (L ∘ φ) atTop (nhds Q) ∧
        Tendsto (c ∘ φ) atTop (nhds q) := by
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq (fun k => (L k, c k))
  refine ⟨p.1, p.2, φ, hφ, ?_, ?_⟩
  · exact (continuous_fst.tendsto p).comp hp
  · exact (continuous_snd.tendsto p).comp hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorTemperatureCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature is a bounded tilt with the actual quenched cascade and
constrained spin prior retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology
namespace InvariantIsing

lemma spinPriorTemperature_reference_fold {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p).tilted
        (fun x => t * rotatedEnergy eig (specialRotation p.1.1) x.1) =
      spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h p := by
  filter_upwards [spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let G := fun x : Spin N × LabeledLeaf n => t * rotatedEnergy eig (specialRotation p.1.1) x.1
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change (gibbsProbability ν H).tilted G = gibbsProbability ν
    (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p)
  rw [he, gibbsProbability_eq_tilted ν H hH,
    gibbsProbability_eq_tilted ν (fun x => H x + G x) hi, tilted_tilted hH G]
  rfl

lemma spinPriorTemperatureCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1)
        (spinPriorNamespacedReference π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p) t =
      spinPriorNamespacedLog π (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h p -
        spinPriorNamespacedLog π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h p := by
  filter_upwards [spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    spinPriorNamespaced_exp_integrable_ae μ π (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let Y := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + t * Y x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hH hi]
  rw [show (fun x => H x + t * Y x) = tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p from he.symm]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorTemperatureDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature derivative for the actual constrained cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem hasDerivAt_spinPriorMeanPressure_temperature {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (t : ℝ) :
    HasDerivAt (fun s => spinPriorMeanPressure (n := n) μ π
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp b r h)
      (spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp b r h (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)) t := by
  let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I v 0) c I degree amp r h
  let Y := fun (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation p.1.1) x.1
  have hY : Measurable (Function.uncurry Y) := measurable_tensorTemperatureObservable eig
  have hB (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) : |Y p x| ≤ K * N / 2 :=
    abs_rotatedEnergy_le eig (specialRotation p.1.1) K hK x.1
  have hd := hasDerivAt_bounded_random_cgf P ν
    (measurable_spinPriorNamespacedReference (n := n) π _ c I degree amp r h) Y hY (K * N / 2) hB t
  let M := fun s => spinPriorMeanPressure (n := n) μ π
    (diagonalPerturbedEigenvalues eig I v s) c I degree amp b r h
  have he (s : ℝ) : M s = M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := by
    have hi (s : ℝ) := spinPriorNamespacedLog_integrable (n := n) μ π
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp b r h hh h0
    rw [integral_congr_ae (spinPriorTemperatureCGF_eq_log_difference hN μ π eig c I v degree amp n b r h hh h0 s),
      integral_sub (hi s) (hi 0)]
    dsimp only [M, spinPriorMeanPressure]
    ring
  have hf : M = fun s => M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := funext he
  have hfold : (∫ p, ∫ x, Y p x ∂(ν p).tilted (fun x => t * Y p x) ∂P) =
      ∫ p, ∫ x, Y p x ∂spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp r h p ∂P := by
    apply integral_congr_ae
    filter_upwards [spinPriorTemperature_reference_fold hN μ π eig c I v degree amp n b r h hh h0 t] with p hp
    rw [hp]
  have hhD := (hd.div_const (N : ℝ)).const_add (M 0)
  rw [hfold] at hhD
  rw [← hf] at hhD
  simpa only [M, Y, P, spinPriorObservableAverage, integral_const_mul, integral_mul_const, div_eq_mul_inv,
    mul_comm] using hhD

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector GG identities in weak limits of actual constrained-prior minimizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem spinPriorPerturbation_minimizers_spectralGG
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) (μ k) (π k) (eig k) (c k) (I k) b (t k) (h k) (u k) (v k)≤
        spinPriorPerturbationObjective (n := n) (μ k) (π k) (eig k) (c k) (I k) b (t k) (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) := by
  obtain ⟨C,hC,hbound⟩ := spinPriorPerturbation_arrayResidual_bound hhaar hgauss
  apply spectralGG_of_weak_nonconstant_monomial_residuals hL
  intro z hz i D hD d hd
  cases z with
  | zero => omega
  | succ q =>
    obtain ⟨j,hj⟩ := enumeratedJointMonomial_surjective m d hd
    let BD := BoundedContinuousFunction.mkOfCompact ⟨D,hD⟩
    have hDb : ∀ x, |D x|≤‖BD‖ := fun x => by
      simpa only [BD,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,Real.norm_eq_abs]
        using BD.norm_coe_le_norm x
    let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
    have he : ∀ᶠ k in atTop, perturbationScale (N k)≤1/32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k)≤1/4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hjN : ∀ᶠ k in atTop, j<N k := hNlim.eventually (eventually_gt_atTop j)
    apply squeeze_zero_norm' _ ((tensorContactGGRate_tendsto j m L ‖BD‖).comp hNlim)
    filter_upwards [he,hs,hjN] with k he hs hjN
    let j' : Fin (N k) := ⟨j,hjN⟩
    have hg := hbound (N k) (hN k) (μ k) (hμinv k) m n (π k) b hb
      (eig k) (c k) K hK (heig k) (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k)
      (h k) (hh k) (h0 k) H (hH k) he hs (hmin k) j' q i D hD ‖BD‖ (norm_nonneg BD) hDb
    simpa only [spinPriorPerturbedArrayLaw,j',hj,Real.norm_eq_abs,Function.comp_def,L] using hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorGeometricLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every prescribed sequence of actual prior minima has a geometric GG subsequence. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinPriorPerturbedArrayLaw_gram {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ∀ᵐ x ∂(spinPriorPerturbedArrayLaw (n := n) μ π b eig c I u v t h : Measure (SpectralArray (m+1))),
      SpectralGram x := by
  unfold spinPriorPerturbedArrayLaw spinPriorArrayLaw
  exact spectralArrayLaw_gram _ _ _ _ _ _ _

lemma spinPriorPerturbedArrayLaw_reindex {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ)
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (spinPriorPerturbedArrayLaw (n := n) μ π b eig c I u v t h : Measure (SpectralArray (m+1))).map
      (permuteSpectralArray e)=spinPriorPerturbedArrayLaw (n := n) μ π b eig c I u v t h := by
  unfold spinPriorPerturbedArrayLaw spinPriorArrayLaw
  exact spectralArrayLaw_map_reindex _ _ _ _ _ _ _ e he


theorem spinPrior_minimizers_geometric_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) (μ k) (π k) (eig k) (c k) (I k) b (t k) (h k) (u k) (v k)≤
        spinPriorPerturbationObjective (n := n) (μ k) (π k) (eig k) (c k) (I k) b (t k) (h k) u' v') :
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ (φ k)) (π (φ k)) b (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) := by
  let L := fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
    (u k) (v k) (t k) (h k)
  let center := fun k => tensorMinimumArrayDiagonal (N k) n (v k)
  obtain ⟨Q,q,φ,hφ,hL,hc⟩ := spectralArray_center_subsequence (m+1) L center
  have hgg := spinPriorPerturbation_minimizers_spectralGG hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => π (φ k)) b hb
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL
  have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  have hd := spinPriorPerturbation_minimizers_constantDiagonal hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => π (φ k)) b hb
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL (fun a => (q a : ℝ)) ((hco.tendsto q).comp hc)
  have hg := spectralArray_limit_gram hL (fun k => spinPriorPerturbedArrayLaw_gram
    (μ (φ k)) (π (φ k)) b (eig (φ k)) (c (φ k)) (I (φ k))
    (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)))
  have hr : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q := by
    intro e he
    exact spectralArray_limit_reindex hL e (fun k => spinPriorPerturbedArrayLaw_reindex
      (μ (φ k)) (π (φ k)) b (eig (φ k)) (c (φ k)) (I (φ k))
      (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)) e he)
  exact ⟨Q,q,φ,hφ,hL,hgg,hd,hg,hr,
    spectralGG_coordinate_nonnegative hgg hg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteSpectralSlope ρ eig hρ hρsum) := by
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_projectedResolventDerivative ρ eig hρ hρsum a)

theorem finiteSpectralSlope_bounds (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteSpectralSlope ρ eig hρ hρsum x ∧ finiteSpectralSlope ρ eig hρ hρsum x ≤ u := by
  have hw := sum_projectedResolventDerivative ρ eig hρ hρsum x
  constructor
  · calc
      l = ∑ a, l * projectedResolventDerivative ρ eig hρ hρsum a x := by
        rw [← Finset.mul_sum, hw, mul_one]
      _ ≤ finiteSpectralSlope ρ eig hρ hρsum x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hl a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
  · calc
      finiteSpectralSlope ρ eig hρ hρsum x ≤
          ∑ a, u * projectedResolventDerivative ρ eig hρ hρsum a x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hu a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
      _ = u := by rw [← Finset.mul_sum, hw, mul_one]

theorem sum_eig_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, eig a * projectedResolvent ρ eig hρ hρsum a x) =
      x * finiteR ρ eig hρ hρsum x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero,
      Finset.sum_const_zero, zero_mul]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hterm : ∀ a, eig a * (ρ a / (B - eig a)) = B * (ρ a / (B - eig a)) - ρ a := by
      intro a
      have hgap : B - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
      field_simp [hgap]
      ring
    simp only [projectedResolvent, finiteR, ite_eq_left h]
    change (∑ a, eig a * (ρ a / (B - eig a))) = x * (B - 1 / x)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hρsum]
    change B * finiteResolvent ρ eig B - 1 = x * (B - 1 / x)
    rw [hs.2]
    field_simp

theorem hasDerivWithinAt_mul_finiteR_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
  have hd : HasDerivWithinAt
      (fun y => ∑ a, eig a * projectedResolvent ρ eig hρ hρsum a y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
    convert! HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx).const_mul (eig a)) using 1
    all_goals try with_reducible_and_instances rfl
  exact hd.congr (fun y hy => (sum_eig_projectedResolvent ρ eig hρ hρsum hy).symm)
    (sum_eig_projectedResolvent ρ eig hρ hρsum hx).symm

theorem finiteSpectralSlope_monotoneOn (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    MonotoneOn (finiteSpectralSlope ρ eig hρ hρsum) (Ici 0) := by
  intro x hx y hy hxy
  let c := y + 1
  have hc : 0 < c := by dsimp [c] <;> linarith [show 0 ≤ y from hy]
  have hdx : HasDerivWithinAt (fun z => z * finiteR ρ eig hρ hρsum z)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Icc 0 c) x :=
    (hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hx).mono (fun _ hz => hz.1)
  have hdy : HasDerivWithinAt (fun z => z * finiteR ρ eig hρ hρsum z)
      (finiteSpectralSlope ρ eig hρ hρsum y) (Icc 0 c) y :=
    (hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hy).mono (fun _ hz => hz.1)
  have hdiff : DifferentiableOn ℝ (fun z => z * finiteR ρ eig hρ hρsum z) (Icc 0 c) := by
    intro z hz
    exact ((hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum hz.1).mono
      (fun _ hu => hu.1)).differentiableWithinAt
  have hmono := (convexOn_mul_finiteR ρ eig hρ hρsum).monotoneOn_derivWithin hdiff
  have hx' : x ∈ Icc 0 c := ⟨hx, by dsimp [c] <;> linarith⟩
  have hy' : y ∈ Icc 0 c := ⟨hy, by dsimp [c] <;> linarith⟩
  have h := hmono hx' hy' hxy
  rw [hdx.derivWithin (uniqueDiffOn_Icc hc x hx'),
    hdy.derivWithin (uniqueDiffOn_Icc hc y hy')] at h
  exact h

theorem finiteInteractionEnergy_mono_deficit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p q : OverlapPath)
    (hD : ∀ r ∈ Icc (0 : ℝ) 1, deficit p r ≤ deficit q r) :
    finiteInteractionEnergy ρ eig hρ hρsum t p ≤ finiteInteractionEnergy ρ eig hρ hρsum t q := by
  have hc : Continuous (fun x => finiteSpectralSlope ρ eig hρ hρsum (t * x)) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).comp (continuous_const.mul continuous_id)
  unfold finiteInteractionEnergy spectralFunctional
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae (integrable_spectral_composition _ hc p) (integrable_spectral_composition _ hc q)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hp := deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩
  have hq := deficit_mem_unit q ⟨hr.1.le, hr.2.le⟩
  exact finiteSpectralSlope_monotoneOn ρ eig hρ hρsum
    (mul_nonneg ht hp.1) (mul_nonneg ht hq.1)
    (mul_le_mul_of_nonneg_left (hD r ⟨hr.1.le, hr.2.le⟩) ht)

/-- The energy comparison in Section 4 follows from the upper-tail order,
including paths with atoms. -/
theorem finiteInteractionEnergy_mono_tail (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p q : OverlapPath)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) :
    finiteInteractionEnergy ρ eig hρ hρsum t p ≤ finiteInteractionEnergy ρ eig hρ hρsum t q := by
  exact finiteInteractionEnergy_mono_deficit ρ eig hρ hρsum ht p q
    (fun r _ => deficit_le_of_pathTail_le p q htail r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperatureFunctional
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteInteractionEnergy_temperature (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (fun t => finiteInteractionEnergy ρ eig hρ hρsum t p) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hbound (t r : ℝ) : |finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r)| ≤ K :=
    abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) _)
  have hc : Continuous (fun t => ∫ r, finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r)
      ∂pathMeasure) := by
    apply continuous_of_dominated (bound := fun _ => K)
    · intro t
      exact ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit p))).aestronglyMeasurable
    · intro t
      exact ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using hbound t r
    · exact integrable_const K
    · exact ae_of_all _ fun r => (continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
        (continuous_id.mul continuous_const)
  exact continuous_const.mul hc

theorem continuous_finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (finiteTemperatureFunctional ρ eig hρ hρsum p) :=
  intervalIntegral.continuous_primitive
    (continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum p).intervalIntegrable 0

theorem hasDerivAt_finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (t : ℝ) :
    HasDerivAt (finiteTemperatureFunctional ρ eig hρ hρsum p)
      (finiteInteractionEnergy ρ eig hρ hρsum t p) t := by
  have hc := continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum p
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactTemperature
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The energy inequality at an actual constrained-prior contact minimum,
including a minimum at the upper temperature endpoint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorContact_minimum_temperature
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q)
    (ht : 0 < p.1) (K : ℝ) (hK : ∀ i, |eig i| ≤ K)
    {V' : ℝ} (hV : HasDerivAt V V' p.1) :
    V' ≤ spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
      c I (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1) b
      (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
      (fun U x => (N : ℝ)⁻¹*rotatedEnergy eig (specialRotation U) x.1) := by
  obtain ⟨hpt,ha,hsum,hu,hv⟩ := tensorContactRegion_bounds hp
  let M := fun t => spinPriorPerturbationPressureMean (n := n) μ π eig c I b t (finiteFieldPath p.2.1)
    p.2.2.1 p.2.2.2
  let E := spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
    c I (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1) b
    (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
    (fun U x => (N : ℝ)⁻¹*rotatedEnergy eig (specialRotation U) x.1)
  have hdM : HasDerivAt M E p.1 := by
    have hd := hasDerivAt_spinPriorMeanPressure_temperature hN
      μ π eig c I p.2.2.2 (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N p.2.2.1) n b (fun j : Fin N => enumeratedTreeDegree m j)
      (finiteFieldPath p.2.1) (monotone_finiteFieldPath ha)
      (finiteFieldPath_nonneg ha 0) K hK p.1
    convert hd.add_const (finiteFieldPath p.2.1 n / 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [M, spinPriorPerturbationPressureMean]

  let F := fun t => -M t+V t
  have hdF : HasDerivAt F (-E+V') (p.1-id 0) := by
    convert! hdM.fun_neg.fun_add hV using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq,sub_zero]
  have hd := hdF.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub p.1)
  simp only [mul_neg_one] at hd
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < p.1 :=
    (show ∀ᶠ a in 𝓝 (0 : ℝ), a < p.1 from Iio_mem_nhds ht).filter_mono nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hd.hasDerivWithinAt (by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a hal ha0
    have hnew : (p.1-a,p.2.1,p.2.2.1,p.2.2.2) ∈ tensorContactRegion N m n H :=
      tensorContactRegion_mem ⟨sub_nonneg.mpr hal.le,(sub_le_self _ ha0.le).trans hpt.2⟩
        ha hsum hu hv
    have hm := hmin _ hnew
    simp only [spinPriorContactObjective,spinPriorContactPressure] at hm
    change F (p.1-0) ≤ F (p.1-a)
    rw [sub_zero]
    dsimp only [F,M,spinPriorPerturbationPressureMean]
    linarith)
  change V' ≤ E
  linarith

theorem spinPriorContact_minimum_energy_gap
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (trial : OverlapPath) (δ S H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t+t*δ) p ≤
      spinPriorContactObjective μ π eig c I b w S
        (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t+t*δ) q)
    (ht : 0 < p.1) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    finiteInteractionEnergy ρ lam hρ hρsum p.1 trial+δ ≤
      spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
        c I (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1) b
        (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun U x => (N : ℝ)⁻¹*rotatedEnergy eig (specialRotation U) x.1) := by
  apply spinPriorContact_minimum_temperature hN μ π b eig c I w S
    (fun t => finiteTemperatureFunctional ρ lam hρ hρsum trial t+t*δ) H p hp hmin ht K hK
  convert! (hasDerivAt_finiteTemperatureFunctional ρ lam hρ hρsum trial p.1).fun_add
    ((hasDerivAt_id p.1).mul_const δ) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperature
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature-scaled group diagonals and the interaction energy. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteR_scale_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    finiteR ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp only [zero_mul, finiteR_constant]
  · exact finiteR_scale ρ eig hρ hρsum hx h

theorem projectedResolventDerivative_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    projectedResolventDerivative ρ (fun b => t * eig b) hρ hρsum a x =
      projectedResolventDerivative ρ eig hρ hρsum a (t * x) := by
  rw [projectedResolventDerivative_eq_regular ρ (fun b => t * eig b) hρ hρsum a hx,
    projectedResolventDerivative_eq_regular ρ eig hρ hρsum a (mul_nonneg ht hx),
    finiteR_scale_nonneg ρ eig hρ hρsum hx ht]
  have he : ∀ b, 1 + x * (t * finiteR ρ eig hρ hρsum (t * x) - t * eig b) =
      1 + (t * x) * (finiteR ρ eig hρ hρsum (t * x) - eig b) := by intro b; ring
  simp_rw [he]

/-- The derivative formula for energy is exactly the weighted group-diagonal
formula for the spectrum at temperature `t`, including zero temperature. -/
theorem finiteInteractionEnergy_eq_groupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    finiteInteractionEnergy ρ eig hρ hρsum t p =
      (1 / 2 : ℝ) * ∑ a, eig a *
        spectralGroupDiagonal ρ (fun b => t * eig b) hρ hρsum p a := by
  unfold finiteInteractionEnergy spectralFunctional spectralGroupDiagonal
  congr 1
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun a _ =>
    (spectralPathDensity_intervalIntegrable ρ (fun b => t * eig b) hρ hρsum p a
      ⟨zero_le_one, le_rfl⟩).const_mul (eig a))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  change (∫ r, finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure) =
    ∫ r, (∑ a, eig a * spectralPathDensity ρ (fun b => t * eig b) hρ hρsum p a r)
      ∂pathMeasure
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  unfold finiteSpectralSlope spectralPathDensity
  apply Finset.sum_congr rfl
  intro a _
  rw [projectedResolventDerivative_scale ρ eig hρ hρsum a (deficit_nonneg p hr.2.le) ht]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayEnergy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interaction before temperature multiplication is an exact bounded
continuous spectral-array observable, so its Gibbs mean passes to weak limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma normalized_rotatedEnergy_eq_blocks {N m : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → eig i = lam a) (σ : Spin N) :
    (N : ℝ)⁻¹ * rotatedEnergy eig U σ =
      (1 / 2 : ℝ) * ∑ a, lam a * projectedOverlap U (I a) σ σ := by
  classical
  have hs : (∑ a, ∑ i ∈ I a, eig i * (U (spinVector σ) i) ^ 2) =
      ∑ i, eig i * (U (spinVector σ) i) ^ 2 := by
    rw [← Finset.sum_biUnion (show Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis), hcover]
  have he : (∑ i, eig i * (U (spinVector σ) i) ^ 2) =
      ∑ a, lam a * ∑ i ∈ I a, (U (spinVector σ) i) ^ 2 := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hlam a i hi])
  simp only [rotatedEnergy, he, projectedOverlap, ← pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring_nf

lemma continuous_spectralArrayInteractionEnergy {m : ℕ} (lam : Fin m → ℝ) :
    Continuous (spectralArrayInteractionEnergy lam) := by
  unfold spectralArrayInteractionEnergy
  fun_prop

lemma spectralArrayInteractionEnergy_weak_limit {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    (lam : Fin m → ℝ) :
    Tendsto (fun k => ∫ x, spectralArrayInteractionEnergy lam x
      ∂(L k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, spectralArrayInteractionEnergy lam x ∂(Q : Measure (SpectralArray (m + 1))))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_spectralArrayInteractionEnergy lam⟩)

lemma spectralArrayInteractionEnergy_eq_finiteEnergy {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath)
    (hdiag : ∀ a, q a.castSucc = spectralGroupDiagonal ρ (fun a => t * lam a) hρ hρsum p a) :
    (∫ x, spectralArrayInteractionEnergy lam x ∂(Q : Measure (SpectralArray (m + 1)))) =
      finiteInteractionEnergy ρ lam hρ hρsum t p := by
  rw [finiteInteractionEnergy_eq_groupDiagonal ρ lam hρ hρsum ht p]
  calc
    _ = ∫ _x : SpectralArray (m + 1), (1 / 2 : ℝ) * ∑ a, lam a * q a.castSucc
        ∂(Q : Measure (SpectralArray (m + 1))) := by
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp only [spectralArrayInteractionEnergy, hx]
    _ = _ := by simp only [integral_const, probReal_univ, one_smul, hdiag]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorEnergyLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original interaction energy in a constrained-prior GG limit is
identified by the actual rotation Ward equations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinPriorPerturbedArrayLaw_partition {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I=Finset.univ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ∀ᵐ x ∂(spinPriorPerturbedArrayLaw (n := n) μ π b eig c I u v t h : Measure (SpectralArray (m+1))),
      SpectralPartitionGeometry m x := by
  unfold spinPriorPerturbedArrayLaw spinPriorArrayLaw
  exact spectralArrayLaw_partition hN _ _ _ _ hdis hcover _ _ _


lemma spinPriorObservableAverage_eq_replica_one {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) :
    spinPriorObservableAverage (n := n) μ π eig c I degree amp b r h D =
      spinPriorReplicaAverage μ π eig c I degree amp n b r h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) => D U (σ 0)) := by
  unfold spinPriorObservableAverage spinPriorReplicaAverage
  apply integral_congr_ae
  exact ae_of_all _ fun p => (referenceReplicaMean_zero_one
    (spinPriorNamespacedReference (n := n) π eig c I degree amp r h p)
    (D p.1.1)).symm

lemma spinPriorArrayLaw_interactionEnergy {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) (b : ℕ → ℝ) [IsProbabilityMeasure π]
    (modelEig energyEig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I=Finset.univ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → energyEig i=lam a)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    (∫ x, spectralArrayInteractionEnergy lam x
      ∂(spinPriorArrayLaw μ π modelEig c I degree amp n b r h : Measure (SpectralArray (m+1)))) =
      spinPriorReplicaAverage μ π modelEig c I degree amp n b r h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) =>
          (N : ℝ)⁻¹*rotatedEnergy energyEig (specialRotation U) (σ 0).1) := by
  apply spinPriorArrayLaw_test μ π modelEig c I degree amp n b r h
    _ (continuous_spectralArrayInteractionEnergy lam) _ (fun i : Fin 1 => i.val) Fin.val_injective
  intro U σ
  simp only [spectralArrayInteractionEnergy, spectralJointEntry_spectral, Fin.val_zero]
  exact (normalized_rotatedEnergy_eq_blocks energyEig (specialRotation U) I hdis hcover lam hlam
    (σ 0).1).symm

theorem spinPriorPerturbedArrayLaw_interactionEnergy_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (b : ℕ → ℝ)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i=lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))))
    (q : Fin (m+1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a)
    (ht₀ : 0 ≤ t₀) :
    ∃ hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x,
    ∃ hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0 ≤ (x (0,1) a : ℝ),
      Tendsto (fun k => spinPriorObservableAverage (n := n) (μ k) (π k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k))
        b (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U x => (N k : ℝ)⁻¹*rotatedEnergy (eig k) (specialRotation U) x.1)) atTop
        (𝓝 (finiteInteractionEnergy ρ lam hρpos hρsum t₀ (spectralSpinQuantilePath Q hP hn))) := by
  have hG := spectralArray_limit_gram hL (fun k => spinPriorPerturbedArrayLaw_gram (n := n)
    (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k))
  have hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q := by
    intro e he
    exact spectralArray_limit_reindex hL e (fun k => spinPriorPerturbedArrayLaw_reindex (n := n)
      (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k) e he)
  have hP := spectralArray_limit_partition hL (fun k => spinPriorPerturbedArrayLaw_partition (n := n)
    (hN k) (μ k) (π k) b (eig k) (c k) (I k) (hdis k) (hcover k) (u k) (v k) (t k) (h k))
  have hn := spectralGG_coordinate_nonnegative hgg hG q hq hd
  obtain ⟨hoff,hdiag⟩ := spinPriorPerturbedArrayLaw_ward_limits N hN hNlim m n μ hμinv π b
    eig c I hdis hcover lam hlam u hu v hv t ht h hh h0 Q hL ρ hρ
  have hid := spectralCanonical_identification hgg hG q hq hd hE hP hn
    ρ (fun a => t₀*lam a) hρpos hρsum hoff hdiag
  refine ⟨hP,hn,?_⟩
  have he k : (∫ x, spectralArrayInteractionEnergy lam x
      ∂(spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k) :
        Measure (SpectralArray (m+1)))) =
      spinPriorObservableAverage (n := n) (μ k) (π k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k))
        b (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U x => (N k : ℝ)⁻¹*rotatedEnergy (eig k) (specialRotation U) x.1) := by
    rw [spinPriorObservableAverage_eq_replica_one]
    exact spinPriorArrayLaw_interactionEnergy (n := n) (μ k) (π k) b _ (eig k) (c k) (I k)
      (hdis k) (hcover k) lam (hlam k) _ _ _ (h k)
  have hlim := spectralArrayInteractionEnergy_weak_limit hL lam
  simp_rw [he] at hlim
  rw [spectralArrayInteractionEnergy_eq_finiteEnergy Q q hd ρ lam hρpos hρsum ht₀
    (spectralSpinQuantilePath Q hP hn) hid.1] at hlim
  exact hlim

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralContactContradiction
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict temperature tilt contradicts the energy order obtained from
contact tails. The energy sequence is the actual interaction observable
when this lemma is applied to contact minima. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma spectralContact_contradiction {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p q : OverlapPath) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (tk energy : ℕ → ℝ) (htk : Tendsto tk atTop (𝓝 t))
    (henergy : Tendsto energy atTop (𝓝 (finiteInteractionEnergy ρ eig hρ hρsum t p)))
    (hcontact : ∀ᶠ k in atTop, finiteInteractionEnergy ρ eig hρ hρsum (tk k) q + δ ≤ energy k)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) : False := by
  have hq := ((continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum q).tendsto t).comp htk
  have hle := le_of_tendsto_of_tendsto (hq.add_const δ) henergy hcontact
  have hord := finiteInteractionEnergy_mono_tail ρ eig hρ hρsum ht p q htail
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactContradiction
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At an actual positive-temperature contact minimum, the field directions
and temperature direction contradict the identified limiting energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_limit_contradiction
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (δ S H : ℝ) (hδ : 0 < δ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) (p k) ≤
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (hpos : ∀ k, 0 < (p k).1)
    (t : ℝ) (ht : Tendsto (fun k => (p k).1) atTop (𝓝 t))
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 (finiteFieldPath (p k).2.1))
      atTop (𝓝 Q))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) : False := by
  have ht0 : 0 ≤ t := ge_of_tendsto' ht (fun k => (hpos k).le)
  have hh k := monotone_finiteFieldPath (tensorContactRegion_bounds (hp k)).2.1
  have h0 k := finiteFieldPath_nonneg (tensorContactRegion_bounds (hp k)).2.1 0
  have hu k j : |(p k).2.2.1 j| ≤ 2 := by
    have h := (tensorContactRegion_bounds (hp k)).2.2.2.1 j
    rw [abs_of_nonneg (by linarith [h.1] : 0 ≤ (p k).2.2.1 j)]
    exact h.2
  have hv k a : |(p k).2.2.2 a| ≤ 2 := by
    have h := (tensorContactRegion_bounds (hp k)).2.2.2.2 a
    rw [abs_of_nonneg (by linarith [h.1] : 0 ≤ (p k).2.2.2 a)]
    exact h.2
  obtain ⟨hP, hn, henergy⟩ := spinPriorPerturbedArrayLaw_interactionEnergy_limit N hN hNlim m n
    μ hμinv π (chainExponent cut) eig c I hdis hcover lam hlam
    (fun k => (p k).2.2.1) hu (fun k => (p k).2.2.2) hv
    (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1)
    hh h0 Q hL ρ hρpos hρsum hρ hgg q hq hd ht0
  have htail := spinPriorContact_limit_tail_order N hN m n μ π eig c I hdis hcover
    cut hc hfirst hlast trial values hvalues S
    (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ)
    H p hp hmin hcap Q hL hgg q hq hd hP hn
  apply spectralContact_contradiction ρ lam hρpos hρsum
    (spectralSpinQuantilePath Q hP hn) trial hδ ht0 (fun k => (p k).1) _ ht henergy _ htail
  apply Filter.Eventually.of_forall
  intro k
  have he := spinPriorContact_minimum_energy_gap (hN k) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
    (fun i => (cut i.succ - cut i.castSucc) * values i)
    ρ lam hρpos hρsum trial δ S H (p k) (hp k) (hmin k) (hpos k) K (heig k)
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric GG limits at the same joint constrained-prior contact minima.
The perturbation parameters are not reselected after minimizing temperature
and field, so subsequent contact inequalities refer to this same sequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorContact_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (w : Fin (n+1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) b w S V (p k) ≤
        spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) b w S V q) :
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ (φ k)) (π (φ k)) b
        (eig (φ k)) (c (φ k)) (I (φ k))
        (p (φ k)).2.2.1 (p (φ k)).2.2.2 (p (φ k)).1 (finiteFieldPath (p (φ k)).2.1))
        atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) := by
  have hbounds k := tensorContactRegion_bounds (hp k)
  have ht k : |(p k).1| ≤ 1 := by
    rw [abs_of_nonneg (hbounds k).1.1]
    exact (hbounds k).1.2
  have hh k : Monotone (finiteFieldPath (p k).2.1) := monotone_finiteFieldPath (hbounds k).2.1
  have h0 k : 0 ≤ finiteFieldPath (p k).2.1 0 := finiteFieldPath_nonneg (hbounds k).2.1 0
  have hcap k : finiteFieldPath (p k).2.1 n ≤ H := by
    rw [finiteFieldPath_last]
    exact (hbounds k).2.2.1
  exact spinPrior_minimizers_geometric_GG_limit hhaar hgauss N hN hNlim m n μ hμinv π b hb
    eig c K hK heig I (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1) hh h0 H hcap
    (fun k => (p k).2.2.1) (fun k => (hbounds k).2.2.2.1)
    (fun k => (p k).2.2.2) (fun k => (hbounds k).2.2.2.2)
    (fun k => spinPriorContact_minimum_perturbations (μ k) (π k) (eig k) (c k) (I k) b
      w S V H (p k) (hp k) (hmin k))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactNoSequence
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and the minimizing GG subsequence discharge the limiting
array assumptions in the contact contradiction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_no_positive_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (δ S H : ℝ) (hδ : 0 < δ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) (p k) ≤
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (hpos : ∀ k, 0 < (p k).1) : False := by
  obtain ⟨Q, q, φ, hφ, hL, hgg, hd, _⟩ := spinPriorContact_minimizers_have_GG_limit hhaar hgauss
    N hN hNlim m n μ hμinv π (chainExponent cut) (chainExponent_admissible hc hfirst hlast)
    eig c K hK heig I (fun i => (cut i.succ - cut i.castSucc) * values i) S
    (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) H p hp hmin
  obtain ⟨t, _, ψ, hψ, hT⟩ := isCompact_Icc.tendsto_subseq
    (fun k => (tensorContactRegion_bounds (hp (φ k))).1)
  let τ : ℕ → ℕ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  apply spinPriorContact_limit_contradiction (fun k => N (τ k)) (fun k => by have := hN (τ k); omega)
    (hNlim.comp hτ.tendsto_atTop) m n (fun k => μ (τ k)) (fun k => hμinv (τ k)) (fun k => π (τ k))
    (fun k => eig (τ k)) (fun k => c (τ k)) K (fun k => heig (τ k))
    (fun k => I (τ k)) (fun k => hdis (τ k)) (fun k => hcover (τ k))
    lam (fun k => hlam (τ k)) ρ hρpos hρsum (hρ.comp hτ.tendsto_atTop)
    cut hc hfirst hlast trial values hvalues δ S H hδ
    (fun k => p (τ k)) (fun k => hp (τ k)) (fun k => hmin (τ k))
    (fun k => hcap (τ k)) (fun k => hpos (τ k)) t hT Q
    (hL.comp hψ.tendsto_atTop) hgg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorRestrictedBoundary
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained contact boundary retains the cube-mass constant
until it cancels from the physical objective. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorRestrictedContact_zero_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (cut : Fin (n+2) → ℝ) (hc : StrictMono cut) (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1)
    (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (trial : OverlapPath) (values : Fin (n+1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s=values i)
    (S : ℝ) (hS : constrainedBlockValue C (contactFieldStep cut hc hfirst hlast a ha)+
      fieldPairing trial (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S)
    (V : ℝ → ℝ) (hV : V 0=0) :
    -(2*m*perturbationScale N+8*perturbationScale N^2) ≤
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I
        (chainExponent cut) (fun i => (cut i.succ-cut i.castSucc)*values i)
        (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V (0,a,u,v) := by
  have hp := spinPriorRestrictedContact_zero_cost hhaar hgauss hN μ hμ C hC eig I
    cut hc hfirst hlast a ha u hu v hv
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast a ha values hvalues
  rw [hpair] at hS
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _)
  have hW : 0 ≤ ∑ j : Fin m, (v j-3/2)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hh := (abs_le.mp hp).2
  simp only [spinPriorContactObjective, hV]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorRestrictedCap
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed field cap for constrained contact objectives, uniform in the
finite constraint and with its cube mass canceled. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

/-- A coercive lower bound in the total nonnegative field increment. -/
theorem spinPriorRestrictedContactObjective_cap_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (C : Finset (Spin N)) (hC : C.Nonempty)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 ≤ d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n)
    (ht : p.1 ∈ Icc (0 : ℝ) 1) (ha : ∀ i, 0 ≤ p.2.1 i)
    (hu : ∀ j, |p.2.2.1 j| ≤ 2) (hv : ∀ j, |p.2.2.2 j| ≤ 2) :
    (d * (1 - cut (Fin.last n).castSucc) / 2) * (∑ i, p.2.1 i) -
        gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) -
        (∑ i : Fin n, Real.log 2 / cut i.succ.castSucc) - K / 2 -
        (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) + S + V p.1 ≤
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V p := by
  let step := contactFieldStep cut hc hfirst hlast p.2.1 ha
  have hp := spinPriorRestrictedContactPressure_field_le hhaar hgauss hN μ hμ C hC eig I K heig
    cut hc hfirst hlast p ht ha hu hv
  have hf := fieldValue_add_pairing_cap trial hd htrial step
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast p.2.1 ha values hvalues
  change fieldPairing trial step = _ at hpair
  rw [hpair, fieldPartitionConstant_contactFieldStep] at hf
  change fieldValue step 0 + (∑ i, ((cut i.succ - cut i.castSucc) * values i) *
      finiteFieldPath p.2.1 i) / 2 ≤
    -(d * (1 - cut (Fin.last n).castSucc) / 2) * finiteFieldPath p.2.1 n +
      gaussianAbsoluteMean * Real.sqrt (finiteFieldPath p.2.1 n) +
      (∑ i : Fin n, Real.log 2 / cut i.succ.castSucc) at hf
  rw [finiteFieldPath_last] at hf
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  have hW : 0 ≤ ∑ j : Fin m, (p.2.2.2 j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  change spinPriorContactPressure μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut) p+(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2) ≤
    fieldValue step 0 + K / 2 + (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) at hp
  unfold spinPriorContactObjective
  linarith

/-- One fixed cap works for every dimension and every allowed perturbation
parameter.  Thus a negative contact sublevel cannot touch its field face. -/
theorem exists_spinPriorRestrictedContactObjective_cap
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m n : ℕ) (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (K S L : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ) (_hN : 3 ≤ N)
      (μ : Measure (SpecialOrthogonal N)) (_hμprob : IsProbabilityMeasure μ)
      (_hμ : μ.IsMulLeftInvariant) (C : Finset (Spin N)) (hC : C.Nonempty) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
      (_heig : ∀ i, |eig i| ≤ K) (V : ℝ → ℝ)
      (_hV : ∀ t ∈ Icc (0 : ℝ) 1, L ≤ V t) (p : TensorContactParameter N m n),
      p.1 ∈ Icc (0 : ℝ) 1 → (∀ i, 0 ≤ p.2.1 i) →
      (∀ j, |p.2.2.1 j| ≤ 2) → (∀ j, |p.2.2.2 j| ≤ 2) →
      spinPriorContactObjective μ (restrictedSpinPrior C hC : Measure (Spin N)) eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N : ℝ)⁻¹*(Real.log C.card-N*Real.log 2)) V p < 0 →
      (∑ i, p.2.1 i) < H := by
  let e := d * (1 - cut (Fin.last n).castSucc) / 2
  let Cq := ∑ i : Fin n, Real.log 2 / cut i.succ.castSucc
  have he : 0 < e := by
    have hcut : cut (Fin.last n).castSucc < 1 := by
      simpa only [hlast] using hc (Fin.castSucc_lt_last (Fin.last n))
    dsimp only [e]
    positivity
  obtain ⟨H, hH, hbound⟩ := exists_linear_sqrt_cap he gaussianAbsoluteMean
    (Cq + K / 2 + (2 * m + 8) - S - L) 0
  refine ⟨H, hH, ?_⟩
  intro N hN μ hμprob hμ C hC eig I heig V hV p ht ha hu hv hneg
  have : IsProbabilityMeasure μ := hμprob
  by_contra hn
  have hx : H ≤ ∑ i, p.2.1 i := le_of_not_gt hn
  have hs := hbound (∑ i, p.2.1 i) hx
  have hcap := spinPriorRestrictedContactObjective_cap_bound hhaar hgauss hN μ hμ C hC eig I K heig
    cut hc hfirst hlast trial values hvalues d hd.le htrial S V p ht ha hu hv
  have herr : 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 ≤ 2 * m + 8 := by
    have h1 := InvariantIsing.perturbationScale_le_one (by omega : 0 < N)
    have h2 := perturbationScale_sq_le_one (by omega : 0 < N)
    have h1' := mul_le_mul_of_nonneg_left h1
      (show 0 ≤ (2 : ℝ) * m from mul_nonneg (by norm_num) (Nat.cast_nonneg m))
    have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (8 : ℝ) by norm_num)
    linarith
  have hv' := hV p.1 ht
  change -e * (∑ i, p.2.1 i) + gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) +
    (Cq + K / 2 + (2 * m + 8) - S - L) ≤ 0 at hs
  change e * (∑ i, p.2.1 i) - gaussianAbsoluteMean * Real.sqrt (∑ i, p.2.1 i) -
    Cq - K / 2 - _ + S + V p.1 ≤ _ at hcap
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorRestrictedEntropyLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Uniform asymptotic nonnegativity of the actual contact problem for a
fixed trial partition. The hypotheses are the Haar and root/cascade concentration estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorRestrictedContact_entropy_limit_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (C : (k : ℕ) → Finset (Spin (N k))) (hC : ∀ k, (C k).Nonempty)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (δ S : ℝ) (hδ : 0 < δ) (hS : ∀ H ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      ∀ (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i), (∑ i, a i) ≤ H →
        constrainedBlockValue (C k) (contactFieldStep cut hc hfirst hlast a ha)+
          fieldPairing trial (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S+ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ p ∈ tensorContactRegion (N k) m n H,
        -η ≤ spinPriorContactObjective (μ k) (restrictedSpinPrior (C k) (hC k) : Measure (Spin (N k))) (eig k) (fun _ => 0) (I k) (chainExponent cut)
          (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N k : ℝ)⁻¹*(Real.log (C k).card-N k*Real.log 2))
          (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) p := by
  classical
  let V : ℝ → ℝ := fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ
  have hV : Continuous V := (continuous_finiteTemperatureFunctional ρ lam hρpos hρsum trial).add
    (continuous_id.mul continuous_const)
  have hV0 : V 0 = 0 := by simp [V, finiteTemperatureFunctional]
  obtain ⟨tmin, _, hlow⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hV.continuousOn
  obtain ⟨H, hH, hcap⟩ := exists_spinPriorRestrictedContactObjective_cap hhaar hgauss m n cut hc hfirst hlast
    trial values hvalues d hd htrial K S (V tmin)
  refine ⟨H, hH, ?_⟩
  intro η hη
  have hcost : ∀ᶠ k in atTop,
      2 * m * perturbationScale (N k) + 8 * perturbationScale (N k) ^ 2 < η/3 :=
    ((fullPerturbationCost_tendsto m).comp hNlim).eventually (gt_mem_nhds (show 0<η/3 by positivity))
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ p ∈ tensorContactRegion (N k) m n H,
      spinPriorContactObjective (μ k) (restrictedSpinPrior (C k) (hC k) : Measure (Spin (N k))) (eig k) (fun _ => 0) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N k : ℝ)⁻¹*(Real.log (C k).card-N k*Real.log 2)) V p < -η := by
    simpa only [V, Filter.not_eventually, not_forall, _root_.not_imp, not_le, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop (hbad'.and_eventually (hcost.and (hS H (η/3) (by positivity))))
  have hmins (k : ℕ) := spinPriorContactObjective_exists_minimum hhaar hgauss (hN (φ k))
    (μ (φ k)) (hμinv (φ k)) (restrictedSpinPrior (C (φ k)) (hC (φ k)) : Measure (Spin (N (φ k)))) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
    K (heig (φ k))
    (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N (φ k) : ℝ)⁻¹*(Real.log (C (φ k)).card-N (φ k)*Real.log 2)) V hV H hH.le
  choose p hp hmin using hmins
  have hneg (k : ℕ) :
      spinPriorContactObjective (μ (φ k)) (restrictedSpinPrior (C (φ k)) (hC (φ k)) : Measure (Spin (N (φ k)))) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) (S-(N (φ k) : ℝ)⁻¹*(Real.log (C (φ k)).card-N (φ k)*Real.log 2)) V (p k) < -η := by
    obtain ⟨q, hq, hqneg⟩ := (hφbad k).1
    exact (hmin k q hq).trans_lt hqneg
  have hcap' (k : ℕ) : (∑ i, (p k).2.1 i) < H := by
    have hb := tensorContactRegion_bounds (hp k)
    apply hcap (N (φ k)) (hN (φ k)) (μ (φ k)) inferInstance (hμinv (φ k)) (C (φ k)) (hC (φ k))
      (eig (φ k)) (I (φ k)) (heig (φ k)) V (fun t ht => hlow ht) (p k) hb.1 hb.2.1
    · intro j
      rw [abs_of_nonneg (by have := (hb.2.2.2.1 j).1; linarith)]
      exact (hb.2.2.2.1 j).2
    · intro j
      rw [abs_of_nonneg (by have := (hb.2.2.2.2 j).1; linarith)]
      exact (hb.2.2.2.2 j).2
    · linarith [hneg k]
  have hpos (k : ℕ) : 0 < (p k).1 := by
    have hb := tensorContactRegion_bounds (hp k)
    by_contra hzero
    have heq : (p k).1 = 0 := le_antisymm (not_lt.mp hzero) hb.1.1
    have hu j : |(p k).2.2.1 j| ≤ 2 := by
      rw [abs_of_nonneg (by have := (hb.2.2.2.1 j).1; linarith)]
      exact (hb.2.2.2.1 j).2
    have hv j : |(p k).2.2.2 j| ≤ 2 := by
      rw [abs_of_nonneg (by have := (hb.2.2.2.2 j).1; linarith)]
      exact (hb.2.2.2.2 j).2
    have hzeroBound := spinPriorRestrictedContact_zero_bound hhaar hgauss (hN (φ k))
      (μ (φ k)) (hμinv (φ k)) (C (φ k)) (hC (φ k)) (eig (φ k)) (I (φ k)) cut hc hfirst hlast
      (p k).2.1 hb.2.1 (p k).2.2.1 hu (p k).2.2.2 hv trial values hvalues (S+η/3) ((hφbad k).2.2 (p k).2.1 hb.2.1 hb.2.2.1) V hV0
    have hpEq : p k = (0, (p k).2.1, (p k).2.2.1, (p k).2.2.2) := by
      exact Prod.ext heq (Prod.ext rfl (Prod.ext rfl rfl))
    rw [← hpEq] at hzeroBound
    have hshift : spinPriorContactObjective (μ (φ k))
        (restrictedSpinPrior (C (φ k)) (hC (φ k)) : Measure (Spin (N (φ k))))
        (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ-cut i.castSucc)*values i)
        (S+η/3-(N (φ k) : ℝ)⁻¹*(Real.log (C (φ k)).card-N (φ k)*Real.log 2)) V (p k) =
        spinPriorContactObjective (μ (φ k))
          (restrictedSpinPrior (C (φ k)) (hC (φ k)) : Measure (Spin (N (φ k))))
          (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
          (fun i => (cut i.succ-cut i.castSucc)*values i)
          (S-(N (φ k) : ℝ)⁻¹*(Real.log (C (φ k)).card-N (φ k)*Real.log 2)) V (p k)+η/3 := by
      unfold spinPriorContactObjective
      ring
    rw [hshift] at hzeroBound
    have := (hφbad k).2.1
    linarith [hneg k]
  have hmin0 (k : ℕ) (z : TensorContactParameter (N (φ k)) m n)
      (hz : z ∈ tensorContactRegion (N (φ k)) m n H) :
      spinPriorContactObjective (μ (φ k)) (restrictedSpinPrior (C (φ k)) (hC (φ k)))
        (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ-cut i.castSucc)*values i) 0 V (p k) ≤
      spinPriorContactObjective (μ (φ k)) (restrictedSpinPrior (C (φ k)) (hC (φ k)))
        (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ-cut i.castSucc)*values i) 0 V z := by
    have hm := hmin k z hz
    simp only [spinPriorContactObjective] at hm ⊢
    linarith
  exact spinPriorContact_no_positive_minimizing_sequence hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k))
    (fun k => (restrictedSpinPrior (C (φ k)) (hC (φ k)) : Measure (Spin (N (φ k))))) (fun k => eig (φ k)) (fun _ _ => 0)
    K hK (fun k => heig (φ k)) (fun k => I (φ k)) (fun k => hdis (φ k))
    (fun k => hcover (φ k)) lam (fun k => hlam (φ k)) ρ hρpos hρsum
    (hρ.comp hφ.tendsto_atTop) cut hc hfirst hlast trial values hvalues δ 0 H hδ p hp hmin0 hcap' hpos

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit_oai := @OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit_oai
