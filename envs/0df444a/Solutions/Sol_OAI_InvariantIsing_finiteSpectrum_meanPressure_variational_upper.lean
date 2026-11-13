-- Prove2me | solution 1 for OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:55:03.803199+00:00
-- url     : https://prove2.me/submissions/88b15674-c2fd-481c-a1ed-b91aa00ad617

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_tensorContactObjective_exists_minimum
import Theorems.Thm_OAI_InvariantIsing_tensorContact_no_positive_minimizing_sequence
import Theorems.Thm_OAI_InvariantIsing_tensorNamespacedMeanPressure_perturbation_cost

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

/-- Equation (4.10): uniform deficit error is bounded by the L¹ path error. -/
lemma abs_deficit_sub_path_le (p q : OverlapPath) (r : ℝ) :
    |deficit p r - deficit q r| ≤ ∫ s, |p s - q s| ∂pathMeasure := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (q.integrable_complement_max r)]
  calc
    _ ≤ ∫ s, |(1 - max (p s) r) - (1 - max (q s) r)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, |p s - q s| ∂pathMeasure := by
      apply integral_mono
        ((p.integrable_complement_max r).sub (q.integrable_complement_max r)).abs
        (p.integrable.sub q.integrable).abs
      intro s
      have he : (1 - max (p s) r) - (1 - max (q s) r) =
          -(max (p s) r - max (q s) r) := by ring
      change |(1 - max (p s) r) - (1 - max (q s) r)| ≤ |p s - q s|
      rw [he, abs_neg]
      exact abs_max_sub_max_le_abs (p s) (q s) r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
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

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MarkedPartitionNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

end IsingPerceptron

namespace IsingPerceptron

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

open scoped ProbabilityTheory

end IsingPerceptron

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
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

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







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

end IsingPerceptron

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
namespace IsingPerceptron


lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

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
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ContactFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Faces. -/

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma lowerGrid_le {p : ℝ → ℝ} (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1)
    (n : ℕ) {u : ℝ} (hu : 0≤u) : lowerGrid p n u ≤ p u := by
  have hf : (⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ)≤u :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hu))
  have hv := hp hf
  have hb' := (hb ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ))).1
  dsimp only [lowerGrid]
  nlinarith [show (0:ℝ)≤1/(n+1:ℕ) by positivity]

lemma floor_on_uniformCell (n : ℕ) (i : Fin (n+1)) {u : ℝ}
    (hu : uniformCut n i.castSucc<u ∧ u<uniformCut n i.succ) : ⌊(n+1:ℕ)*u⌋₊=i.val := by
  have hleft : (i.val:ℝ)<(n+1:ℕ)*u := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mp hu.1
    simpa [uniformCut,mul_comm] using this
  apply (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i.val) hleft.le)).mpr
  constructor
  · exact hleft.le
  · have := (lt_div_iff₀ (by positivity)).mp hu.2
    simpa [uniformCut,mul_comm] using this

lemma lowerGrid_ae_tendsto {p : ℝ → ℝ} (hp : Monotone p) :
    ∀ᵐ u ∂pathMeasure, Tendsto (fun n => lowerGrid p n u) atTop (𝓝 (p u)) := by
  have hc : ∀ᵐ u ∂pathMeasure, ContinuousAt p u := monotone_ae_continuous_unit hp
  filter_upwards [hc,ae_restrict_mem measurableSet_Ioo] with u hc hu
  have hf := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl := hc.tendsto.comp (uniformCell_left_tendsto ⟨hu.1.le,hu.2⟩)
  simpa only [lowerGrid,uniformCellIndex_eq_floor _ ⟨hu.1.le,hu.2⟩,
    Nat.cast_add,Nat.cast_one,sub_zero,one_mul,Function.comp_apply] using hf.mul hl

lemma lowerGrid_integral_tendsto {p : ℝ → ℝ} (hp : Monotone p)
    (hb : ∀ u, p u∈Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ u, lowerGrid p n u ∂pathMeasure) atTop (𝓝 (∫ u, p u ∂pathMeasure)) := by
  let : IsFiniteMeasure pathMeasure := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)))
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (lowerGrid_monotone hp n).measurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (lowerGrid_mem hb n u).1]; exact (lowerGrid_mem hb n u).2)
  · exact lowerGrid_ae_tendsto hp

end IsingPerceptron

 

 

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
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
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

lemma heightSequence_mono (h : FieldStep) : Monotone (heightSequence h) := by
  intro i j hij
  apply h.ordered_height
  exact min_le_min_right h.depth hij

lemma heightSequence_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ heightSequence h i :=
  h.nonneg _

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

/-- Equality with the scalar recursion, including its root Gaussian average
and diagonal covariance subtraction. -/
lemma fieldValue_eq_magneticFieldValue (h : FieldStep) :
    fieldValue h 0 = IsingPerceptron.magneticFieldValue h.depth
      (IsingPerceptron.chainExponent h.cut) (heightSequence h) := by
  let w := heightSequence h
  have hw : Monotone w := heightSequence_mono h
  have hw0 : 0 ≤ w 0 := heightSequence_nonneg h 0
  have htail : List.ofFn (fun i : Fin h.depth =>
      ((fieldIncrement h i.succ).2, (fieldIncrement h i.succ).1)) =
      List.ofFn (fun i : Fin h.depth =>
        ((IsingPerceptron.pathAmplitude w (i + 1)) ^ 2,
          IsingPerceptron.chainExponent h.cut i)) := by
    apply congrArg List.ofFn
    funext i
    rw [IsingPerceptron.pathAmplitude_sq hw hw0]
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, IsingPerceptron.pathIncrement,
      IsingPerceptron.chainExponent_apply h.cut i.isLt]
    congr 1
    change h.height i.succ - h.height ⟨i.val, by omega⟩ =
      heightSequence h (i.val + 1) - heightSequence h i.val
    rw [heightSequence_eq h _ (by omega), heightSequence_eq h _ (by omega)]
    rfl
  have hfold : (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) =
      IsingPerceptron.magneticRecursion h.depth
        (fun i => IsingPerceptron.pathAmplitude w (i + 1))
        (IsingPerceptron.chainExponent h.cut) := by
    simp_rw [gaussianOperator_eq_transform]
    rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
      (g := fun sd f => IsingPerceptron.gaussianTransform sd.1 sd.2 f)]
    rw [List.map_ofFn]
    simp only [Function.comp_def]
    rw [htail]
    exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
      (fun i => IsingPerceptron.pathAmplitude w (i + 1))
      (IsingPerceptron.chainExponent h.cut)).symm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    dsimp only [fieldIncrement]
    simp [h.first]
  have hzero : w 0 = h.height 0 := heightSequence_eq h 0 (Nat.zero_le _)
  have hlast : w h.depth = h.height (Fin.last h.depth) := heightSequence_eq h _ le_rfl
  have hamp : IsingPerceptron.pathAmplitude w 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, hzero]
  rw [fieldValue, List.ofFn_succ, List.foldr_cons, hfold, hroot]
  simp only [gaussianOperator, ite_true, if_true, zero_add, IsingPerceptron.magneticFieldValue]
  dsimp only [w] at hamp hlast ⊢
  rw [hamp, hlast]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-depth Gaussian marking input used in the one-site functional.
The logarithmic terminal is unbounded; the linear-growth cascade theorem
supplies its integrability. This is the Gaussian specialization of
Bolthausen--Sznitman (1998), Appendix Proposition A.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma gaussianOperator_eq_gaussian_logMean {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0)
    {F : ℝ → ℝ} (hF : Measurable F) (x : ℝ) :
    gaussianOperator a v F x =
      IsingPerceptron.logMean a (gaussianReal 0 v) (fun g => F (x + g)) := by
  simp only [gaussianOperator, ha, ite_false, if_false, IsingPerceptron.logMean]
  have hm : Measurable (fun g : ℝ => Real.exp (a * F (x + g))) :=
    (((hF.comp (measurable_const.add measurable_id)).const_mul a).exp)
  rw [integral_gaussianReal_zero_eq_standard v hm]
  ring

lemma gaussianCascadeRecursion_eq_fold (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, b i ≠ 0) {F : ℝ → ℝ} (hF : Measurable F) :
    IsingPerceptron.cascadeRecursion n b
      (fun i => ⟨gaussianReal 0 (v i), inferInstance⟩)
      (fun _ p => p.1 + p.2) F =
      (List.ofFn (fun i : Fin n => (b i, (v i : ℝ)))).foldr
        (fun av U => gaussianOperator av.1 av.2 U) F := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have ht := IsingPerceptron.measurable_cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ => measurable_fst.add measurable_snd) hF
    have he := ih (fun i => b (i + 1)) (fun i => v (i + 1))
      (fun i hi => hb (i + 1) (by omega))
    change Measurable (IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ p => p.1 + p.2) F) at ht
    rw [he] at ht
    rw [List.ofFn_succ, List.foldr_cons]
    funext x
    change IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
      (fun g => IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
        (fun i => ⟨gaussianReal 0 (v (i + 1)), inferInstance⟩)
        (fun _ p => p.1 + p.2) F (x + g)) = _
    rw [he]
    exact (gaussianOperator_eq_gaussian_logMean (hb 0 (by omega)) (v 0) ht x).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma logPartition_eq {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    logPartition H = Real.log (∑ x, Real.exp (H x)) - Real.log (Fintype.card X) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, Real.log_mul (inv_ne_zero hc) (sum_exp_pos H).ne', Real.log_inv]
  ring

lemma logPartition_add_const {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (c : ℝ) :
    logPartition (fun x => H x + c) = logPartition H + c := by
  rw [logPartition_eq, logPartition_eq]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul (sum_exp_pos H).ne' (Real.exp_ne_zero c),
    Real.log_exp]
  ring

lemma logPartition_le_add {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, H x ≤ K x + c) :
    logPartition H ≤ logPartition K + c := by
  have hs : (∑ x, Real.exp (H x)) ≤ ∑ x, Real.exp (K x + c) :=
    Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (h x)
  have hl : logPartition H ≤ logPartition (fun x => K x + c) := by
    rw [logPartition_eq, logPartition_eq]
    exact sub_le_sub_right (Real.log_le_log (sum_exp_pos H) hs) _
  simpa only [logPartition_add_const] using hl

lemma abs_logPartition_sub_le {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, |H x - K x| ≤ c) :
    |logPartition H - logPartition K| ≤ c := by
  have h₁ := logPartition_le_add H K c fun x => by
    have := (abs_le.mp (h x)).2
    linarith
  have h₂ := logPartition_le_add K H c fun x => by
    have := (abs_le.mp (h x)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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

@[simp] lemma logPartition_zero {X : Type*} [Fintype X] [Nonempty X] :
    logPartition (fun _ : X => (0 : ℝ)) = 0 := by
  rw [logPartition_eq]
  simp

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : Measurable (rotatedFieldTerminal eig U c) := by
  unfold rotatedFieldTerminal logPartition fieldEnergy
  fun_prop

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma finiteLogIntegral_uniformSpinPrior {N : ℕ} (H : Spin N → ℝ) :
    IsingPerceptron.finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) H = logPartition H := by
  unfold IsingPerceptron.finiteLogIntegral logPartition
  congr 1
  change (∫ σ, Real.exp (H σ) ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCascade
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite one-site functional as a Gaussian cascade expectation. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldCascadeFold_eq_magneticRecursion (h : FieldStep) :
    (List.ofFn (fun i : Fin h.depth =>
      (IsingPerceptron.chainExponent h.cut i, (fieldCascadeVariance h i : ℝ)))).foldr
      (fun av U => gaussianOperator av.1 av.2 U) (fun x => Real.log (Real.cosh x)) =
    IsingPerceptron.magneticRecursion h.depth
      (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
      (IsingPerceptron.chainExponent h.cut) := by
  simp_rw [gaussianOperator_eq_transform]
  rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
    (g := fun sd U => IsingPerceptron.gaussianTransform sd.1 sd.2 U), List.map_ofFn]
  simp only [Function.comp_def, fieldCascadeVariance, NNReal.coe_mk]
  exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
    (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
    (IsingPerceptron.chainExponent h.cut)).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact factorization of the Ising reference at zero interaction. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma sum_exp_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    (∑ σ : Spin N, Real.exp (fieldEnergy c σ)) = ∏ i, 2 * Real.cosh (c i) := by
  simp only [fieldEnergy, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) => Real.exp (c i * spinValue b))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  norm_num [spinValue, Real.cosh_eq]
  ring

/-- The site factorization used before the backward Gaussian cascade recursion. -/
theorem logPartition_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    logPartition (fieldEnergy c) = ∑ i, Real.log (Real.cosh (c i)) := by
  have hcard : (Fintype.card (Spin N) : ℝ) = ∏ _ : Fin N, (2 : ℝ) := by
    simp [Spin]
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, sum_exp_fieldEnergy, Finset.prod_mul_distrib, ← hcard,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact Real.log_prod (fun i _ => (Real.cosh_pos (c i)).ne')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinFactorization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.mem_fieldCutSet _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Site factorization through the finite Gaussian backward recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

theorem vectorCascade_logCosh_sum (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (c z : Fin N → ℝ) :
    IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
      (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) z =
    ∑ i, IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks (v := v) j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y)) (c i + z i) := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let F := IsingPerceptron.cascadeRecursion n bs (fun j => gaussianCascadeMarks vs j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
    have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun j => gaussianCascadeMarks vs j) (fun _ => measurable_fst.add measurable_snd)
      IsingPerceptron.measurable_logCosh
    have hg : IsingPerceptron.HasLinearGrowth F :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun j => gaussianCascadeMarks vs j)
        (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (vs j))
        IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth hbs
    have he : (fun g : Fin N → ℝ => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
        (fun g => ∑ i, F ((c i + z i) + g i)) := by
      funext g
      rw [ih bs vs hbs]
      simp only [F, Pi.add_apply, add_assoc]
    change IsingPerceptron.logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun g => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
      ∑ i, IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
        (fun g => F ((c i + z i) + g))
    rw [he]
    exact IsingPerceptron.logMean_independent_sum (fun _ : Fin N => gaussianReal 0 (v 0))
      (fun i g => F ((c i + z i) + g)) (hb 0 (by omega)).ne'
      (fun _ => hm.comp (measurable_const.add measurable_id))
      (fun i => IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left (c i + z i)) (b 0))

theorem rotatedCascadeValue_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c z : Fin N → ℝ) :
    rotatedCascadeValue n b v (fun _ => 0) U c z =
      ∑ i, ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
        (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)))
        (c i + z i) := by
  have ht : rotatedFieldTerminal (fun _ : Fin N => 0) U c =
      (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) := by
    funext y
    simp only [rotatedFieldTerminal, rotatedEnergy_constant, zero_mul, zero_div, zero_add]
    simpa only [Pi.add_apply] using logPartition_fieldEnergy (c + y)
  unfold rotatedCascadeValue
  rw [ht, vectorCascade_logCosh_sum N n b v (fun i hi => (hb.1 i hi).1)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (gaussianCascadeRecursion_eq_fold n b v
    (fun j hj => (hb.1 j hj).1.ne') IsingPerceptron.measurable_logCosh) (c i + z i)

lemma integrable_gaussianReal_of_linearGrowth (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : IsingPerceptron.HasLinearGrowth F) :
    Integrable F (gaussianReal 0 v) := by
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add
    ((IsingPerceptron.gaussianReal_exponentialNormMoments 0 v 1).const_mul L)
  apply hi.mono' hF.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |F z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

theorem rotatedEnrichedPressure_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (root : ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b v root (fun _ => 0) U c =
      (N : ℝ)⁻¹ * ∑ i, gaussianOperator 0 root
        ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
          (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y))) (c i) := by
  let F := IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks v j)
    (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
  have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n b
    (fun j => gaussianCascadeMarks v j) (fun _ => measurable_fst.add measurable_snd)
    IsingPerceptron.measurable_logCosh
  have hg : IsingPerceptron.HasLinearGrowth F :=
    IsingPerceptron.cascadeRecursion_linearGrowth n b (fun j => gaussianCascadeMarks v j)
      (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v j))
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
      (fun j hj => (hb.1 j hj).1)
  have hfi (i : Fin N) : Integrable (fun g => F (c i + g)) (gaussianReal 0 root) :=
    integrable_gaussianReal_of_linearGrowth root (hm.comp (measurable_const.add measurable_id))
      (hg.add_left (c i))
  have hF : F = (List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)) :=
    gaussianCascadeRecursion_eq_fold n b v (fun j hj => (hb.1 j hj).1.ne')
      IsingPerceptron.measurable_logCosh
  unfold rotatedEnrichedPressure
  congr 1
  calc
    _ = ∫ z : Fin N → ℝ, (∑ i, F (c i + z i))
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        rw [rotatedCascadeValue_zero_interaction n b v hb U c z]
        simp only [hF]
    _ = ∑ i, ∫ z : Fin N → ℝ, F (c i + z i)
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) :=
      integral_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).integrable_comp
          (hfi i).aestronglyMeasurable |>.mpr (hfi i))
    _ = ∑ i, ∫ g, F (c i + g) ∂gaussianReal 0 root := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).hasLaw.integral_comp
        ((hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hs : Measurable (fun g : ℝ => F (c i + g)) :=
        hm.comp (measurable_const.add measurable_id)
      rw [integral_gaussianReal_zero_eq_standard root hs, hF]
      simp [gaussianOperator]

/-- The exact zero-time normalization in `up:zero-time`, before perturbations. -/
theorem rotatedEnrichedPressure_field_zero_time {N : ℕ} (hN : 0 < N)
    (h : FieldStep) (U : Rotation N) :
    rotatedEnrichedPressure h.depth (IsingPerceptron.chainExponent h.cut) (fieldCascadeVariance h)
      (NNReal.mk (h.height 0) (h.nonneg 0)) (fun _ => 0) U (fun _ => 0) -
      h.height (Fin.last h.depth) / 2 = fieldValue h 0 := by
  rw [rotatedEnrichedPressure_zero_interaction h.depth (IsingPerceptron.chainExponent h.cut)
    (fieldCascadeVariance h) _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last) U (fun _ => 0)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul, fieldCascadeFold_eq_magneticRecursion]
  simp only [gaussianOperator, zero_add, NNReal.coe_mk]
  rw [ite_true]
  rw [fieldValue_eq_magneticFieldValue]
  unfold IsingPerceptron.magneticFieldValue
  have hroot : IsingPerceptron.pathAmplitude (heightSequence h) 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, heightSequence]
  have hlast : heightSequence h h.depth = h.height (Fin.last h.depth) :=
    heightSequence_eq h _ le_rfl
  rw [hroot, hlast]

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

private lemma measurable_tensorBaseEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1 + fieldEnergy c p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  have hrot : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  exact (hrot.comp measurable_fst).add_const (fieldEnergy c x.1)

private lemma tensorBase_exp_integrable {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Integrable (fun x : Spin N × LabeledLeaf n =>
      Real.exp (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1))
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) :=
  (Integrable.of_finite : Integrable
    (fun σ : Spin N => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (uniformSpinPrior N : Measure (Spin N))).comp_fst (labeledLeafLaw n ω.2)

private lemma measurable_namespacedPathField {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : ((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hm : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hm
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  rfl

/-- Exponentials of the tensor Hamiltonian are integrable for
almost every joint rotation/tree/Gaussian disorder. No concentration or
limiting-pressure hypothesis is used. -/
theorem tensorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) := tensorBase_exp_integrable eig c n ω
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorBaseEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_namespacedPathField I degree amplitude n treeDegree h
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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma tensorDeterministicLog_eq {N n : ℕ} (eig c : Fin N → ℝ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
      (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
      ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) =
      logPartition (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ) := by
  unfold labeledSpinReference
  rw [integral_fun_fst (μ := (uniformSpinPrior N : Measure (Spin N)))
    (ν := labeledLeafLaw n ω.2) (fun σ => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))]
  simp only [probReal_univ, one_smul]
  exact finiteLogIntegral_uniformSpinPrior _

lemma tensorDeterministicLog_abs_le {N : ℕ} (eig c : Fin N → ℝ)
    (U : Rotation N) :
    |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)| ≤
      (∑ i, |eig i|) * N / 2 + ∑ i, |c i| := by
  have he (σ : Spin N) : |rotatedEnergy eig U σ| ≤ (∑ i, |eig i|) * N / 2 := by
    have ht := abs_rotatedEnergy_sub_le eig (fun _ => 0) U (∑ i, |eig i|)
      (fun i => by simpa only [sub_zero] using
        (Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i))) σ
    simpa only [rotatedEnergy, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero] using ht
  have hf (σ : Spin N) : |fieldEnergy c σ| ≤ ∑ i, |c i| := by
    simpa only [fieldEnergy, zero_mul, Finset.sum_const_zero, sub_zero] using
      abs_fieldEnergy_sub_le c (fun _ => 0) σ
  have ht := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) (fun _ : Spin N => 0)
    ((∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    (fun σ => by simpa only [sub_zero] using (abs_add_le _ _).trans (add_le_add (he σ) (hf σ)))
  simpa only [logPartition_zero, sub_zero] using ht

lemma measurable_tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (Function.uncurry (tensorDeterministicEnergy eig c n)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add_const (fieldEnergy c x.1)

lemma tensorDeterministicLog_integrable {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) :
    Integrable (fun ω : SpecialOrthogonal N × LabeledTree n => Real.log
      (∫ x, Real.exp (tensorDeterministicEnergy eig c n ω x)
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2))
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  apply integrable_of_measurable_abs_le (c := (∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    ((measurable_random_referencePartition (ν := ν)
      (H := Function.uncurry (tensorDeterministicEnergy eig c n)) hν
        (measurable_tensorDeterministicEnergy eig c n)).log)
  intro ω
  change |Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)| ≤ _
  rw [tensorDeterministicLog_eq]
  exact tensorDeterministicLog_abs_le eig c (specialRotation ω.1)

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

theorem tensorNamespacedLog_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (tensorNamespacedLog eig c I degree amp n treeDegree h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  exact randomCoefficient_log_partition_integrable hν (tensorDeterministicEnergy eig c n)
    (measurable_tensorDeterministicEnergy eig c n)
    (fun ω => finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (tensorDeterministicLog_integrable μ eig c n b)
    (fun ω => tensorNamespacedCoefficients (specialRotation ω.1) I degree amp n
      (fun a => tensorPathProfile I degree n treeDegree h a))
    (measurable_tensorNamespacedPathFields I degree amp n treeDegree h)
    (fun ω x => tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amp n treeDegree h hh h0 x)

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

lemma tensorTemperature_reference_fold {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p).tilted
        (fun x => t * rotatedEnergy eig (specialRotation p.1.1) x.1) =
      tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p := by
  filter_upwards [tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let H := tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p
  let G := fun x : Spin N × LabeledLeaf n => t * rotatedEnergy eig (specialRotation p.1.1) x.1
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    change Integrable (fun x => Real.exp
      (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p x)) ν at ht
    rw [he] at ht
    exact ht
  change (gibbsProbability ν H).tilted G = gibbsProbability ν _
  rw [he, gibbsProbability_eq_tilted ν H hH,
    gibbsProbability_eq_tilted ν (fun x => H x + G x) hi, tilted_tilted hH G]
  rfl

lemma tensorTemperatureCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1.1) x.1)
        (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p) t =
      tensorNamespacedLog (diagonalPerturbedEigenvalues eig I v t) c I degree amp n r h p -
        tensorNamespacedLog (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h p := by
  filter_upwards [tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp n b r h hh h0,
    tensorNamespaced_exp_integrable_ae μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amp n b r h hh h0] with p hp ht
  have he := tensorTemperatureHamiltonian_affine hN eig c I v degree amp n r h p t
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTemperatureDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual enriched mean pressure is differentiable in temperature.
Its derivative is the Gibbs interaction energy before temperature scaling. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem hasDerivAt_tensorNamespacedMeanPressure_temperature {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (t : ℝ) :
    HasDerivAt (fun s => tensorNamespacedMeanPressure μ
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h)
      (tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp n b r h (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)) t := by
  let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v 0) c I degree amp n r h
  let Y := fun (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation p.1.1) x.1
  have hY : Measurable (Function.uncurry Y) := measurable_tensorTemperatureObservable eig
  have hB (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) : |Y p x| ≤ K * N / 2 :=
    abs_rotatedEnergy_le eig (specialRotation p.1.1) K hK x.1
  have hd := hasDerivAt_bounded_random_cgf P ν
    (measurable_tensorNamespacedReference _ c I degree amp n r h) Y hY (K * N / 2) hB t
  let M := fun s => tensorNamespacedMeanPressure μ
    (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h
  have he (s : ℝ) : M s = M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := by
    have hi (s : ℝ) := tensorNamespacedLog_integrable μ
      (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h hh h0
    rw [integral_congr_ae (tensorTemperatureCGF_eq_log_difference hN μ eig c I v degree amp n b r h hh h0 s),
      integral_sub (hi s) (hi 0)]
    dsimp only [M, tensorNamespacedMeanPressure, tensorNamespacedPressure]
    simp only [integral_const_mul]
    ring
  have hf : M = fun s => M 0 + (∫ p, cgf (Y p) (ν p) s ∂P) / N := funext he
  have hfold : (∫ p, ∫ x, Y p x ∂(ν p).tilted (fun x => t * Y p x) ∂P) =
      ∫ p, ∫ x, Y p x ∂tensorNamespacedReference (diagonalPerturbedEigenvalues eig I v t)
        c I degree amp n r h p ∂P := by
    apply integral_congr_ae
    filter_upwards [tensorTemperature_reference_fold hN μ eig c I v degree amp n b r h hh h0 t] with p hp
    rw [hp]
  have hhD := (hd.div_const (N : ℝ)).const_add (M 0)
  rw [hfold] at hhD
  rw [← hf] at hhD
  simpa only [M, Y, P, tensorNamespacedObservableAverage, integral_const_mul, integral_mul_const, div_eq_mul_inv,
    mul_comm] using hhD

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTemperatureModulus
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform temperature continuity of the enriched pressure and its
identity with the pressure under the original disorder law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma abs_tensorNamespaced_interactionEnergy_le {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig modelEig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |tensorNamespacedObservableAverage μ modelEig c I degree amp n b r h
      (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)| ≤ K / 2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hb (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) :
      |(N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1| ≤ K / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    calc
      _ ≤ (N : ℝ)⁻¹ * (K * N / 2) := mul_le_mul_of_nonneg_left
        (abs_rotatedEnergy_le eig (specialRotation U) K hK x.1) (by positivity)
      _ = K / 2 := by field_simp
  have hi (p : TensorFlatDisorder N n) :
      ‖∫ x, (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation p.1.1) x.1
        ∂tensorNamespacedReference modelEig c I degree amp n r h p‖ ≤ K / 2 := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := tensorNamespacedReference modelEig c I degree amp n r h p)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb p.1.1 x)
  unfold tensorNamespacedObservableAverage
  simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const
      (μ := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
      (ae_of_all _ hi)

theorem tensorNamespacedMeanPressure_temperature_modulus {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (s t : ℝ) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h -
      tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amp n b r h| ≤
      (K / 2) * |s - t| := by
  have hd (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :=
    (hasDerivAt_tensorNamespacedMeanPressure_temperature hN μ eig c I v degree amp n b r h hh h0 K hK a).hasDerivWithinAt
      (s := univ)
  have hb (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :
      ‖tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v a)
        c I degree amp n b r h
        (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)‖ ≤ K / 2 := by
    rw [Real.norm_eq_abs]
    exact abs_tensorNamespaced_interactionEnergy_le hN μ eig _ c I degree amp n b r h K hK
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd hb (mem_univ t) (mem_univ s)

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
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
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

lemma entropyFunctional_mono {p q : OverlapPath}
    (hpq : p.val ≤ᵐ[pathMeasure] q.val) : entropyFunctional p ≤ entropyFunctional q := by
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe_iff.mpr
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae (integrable_path_mul_field p h) (integrable_path_mul_field q h)
  filter_upwards [hpq] with s hs
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


lemma heightSequence_contactFieldStep {n : ℕ} (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) :
    heightSequence (contactFieldStep cut hc hfirst hlast a ha) = finiteFieldPath a := by
  funext i
  change finiteFieldPath a (min i n) = finiteFieldPath a i
  unfold finiteFieldPath
  apply Finset.sum_congr rfl
  intro j _
  have he : j.val ≤ min i n ↔ j.val ≤ i := by omega
  simp only [he]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorZeroAmplitude
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing zero-amplitude tensor marks

Projection onto the site coordinates sends the tensor Gaussian product law
to the original site-field law.  This identifies the actual zero-amplitude
cascade pressure with the unperturbed rotated enriched pressure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorSiteProjection_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) (site : ℝ≥0)
    (hv : ∀ i, v (Sum.inl i) = site) :
    MeasurePreserving (tensorSiteProjection I degree)
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ))
      (vectorGaussianLaw N site : Measure (Fin N → ℝ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i))
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i))))
    (ν := Measure.pi (fun j : Sigma (fun j : Fin k => SpectralTensorIndex I (degree j)) =>
      gaussianReal 0 (v (Sum.inr j))))
  have h := hfst.comp hsplit
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 site))
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i)))) at h
  simpa only [hv] using h

lemma spinTensorEnergy_zero_amplitude {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) :
    spinTensorEnergy U I degree (fun _ => 0) z σ =
      fieldEnergy (tensorSiteProjection I degree z) σ := by
  classical
  simp only [spinTensorEnergy, Fintype.sum_sum_type, spinTensorFeature, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero, tensorSiteProjection, fieldEnergy]

lemma spinTensorTerminal_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) :
    spinTensorTerminal eig U c I degree (fun _ => 0) z =
      rotatedFieldTerminal eig U c (tensorSiteProjection I degree z) := by
  unfold spinTensorTerminal rotatedFieldTerminal
  congr 1
  funext σ
  rw [spinTensorEnergy_zero_amplitude]
  simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Zero-amplitude tensor coordinates disappear at every Gaussian recursion
step, irrespective of their unused variances. -/
theorem tensorCascadeValue_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (z : SpinTensorIndex I degree → ℝ) :
    tensorCascadeValue eig U c I degree (fun _ => 0) n b v z =
      rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z) := by
  induction n generalizing b v site z with
  | zero => exact spinTensorTerminal_zero_amplitude eig U c I degree z
  | succ n ih =>
    let F := rotatedCascadeValue n (fun j => b (j + 1)) (fun j => site (j + 1)) eig U c
    have hF : Measurable F :=
      measurable_cascadeRecursion n (fun j => b (j + 1))
        (fun j => vectorGaussianLaw N (site (j + 1)))
        (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
    have hE : Measurable (fun w : Fin N → ℝ =>
        Real.exp (b 0 * F (tensorSiteProjection I degree z + w))) :=
      ((hF.comp (measurable_const.add measurable_id)).const_mul (b 0)).exp
    have hm := tensorSiteProjection_measurePreserving I degree (v 0) (site 0) (hv 0)
    change logMean (b 0) (tensorGaussianLaw I degree (v 0) : Measure _)
        (fun w => tensorCascadeValue eig U c I degree (fun _ => 0) n
          (fun j => b (j + 1)) (fun j => v (j + 1)) (z + w)) =
      logMean (b 0) (vectorGaussianLaw N (site 0) : Measure _)
        (fun w => F (tensorSiteProjection I degree z + w))
    unfold logMean
    congr 1
    congr 1
    calc
      _ = ∫ w : SpinTensorIndex I degree → ℝ,
          Real.exp (b 0 * F (tensorSiteProjection I degree z + tensorSiteProjection I degree w))
          ∂(tensorGaussianLaw I degree (v 0) : Measure _) := by
        apply integral_congr_ae
        refine ae_of_all _ fun w => ?_
        dsimp only
        rw [ih (fun j => b (j + 1)) (fun j => v (j + 1))
          (fun j => site (j + 1)) (fun j i => hv (j + 1) i)]
        rfl
      _ = _ := hm.hasLaw.integral_comp hE.aestronglyMeasurable

/-- The exact unperturbed enriched-pressure identity used at temperature zero. -/
theorem tensorEnrichedPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (root : SpinTensorIndex I degree → ℝ≥0) (rootSite : ℝ≥0)
    (hroot : ∀ i, root (Sum.inl i) = rootSite) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b v root =
      rotatedEnrichedPressure n b site rootSite eig U c := by
  unfold tensorEnrichedPressure rotatedEnrichedPressure
  congr 1
  have hF : Measurable (rotatedCascadeValue n b site eig U c) :=
    measurable_cascadeRecursion n b (fun j => vectorGaussianLaw N (site j))
      (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
  calc
    _ = ∫ z : SpinTensorIndex I degree → ℝ,
        rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z)
        ∂(tensorGaussianLaw I degree root : Measure _) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => tensorCascadeValue_zero_amplitude eig U c I degree n b v site hv z
    _ = _ := (tensorSiteProjection_measurePreserving I degree root rootSite hroot).hasLaw.integral_comp
      hF.aestronglyMeasurable

/-- The manuscript profile retains precisely the original linear-field
increments when the monomial amplitudes vanish. -/
theorem tensorPathPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0) =
    rotatedEnrichedPressure n b (fun i => varianceIncrement h (i + 1))
      (varianceIncrement h 0) eig U c :=
  tensorEnrichedPressure_zero_amplitude eig U c I degree n b _ _
    (fun _ _ => rfl) _ _ (fun _ => rfl)

lemma varianceIncrement_heightSequence (h : FieldStep) (i : ℕ) :
    varianceIncrement (heightSequence h) (i + 1) = fieldCascadeVariance h i := by
  apply NNReal.eq
  rw [varianceIncrement_coe (heightSequence_mono h) (heightSequence_nonneg h 0)]
  exact (pathAmplitude_sq (heightSequence_mono h) (heightSequence_nonneg h 0) (i + 1)).symm

lemma varianceIncrement_heightSequence_zero (h : FieldStep) :
    varianceIncrement (heightSequence h) 0 = NNReal.mk (h.height 0) (h.nonneg 0) := by
  apply NNReal.eq
  rw [varianceIncrement_coe (heightSequence_mono h) (heightSequence_nonneg h 0)]
  simp only [pathIncrement, heightSequence, Nat.zero_min]
  change h.height ⟨0, _⟩ = h.height 0
  congr 1

/-- The exact zero-temperature base value in the tensor model, with all
unused monomial variances still present. -/
theorem tensorPathPressure_field_zero_time {N m k : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (treeDegree : Fin k → ℕ) (h : FieldStep) :
    tensorEnrichedPressure (fun _ => 0) U (fun _ => 0) I degree (fun _ => 0)
      h.depth (chainExponent h.cut)
      (fun i => tensorPathProfile I degree h.depth treeDegree (heightSequence h) (i + 1))
      (tensorPathProfile I degree h.depth treeDegree (heightSequence h) 0) -
      h.height (Fin.last h.depth) / 2 = fieldValue h 0 := by
  rw [tensorPathPressure_zero_amplitude, varianceIncrement_heightSequence_zero]
  simp_rw [varianceIncrement_heightSequence]
  exact rotatedEnrichedPressure_field_zero_time hN h U

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactCap
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.mem_fieldCutSet _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field cap in the fixed-partition contact problem is inactive on
negative sublevels.  All estimates concern the actual perturbed pressure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContactPressure_field_le
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (p : TensorContactParameter N m n) (ht : p.1 ∈ Icc (0 : ℝ) 1)
    (ha : ∀ i, 0 ≤ p.2.1 i) (hu : ∀ j, |p.2.2.1 j| ≤ 2)
    (hv : ∀ j, |p.2.2.2 j| ≤ 2) :
    tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p ≤
      fieldValue (contactFieldStep cut hc hfirst hlast p.2.1 ha) 0 + K / 2 +
        (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) := by
  let step := contactFieldStep cut hc hfirst hlast p.2.1 ha
  let p0 : TensorContactParameter N m n := (0, p.2.1, p.2.2.1, p.2.2.2)
  have hb : CascadeExponents n (chainExponent cut) := chainExponent_admissible hc hfirst hlast
  have hP := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ
    eig (fun _ => 0) I p.2.2.1 hu p.2.2.2 hv 0 n (chainExponent cut)
    (finiteFieldPath p.2.1) hb (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => (0 : ℝ) * eig i) (specialRotation U) (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n (chainExponent cut)
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1) 0) =
      fieldValue step 0 + finiteFieldPath p.2.1 n / 2 := by
    have he := tensorPathPressure_field_zero_time (by omega : 0 < N) (specialRotation U) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (fun j => enumeratedTreeDegree m j) step
    have hs : heightSequence step = finiteFieldPath p.2.1 :=
      heightSequence_contactFieldStep cut hc hfirst hlast p.2.1 ha
    rw [hs] at he
    change _ - finiteFieldPath p.2.1 n / 2 = fieldValue step 0 at he
    convert (sub_eq_iff_eq_add).mp he using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_mul]
    rfl
  simp_rw [hbase] at hP
  simp only [integral_const, probReal_univ, one_smul, add_sub_cancel_right] at hP
  change |tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p0 -
    fieldValue step 0| ≤ _ at hP
  have hT := tensorNamespacedMeanPressure_temperature_modulus (by omega : 0 < N)
    μ eig (fun _ => 0) I p.2.2.2 (fun j => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N p.2.2.1) n (chainExponent cut)
    (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) K heig p.1 0
  have hK : 0 ≤ K := (abs_nonneg (eig ⟨0, by omega⟩)).trans (heig _)
  have ht' : |p.1 - 0| ≤ 1 := by simpa only [sub_zero, abs_of_nonneg ht.1] using ht.2
  have hT' := hT.trans (mul_le_of_le_one_right (div_nonneg hK (by norm_num)) ht')
  change |tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p -
    tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p0| ≤ K / 2 at hT'
  have hp := (le_abs_self _).trans hP
  have htemp := (le_abs_self _).trans hT'
  change tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p ≤
    fieldValue step 0 + K / 2 + (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2)
  linarith

/-- A coercive lower bound in the total nonnegative field increment. -/
theorem tensorContactObjective_cap_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
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
      tensorContactObjective μ eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V p := by
  let step := contactFieldStep cut hc hfirst hlast p.2.1 ha
  have hp := tensorContactPressure_field_le hhaar hgauss hN μ hμ eig I K heig
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
  change tensorContactPressure μ eig (fun _ => 0) I (chainExponent cut) p ≤
    fieldValue step 0 + K / 2 + (2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) at hp
  unfold tensorContactObjective
  linarith

/-- One fixed cap works for every dimension and every allowed perturbation
parameter.  Thus a negative contact sublevel cannot touch its field face. -/
theorem exists_tensorContactObjective_cap
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m n : ℕ) (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (K S L : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ) (_hN : 3 ≤ N)
      (μ : Measure (SpecialOrthogonal N)) (_hμprob : IsProbabilityMeasure μ)
      (_hμ : μ.IsMulLeftInvariant) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
      (_heig : ∀ i, |eig i| ≤ K) (V : ℝ → ℝ)
      (_hV : ∀ t ∈ Icc (0 : ℝ) 1, L ≤ V t) (p : TensorContactParameter N m n),
      p.1 ∈ Icc (0 : ℝ) 1 → (∀ i, 0 ≤ p.2.1 i) →
      (∀ j, |p.2.2.1 j| ≤ 2) → (∀ j, |p.2.2.2 j| ≤ 2) →
      tensorContactObjective μ eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V p < 0 →
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
  intro N hN μ hμprob hμ eig I heig V hV p ht ha hu hv hneg
  have : IsProbabilityMeasure μ := hμprob
  by_contra hn
  have hx : H ≤ ∑ i, p.2.1 i := le_of_not_gt hn
  have hs := hbound (∑ i, p.2.1 i) hx
  have hcap := tensorContactObjective_cap_bound hhaar hgauss hN μ hμ eig I K heig
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

theorem finiteSpectralSlope_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    finiteSpectralSlope ρ eig hρ hρsum 0 = ∑ a, ρ a * eig a := by
  simp only [finiteSpectralSlope, projectedResolventDerivative, lt_self_iff_false, ite_false, if_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

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

theorem hasDerivWithinAt_finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum t)
      (finiteSpectralSlope ρ eig hρ hρsum (t * x)) (Ici 0) x := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_mul, finiteSpectralSlope_zero]
    have hd := (hasDerivAt_id x).mul_const (∑ a, ρ a * eig a)
    convert! hd.hasDerivWithinAt using 1
    · funext y
      simp [finiteThermalScalar, finiteR]
    · simp
  · have hdH := hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum (mul_nonneg h.le hx)
    have hdlin : HasDerivWithinAt (fun y : ℝ => t * y) t (Ici 0) x := by
      convert! ((hasDerivAt_id x).const_mul t).hasDerivWithinAt using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd := (hdH.comp x hdlin (fun y hy => mul_nonneg h.le hy)).const_mul (1 / t)
    convert! hd using 1
    · funext y
      dsimp [finiteThermalScalar, Function.comp_def]
      field_simp [h.ne']
    · field_simp [h.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergyPrimitive
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature primitive of the finite-spectrum interaction energy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralSlope_temperature (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (∫ u in 0..t, finiteSpectralSlope ρ eig hρ hρsum (u * x)) =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  have hc : Continuous (finiteThermalScalar ρ eig hρ hρsum x) :=
    continuous_id.mul ((continuous_finiteR ρ eig hρ hρsum).comp
      (continuous_const.mul continuous_id))
  have hd : ∀ u ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum x)
        (finiteSpectralSlope ρ eig hρ hρsum (u * x)) (Ioi u) u := by
    intro u hu
    have h := hasDerivWithinAt_finiteThermalScalar ρ eig hρ hρsum hx hu.1.le
    rw [mul_comm x u] at h
    exact h.mono fun y hy => (lt_trans hu.1 (show u < y from hy)).le
  have hint : IntervalIntegrable (fun u => finiteSpectralSlope ρ eig hρ hρsum (u * x))
      volume 0 t :=
    ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
      (continuous_id.mul continuous_const)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc.continuousOn hd hint
  simpa only [finiteThermalScalar, zero_mul, sub_zero, mul_comm x t] using hFTC

/-- Equation `up:primitive`, for the actual finite atomic spectral transform. -/
theorem integral_finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    (∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p) =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p := by
  let K := ∑ a, |eig a|
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hS : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  let f : ℝ → ℝ → ℝ := fun u r => finiteSpectralSlope ρ eig hρ hρsum (u * deficit p r)
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (Function.uncurry f) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).measurable.comp
      (measurable_fst.mul ((continuous_deficit p).measurable.comp measurable_snd))
  have hi : Integrable (Function.uncurry f) ((volume.restrict (uIoc 0 t)).prod pathMeasure) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖finiteSpectralSlope ρ eig hρ hρsum (z.1 * deficit p z.2)‖ ≤ K
      simpa only [Real.norm_eq_abs] using hS (z.1 * deficit p z.2)
  have hswap := intervalIntegral_integral_swap hi
  unfold finiteInteractionEnergy spectralFunctional
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in 0..t, ∫ r, f u r ∂pathMeasure) =
    (1 / 2 : ℝ) * ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact integral_finiteSpectralSlope_temperature ρ eig hρ hρsum ht (deficit_nonneg p hr.2.le)

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

theorem finiteTemperatureFunctional_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {t : ℝ} (ht : 0 ≤ t) :
    finiteTemperatureFunctional ρ eig hρ hρsum p t =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p :=
  integral_finiteInteractionEnergy ρ eig hρ hρsum ht p

theorem continuous_finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (finiteTemperatureFunctional ρ eig hρ hρsum p) :=
  intervalIntegral.continuous_primitive
    (continuous_finiteInteractionEnergy_temperature ρ eig hρ hρsum p).intervalIntegrable 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactZeroBoundary
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine zero-temperature boundary differs from the entropy contact
bound only by the already controlled finite perturbation cost. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContact_zero_temperature_bound
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (S : ℝ) (hS : entropyFunctional trial ≤ (S : EReal))
    (V : ℝ → ℝ) (hV : V 0 = 0) :
    -(2 * m * perturbationScale N + 8 * perturbationScale N ^ 2) ≤
      tensorContactObjective μ eig (fun _ => 0) I (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (0, a, u, v) := by
  let step := contactFieldStep cut hc hfirst hlast a ha
  have hb : CascadeExponents n (chainExponent cut) :=
    chainExponent_admissible hc hfirst hlast
  have hP := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ
    eig (fun _ => 0) I u hu v hv 0 n (chainExponent cut) (finiteFieldPath a) hb
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => (0 : ℝ) * eig i) (specialRotation U) (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n (chainExponent cut)
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath a) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (finiteFieldPath a) 0) =
      fieldValue step 0 + finiteFieldPath a n / 2 := by
    have he := tensorPathPressure_field_zero_time (by omega : 0 < N) (specialRotation U) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (fun j => enumeratedTreeDegree m j) step
    have hs : heightSequence step = finiteFieldPath a :=
      heightSequence_contactFieldStep cut hc hfirst hlast a ha
    rw [hs] at he
    change _ - finiteFieldPath a n / 2 = fieldValue step 0 at he
    convert (sub_eq_iff_eq_add).mp he using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_mul]
    rfl
  simp_rw [hbase] at hP
  simp only [integral_const, probReal_univ, one_smul, add_sub_cancel_right] at hP
  have hSreal : fieldValue step 0 + fieldPairing trial step / 2 ≤ S := by
    have he : ((fieldValue step 0 + fieldPairing trial step / 2 : ℝ) : EReal) ≤ (S : EReal) :=
      (le_iSup (fun h : FieldStep => ((fieldValue h 0 + fieldPairing trial h / 2 : ℝ) : EReal))
        step).trans hS
    exact_mod_cast he
  have hpair := fieldPairing_contactFieldStep trial cut hc hfirst hlast a ha values hvalues
  change fieldPairing trial step = _ at hpair
  rw [hpair] at hSreal
  have hU : 0 ≤ ∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  have hW : 0 ≤ ∑ j : Fin m, (v j - 3 / 2) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  simp only [tensorContactObjective, tensorContactPressure, hV]
  have hp := (le_abs_self _).trans hP
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactAsymptotic
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform asymptotic nonnegativity of the actual contact problem for a
fixed trial partition. Only the two named concentration inputs are assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_eventually_nonnegative
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
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
    (δ S : ℝ) (hδ : 0 < δ) (hS : entropyFunctional trial ≤ (S : EReal)) :
    ∃ H : ℝ, 0 < H ∧ ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ p ∈ tensorContactRegion (N k) m n H,
        -η ≤ tensorContactObjective (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut)
          (fun i => (cut i.succ - cut i.castSucc) * values i) S
          (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) p := by
  classical
  let V : ℝ → ℝ := fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ
  have hV : Continuous V := (continuous_finiteTemperatureFunctional ρ lam hρpos hρsum trial).add
    (continuous_id.mul continuous_const)
  have hV0 : V 0 = 0 := by simp [V, finiteTemperatureFunctional]
  obtain ⟨tmin, _, hlow⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hV.continuousOn
  obtain ⟨H, hH, hcap⟩ := exists_tensorContactObjective_cap hhaar hgauss m n cut hc hfirst hlast
    trial values hvalues d hd htrial K S (V tmin)
  refine ⟨H, hH, ?_⟩
  intro η hη
  have hcost : ∀ᶠ k in atTop,
      2 * m * perturbationScale (N k) + 8 * perturbationScale (N k) ^ 2 < η :=
    ((fullPerturbationCost_tendsto m).comp hNlim).eventually (gt_mem_nhds hη)
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ p ∈ tensorContactRegion (N k) m n H,
      tensorContactObjective (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V p < -η := by
    simpa only [V, Filter.not_eventually, not_forall, _root_.not_imp, not_le, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop (hbad'.and_eventually hcost)
  have hmins (k : ℕ) := tensorContactObjective_exists_minimum hhaar hgauss (hN (φ k))
    (μ (φ k)) (hμinv (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
    (chainExponent_admissible hc hfirst hlast) K (heig (φ k))
    (fun i => (cut i.succ - cut i.castSucc) * values i) S V hV H hH.le
  choose p hp hmin using hmins
  have hneg (k : ℕ) :
      tensorContactObjective (μ (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) < -η := by
    obtain ⟨q, hq, hqneg⟩ := (hφbad k).1
    exact (hmin k q hq).trans_lt hqneg
  have hcap' (k : ℕ) : (∑ i, (p k).2.1 i) < H := by
    have hb := tensorContactRegion_bounds (hp k)
    apply hcap (N (φ k)) (hN (φ k)) (μ (φ k)) inferInstance (hμinv (φ k))
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
    have hzeroBound := tensorContact_zero_temperature_bound hhaar hgauss (hN (φ k))
      (μ (φ k)) (hμinv (φ k)) (eig (φ k)) (I (φ k)) cut hc hfirst hlast
      (p k).2.1 hb.2.1 (p k).2.2.1 hu (p k).2.2.2 hv trial values hvalues S hS V hV0
    have hpEq : p k = (0, (p k).2.1, (p k).2.2.1, (p k).2.2.2) := by
      exact Prod.ext heq (Prod.ext rfl (Prod.ext rfl rfl))
    rw [← hpEq] at hzeroBound
    have := (hφbad k).2
    linarith [hneg k]
  exact tensorContact_no_positive_minimizing_sequence hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => eig (φ k)) (fun _ _ => 0)
    K hK (fun k => heig (φ k)) (fun k => I (φ k)) (fun k => hdis (φ k))
    (fun k => hcover (φ k)) lam (fun k => hlam (φ k)) ρ hρpos hρsum
    (hρ.comp hφ.tendsto_atTop) cut hc hfirst hlast trial values hvalues δ S H hδ p hp hmin hcap' hpos

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorZeroFieldPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With both the linear-field heights and the monomial amplitudes zero,
the cascade leaves the original finite Ising pressure unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma vectorGaussianLaw_zero_ae (N : ℕ) :
    ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z = 0 := by
  have hi (i : Fin N) :
      ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z i = 0 := by
    have hz : ∀ᵐ x ∂gaussianReal 0 0, x = 0 := by
      simp [gaussianReal_zero_var, ae_dirac_eq]
    exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 0) i).quasiMeasurePreserving.ae hz
  filter_upwards [ae_all_iff.mpr hi] with z hz
  funext i
  exact hz i

lemma integral_vectorGaussianLaw_zero {N : ℕ} (F : (Fin N → ℝ) → ℝ) :
    (∫ z, F z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ))) = F 0 := by
  calc
    _ = ∫ _ : Fin N → ℝ, F 0 ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [vectorGaussianLaw_zero_ae N] with z hz
      rw [hz]
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

lemma logMean_vectorGaussianLaw_zero {N : ℕ} {b : ℝ} (hb : b ≠ 0)
    (F : (Fin N → ℝ) → ℝ) :
    logMean b (vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) F = F 0 := by
  unfold logMean
  rw [integral_vectorGaussianLaw_zero, Real.log_exp]
  exact mul_div_cancel_left₀ (F 0) hb

lemma rotatedCascadeValue_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) :
    rotatedCascadeValue n b (fun _ => 0) eig U c z = rotatedFieldTerminal eig U c z := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change logMean (b 0) (vectorGaussianLaw N 0 : Measure (Fin N → ℝ))
      (fun w => rotatedCascadeValue n (fun i => b (i + 1)) (fun _ => 0) eig U c (z + w)) = _
    rw [logMean_vectorGaussianLaw_zero (hb.1 0 (by omega)).1.ne']
    simpa only [add_zero] using ih (fun i => b (i + 1)) hb.tail

lemma rotatedEnrichedPressure_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b (fun _ => 0) 0 eig U c = rotatedPressure eig U c := by
  unfold rotatedEnrichedPressure
  rw [integral_vectorGaussianLaw_zero, rotatedCascadeValue_zero_variance n b hb]
  simp only [rotatedPressure, rotatedFieldTerminal, add_zero]

lemma varianceIncrement_zero_path (i : ℕ) : varianceIncrement (fun _ => 0) i = 0 := by
  cases i <;> simp [varianceIncrement, pathIncrement]

/-- The exact unperturbed pressure at zero field height, including the root. -/
theorem tensorPathPressure_zero_field {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (r : Fin k → ℕ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n r (fun _ => 0) (i + 1))
      (tensorPathProfile I degree n r (fun _ => 0) 0) = rotatedPressure eig U c := by
  rw [tensorPathPressure_zero_amplitude]
  simp_rw [varianceIncrement_zero_path]
  exact rotatedEnrichedPressure_zero_variance n b hb eig U c

/-- At zero random-field height the centered actual pressure differs from
the ordinary Haar-mean pressure only by the established perturbation cost. -/
theorem tensorNamespacedMeanPressure_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) (fun _ => 0) -
      ∫ U : SpecialOrthogonal N, rotatedPressure (fun i => t * eig i) (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  have h := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ eig c I
    u hu v hv t n b (fun _ => 0) hb monotone_const (by rfl)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) 0) =
      rotatedPressure (fun i => t * eig i) (specialRotation U) c := by
    exact tensorPathPressure_zero_field (fun i => t * eig i) (specialRotation U) c I
      (fun j : Fin N => enumeratedSpectralDegree m j) n b hb (fun j => enumeratedTreeDegree m j)
  simp_rw [hbase] at h
  simpa only [zero_div, sub_zero] using h

theorem tensorContactPressure_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorContactPressure μ eig c I b (t, (fun _ : Fin (n + 1) => 0), u, v) -
      ∫ U : SpecialOrthogonal N, rotatedPressure (fun i => t * eig i) (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  have hzero : finiteFieldPath (fun _ : Fin (n + 1) => (0 : ℝ)) = fun _ => 0 := by
    funext i
    simp only [finiteFieldPath, ite_self, Finset.sum_const_zero]
  simpa only [tensorContactPressure, hzero] using
    tensorNamespacedMeanPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I u hu v hv t n b hb

theorem tensorContactPressure_one_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorContactPressure μ eig c I b (1, (fun _ : Fin (n + 1) => 0), u, v) -
      ∫ U : SpecialOrthogonal N, rotatedPressure eig (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  simpa only [one_mul] using
    tensorContactPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I u hu v hv 1 n b hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSpectrumStepUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound against a fixed finite-step
trial. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_step_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
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
    (S : ℝ) (hS : entropyFunctional trial ≤ (S : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) trial + ε := by
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨H, hH, hevent⟩ := tensorContact_eventually_nonnegative hhaar hgauss
    N hN hNlim m n μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    cut hc hfirst hlast trial values hvalues d hd htrial (ε / 3) S hthird hS
  have hcost : ∀ᶠ k in atTop,
      2 * m * perturbationScale (N k) + 8 * perturbationScale (N k) ^ 2 < ε / 3 :=
    ((fullPerturbationCost_tendsto m).comp hNlim).eventually (gt_mem_nhds hthird)
  filter_upwards [hevent (ε / 3) hthird, hcost] with k hk hck
  let p : TensorContactParameter (N k) m n :=
    (1, (fun _ => 0), (fun _ => 3 / 2), (fun _ => 3 / 2))
  have hp : p ∈ tensorContactRegion (N k) m n H := by
    apply tensorContactRegion_mem (by norm_num) (fun _ => le_rfl)
    · simpa only [p, Finset.sum_const_zero] using hH.le
    · intro j; norm_num
    · intro a; norm_num
  have hj := hk p hp
  have hz := tensorContactPressure_one_zero_field_cost hhaar hgauss (hN k) (μ k) (hμinv k)
    (eig k) (fun _ => 0) (I k) (fun _ => 3 / 2) (by intro j; norm_num)
    (fun _ => 3 / 2) (by intro j; norm_num) n (chainExponent cut)
    (chainExponent_admissible hc hfirst hlast)
  have hg : finiteTemperatureFunctional ρ lam hρpos hρsum trial 1 =
      spectralFunctional (finiteR ρ lam hρpos hρsum) trial := by
    simpa only [one_mul] using finiteTemperatureFunctional_eq ρ lam hρpos hρsum trial zero_le_one
  have hzero : finiteFieldPath (fun _ : Fin (n + 1) => (0 : ℝ)) = fun _ => 0 := by
    funext i
    simp only [finiteFieldPath, ite_self, Finset.sum_const_zero]
  simp only [tensorContactObjective, p, hzero, mul_zero, Finset.sum_const_zero, zero_div,
    sub_zero, one_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, hg] at hj
  have hdiff := neg_le_abs (tensorContactPressure (μ k) (eig k) (fun _ => 0) (I k)
    (chainExponent cut) p - ∫ U : SpecialOrthogonal (N k),
      rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k)
  change |tensorContactPressure (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut) p - _| ≤ _ at hz
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPathLimit
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 approximation of the trial path preserves the finite spectral
interaction functional, as required when removing a finite partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma finiteTemperatureFunctional_tendsto_of_L1 {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun k => ∫ s, |q k s - p s| ∂pathMeasure) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => finiteTemperatureFunctional ρ eig hρ hρsum (q k) t) atTop
      (𝓝 (finiteTemperatureFunctional ρ eig hρ hρsum p t)) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun b _ => abs_nonneg (eig b)) (Finset.mem_univ a)
  have hbound (x : ℝ) : |finiteR ρ eig hρ hρsum x| ≤ K :=
    abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hd (r : ℝ) : Tendsto (fun k => deficit (q k) r) atTop (𝓝 (deficit p r)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ hL
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [Real.norm_eq_abs] using abs_deficit_sub_path_le (q k) p r)
  have hi : Tendsto (fun k => ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit (q k) r)
      ∂pathMeasure) atTop
      (𝓝 (∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => t * K)
    · intro k
      exact (continuous_const.mul ((continuous_finiteR ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit (q k))))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left (hbound _) ht)
    · exact ae_of_all _ (fun r =>
        (((continuous_finiteR ρ eig hρ hρsum).tendsto _).comp ((hd r).const_mul t)).const_mul t)
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ ht,
    spectralFunctional] using hi.const_mul (1 / 2 : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TrialGridApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower finite-grid trials approximate each monotone overlap path in L1,
remain below one, and do not increase the entropy functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma lowerGridPath_below_one (p : OverlapPath) (n : ℕ) (s : ℝ) :
    lowerGridPath p n s ≤ 1 - 1 / (n + 1 : ℕ) := by
  change (1 - 1 / (n + 1 : ℕ) : ℝ) * _ ≤ _
  exact mul_le_of_le_one_right (lowerGrid_factor_nonneg n) (p.le_one _)

lemma lowerGridPath_le (p : OverlapPath) (n : ℕ) :
    (lowerGridPath p n).val ≤ᵐ[pathMeasure] p.val := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact lowerGrid_le p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩) n hs.1.le

lemma lowerGridPath_entropy_le (p : OverlapPath) (n : ℕ) :
    entropyFunctional (lowerGridPath p n) ≤ entropyFunctional p :=
  entropyFunctional_mono (lowerGridPath_le p n)

lemma lowerGridPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1))
    (s : ℝ) (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    lowerGridPath p n s = (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)) := by
  change lowerGrid p.val n s = _
  simp only [lowerGrid, floor_on_uniformCell n i hs]

lemma lowerGridPath_L1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have hi := lowerGrid_integral_tendsto p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩)
  change Tendsto (fun n => ∫ s, lowerGridPath p n s ∂pathMeasure) atTop
    (𝓝 (∫ s, p s ∂pathMeasure)) at hi
  have he (n : ℕ) : (∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) =
      (∫ s, p s ∂pathMeasure) - ∫ s, lowerGridPath p n s ∂pathMeasure := by
    rw [← integral_sub p.integrable (lowerGridPath p n).integrable]
    apply integral_congr_ae
    filter_upwards [lowerGridPath_le p n] with s hs
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    ring
  simpa only [he, sub_self] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ s, p s ∂pathMeasure)
      atTop (𝓝 (∫ s, p s ∂pathMeasure))).sub hi)

lemma lowerGridPath_spectral_tendsto {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Tendsto (fun n => spectralFunctional (finiteR ρ eig hρ hρsum) (lowerGridPath p n))
      atTop (𝓝 (spectralFunctional (finiteR ρ eig hρ hρsum) p)) := by
  have ht := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hρsum p
    (lowerGridPath p) (lowerGridPath_L1_tendsto p) zero_le_one
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ zero_le_one, one_mul] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSpectrumUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Manuscript Proposition up:bound, in the equivalent eventual-epsilon
form against every trial of finite entropy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (p : OverlapPath) (S : ℝ) (hS : entropyFunctional p ≤ (S : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hgrid := lowerGridPath_spectral_tendsto ρ lam hρpos hρsum p
  obtain ⟨n, hn⟩ := (hgrid.eventually (gt_mem_nhds
    (show spectralFunctional (finiteR ρ lam hρpos hρsum) p <
      spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε / 2 by linarith))).exists
  have hup := finiteSpectrum_meanPressure_step_upper hhaar hgauss N hN hNlim m n
    μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (lowerGridPath p n)
    (fun i => (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)))
    (lowerGridPath_on_cell p n) (1 / (n + 1 : ℕ)) (by positivity)
    (ae_of_all _ (lowerGridPath_below_one p n)) S
    ((lowerGridPath_entropy_le p n).trans hS) (ε / 2) hhalf
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteVariationalBounds
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness and finite-entropy approximate minimizers of the finite-spectrum
variational problem. These justify taking the infimum in the pressure bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem exists_finiteEntropy_trial_near_finiteVariational {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : OverlapPath, ∃ S : ℝ, entropyFunctional p = (S : EReal) ∧
      S + spectralFunctional (finiteR ρ eig hρ hρsum) p <
        (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε := by
  have hf := finiteVariational_ne_top_bot ρ eig hρ hρsum
  have hlt : variationalFunctional (finiteR ρ eig hρ hρsum) <
      ((variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε : ℝ) := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    exact_mod_cast (show (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal <
      (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε by linarith)
  obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
  have htop : entropyFunctional p ≠ ⊤ := by
    intro he
    simp only [he, EReal.top_add_coe, not_top_lt] at hp
  have hbot : entropyFunctional p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (entropyFunctional_nonneg p)
  refine ⟨p, (entropyFunctional p).toReal, (EReal.coe_toReal htop hbot).symm, ?_⟩
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add] at hp
  exact_mod_cast hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSpectrumVariationalUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_variational_upper_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      (variationalFunctional (finiteR ρ lam hρpos hρsum)).toReal + ε := by
  intro ε hε
  obtain ⟨p, S, hS, hp⟩ := exists_finiteEntropy_trial_near_finiteVariational
    ρ lam hρpos hρsum (half_pos hε)
  have hup := finiteSpectrum_meanPressure_upper hhaar hgauss N hN hNlim m μ hμinv
    eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ p S hS.le (ε / 2) (half_pos hε)
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper_oai := @OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper_oai
