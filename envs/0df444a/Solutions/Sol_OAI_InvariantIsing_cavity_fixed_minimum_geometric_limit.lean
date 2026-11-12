-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:20.679102+00:00
-- url     : https://prove2.me/submissions/88b40d94-c5ff-476a-8a36-d6dba68f995b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_base_perturbed_array_law
import Theorems.Thm_OAI_InvariantIsing_fullPerturbationPressure_variance
import Theorems.Thm_OAI_InvariantIsing_tensorDiagonal_fluctuation_at_minimum
import Theorems.Thm_OAI_InvariantIsing_tensorFiniteGG_individualDiagonal_bound
import Theorems.Thm_OAI_InvariantIsing_tensorFrozenCGF_centered_L1_bound
import Theorems.Thm_OAI_InvariantIsing_tensorFrozenCGF_mean
import Theorems.Thm_OAI_InvariantIsing_tensorGaussianCoordinatePressure_cost
import Theorems.Thm_OAI_InvariantIsing_tensorGrowingPerturbedArrayLaw_ward_limits

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
end OAICompat434

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

lemma convex_derivative_fluctuation {f g : ℝ → ℝ} {v s df dg C : ℝ}
    (hs : 0 < s) (hc : ConvexOn ℝ (Icc (v-s) (v+s)) f)
    (hd : HasDerivAt f df v)
    (hplus : g (v+s) - g v - s * dg ≤ C * s^2)
    (hminus : g (v-s) - g v + s * dg ≤ C * s^2) :
    |df-dg| ≤ C*s +
      (|f (v+s)-g (v+s)| + |f (v-s)-g (v-s)| + 2*|f v-g v|)/s := by
  have hv : v ∈ Icc (v-s) (v+s) := ⟨by linarith, by linarith⟩
  have hl := hc.slope_le_of_hasDerivAt (show v-s ∈ Icc (v-s) (v+s) from
    ⟨le_rfl, by linarith⟩) hv (by linarith : v-s < v) hd
  have hr := hc.le_slope_of_hasDerivAt hv (show v+s ∈ Icc (v-s) (v+s) from
    ⟨by linarith, le_rfl⟩) (by linarith : v < v+s) hd
  rw [slope_def_field] at hl hr
  have hl' : f v - f (v-s) ≤ df*s := by
    have := (div_le_iff₀ (show 0 < v-(v-s) by linarith)).mp hl
    nlinarith
  have hr' : df*s ≤ f (v+s)-f v := by
    have := (le_div_iff₀ (show 0 < v+s-v by linarith)).mp hr
    nlinarith
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [neg_mul, add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v-s)-g (v-s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v+s)-g (v+s)), abs_nonneg (f v-g v)]
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v+s)-g (v+s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v-s)-g (v-s)), abs_nonneg (f v-g v)]

lemma minimizer_quadratic_remainder {g : ℝ → ℝ} {v c a dg x : ℝ}
    (hmin : -g v + c*(v-a)^2 ≤ -g x + c*(x-a)^2)
    (hstationary : dg = 2*c*(v-a)) :
    g x - g v - (x-v)*dg ≤ c*(x-v)^2 := by
  rw [hstationary]
  nlinarith

open ProbabilityTheory Filter

lemma tendsto_central_second_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ) :
    Tendsto (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f v)) := by
  have ht := Real.taylor_tendsto (x₀ := v) (n := 2) convex_univ (mem_univ v) hf.contDiffOn
  simp only [nhdsWithin_univ] at ht
  have ht' : Tendsto (fun x => (f x-(f v+(x-v)*deriv f v+
      (x-v)^2/2*iteratedDeriv 2 f v))/(x-v)^2) (𝓝 v) (𝓝 0) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
      iteratedDeriv_one, smul_eq_mul]
    ring
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp := ht'.comp (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v)
  have hn := ht'.comp (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v)
  have he : (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2) =ᶠ[𝓝[≠] 0]
      (fun h => ((f (v+h)-(f v+(v+h-v)*deriv f v+
        (v+h-v)^2/2*iteratedDeriv 2 f v))/(v+h-v)^2)+
        ((f (v-h)-(f v+(v-h-v)*deriv f v+
        (v-h-v)^2/2*iteratedDeriv 2 f v))/(v-h-v)^2)+iteratedDeriv 2 f v) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : h ≠ 0 := hh
    field_simp [hh']
    ring
  simpa only [zero_add] using ((hp.add hn).add_const (iteratedDeriv 2 f v)).congr' he.symm

lemma integrable_limit_of_integral_bound {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hi : ∀ i, Integrable (F i) μ) (hnn : ∀ i ω, 0 ≤ F i ω)
    (hb : ∀ᶠ i in l, (∫ ω, F i ω ∂μ) ≤ C)
    (hl : ∀ ω, Tendsto (fun i => F i ω) l (𝓝 (g ω))) :
    Integrable g μ ∧ (∫ ω, g ω ∂μ) ≤ C := by
  have hgn (ω : Ω) : 0 ≤ g ω := ge_of_tendsto (hl ω) (Eventually.of_forall (fun i => hnn i ω))
  have hgm : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae l
    (fun i => (hi i).aestronglyMeasurable) (ae_of_all _ hl)
  have hC : 0 ≤ C := by
    obtain ⟨i, h⟩ := hb.exists
    exact (integral_nonneg (hnn i)).trans h
  have he : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (F i ω)) l ∂μ := by
        apply lintegral_congr
        intro ω
        exact (ENNReal.tendsto_ofReal (hl ω)).liminf_eq.symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (F i ω) ∂μ) l :=
        lintegral_liminf_le' (fun i => (hi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ _ := by
        refine liminf_le_of_frequently_le ?_ (isBoundedUnder_of ⟨0, fun _ => zero_le⟩)
        apply Eventually.frequently
        filter_upwards [hb] with i hiC
        rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (hnn i))]
        exact ENNReal.ofReal_le_ofReal hiC
  have hgi : Integrable g μ := (lintegral_ofReal_ne_top_iff_integrable hgm (ae_of_all _ hgn)).mp
    (ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgn) hgm]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

lemma central_second_difference_nonneg {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) (v h : ℝ) : 0 ≤ (f (v+h)+f (v-h)-2*f v)/h^2 := by
  have he := hc.2 (mem_univ (v+h)) (mem_univ (v-h))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hav : (1/2:ℝ) • (v+h)+(1/2:ℝ) • (v-h) = v := by simp only [smul_eq_mul] <;> ring
  rw [hav] at he
  simp only [smul_eq_mul] at he
  exact div_nonneg (by linarith) (sq_nonneg h)

theorem expected_curvature_at_minimum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ ω, ConvexOn ℝ univ (f ω)) (hd : ∀ ω, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  let F := fun h ω => (f ω (v+h)+f ω (v-h)-2*f ω v)/h^2
  have hF (h : ℝ) : Integrable (F h) μ := ((hi (v+h)).add (hi (v-h)) |>.sub
    ((hi v).const_mul 2)).div_const _
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v+h) ∂μ)+c*(v+h-a)^2 :=
    (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v).eventually hmin
  have hn : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v-h) ∂μ)+c*(v-h-a)^2 :=
    (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v).eventually hmin
  apply integrable_limit_of_integral_bound (l := 𝓝[≠] (0:ℝ)) hF
    (fun h ω => central_second_difference_nonneg (hc ω) v h) ?_
    (fun ω => tendsto_central_second_difference (hd ω) v)
  filter_upwards [hp, hn, self_mem_nhdsWithin] with h hp' hn' hz
  dsimp only [F]
  rw [integral_div, integral_sub (f := fun ω => f ω (v+h)+f ω (v-h))
    (g := fun ω => 2*f ω v) ((hi (v+h)).add (hi (v-h))) ((hi v).const_mul 2),
    integral_add (hi (v+h)) (hi (v-h)), integral_const_mul]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (show h ≠ 0 from hz))).mpr
  nlinarith

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

lemma probability_thermal_young {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ} (hY : MemLp Y 2 ν)
    {K : ℝ} (hK : 0 < K) :
    (∫ x, |Y x-(∫ y, Y y ∂ν)| ∂ν) ≤ (Var[Y; ν]+K^2)/(2*K) := by
  let m := ∫ y, Y y ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := ((hY.integrable (by norm_num)).sub (integrable_const m)).abs
  have hs : Integrable (fun x => (Y x-m)^2) ν := (hY.sub (memLp_const m)).integrable_sq
  calc
    _ ≤ ∫ x, ((Y x-m)^2+K^2)/(2*K) ∂ν := by
      apply integral_mono hi ((hs.add (integrable_const _)).div_const _)
      intro x
      change |Y x-m| ≤ ((Y x-m)^2+K^2)/(2*K)
      apply (le_div_iff₀ (by positivity : 0 < 2*K)).mpr
      nlinarith [sq_nonneg (|Y x-m|-K), sq_abs (Y x-m)]
    _ = _ := by
      rw [integral_div, integral_add hs (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [variance_eq_integral hY.aemeasurable]

end IsingPerceptron

namespace IsingPerceptron

theorem expected_curvature_at_minimum_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ univ (f ω))
    (hd : ∀ᵐ ω ∂μ, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  classical
  let f' : Ω → ℝ → ℝ := fun ω =>
    if ConvexOn ℝ univ (f ω) ∧ ContDiff ℝ 2 (f ω) then f ω else fun _ => 0
  have he : ∀ᵐ ω ∂μ, f' ω = f ω := by
    filter_upwards [hc,hd] with ω hω hω'
    simp [f',hω,hω']
  have hc' (ω) : ConvexOn ℝ univ (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.1
    · exact convexOn_const _ (convex_univ)   
  have hd' (ω) : ContDiff ℝ 2 (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.2
    · exact contDiff_const
  have hi' (t) : Integrable (fun ω => f' ω t) μ :=
    (hi t).congr (he.mono fun _ h => congrFun h.symm t)
  have heI (t) : (∫ ω, f' ω t ∂μ) = ∫ ω, f ω t ∂μ :=
    integral_congr_ae (he.mono fun _ h => congrFun h t)
  have hmin' : IsLocalMin (fun t => -(∫ ω, f' ω t ∂μ)+c*(t-a)^2) v := by
    simpa only [heI] using hmin
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum hc' hd' hi' hmin'
  have hed : (fun ω => iteratedDeriv 2 (f' ω) v) =ᵐ[μ]
      (fun ω => iteratedDeriv 2 (f ω) v) := he.mono fun _ h => congrArg (fun k => iteratedDeriv 2 k v) h
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem expected_tilted_variance_at_minimum_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω}
    (ν : Ω → Measure X) (Y : Ω → X → ℝ) {v c a : ℝ}
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (Y ω) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) μ ∧
      (∫ ω, Var[Y ω; (ν ω).tilted (v*Y ω ·)] ∂μ) ≤ 2*c := by
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum_ae
    (he.mono fun _ h => convexOn_cgf_of_all_exp h)
    (he.mono fun _ h => contDiff_cgf_of_all_exp h) hi hmin
  have hed : (fun ω => iteratedDeriv 2 (cgf (Y ω) (ν ω)) v) =ᵐ[μ]
      (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) := by
    filter_upwards [he] with ω hω
    exact (variance_tilted_mul (mem_interior_integrableExpSet_of_all hω v)).symm
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem integral_convex_derivative_fluctuation_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ → ℝ} {g : ℝ → ℝ}
    {v s dg C δ : ℝ} {df : Ω → ℝ} (hs : 0 < s)
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ (Icc (v-s) (v+s)) (f ω))
    (hd : ∀ᵐ ω ∂μ, HasDerivAt (f ω) (df ω) v)
    (hplus : g (v+s)-g v-s*dg ≤ C*s^2)
    (hminus : g (v-s)-g v+s*dg ≤ C*s^2)
    (hfplus : Integrable (fun ω => f ω (v+s)) μ)
    (hfminus : Integrable (fun ω => f ω (v-s)) μ)
    (hfv : Integrable (fun ω => f ω v) μ)
    (hm : AEStronglyMeasurable df μ)
    (hep : (∫ ω, |f ω (v+s)-g (v+s)| ∂μ) ≤ δ)
    (hem : (∫ ω, |f ω (v-s)-g (v-s)| ∂μ) ≤ δ)
    (hev : (∫ ω, |f ω v-g v| ∂μ) ≤ δ) :
    Integrable df μ ∧ (∫ ω, |df ω-dg| ∂μ) ≤ C*s+4*δ/s := by
  have hp : Integrable (fun ω => |f ω (v+s)-g (v+s)|) μ := (hfplus.sub (integrable_const (g (v+s)))).abs
  have hn : Integrable (fun ω => |f ω (v-s)-g (v-s)|) μ := (hfminus.sub (integrable_const (g (v-s)))).abs
  have hv : Integrable (fun ω => |f ω v-g v|) μ := (hfv.sub (integrable_const (g v))).abs
  let B := fun ω => C*s+(|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s
  have hi : Integrable B μ := (integrable_const (C*s)).add
    ((hp.add hn |>.add (hv.const_mul 2)).div_const s)
  have hb : ∀ᵐ ω ∂μ, |df ω-dg| ≤ B ω := by
    filter_upwards [hc,hd] with ω hω hω'
    exact convex_derivative_fluctuation hs hω hω' hplus hminus
  have hid : Integrable (fun ω => df ω-dg) μ :=
    hi.mono' (hm.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨?_,?_⟩
  · have hdi : Integrable (fun ω => (df ω-dg)+dg) μ := hid.add (integrable_const dg)
    simpa only [sub_add_cancel] using hdi
  have hib : Integrable (fun ω => (|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s) μ :=
    (hp.add hn |>.add (hv.const_mul 2)).div_const s
  have hic : Integrable (fun ω => |f ω (v+s)-g (v+s)|+|f ω (v-s)-g (v-s)|) μ := hp.add hn
  have hie : Integrable (fun ω => 2*|f ω v-g v|) μ := hv.const_mul 2
  calc
    _ ≤ ∫ ω, B ω ∂μ := integral_mono_ae hid.abs hi hb
    _ = C*s+((∫ ω, |f ω (v+s)-g (v+s)| ∂μ)+
        (∫ ω, |f ω (v-s)-g (v-s)| ∂μ)+2*(∫ ω, |f ω v-g v| ∂μ))/s := by
      dsimp [B]
      rw [integral_add (integrable_const _) hib,
        integral_div,integral_add hic hie,integral_add hp hn,integral_const_mul]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ ≤ C*s+4*δ/s := by gcongr; linarith

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

lemma integrate_thermal_majorant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T V : Ω → ℝ} {K C : ℝ}
    (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω) (hK : 0 < K)
    (hVi : Integrable V μ) (hVb : (∫ ω, V ω ∂μ) ≤ C)
    (hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K)) :
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (C+K^2)/(2*K) := by
  have hbI : Integrable (fun ω => (V ω+K^2)/(2*K)) μ :=
    (hVi.add (integrable_const _)).div_const _
  have hTi : Integrable T μ := hbI.mono' hT.aestronglyMeasurable
    (hb.mono fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hT0 ω)] using hω)
  refine ⟨hTi,(integral_mono_ae hTi hbI hb).trans ?_⟩
  rw [integral_div,integral_add hVi (integrable_const _),integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  exact div_le_div_of_nonneg_right (by linarith : (∫ ω, V ω ∂μ)+K^2 ≤ C+K^2) (by positivity)

lemma measurable_random_thermal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) (v : ℝ) :
    Measurable (fun ω => ∫ x, |Y (ω,x)-(∫ z, Y (ω,z) ∂(ν ω).tilted (fun z => v*Y (ω,z)))|
      ∂(ν ω).tilted (fun x => v*Y (ω,x))) := by
  have hm := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  exact measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z)
    (F := fun z : Ω × X => |Y z-(∫ x, Y (z.1,x) ∂(ν z.1).tilted (fun x => v*Y (z.1,x)))|)
    hν (hY.const_mul v) (hY.sub (hm.comp measurable_fst) |>.abs)

theorem expected_tilted_thermal_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a K : ℝ} (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (2*c+K^2)/(2*K) := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let V := fun ω => Var[(fun x => Y (ω,x)); (ν ω).tilted (fun x => v*Y (ω,x))]
  have hT : Measurable T := measurable_random_thermal hν hY v
  obtain ⟨hVi,hVb⟩ := expected_tilted_variance_at_minimum_ae (μ := μ) (v := v) (c := c) (a := a)
    ν (fun ω x => Y (ω,x)) he hi hmin
  change Integrable V μ at hVi
  change (∫ ω, V ω ∂μ) ≤ 2*c at hVb
  have hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K) := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) :=
      isProbabilityMeasure_tilted (hω v)
    exact probability_thermal_young (by simpa using (memLp_tilted_mul
      (mem_interior_integrableExpSet_of_all hω v) (2:NNReal))) hK
  exact integrate_thermal_majorant (μ := μ) hT
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hK hVi hVb hb

theorem expected_tilted_mean_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ : ℝ} (hs : 0 < s)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable m μ ∧ (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hm : Measurable m := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  apply integral_convex_derivative_fluctuation_ae (μ := μ) (v := v) (C := c)
    (dg := 2*c*(v-a)) (df := m) (δ := δ)
    (f := fun ω t => cgf (fun x => Y (ω,x)) (ν ω) t)
    (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ) hs
  · filter_upwards [he] with ω hω
    exact (convexOn_cgf_of_all_exp hω).subset (subset_univ _) (convex_Icc _ _)
  · filter_upwards [he] with ω hω
    have ht := mem_interior_integrableExpSet_of_all hω v
    have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
    rwa [← integral_tilted_mul_self ht] at hd
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v+s) (hmin (v+s) ⟨by linarith,le_rfl⟩) rfl
    simpa only [add_sub_cancel_left] using h
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v-s) (hmin (v-s) ⟨le_rfl,by linarith⟩) rfl
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  · exact hi _
  · exact hi _
  · exact hi _
  · exact hm.aestronglyMeasurable
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)

lemma probability_energy_triangle {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ}
    (hY : Integrable Y ν) (b : ℝ) :
    (∫ x, |Y x-b| ∂ν) ≤ (∫ x, |Y x-(∫ z, Y z ∂ν)| ∂ν)+|(∫ z, Y z ∂ν)-b| := by
  let m := ∫ z, Y z ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := (hY.sub (integrable_const m)).abs
  calc
    _ ≤ ∫ x, |Y x-m|+|m-b| ∂ν := by
      apply integral_mono ((hY.sub (integrable_const b)).abs) (hi.add (integrable_const _))
      intro x
      exact abs_sub_le (Y x) m b
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp [m]

theorem expected_tilted_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable E μ ∧ (∫ ω, E ω ∂μ) ≤ (2*c+K^2)/(2*K)+c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hloc : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v := by
    filter_upwards [Icc_mem_nhds (by linarith : v-s < v) (by linarith : v < v+s)] with t ht
    exact hmin t ht
  obtain ⟨hTi,hTb⟩ := expected_tilted_thermal_at_minimum hν hY hK he hi hloc
  obtain ⟨hmi,hmb⟩ := expected_tilted_mean_at_minimum hν hY hs he hi hmin hconc
  change Integrable T μ at hTi
  change (∫ ω, T ω ∂μ) ≤ _ at hTb
  change Integrable m μ at hmi
  change (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ _ at hmb
  have hEi : Measurable E := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := fun z => |Y z-2*c*(v-a)|)
    hν (hY.const_mul v) (hY.sub_const _ |>.abs)
  have hb : ∀ᵐ ω ∂μ, E ω ≤ T ω+|m ω-2*c*(v-a)| := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) := isProbabilityMeasure_tilted (hω v)
    exact probability_energy_triangle
      ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hω v) (1:NNReal)).integrable (by norm_num)) _
  have hbi : Integrable (fun ω => T ω+|m ω-2*c*(v-a)|) μ :=
    hTi.add ((hmi.sub (integrable_const _)).abs)
  have hE : Integrable E μ := hbi.mono' hEi.aestronglyMeasurable
    (hb.mono fun ω hω => by
      have hnonneg : 0 ≤ E ω := integral_nonneg (fun _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hω)
  refine ⟨hE,(integral_mono_ae hE hbi hb).trans ?_⟩
  have hai : Integrable (fun ω => |m ω-2*c*(v-a)|) μ := (hmi.sub (integrable_const _)).abs
  rw [integral_add hTi hai]
  linarith

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

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true, if_true] <;> ring
  · simp only [h,ite_false, if_false,zero_mul]

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

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

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

lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma perturbationScale_nonneg (N : ℕ) : 0 ≤ perturbationScale N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
namespace IsingPerceptron

lemma measurable_gaussianNamespaceJoin (j : ℕ) : Measurable (gaussianNamespaceJoin j) := by
  apply Measurable.of_eval
  intro i
  by_cases h : (Nat.unpair i).1 = j
  · simp only [gaussianNamespaceJoin,dite_eq_left h]
    fun_prop
  · simp only [gaussianNamespaceJoin,dite_eq_right h]
    fun_prop

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma update_abs_le_two {N : ℕ} {u : Fin N → ℝ} (hu : ∀ j, |u j| ≤ 2)
    (j : Fin N) {v : ℝ} (hv : |v| ≤ 2) : ∀ k, |Function.update u j v k| ≤ 2 := by
  intro k
  by_cases hk : k = j
  · subst k; simpa using hv
  · simpa [hk] using hu k

lemma perturbationAmplitude_pos {N : ℕ} (hN : 0 < N) (j : ℕ) :
    0 < perturbationAmplitude N j := by
  unfold perturbationAmplitude perturbationScale perturbationWeight
  positivity

end IsingPerceptron

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

lemma perturbationAmplitude_sq (N j : ℕ) :
    (perturbationAmplitude N j)^2 = N*(perturbationScale N)^2*(perturbationWeight j)^2 := by
  unfold perturbationAmplitude
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

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

lemma tensorPerturbationAmplitude_update {N : ℕ} (u : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    tensorPerturbationAmplitude N (Function.update u j t) =
      Function.update (tensorPerturbationAmplitude N u) j (perturbationAmplitude N j * t) := by
  classical
  funext i
  by_cases hi : i = j
  · subst i
    simp only [tensorPerturbationAmplitude, Function.update_self]
  · simp only [tensorPerturbationAmplitude, Function.update_of_ne hi]

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
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedGGFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched G G Finite. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma newReplicaEmbedding_injective (k : ℕ) (e : Equiv.Perm (Fin k)) :
    Function.Injective (newReplicaEmbedding k e) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · exact fun _ => rfl
    · intro hab
      have hlt := (e b).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      have hlt := (e a).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
    · intro hab
      apply congrArg Fin.succ
      apply e.injective
      apply Fin.val_injective
      exact hab

lemma sum_nonzero_permutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (f : Fin (m+1) → ℝ) :
    (∑ l : Fin m, f (e l.succ)) = ∑ j ∈ Finset.univ.erase (e 0), f j := by
  classical
  have he := Equiv.sum_comp e f
  rw [Fin.sum_univ_succ,← Finset.add_sum_erase _ _ (Finset.mem_univ (e 0))] at he
  exact add_left_cancel he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

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

lemma treeOverlap_self (n : ℕ) (x : LabeledLeaf n) : treeOverlap n x x = (n:ℝ)/(n+1:ℕ) := by
  simp only [treeOverlap,labeledCommonDepth_self]

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

lemma projectedOverlap_self_nonneg {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Spin N) : 0 ≤ projectedOverlap U I σ σ := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapBounds
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent bounds for projected spectral overlap kernels. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma projectedOverlap_self_le_one {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ : Spin N) :
    projectedOverlap U I σ σ ≤ 1 :=
  (le_abs_self _).trans (projectedOverlap_abs_le_one U I σ σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
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

theorem jointSpectralMonomialCoefficients_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x y : Spin N × IsingPerceptron.LabeledLeaf n) :
    IsingPerceptron.cylinderCross (jointSpectralMonomialCoefficients U I d n r x)
      (jointSpectralMonomialCoefficients U I d n r y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a) *
        IsingPerceptron.treeOverlap n x.2 y.2 ^ r := by
  unfold jointSpectralMonomialCoefficients
  rw [IsingPerceptron.treeField_path_cross n x.2 y.2
    (IsingPerceptron.monomialPath_monotone n r)
    (IsingPerceptron.monomialPath_nonneg n r 0), spectralMonomialFeature_cross]
  exact mul_comm _ _

theorem jointSpectralMonomialCoefficients_variance_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × IsingPerceptron.LabeledLeaf n) :
    (jointSpectralMonomialCoefficients U I d n r x).sum (fun _ c => c ^ 2) ≤ 1 := by
  rw [← IsingPerceptron.cylinderCross_self, jointSpectralMonomialCoefficients_cross]
  have ht : 0 ≤ IsingPerceptron.treeOverlap n x.2 x.2 ^ r := by
    unfold IsingPerceptron.treeOverlap
    positivity
  have htl : IsingPerceptron.treeOverlap n x.2 x.2 ^ r ≤ 1 := by
    simpa only [IsingPerceptron.treeOverlap, IsingPerceptron.labeledCommonDepth_self,
      IsingPerceptron.monomialPath] using IsingPerceptron.monomialPath_diag_le_one n r
  exact (mul_le_mul ((le_abs_self _).trans (spectralMonomial_abs_le_one U I d x.1 x.1))
    htl ht (by norm_num)).trans_eq (one_mul 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly measurable Haar-dependent Gaussian tensor fields. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cylinderField_add (a b : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (a + b) g = cylinderField a g + cylinderField b g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma cylinderField_single (j : ℕ) (c : ℝ) (g : ℕ → ℝ) :
    cylinderField (Finsupp.single j c) g = c * g j :=
  Finsupp.sum_single_index (zero_mul _)

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderField]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, cylinderField_add, ih]

lemma cylinderField_featureCoefficients {J : Type*} [Fintype J]
    (tag : J → ℕ) (c : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients tag c) g = ∑ j, c j * g (tag j) := by
  rw [featureCoefficients, cylinderField_finset_sum]
  simp_rw [cylinderField_single]

lemma measurable_jointSpectralMonomialField {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (jointSpectralMonomialCoefficients (specialRotation p.1) I d n r x) p.2) := by
  unfold jointSpectralMonomialCoefficients treeFieldCoefficients
  simp_rw [cylinderField_featureCoefficients]
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_spectralMonomialFeature I d x.1 j.2).comp measurable_fst |>.const_mul _).mul
    ((measurable_pi_apply _).comp measurable_snd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma measurable_tensorFrozenBaseEnergy {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (Function.uncurry (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j)) := by
  change Measurable (fun p : TensorFrozenData N n j × (Spin N × LabeledLeaf n) =>
    tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j p.1 p.2)
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun ω : TensorFrozenData N n j =>
    rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (gaussianNamespaceJoin (j + 1) (0, ω.2)))
  have hrot0 : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  have hrot : Measurable (fun ω : TensorFrozenData N n j => rotatedEnergy eig (specialRotation ω.1.1) x.1) :=
    hrot0.comp measurable_fst.fst
  have hm : Measurable (fun ω : TensorFrozenData N n j =>
      (ω.1.1, gaussianNamespaceJoin (j + 1) (0, ω.2))) :=
    measurable_fst.fst.prodMk ((measurable_gaussianNamespaceJoin (j + 1)).comp
      (measurable_const.prodMk measurable_snd))
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hfield0 := measurable_tensorNamespacedFields_joint I degree
    (Function.update amplitude j 0) n v x
  have hfield : Measurable (fun ω : TensorFrozenData N n j =>
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n v x) (gaussianNamespaceJoin (j + 1) (0, ω.2))) := by
    convert hfield0.comp hm using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  convert (hrot.add_const (fieldEnergy c x.1)).add hfield using 1
  all_goals try with_reducible_and_instances rfl

lemma measurable_tensorFrozenReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (tensorFrozenReference eig c I degree amplitude n treeDegree h j) := by
  have : ∀ ω : TensorFrozenData N n j, IsProbabilityMeasure
      ((labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ∘ (fun ω : TensorFrozenData N n j => ω.1.2)) ω) :=
    fun ω => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.1.2)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact measurable_gibbsProbability
    (H := Function.uncurry (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j))
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd)
    (measurable_tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureCoordinateMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of a pressure-coordinate minimum to its selected-field CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma pressureCoordinate_minimum_rescale {M L : ℝ → ℝ} {N a w s c : ℝ}
    (hN : 0 ≤ N) (ha : 0 < a) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (hlo : 1 ≤ w - s) (hhi : w + s ≤ 2)
    (hmean : ∀ v ∈ Set.Icc (1 : ℝ) 2, L (a * v) = N * (M v - M 0))
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -M w + c * (w - 3 / 2) ^ 2 ≤ -M v + c * (v - 3 / 2) ^ 2) :
    ∀ t ∈ Set.Icc (a * w - a * s) (a * w + a * s),
      -L (a * w) + (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 ≤
      -L t + (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 := by
  intro t ht
  have htv : t / a ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ ha).mpr
      nlinarith [ht.1]
    · apply (div_le_iff₀ ha).mpr
      nlinarith [ht.2]
  have hm := hmean (t / a) htv
  rw [mul_div_cancel₀ _ ha.ne'] at hm
  rw [hm, hmean w hw]
  have hc := mul_le_mul_of_nonneg_left (hmin (t / a) htv) hN
  have he1 : (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 =
      N * (c * (w - 3 / 2) ^ 2) := by field_simp
  have he2 : (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 =
      N * (c * (t / a - 3 / 2) ^ 2) := by field_simp
  rw [he1, he2]
  linarith

/-- Comparing a Gaussian-coordinate minimum with its centered choice
puts it in the interior, using the Gaussian variance cap of the frozen field. -/
lemma gaussianCoordinate_minimum_penalty {N : ℕ} (hN : 0 < N) (j : Fin N)
    (M : ℝ → ℝ) (u : ℝ) (hu : |u| ≤ 2)
    (hcost : 0 ≤ M (3 / 2) - M 0 ∧ M u - M 0 ≤ (perturbationAmplitude N j * u) ^ 2 / (2 * N))
    (hmin : -M u + perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      -M (3 / 2) + perturbationWeight j * (3 / 2 - 3 / 2) ^ 2) :
    (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := perturbationWeight_pos j
  have ha := perturbationAmplitude_sq N j
  have hu2 : u ^ 2 ≤ 4 := by
    have hb := abs_le.mp hu
    nlinarith [sq_nonneg (u + 2), sq_nonneg (u - 2)]
  have hanu : (perturbationAmplitude N j * u) ^ 2 / (2 * N) ≤
      2 * perturbationScale N ^ 2 * perturbationWeight j ^ 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (N : ℝ) by positivity)).mpr
    rw [mul_pow, ha]
    nlinarith [mul_le_mul_of_nonneg_left hu2
      (show 0 ≤ (N : ℝ) * perturbationScale N ^ 2 * perturbationWeight j ^ 2 by positivity)]
  have hm : perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      perturbationWeight j * (2 * perturbationScale N ^ 2 * perturbationWeight j) := by
    nlinarith [hcost.1, hcost.2]
  exact (mul_le_mul_iff_right₀ hw).mp hm

lemma gaussianCoordinate_minimum_interior {N : ℕ} (j : Fin N) {u s : ℝ}
    (hpen : (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j)
    (he : perturbationScale N ≤ 1 / 8) (hs : s ≤ 1 / 4) :
    1 ≤ u - s ∧ u + s ≤ 2 := by
  have he0 := perturbationScale_nonneg N
  have hw := perturbationWeight_le_one j
  have hbnd : (u - 3 / 2) ^ 2 ≤ 1 / 32 := by
    have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * perturbationScale N ^ 2 by positivity)
    nlinarith [sq_nonneg (perturbationScale N - 1 / 8)]
  constructor <;> nlinarith [sq_nonneg (u - 3 / 2 - 1 / 4), sq_nonneg (u - 3 / 2 + 1 / 4)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomCoefficientGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! GG estimates for Haar-dependent Gaussian perturbation tensors. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

variable [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

/-- The local-minimum fluctuation estimate applies to the actual
Haar-dependent Gaussian fields, rather than requiring fixed coefficients. -/
theorem randomCoefficient_energy_at_minimum (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Set.Icc (v - s) (v + s),
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) v
        ∂P.prod gaussianCoordinates) + c * (v - a) ^ 2 ≤
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
        ∂P.prod gaussianCoordinates) + c * (t - a) ^ 2)
    (hconc : ∀ t ∈ ({v - s, v, v + s} : Set ℝ),
      (∫ z : Ω × (ℕ → ℝ), |cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t -
        (∫ z' : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z'.1 x) z'.2) (ν z'.1) t
          ∂P.prod gaussianCoordinates)| ∂P.prod gaussianCoordinates) ≤ δ) :
    let E := fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A z.1 x) z.2 - 2 * c * (v - a)|
        ∂(ν z.1).tilted (fun x => v * cylinderField (A z.1 x) z.2)
    Integrable E (P.prod gaussianCoordinates) ∧
      (∫ z, E z ∂P.prod gaussianCoordinates) ≤ (2 * c + K ^ 2) / (2 * K) + c * s + 4 * δ / s := by
  exact expected_tilted_energy_at_minimum (μ := P.prod gaussianCoordinates)
    (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (Y := fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2)
    (hν.comp measurable_fst) hAm hs hK
    (randomCoefficient_all_exp_ae hν A hAm hA)
    (integrable_randomCoefficient_cgf hν A hAm hA) hmin hconc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian GG bound specialized to the manuscript's spectral/tree kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_spectralPerturbationFields {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (spectralPerturbationCoefficients U I d n r p.1.1 p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have h := (measurable_jointSpectralMonomialField I d n r x).comp
    (hU.prodMap measurable_id)
  simpa only [spectralPerturbationCoefficients, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoordinateMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor coordinates at a penalized pressure minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- At a deterministic minimum of the actual Gaussian coordinate, its
Gibbs energy concentrates around the derivative of the quadratic penalty. -/
theorem tensorGaussianCoordinate_energy_at_minimum {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin N)
    (w s K B : ℝ) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (he : perturbationScale N ≤ 1 / 8) (hs : 0 < s) (hs' : s ≤ 1 / 4) (hK : 0 < K)
    (hF : ∀ v : ℝ, |v| ≤ 2 →
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ v : ℝ, |v| ≤ 2 →
      variance (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ B)
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j w +
        perturbationWeight j * (w - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j v +
        perturbationWeight j * (v - 3 / 2) ^ 2) :
    let a := perturbationAmplitude N j
    let c₀ := N * perturbationWeight j / a ^ 2
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let A := fun ω : TensorFrozenData N n j =>
      jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (r j)
    let ν := tensorFrozenReference eig c I degree amplitude n r h j
    let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
      |cylinderField (A p.1 x) p.2 - 2 * c₀ * (a * w - a * (3 / 2))|
        ∂(ν p.1).tilted (fun x => a * w * cylinderField (A p.1 x) p.2)
    Integrable E Q ∧ (∫ p, E p ∂Q) ≤
      (2 * c₀ + K ^ 2) / (2 * K) + c₀ * (a * s) + 4 * (2 * N * Real.sqrt B) / (a * s) := by
  intro a c₀ Q A ν E
  let M := tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j
  let L := fun t => ∫ p, tensorFrozenCGF eig c I degree amplitude n r h j t p ∂Q
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hwa : |w| ≤ 2 := abs_le.mpr ⟨by linarith [hw.1], hw.2⟩
  have hFa (v : ℝ) (hva : |v| ≤ 2) : ∀ t : ℝ, t = a * v ∨ t = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j t) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) := by
    intro t ht
    rcases ht with rfl | rfl
    · exact hF v hva
    · simpa only [mul_zero] using hF 0 (by norm_num)
  have hmean (v : ℝ) (hva : |v| ≤ 2) : L (a * v) = N * (M v - M 0) := by
    simpa only [L, M, Q, tensorGaussianCoordinatePressure, mul_zero] using
      tensorFrozenCGF_mean hN μ eig c I degree amplitude n b r h hh h0 hb j (a * v) (hFa v hva)
  have hc₀ := tensorGaussianCoordinatePressure_cost hN μ eig c I degree amplitude n b r h hh h0 hb j
    (3 / 2) (hFa (3 / 2) (by norm_num))
  have hcw := tensorGaussianCoordinatePressure_cost hN μ eig c I degree amplitude n b r h hh h0 hb j
    w (hFa w hwa)
  have hpen := gaussianCoordinate_minimum_penalty hN j M w hwa ⟨hc₀.1, hcw.2⟩
    (hmin (3 / 2) (by constructor <;> norm_num))
  obtain ⟨hlo, hhi⟩ := gaussianCoordinate_minimum_interior j hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) ha hw hlo hhi
    (fun v hv => hmean v (abs_le.mpr ⟨by linarith [hv.1], hv.2⟩)) hmin
  have hconc (t : ℝ) (ht : t ∈ ({a * w - a * s, a * w, a * w + a * s} : Set ℝ)) :
      (∫ p, |tensorFrozenCGF eig c I degree amplitude n r h j t p - L t| ∂Q) ≤
        2 * N * Real.sqrt B := by
    have hti : t ∈ Set.Icc (a * w - a * s) (a * w + a * s) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos ha hs]
    have htv : t / a ∈ Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ ha).mpr
        nlinarith [hti.1]
      · apply (div_le_iff₀ ha).mpr
        nlinarith [hti.2]
    have hta : |t / a| ≤ 2 := abs_le.mpr ⟨by linarith [htv.1], htv.2⟩
    have htF : ∀ q : ℝ, q = t ∨ q = 0 →
        MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j q) n) 2
          (μ.prod (tensorRootTreeLaw I degree n b
            (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) := by
      simpa only [mul_div_cancel₀ _ ha.ne'] using hFa (t / a) hta
    have htV : ∀ q : ℝ, q = t ∨ q = 0 →
        variance (tensorDisorderPressure eig c I degree (Function.update amplitude j q) n)
          (μ.prod (tensorRootTreeLaw I degree n b
            (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ B := by
      intro q hq
      rcases hq with hq | hq
      · rw [hq]
        simpa only [a, mul_div_cancel₀ _ ha.ne'] using hv (t / a) hta
      · rw [hq]
        simpa only [mul_zero] using hv 0 (by norm_num)
    exact (tensorFrozenCGF_centered_L1_bound hN μ eig c I degree amplitude n b r h hh h0 hb j
      t B htF htV).2
  exact randomCoefficient_energy_at_minimum
    (P := tensorFrozenLaw μ n b j) (measurable_tensorFrozenReference eig c I degree amplitude n r h j) A
    (measurable_spectralPerturbationFields (fun ω : TensorFrozenData N n j => ω.1.1)
      measurable_fst.fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one (specialRotation ω.1.1)
      I (degree j) n (r j) x) (mul_pos ha hs) hK hlocal hconc

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact deterministic centers without assuming constant finite self-overlap. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma abs_sub_spectralDiagonalCenter_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) :
    |x - spectralDiagonalCenter b| ≤ |x - b| := by
  by_cases hb : b ≤ 0
  · rw [spectralDiagonalCenter, min_eq_right (by linarith : b ≤ 1), max_eq_left hb,
      sub_zero, abs_of_nonneg hx.1, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - b)]
    linarith
  · by_cases hb' : 1 ≤ b
    · rw [spectralDiagonalCenter, min_eq_left hb', max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0), abs_of_nonpos (by linarith [hx.2] : x - b ≤ 0)]
      linarith
    · rw [spectralDiagonalCenter, min_eq_right (le_of_not_ge hb'), max_eq_right (le_of_not_ge hb)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorObservableAverageLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both frozen coordinates control observables in the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_tensorNamespacedObservableMean {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
      ∂tensorNamespacedReference eig c I degree amplitude n r h p) := by
  have hm := measurable_random_tilted_integral
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h)
    (H := fun _ => 0) measurable_const
    (hD.comp (measurable_fst.fst.fst.prodMk measurable_snd))
  change Measurable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
    ∂(tensorNamespacedReference eig c I degree amplitude n r h p).tilted 0) at hm
  simpa only [tilted_zero] using hm

lemma tensorNamespacedObservableAverage_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : ∀ U x, |D U x| ≤ B) :
    Integrable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x
      ∂tensorNamespacedReference eig c I degree amplitude n r h p)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  apply Integrable.of_bound
    (measurable_tensorNamespacedObservableMean eig c I degree amplitude n r h D hD).aestronglyMeasurable B
  exact ae_of_all _ fun p => by
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := tensorNamespacedReference eig c I degree amplitude n r h p)
        (f := fun x => D p.1.1 x) (C := B) (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs] using hB p.1.1 x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalError
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full-model monomial diagonal error is controlled coordinate by coordinate. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_spectralDiagonalDeviation {N : ℕ} (I : Finset (Fin N)) (n : ℕ) (b : ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (Spin N × LabeledLeaf n) =>
      |projectedOverlap (specialRotation p.1) I p.2.1 p.2.1 - b|) := by
  apply measurable_from_prod_countable_left
  intro x
  exact ((measurable_projectedOverlap I x.1 x.1).sub_const b).abs

lemma spectralDiagonalDeviation_abs_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (b : ℝ) (σ : Spin N) :
    abs (abs (projectedOverlap U I σ σ - b)) ≤ 1 + |b| := by
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (projectedOverlap_abs_le_one _ _ _ _) le_rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGGMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! GG error rates at actual finite Gaussian-coordinate pressure minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorGaussianGG_at_minimum {N m q : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin N)
    (w L : ℝ) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (he : perturbationScale N ≤ 1 / 8) (hs : contactStep N ≤ 1 / 4)
    (hamp : amplitude j = perturbationAmplitude N j * w)
    (hF : ∀ v : ℝ, |v| ≤ 2 →
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ v : ℝ, |v| ≤ 2 →
      variance (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ L / N)
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j w +
        perturbationWeight j * (w - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j v +
        perturbationWeight j * (v - 3 / 2) ^ 2)
    (C : ℝ) (hC : 0 ≤ C)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a) :
    |tensorSpectralGGResidual μ eig c I degree amplitude n b r h j D| ≤
      contactGGRate N j L C + 2 * C * ∑ a, (degree j a : ℝ) * δ a := by
  let a := perturbationAmplitude N j
  let c₀ := N * perturbationWeight j / a ^ 2
  let θ := 1 / perturbationScale N
  let G := (2 * c₀ + θ ^ 2) / (2 * θ) + c₀ * (a * contactStep N) +
    4 * (2 * N * Real.sqrt (L / N)) / (a * contactStep N)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < θ := one_div_pos.mpr he'
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hc₀ : 0 < c₀ := div_pos (mul_pos hn (perturbationWeight_pos j)) (sq_pos_of_pos ha)
  have hG : 0 ≤ G := by dsimp only [G] <;> positivity
  have hE := tensorGaussianCoordinate_energy_at_minimum hN μ eig c I degree amplitude n b r h hh h0 hb j
    w (contactStep N) θ (L / N) hw he hs' hs hθ hF hv hmin
  have hamp' : 0 < |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha]
    exact mul_pos ha (abs_pos.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)))
  have hEa :
      let A := spectralPerturbationCoefficients (fun ω : TensorFrozenData N n j => ω.1.1)
        I (degree j) n (r j)
      let ν := tensorFrozenReference eig c I degree amplitude n r h j
      let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - 2 * c₀ * (a * w - a * (3 / 2))|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ≤ G := by
    simpa only [hamp, spectralPerturbationCoefficients, a, c₀, G] using hE
  have hgg := tensorFiniteGG_individualDiagonal_bound μ eig c I degree amplitude n b r h hh h0 j
    (2 * c₀ * (a * w - a * (3 / 2))) G C hC hamp' D hD hDb center δ hδ hEa
  have hampl : a ≤ |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)]
    nlinarith [hw.1]
  calc
    _ ≤ 2 * C * (G / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := hgg
    _ ≤ 2 * C * (G / a + ∑ a, (degree j a : ℝ) * δ a) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_left hG ha hampl) le_rfl) (mul_nonneg (by norm_num) hC)
    _ = _ := by unfold contactGGRate; dsimp only [G, c₀, θ, a] <;> ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_FullPerturbationMinima
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For the complete perturbation, both coordinate minima force the
Ghirlanda–Guerra errors to vanish. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- For the manuscript's full finite perturbation, genuine pressure-coordinate
minima give a GG residual bounded by two explicit rates tending to zero. -/
theorem fullPerturbationPressure_minimumGG (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
        ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
      perturbationScale N ≤ 1 / 32 → contactStep N ≤ 1 / 4 →
      (∀ (j : Fin N) (w : ℝ), w ∈ Set.Icc (1 : ℝ) 2 →
        -M u v t + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
        -M (Function.update u j w) v t + perturbationWeight j * (w - 3 / 2) ^ 2) →
      (∀ (a : Fin m) (w : ℝ), w ∈ Set.Icc (1 : ℝ) 2 →
        -M u v t + (v a - 3 / 2) ^ 2 ≤ -M u (Function.update v a w) t + (w - 3 / 2) ^ 2) →
      ∀ j : Fin N, ∀ q : ℕ, ∀ B : ℝ, 0 ≤ B →
      ∀ D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ,
      Measurable (Function.uncurry D) → (∀ U σ, |D U σ| ≤ B) →
      |tensorSpectralGGResidual μ (diagonalPerturbedEigenvalues eig I v t) c I degree
        (tensorPerturbationAmplitude N u) n b treeDegree h j D| ≤
        contactGGRate N j L B +
          2 * B * (∑ a, (degree j a : ℝ)) * diagonalContactRate N L := by
  obtain ⟨C, hC, hvar⟩ := fullPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    M degree treeDegree L he hs hminu hminv j q B hB D hD hDb
  let : IsProbabilityMeasure μ := hμ
  have hNp : 0 < N := by omega
  have hua : ∀ j, |u j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1], (hu j).2⟩
  have hva : ∀ a, |v a| ≤ 2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1], (hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  let R := μ.prod (tensorRootTreeLaw I degree n b
    (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
    (tensorPathProfile I degree n treeDegree h 0))
  have hgu (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (Function.update amplitude j (perturbationAmplitude N j * w)) n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (Function.update amplitude j (perturbationAmplitude N j * w)) n) R ≤ L / N := by
    simpa only [tensorPerturbationAmplitude_update] using
      hvar N hN μ hμ hμinv m eig c K hK heig I (Function.update u j w)
        (update_abs_le_two hua j hw) v hva t ht n b hb h hh h0 H hH
  have hgv (a : Fin m) (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) R ≤ L / N := by
    exact hvar N hN μ hμ hμinv m eig c K hK heig I u hua (Function.update v a w)
      (update_abs_le_two hva a hw) t ht n b hb h hh h0 H hH
  have hdiag (a : Fin m) : tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amplitude n b treeDegree h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - diagonalMinimumCenter N (v a)|) ≤
      diagonalContactRate N L := by
    have hd := tensorDiagonal_fluctuation_at_minimum hNp μ eig c I degree amplitude n b treeDegree h
      hh h0 hb v t a (v a) L (hv a) he hs (fun w hw => (hgv a w hw).1)
      (fun w hw => (hgv a w hw).2) (by
        dsimp only
        intro w hw
        simpa only [M, tensorPerturbationPressureMean, Function.update_eq_self] using hminv a w hw)
    simpa only [Function.update_eq_self, diagonalMinimumCenter] using hd
  have hgm : ∀ w ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
        n b treeDegree h j (u j) + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
        n b treeDegree h j w + perturbationWeight j * (w - 3 / 2) ^ 2 := by
    intro w hw
    simpa only [amplitude, M, tensorPerturbationPressureMean, tensorGaussianCoordinatePressure, ← tensorPerturbationAmplitude_update,
      Function.update_eq_self] using hminu j w hw
  have hg := tensorGaussianGG_at_minimum hNp μ (diagonalPerturbedEigenvalues eig I v t) c I degree
    amplitude n b treeDegree h hh h0 hb j (u j) L (hu j) (by linarith) hs rfl
    (fun w hw => (hgu w hw).1) (fun w hw => (hgu w hw).2) hgm B hB D hD hDb
    (fun a => diagonalMinimumCenter N (v a)) (fun _ => diagonalContactRate N L) hdiag
  simpa only [← Finset.sum_mul, mul_assoc] using hg

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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
theorem tensorNamespacedArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h D := by
  rw [tensorNamespacedArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold tensorNamespacedReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := tensorNamespacedReference eig c I degree amplitude n r h p
  have ht := integral_map hm.aemeasurable (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [replica_injective_map ν ι hi] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ σ, D p.1.1 σ ∂Measure.pi (fun _ : Fin z => ν)
  simp_rw [he]
  exact ht.symm

private lemma measurable_finiteReplicaBlock {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (J : Ω → X → X → Y)
    (hJ : Measurable (fun p : Ω × (X × X) => J p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Ω × (Fin z → X) => fun i j : Fin z => J p.1 (p.2 i) (p.2 j)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hi : Measurable (fun p : Ω × (Fin z → X) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hj : Measurable (fun p : Ω × (Fin z → X) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact hJ.comp (measurable_fst.prodMk (hi.prodMk hj))

lemma measurable_finiteSpectralBlock {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × (Fin z → Spin N × LabeledLeaf n) =>
      finiteSpectralBlock (specialRotation p.1) I n p.2) := by
  exact measurable_finiteReplicaBlock (fun U => spectralJointEntry (specialRotation U) I n)
    (measurable_spectralJointEntry I n)

private lemma measurable_permutedReplicaTest {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (B : Ω → (Fin z → X) → Y) (hB : Measurable (Function.uncurry B))
    (e : Equiv.Perm (Fin z)) (D : Y → ℝ) (hD : Measurable D) :
    Measurable (Function.uncurry (fun U σ => D (B U (σ ∘ e.symm)))) := by
  have hm : Measurable (fun p : Ω × (Fin z → X) => (p.1, p.2 ∘ e.symm)) :=
    measurable_fst.prodMk (Measurable.of_eval fun i => (measurable_pi_apply (e.symm i)).comp measurable_snd)
  exact hD.comp (hB.comp hm)

lemma measurable_permutedSpectralBlockTest {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (hD : Continuous D) :
    Measurable (Function.uncurry (permutedSpectralBlockTest I n e D)) := by
  exact measurable_permutedReplicaTest (fun U => finiteSpectralBlock (specialRotation U) I n)
    (measurable_finiteSpectralBlock I n) e D hD.measurable

lemma permutedSpectralBlockTest_embedding {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (U : SpecialOrthogonal N)
    (σ : ℕ → Spin N × LabeledLeaf n) :
    permutedSpectralBlockTest I n e D U (fun j => σ (e j)) =
      D (spectralBlockView (m + 1) z (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) := by
  apply congrArg D
  funext i j
  simp only [finiteSpectralBlock, Function.comp_apply,
    Equiv.apply_symm_apply, spectralBlockView]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayDiagonal
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual array self-overlap deviations, with compact deterministic centers. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorNamespacedObservableAverage_mono {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D E : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hE : Measurable (Function.uncurry E))
    {B C : ℝ} (hDb : ∀ U x, |D U x| ≤ B) (hEb : ∀ U x, |E U x| ≤ C)
    (hDE : ∀ U x, D U x ≤ E U x) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h D ≤
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h E := by
  apply integral_mono
    (tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h D hD hDb)
    (tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h E hE hEb)
  intro p
  apply integral_mono
    (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hDb p.1.1 x))
    (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hEb p.1.1 x))
  exact hDE p.1.1

lemma tensorSpectralDiagonal_clipping {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (a : Fin m) (center : ℝ) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - spectralDiagonalCenter center|) ≤
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) := by
  exact tensorNamespacedObservableAverage_mono μ eig c I degree amplitude n b r h _ _
    (measurable_spectralDiagonalDeviation (I a) n _) (measurable_spectralDiagonalDeviation (I a) n _)
    (fun U x => spectralDiagonalDeviation_abs_le (specialRotation U) (I a) _ x.1)
    (fun U x => spectralDiagonalDeviation_abs_le (specialRotation U) (I a) _ x.1)
    (fun U x => abs_sub_spectralDiagonalCenter_le
      ⟨projectedOverlap_self_nonneg _ _ _, projectedOverlap_self_le_one _ _ _⟩ center)

theorem tensorNamespacedArrayLaw_observable_test {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) (i : ℕ)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n),
      F (fun ij : ℕ × ℕ => spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (σ i)) :
    (∫ x, F x ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h D := by
  rw [tensorNamespacedArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold tensorNamespacedObservableAverage
  apply integral_congr_ae
  filter_upwards [] with p
  let ν := tensorNamespacedReference eig c I degree amplitude n r h p
  have ht := integral_map (measurable_pi_apply i).aemeasurable
    (μ := Measure.infinitePi (fun _ : ℕ => ν)) (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ x, D p.1.1 x ∂ν
  simp_rw [he]
  exact ht.symm

theorem tensorNamespacedArrayLaw_spectralDiagonal {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (i : ℕ) (a : Fin m) (center : ℝ) :
    (∫ x, |(x (i, i) a.castSucc : ℝ) - center|
      ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) := by
  apply tensorNamespacedArrayLaw_observable_test μ eig c I degree amplitude n b r h _
    (by fun_prop) _ i
  intro U σ
  rw [spectralJointEntry_spectral]

lemma tensorNamespacedArrayLaw_treeDiagonal {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (i : ℕ) :
    (∫ x, |(x (i, i) (Fin.last m) : ℝ) - (n : ℝ) / (n + 1 : ℕ)|
      ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h : Measure (SpectralArray (m + 1)))) = 0 := by
  calc
    _ = tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h (fun _ _ => 0) := by
      apply tensorNamespacedArrayLaw_observable_test μ eig c I degree amplitude n b r h _
        (by fun_prop) _ i
      intro U σ
      rw [spectralJointEntry_tree, treeOverlap_self, sub_self, abs_zero]
    _ = 0 := by unfold tensorNamespacedObservableAverage; simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayResidual
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tensor GG residual is the spectral-array residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralJointEntry_monomial {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n) (d : Fin (m + 1) → ℕ) :
    spectralEntryMonomial d (spectralJointEntry U I n x y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a.castSucc) *
        treeOverlap n x.2 y.2 ^ d (Fin.last m) := by
  unfold spectralEntryMonomial
  rw [Fin.prod_univ_castSucc]
  simp only [spectralJointEntry_spectral, spectralJointEntry_tree]

lemma spectralJointEntry_selectedMonomial {N m : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n)
    (d : Fin m → ℕ) (r : ℕ) :
    spectralEntryMonomial (Fin.lastCases r d) (spectralJointEntry (specialRotation U) I n x y) =
      spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I d n r U x y := by
  rw [spectralJointEntry_monomial]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, spectralPerturbationKernel, id_eq]

/-- Common rotation is retained in every finite test; arbitrary replica
indices are handled by injective sampling, not by independence of rotations. -/
theorem tensorNamespacedArrayLaw_residual {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (e : Equiv.Perm (Fin (q + 1))) (D : SpectralBlock (m + 1) (q + 1) → ℝ) (hD : Continuous D) :
    spectralMonomialResidual (tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h)
      (q + 1) (e 0) D (Fin.lastCases (r j) (degree j)) =
      tensorSpectralGGResidual μ eig c I degree amplitude n b r h j
        (permutedSpectralBlockTest I n e D) := by
  classical
  let L := tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h
  let d : Fin (m + 1) → ℕ := Fin.lastCases (r j) (degree j)
  let D' := permutedSpectralBlockTest I n e D
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  have hcD : Continuous (fun x => D (spectralBlockView (m + 1) (q + 1) x)) :=
    hD.comp (continuous_spectralBlockView _ _)
  have hmono : Continuous (spectralEntryMonomial d) := continuous_spectralEntryMonomial d
  have hnew : (∫ x, D (spectralBlockView (m + 1) (q + 1) x) *
      spectralEntryMonomial d (x (e 0, q + 1)) ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U (τ : Fin (q + 1 + 1) → Spin N × LabeledLeaf n) =>
          D' U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h
      _ (hcD.mul (hmono.comp (continuous_apply _))) _
      (newReplicaEmbedding (q + 1) e) (newReplicaEmbedding_injective _ e)
    intro U σ
    simp only [Pi.mul_apply, Function.comp_apply, newReplicaEmbedding, Fin.cases_zero, Fin.cases_succ, Fin.tail]
    change D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) *
        spectralEntryMonomial d (spectralJointEntry (specialRotation U) I n (σ (e 0)) (σ (q + 1))) =
      D' U (fun i => σ (e i)) * κ U (σ (e 0)) (σ (q + 1))
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    simp only [spectralJointEntry_selectedMonomial, d, κ]
  have hblock : (∫ x, D (spectralBlockView (m + 1) (q + 1) x)
      ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h D' := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h _ hcD D'
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    exact (permutedSpectralBlockTest_embedding I n e D U σ).symm
  have hpair : (∫ x, spectralEntryMonomial d (x (0, 1))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U (τ : Fin 2 → Spin N × LabeledLeaf n) => κ U (τ 1) (τ 0)) := by
    refine tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h _
      (hmono.comp (continuous_apply _)) _ ![1, 0] ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro U σ
      exact spectralJointEntry_selectedMonomial U I n (σ 0) (σ 1) (degree j) (r j)
  have hsum : (∑ a ∈ Finset.univ.erase (e 0), ∫ x,
      D (spectralBlockView (m + 1) (q + 1) x) * spectralEntryMonomial d (x (e 0, a))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h
        (fun U σ => D' U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ)) := by
    have hI (a : Fin (q + 1)) : Integrable
        (fun x : SpectralArray (m + 1) => D (spectralBlockView (m + 1) (q + 1) x) *
          spectralEntryMonomial d (x (e 0, a))) (L : Measure (SpectralArray (m + 1))) :=
      compact_integrable (hcD.mul (hmono.comp (continuous_apply _)))
    rw [← integral_finsetSum _ (fun a _ => hI a)]
    apply tensorNamespacedArrayLaw_test μ eig c I degree amplitude n b r h
      _ (continuous_finsetSum _ fun a _ => hcD.mul (hmono.comp (continuous_apply _))) _
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    rw [sum_nonzero_permutation e (fun a => κ U (σ (e 0)) (σ a)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.mul_apply, Function.comp_apply, d, spectralJointEntry_selectedMonomial, κ]
  unfold spectralMonomialResidual
  rw [hnew, hblock, hpair, hsum]
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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPerturbationObjective
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global minima of the actual finite perturbation objective imply both
coordinate minimum conditions used by the GG estimates. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

private lemma penalty_update_p0 {z : ℕ} (u w : Fin z → ℝ) (j : Fin z) (s : ℝ) :
    (∑ i, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      (∑ i, w i * (u i - 3 / 2) ^ 2) - w j * (u j - 3 / 2) ^ 2 + w j * (s - 3 / 2) ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      ∑ i ∈ Finset.univ.erase j, w i * (u i - 3 / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he, Function.update_self]
  ring

private lemma update_mem_Icc_p0 {z : ℕ} (u : Fin z → ℝ) (hu : ∀ i, u i ∈ Set.Icc (1 : ℝ) 2)
    (j : Fin z) (s : ℝ) (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    ∀ i, Function.update u j s i ∈ Set.Icc (1 : ℝ) 2 := by
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self] using hs
  · simpa only [Function.update_of_ne hi] using hu i

/-- This is a direct restriction of the genuine joint finite-model minimum. -/
theorem tensorPerturbation_minimum_coordinates {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b h u v ≤ tensorPerturbationObjective μ eig c I t n b h u' v') :
    let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
    (∀ (j : Fin N) (s : ℝ), s ∈ Set.Icc (1 : ℝ) 2 →
      -M u v t + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
        -M (Function.update u j s) v t + perturbationWeight j * (s - 3 / 2) ^ 2) ∧
    (∀ (a : Fin m) (s : ℝ), s ∈ Set.Icc (1 : ℝ) 2 →
      -M u v t + (v a - 3 / 2) ^ 2 ≤ -M u (Function.update v a s) t + (s - 3 / 2) ^ 2) := by
  intro M
  constructor
  · intro j s hs
    have hc := hmin (Function.update u j s) v (update_mem_Icc_p0 u hu j s hs) hv
    unfold tensorPerturbationObjective at hc
    rw [penalty_update_p0] at hc
    linarith
  · intro a s hs
    have hc := hmin u (Function.update v a s) hu (update_mem_Icc_p0 v hv a s hs)
    unfold tensorPerturbationObjective at hc
    have he := penalty_update_p0 v (fun _ => 1) a s
    simp only [one_mul] at he
    rw [he] at hc
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimizerArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! GG estimates for actual tensor perturbation minimizers in spectral-array form. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem tensorPerturbation_minimizers_arrayResidual_bound (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
        ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
      perturbationScale N ≤ 1 / 32 → contactStep N ≤ 1 / 4 →
      (∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective μ eig c I t n b h u v ≤
          tensorPerturbationObjective μ eig c I t n b h u' v') →
      ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q + 1),
      ∀ D : SpectralBlock (m + 1) (q + 1) → ℝ, Continuous D →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |D x| ≤ B) →
      |spectralMonomialResidual
        (tensorNamespacedArrayLaw μ (diagonalPerturbedEigenvalues eig I v t) c I degree
          (tensorPerturbationAmplitude N u) n b treeDegree h)
        (q + 1) i D (Fin.lastCases (treeDegree j) (degree j))| ≤ tensorContactGGRate N j m L B := by
  obtain ⟨C, hC, hgg⟩ := fullPerturbationPressure_minimumGG hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    degree treeDegree L he hs hmin j q i D hD B hB hDb
  let : IsProbabilityMeasure μ := hμ
  have hc := tensorPerturbation_minimum_coordinates μ eig c I t n b h u v hu hv hmin
  let e := Equiv.swap 0 i
  have hg := hgg N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    he hs hc.1 hc.2 j q B hB (permutedSpectralBlockTest I n e D)
    (measurable_permutedSpectralBlockTest I n e D hD) (fun U σ => hDb _)
  have hr := tensorNamespacedArrayLaw_residual μ (diagonalPerturbedEigenvalues eig I v t) c I degree
    (tensorPerturbationAmplitude N u) n b treeDegree h j e D hD
  have hei : e 0 = i := Equiv.swap_apply_left 0 i
  rw [hei] at hr
  rw [hr]
  exact hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation _root_.OAI.InvariantIsing.spectralBlockClamp_real
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

/-- Finite-model minimizers enforce the vector Ghirlanda–Guerra
identities in every weak array limit. -/
theorem tensorPerturbation_minimizers_spectralGG
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k))
      atTop (nhds Q)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (Q : Measure (SpectralArray (m + 1))) := by
  obtain ⟨C, hC, hbound⟩ := tensorPerturbation_minimizers_arrayResidual_bound hhaar hgauss
  apply spectralGG_of_weak_nonconstant_monomial_residuals hL
  intro z hz i D hD d hd
  cases z with
  | zero => omega
  | succ q =>
    obtain ⟨j, hj⟩ := enumeratedJointMonomial_surjective m d hd
    let BD := BoundedContinuousFunction.mkOfCompact ⟨D, hD⟩
    have hDb : ∀ x, |D x| ≤ ‖BD‖ := fun x => by
      simpa only [BD, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
        Real.norm_eq_abs] using BD.norm_coe_le_norm x
    let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
      ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
    have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1 / 32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1 / 4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hjN : ∀ᶠ k in atTop, j < N k := hNlim.eventually (eventually_gt_atTop j)
    apply squeeze_zero_norm' _ ((tensorContactGGRate_tendsto j m L ‖BD‖).comp hNlim)
    filter_upwards [he, hs, hjN] with k he hs hjN
    let j' : Fin (N k) := ⟨j, hjN⟩
    have hg := hbound (N k) (hN k) (μ k) (hμinv k) m (eig k) (c k) K hK (heig k)
      (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k) n b hb (h k) (hh k) (h0 k) H (hH k)
      he hs (hmin k) j' q i D hD ‖BD‖ (norm_nonneg BD) hDb
    simpa only [tensorPerturbedArrayLaw, j', hj, Real.norm_eq_abs, Function.comp_def, L] using hg

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of weak limits of the actual perturbed tensor array laws. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorPerturbedArrayLaw_gram {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      SpectralGram x := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_gram _ _ _ _ _ _ _

lemma tensorPerturbedArrayLaw_reindex {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (e : ℕ → ℕ) (he : Function.Injective e) :
    (tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = tensorPerturbedArrayLaw μ eig c I u v t n b h := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_map_reindex _ _ _ _ _ _ _ e he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimizerDiagonal
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual minimizers have compact-centered spectral diagonal fluctuations. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorPerturbation_minimizers_diagonal_bound (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
        ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
      perturbationScale N ≤ 1 / 32 → contactStep N ≤ 1 / 4 →
      (∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective μ eig c I t n b h u v ≤
          tensorPerturbationObjective μ eig c I t n b h u' v') →
      ∀ i : ℕ, ∀ a : Fin m,
      (∫ x, |(x (i, i) a.castSucc : ℝ) - spectralDiagonalCenter (diagonalMinimumCenter N (v a))|
        ∂(tensorNamespacedArrayLaw μ (diagonalPerturbedEigenvalues eig I v t) c I degree
          (tensorPerturbationAmplitude N u) n b treeDegree h : Measure (SpectralArray (m + 1)))) ≤
        diagonalContactRate N L := by
  obtain ⟨C, hC, hvar⟩ := fullPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    degree treeDegree L he hs hmin i a
  let : IsProbabilityMeasure μ := hμ
  have hNp : 0 < N := by omega
  have hua : ∀ j, |u j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1], (hu j).2⟩
  have hva : ∀ a, |v a| ≤ 2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1], (hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
  let R := μ.prod (tensorRootTreeLaw I degree n b
    (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
    (tensorPathProfile I degree n treeDegree h 0))
  have hc := tensorPerturbation_minimum_coordinates μ eig c I t n b h u v hu hv hmin
  have hgv (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) R ≤ L / N := by
    exact hvar N hN μ hμ hμinv m eig c K hK heig I u hua (Function.update v a w)
      (update_abs_le_two hva a hw) t ht n b hb h hh h0 H hH
  have hd := tensorDiagonal_fluctuation_at_minimum hNp μ eig c I degree amplitude n b treeDegree h
    hh h0 hb v t a (v a) L (hv a) he hs (fun w hw => (hgv w hw).1) (fun w hw => (hgv w hw).2) (by
      dsimp only
      intro w hw
      simpa only [M, tensorPerturbationPressureMean, Function.update_eq_self] using hc.2 a w hw)
  have hd' : tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amplitude n b treeDegree h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - diagonalMinimumCenter N (v a)|) ≤
      diagonalContactRate N L := by
    simpa only [Function.update_eq_self, diagonalMinimumCenter] using hd
  rw [tensorNamespacedArrayLaw_spectralDiagonal]
  exact (tensorSpectralDiagonal_clipping μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
    n b treeDegree h a (diagonalMinimumCenter N (v a))).trans hd'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayDiagonalLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spectralLinearLaw_probability
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

/-- Vanishing actual L1 self-overlap fluctuations and converging compact
centers give deterministic diagonals in the weak limiting array. -/
theorem spectralArray_constant_diagonal_of_weak_limit {m : ℕ}
    (L : ℕ → ProbabilityMeasure (SpectralArray m)) (Q : ProbabilityMeasure (SpectralArray m))
    (hL : Tendsto L atTop (nhds Q)) (center : ℕ → Fin m → ℝ) (q : Fin m → ℝ)
    (hc : Tendsto center atTop (nhds q))
    (hdiag : ∀ i a, Tendsto
      (fun k => ∫ x, |(x (i, i) a : ℝ) - center k a| ∂(L k : Measure (SpectralArray m)))
      atTop (nhds 0)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i, i) a : ℝ) = q a := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro a
  let F := fun x : SpectralArray m => |(x (i, i) a : ℝ) - q a|
  have hF : Continuous F := by fun_prop
  have hfixed : Tendsto (fun k => ∫ x, F x ∂(L k : Measure (SpectralArray m))) atTop
      (nhds (∫ x, F x ∂(Q : Measure (SpectralArray m)))) := by
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hbound (k : ℕ) : (∫ x, F x ∂(L k : Measure (SpectralArray m))) ≤
      (∫ x, |(x (i, i) a : ℝ) - center k a| ∂(L k : Measure (SpectralArray m))) + |center k a - q a| := by
    have hg : Continuous (fun x : SpectralArray m => |(x (i, i) a : ℝ) - center k a|) := by fun_prop
    calc
      _ ≤ ∫ x, |(x (i, i) a : ℝ) - center k a| + |center k a - q a|
          ∂(L k : Measure (SpectralArray m)) :=
        integral_mono (compact_integrable hF) (compact_integrable (hg.add continuous_const))
          (fun x => abs_sub_le _ _ _)
      _ = _ := by
        rw [integral_add (compact_integrable hg) (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hcenter : Tendsto (fun k => |center k a - q a|) atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using
      (((tendsto_pi_nhds.mp hc a).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q a) atTop (nhds (q a)))).abs)
  have hzero : Tendsto (fun k => ∫ x, F x ∂(L k : Measure (SpectralArray m))) atTop (nhds 0) :=
    squeeze_zero (fun k => integral_nonneg (fun x => abs_nonneg _)) hbound
      (by simpa only [add_zero] using (hdiag i a).add hcenter)
  have hz : (∫ x, F x ∂(Q : Measure (SpectralArray m))) = 0 := tendsto_nhds_unique hfixed hzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun x : SpectralArray m => abs_nonneg ((x (i, i) a : ℝ) - q a))
    (compact_integrable hF)).mp hz
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp hx)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingDiagonal
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual diagonal-minimum fluctuations give constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorPerturbation_minimizers_constantDiagonal
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k))
      atTop (nhds Q))
    (q : Fin (m + 1) → ℝ)
    (hc : Tendsto (fun k a => (tensorMinimumArrayDiagonal (N k) n (v k) a : ℝ)) atTop (nhds q)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a := by
  obtain ⟨C, hC, hbound⟩ := tensorPerturbation_minimizers_diagonal_bound hhaar hgauss
  apply spectralArray_constant_diagonal_of_weak_limit _ Q hL _ q hc
  intro i a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [tensorMinimumArrayDiagonal, Fin.lastCases_last,
      tensorPerturbedArrayLaw, tensorNamespacedArrayLaw_treeDiagonal]
    exact tendsto_const_nhds
  · let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
      ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
    have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1 / 32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1 / 4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg (fun x => abs_nonneg _)) _
      ((diagonalContactRate_tendsto L).comp hNlim)
    filter_upwards [he, hs] with k he hs
    have hd := hbound (N k) (hN k) (μ k) (hμinv k) m (eig k) (c k) K hK (heig k)
      (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k) n b hb (h k) (hh k) (h0 k) H (hH k)
      he hs (hmin k) i a
    simpa only [tensorPerturbedArrayLaw, tensorMinimumArrayDiagonal, Fin.lastCases_castSucc,
      Function.comp_def, L] using hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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


lemma tensorPerturbedArrayLaw_partition {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      SpectralPartitionGeometry m x := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_partition hN _ _ _ _ hdis hcover _ _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFixedMinimumLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any prescribed sequence of actual finite minima admits a geometric GG
limit. The minimizers are retained, so their pressure envelope can telescope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem tensor_fixed_minimum_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K)
    (heig : ∀ k i, |eig k i|≤K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (fun _ => 0) (I k) 1 depth b
        (fun _ => 0) (u k) (v k) ≤
      tensorPerturbationObjective (μ k) (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) u' v') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => tensorPerturbedArrayLaw (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r))
        (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0)) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b₀ Φ=0) ∧
      (∀ a b₀, spectralDiagonalWardResidual Q ρ lam a b₀=0) := by
  let laws := fun k => tensorPerturbedArrayLaw (μ k) (eig k) (fun _ => 0) (I k)
    (u k) (v k) 1 depth b (fun _ => 0)
  let center := fun k => tensorMinimumArrayDiagonal (N k) depth (v k)
  obtain ⟨Q,q,φ,hφ,hL,hc⟩ := spectralArray_center_subsequence (m+1) laws center
  have hNl := hNlim.comp hφ.tendsto_atTop
  have hpos r : 0<N (φ r) := by have := hN (φ r); omega
  have hgg := tensorPerturbation_minimizers_spectralGG hhaar hgauss (fun r => N (φ r))
    (fun r => hN (φ r)) hNl m depth b hb (fun r => μ (φ r)) (fun r => hμinv (φ r))
    (fun r => eig (φ r)) (fun _ _ => 0) K hK (fun r => heig (φ r)) (fun r => I (φ r))
    (fun r => u (φ r)) (fun r => hu (φ r)) (fun r => v (φ r)) (fun r => hv (φ r))
    (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
    (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hmin (φ r)) Q hL
  have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  have hd := tensorPerturbation_minimizers_constantDiagonal hhaar hgauss (fun r => N (φ r))
    (fun r => hN (φ r)) hNl m depth b hb (fun r => μ (φ r)) (fun r => hμinv (φ r))
    (fun r => eig (φ r)) (fun _ _ => 0) K hK (fun r => heig (φ r)) (fun r => I (φ r))
    (fun r => u (φ r)) (fun r => hu (φ r)) (fun r => v (φ r)) (fun r => hv (φ r))
    (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
    (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hmin (φ r)) Q hL
    (fun a => (q a : ℝ)) ((hco.tendsto q).comp hc)
  have hG := spectralArray_limit_gram hL (fun r => tensorPerturbedArrayLaw_gram
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0))
  have hE (e : ℕ → ℕ) (he : Function.Injective e) :=
    spectralArray_limit_reindex hL e (fun r => tensorPerturbedArrayLaw_reindex
      (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0) e he)
  have hP := spectralArray_limit_partition hL (fun r => tensorPerturbedArrayLaw_partition (hpos r)
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (hdis (φ r)) (hcover (φ r))
    (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0))
  have hn := spectralGG_coordinate_nonnegative hgg hG (fun a => (q a : ℝ))
    (fun a => (q a).property.1) hd
  have hua r j : |u (φ r) j|≤2 := abs_le.mpr ⟨by linarith [(hu (φ r) j).1],(hu (φ r) j).2⟩
  have hva r a : |v (φ r) a|≤2 := abs_le.mpr ⟨by linarith [(hv (φ r) a).1],(hv (φ r) a).2⟩
  have hw := tensorGrowingPerturbedArrayLaw_ward_limits (fun r => N (φ r)) hpos hNl m
    (fun _ => depth) (fun r => μ (φ r)) (fun r => hμinv (φ r)) (fun r => eig (φ r))
    (fun _ _ => 0) (fun r => I (φ r)) (fun r => hdis (φ r)) (fun r => hcover (φ r))
    lam (fun r => hlam (φ r)) (fun r => u (φ r)) hua (fun r => v (φ r)) hva
    (fun _ => 1) tendsto_const_nhds (fun _ => b) (fun _ _ => 0)
    (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ (hρ.comp hφ.tendsto_atTop)
  simp only [one_mul] at hw
  exact ⟨φ,hφ,Q,q,hL,hgg,hd,hG,hE,hP,hn,hw.1,hw.2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityOrientationLift_right {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (V : SpecialOrthogonal N) :
    cavityOrientationLift hN (U * cavitySpecialOrthogonal V) = cavityOrientationLift hN U * V := by
  apply Subtype.ext
  have hd : ((cavitySpecialOrthogonal V : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ).det = 1 :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp V.property).2
  have hs : cavityOrientationSign hN (U * cavitySpecialOrthogonal V) = cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Submonoid.coe_mul, Matrix.det_mul, hd, mul_one]
  change cavityOrientationSign hN (U * cavitySpecialOrthogonal V) *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) =
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [hs, Matrix.mul_assoc]

lemma cavityOrientationLift_measure_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [μ.IsMulRightInvariant] :
    (μ.map (cavityOrientationLift hN)).IsMulRightInvariant := by
  constructor
  intro V
  rw [Measure.map_map (measurable_mul_const V) (measurable_cavityOrientationLift hN)]
  have he : (fun S : SpecialOrthogonal N => S * V) ∘ cavityOrientationLift hN =
      cavityOrientationLift hN ∘ (fun U => U * cavitySpecialOrthogonal V) := by
    funext U
    exact (cavityOrientationLift_right hN U V).symm
  rw [he, ← Measure.map_map (measurable_cavityOrientationLift hN)
    (measurable_mul_const (cavitySpecialOrthogonal V)), map_mul_right_eq_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSides
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A right-invariant probability has the same inverse law and is
left-invariant. In particular the oriented base law supplies the SO Haar
hypothesis used by the finite-model concentration estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

instance cavityOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (Orthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : Orthogonal N × Orthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableMul (N : ℕ) : MeasurableMul₂ (SpecialOrthogonal N) where
  measurable_mul := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun p : SpecialOrthogonal N × SpecialOrthogonal N =>
      ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) i k * (p.2 : Matrix (Fin N) (Fin N) ℝ) k j)
    exact Finset.measurable_sum _ fun k _ =>
      (((Matrix.measurable_apply (i := i) (j := k)).comp measurable_subtype_coe).comp
        measurable_fst).mul
      (((Matrix.measurable_apply (i := k) (j := j)).comp measurable_subtype_coe).comp measurable_snd)

instance cavitySpecialOrthogonal_measurableInv (N : ℕ) : MeasurableInv (SpecialOrthogonal N) where
  measurable_inv := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun U : SpecialOrthogonal N => (U : Matrix (Fin N) (Fin N) ℝ) j i)
    exact (Matrix.measurable_apply (i := j) (j := i)).comp measurable_subtype_coe

lemma cavity_right_probability_inv_eq {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] : μ = μ.inv := by
  let : IsProbabilityMeasure μ.inv :=
    (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ y, ∫⁻ x, f (x*y) ∂μ ∂μ.inv := by
      simp only [lintegral_mul_right_eq_self, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, ∫⁻ y, f (x*y) ∂μ.inv ∂μ :=
      lintegral_lintegral_swap (hf.comp (measurable_snd.mul measurable_fst)).aemeasurable
    _ = ∫⁻ y, f y ∂μ.inv := by
      simp only [lintegral_mul_left_eq_self, lintegral_const, measure_univ, mul_one]

lemma cavity_right_probability_left {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] : μ.IsMulLeftInvariant := by
  rw [cavity_right_probability_inv_eq μ]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cavityOrientedBaseLaw_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    (cavityOrientedBaseLaw hN μ).IsMulRightInvariant := by
  let : μ.IsMulLeftInvariant := cavity_right_probability_left μ
  have he : cavityOrientedBaseLaw hN μ = μ.inv.map (cavityOrientationLift hN) := by
    rw [Measure.inv_def, Measure.map_map (measurable_cavityOrientationLift hN) measurable_inv]
    rfl
  rw [he]
  exact cavityOrientationLift_measure_rightInvariant hN μ.inv

lemma cavityOrientedBaseLaw_leftInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    (cavityOrientedBaseLaw hN μ).IsMulLeftInvariant := by
  let := cavityOrientedBaseLaw_rightInvariant hN μ
  exact cavity_right_probability_left (cavityOrientedBaseLaw hN μ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFixedMinimumLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Haar arrays along any given sequence of zero-field minima
have the complete geometric GG/Ward subsequence used by the lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_fixed_minimum_geometric_limit_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K)
    (heig : ∀ k i, |eig k i|≤K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
        (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) (u k) (v k) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
        (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) u' v') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => cavityRotationArrayLaw (μ (φ r))
        (labeledCascadeLaw depth b : Measure (LabeledTree depth))
        (diagonalPerturbedEigenvalues (eig (φ r)) (I (φ r)) (v (φ r)) 1)
        (I (φ r)) (cavityBaseAmplitude (u (φ r)))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b₀ Φ=0) ∧
      (∀ a b₀, spectralDiagonalWardResidual Q ρ lam a b₀=0) := by
  have hpos k : 0<N k := by have := hN k; omega
  obtain ⟨φ,hφ,Q,q,hL,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩ :=
    tensor_fixed_minimum_geometric_limit hhaar hgauss N hN hNlim m depth b hb
      (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
      (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
      eig K hK heig I hdis hcover lam hlam ρ hρ u v hu hv hmin
  refine ⟨φ,hφ,Q,q,?_,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩
  apply hL.congr
  intro r
  exact (cavity_base_perturbed_array_law (hpos (φ r)) (μ (φ r))
    (eig (φ r)) (I (φ r)) (u (φ r)) (v (φ r)) 1 b).symm

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit_oai := @OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit_oai
