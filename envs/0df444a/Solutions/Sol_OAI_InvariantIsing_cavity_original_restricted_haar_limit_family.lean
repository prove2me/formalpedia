-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_original_restricted_haar_limit_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:25:58.688186+00:00
-- url     : https://prove2.me/submissions/df3adc64-50dd-4fef-b9d4-3f78aac43724

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
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
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
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_cutoff_limit_family

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

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

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

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end IsingPerceptron

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
namespace IsingPerceptron

lemma cylinder_weighted_variant_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j))
    (c : ι → ℝ) :
    (∑ i, c i • a i).sum (fun _ v => v^2) = (∑ i, c i • b i).sum (fun _ v => v^2) := by
  classical
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,hc]

lemma dual_cylinderField {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    L (fun i => cylinderField (a i) g) =
      cylinderField (∑ i, L (Pi.single i 1) • a i) g := by
  have hv : (fun i => cylinderField (a i) g) =
      ∑ i, cylinderField (a i) g • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv,map_sum,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,cylinderField_smul,smul_eq_mul,mul_comm]

 

lemma cylinder_finite_law_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j)) :
    gaussianCoordinates.map (fun g i => cylinderField (a i) g) =
      gaussianCoordinates.map (fun g i => cylinderField (b i) g) := by
  classical
  have ha : Measurable (fun g i => cylinderField (a i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))
  have hb : Measurable (fun g i => cylinderField (b i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,integral_map ha.aemeasurable (by fun_prop),
    integral_map hb.aemeasurable (by fun_prop)]
  simp only [dual_cylinderField]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    ← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law,cylinderField_law,cylinder_weighted_variant_eq a b hc]

 

theorem cylinder_fields_law_eq {X : Type*}
    (a b : X → ℕ →₀ ℝ) (hc : ∀ x y, cylinderCross (a x) (a y) = cylinderCross (b x) (b y)) :
    gaussianCoordinates.map (fun g x => cylinderField (a x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (b x) g) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))).aemeasurable
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))).aemeasurable).mpr
  intro I
  exact cylinder_finite_law_eq (fun i : I => a i) (fun i : I => b i) (fun i j => hc i j)

end IsingPerceptron

 

 

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
namespace IsingPerceptron

lemma perturbationAmplitude_sq (N j : ℕ) :
    (perturbationAmplitude N j)^2 = N*(perturbationScale N)^2*(perturbationWeight j)^2 := by
  unfold perturbationAmplitude
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

private lemma prefixPath_weighted_sum (q : ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (c : ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i * c else 0) = q d * c := by
  calc
    _ = (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [pathIncrement_prefix q n d hd]

private lemma prefixPath_linear_monomials {k : ℕ} (h : ℕ → ℝ)
    (q : Fin k → ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (a : ℝ) (b : Fin k → ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then
      pathIncrement h i * a + ∑ j, pathIncrement (q j) i * b j else 0) =
      h d * a + ∑ j, q j d * b j := by
  calc
    _ = (∑ i : Fin (n + 1), ((if i.1 ≤ d then pathIncrement h i * a else 0) +
        ∑ j, if i.1 ≤ d then pathIncrement (q j) i * b j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_add_distrib, prefixPath_weighted_sum h n d hd a, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact prefixPath_weighted_sum (q j) n d hd (b j)

/-- The tensor mark model with these increments has exactly the paper's
linear field covariance plus the displayed joint spectral/tree monomials. -/
theorem tensorPathProfile_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (tensorLeafCoefficients U I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) y) =
      h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)) +
        ∑ j, amplitude j ^ 2 * (∏ a, projectedOverlap U (I a) x.1 y.1 ^ degree j a) *
          treeOverlap n x.2 y.2 ^ treeDegree j := by
  rw [tensorLeafCoefficients_cross]
  simp_rw [tensorPathProfile, spinTensorFeature_covariance, varianceIncrement_coe hh h0,
    varianceIncrement_coe (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  have he := prefixPath_linear_monomials h (fun j => monomialPath n (treeDegree j)) n
    (labeledCommonDepth n x.2 y.2) (labeledCommonDepth_le n x.2 y.2)
    (∑ a, spinValue (x.1 a) * spinValue (y.1 a))
    (fun j => amplitude j ^ 2 * ∏ a, projectedOverlap U (I a) x.1 y.1 ^ degree j a)
  simp_rw [mul_assoc] at he ⊢
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [monomialPath, treeOverlap]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform covariance bounds for the monomials omitted when the
perturbation cutoff changes by a fixed cavity size. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_weighted_kernel_abs_le {J : ℕ} (u K : Fin J → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |∑ j : Fin J, perturbationWeight j ^ 2 * u j ^ 2 * K j| ≤ 4 := by
  have hw (j : ℕ) : perturbationWeight j ^ 2 ≤ perturbationWeight j := by
    nlinarith [perturbationWeight_nonneg j, perturbationWeight_le_one j]
  calc
    _ ≤ ∑ j : Fin J, |perturbationWeight j ^ 2 * u j ^ 2 * K j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin J, 4 * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hu2 : u j ^ 2 ≤ 4 := by
        have hj := abs_le.mp (hu j)
        nlinarith
      rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc
        _ ≤ perturbationWeight j ^ 2 * u j ^ 2 :=
          mul_le_of_le_one_right (by positivity) (hK j)
        _ ≤ perturbationWeight j ^ 2 * 4 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)
        _ ≤ _ := by nlinarith [hw j]
    _ = 4 * (1 - (1 / 2 : ℝ) ^ J) := by rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ 4 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComparisonRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-dependent errors in the finite cavity comparison.
The geometric cutoff is retained with its full Gaussian amplitude. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityWeightedKernel_abs_le (N : ℕ) (u K : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |cavityWeightedKernel N u K| ≤ 4 :=
  cavity_weighted_kernel_abs_le (fun j : Fin N => u j) (fun j : Fin N => K j)
    (fun j => hu j) (fun j => hK j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity error bound for the actual finite Gaussian perturbation:
the spectral/tree monomials, their amplitudes and dimension cutoff are
kept explicit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityPerturbationCoefficients_cross {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients U I u depth x)
      (cavityPerturbationCoefficients U I u depth y) =
      (N * perturbationScale N ^ 2) * cavityWeightedKernel N u (cavityPerturbationKernel U I x y) := by
  rw [cavityPerturbationCoefficients, cavityPerturbationCoefficients,
    tensorPathProfile_covariance U I _ _ depth _ (fun _ => 0) monotone_const le_rfl]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, tensorPerturbationAmplitude, mul_pow, perturbationAmplitude_sq,
    cavityWeightedKernel, Finset.mul_sum, cavityPerturbationKernel]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma cavityPerturbationKernel_abs_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) (j : ℕ) :
    |cavityPerturbationKernel U I x y j| ≤ 1 := by
  rw [cavityPerturbationKernel, abs_mul, abs_pow]
  have hT : |treeOverlap depth x.2 y.2| ≤ 1 := by
    rw [abs_of_nonneg (treeOverlap_mem depth x.2 y.2).1]
    exact (treeOverlap_mem depth x.2 y.2).2
  exact (mul_le_mul (spectralMonomial_abs_le_one U I _ x.1 y.1)
    (pow_le_one₀ (abs_nonneg _) hT) (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq
      (one_mul 1)

lemma cavityPerturbationCoefficients_sq_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (x : Spin N × LabeledLeaf depth) :
    (cavityPerturbationCoefficients U I u depth x).sum (fun _ z => z ^ 2) ≤
      4 * (N * perturbationScale N ^ 2) := by
  rw [← cylinderCross_self, cavityPerturbationCoefficients_cross]
  have hb := cavityWeightedKernel_abs_le N u (cavityPerturbationKernel U I x x) hu
    (cavityPerturbationKernel_abs_le U I x x)
  have ha : 0 ≤ (N : ℝ) * perturbationScale N ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 ha
  simpa only [mul_comm] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma measurable_cavityWeightNormalizer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) :
    Measurable (fun ω => cavityWeightNormalizer (ν ω) (fun x => w (ω, x))) := by
  let κ : Kernel Ω X := ⟨ν, hν⟩
  let : IsMarkovKernel κ := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  exact (hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma measurable_cavityWeightNumerator {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityWeightNumerator (ν ω) (fun x => w (ω, x)) (fun σ => F (ω, σ))) := by
  let κ : Kernel Ω (Fin r → X) :=
    ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω), measurable_probability_pi hν⟩
  let : IsMarkovKernel κ := ⟨fun ω =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω)))⟩
  have hm : Measurable (fun p : Ω × (Fin r → X) => (∏ i, w (p.1, p.2 i)) * F p) :=
    (Finset.measurable_prod _ fun i _ => hw.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul hF
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityWeightNormalizer_mem {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {a b : ℝ} (ha : 0 ≤ a) (hwb : ∀ x, w x ∈ Icc a b) :
    cavityWeightNormalizer ν w ∈ Icc a b := by
  have hi : Integrable w ν := Integrable.of_bound hw.aestronglyMeasurable b
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hwb x).1)]
      exact (hwb x).2)
  constructor
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const a) hi (fun x => (hwb x).1)
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const b) (fun x => (hwb x).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_bilinear_abs_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin d → ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ b) :
    |∑ i, ∑ j, x i * A i j * y j| ≤ cavityMatrixMass A * (a * b) := by
  calc
    _ ≤ ∑ i, |∑ j, x i * A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (a * b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |A i j| * (|x i| * |y j|) := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) ha)
          (abs_nonneg _)
    _ = _ := by simp only [cavityMatrixMass, Finset.sum_mul]

lemma cavity_quadratic_abs_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    |cavityQuadratic A y| ≤ cavityMatrixMass A * ‖y‖ ^ 2 := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have h := cavity_bilinear_abs_bound A y y (norm_nonneg y) (norm_nonneg y) hy hy
  have hm := cavityMatrixMass_nonneg A
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [sq_nonneg ‖y‖]

lemma cavity_spin_quadratic_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    |cavityQuadratic A (fun j => spinValue (ε j))| ≤ cavityMatrixMass A := by
  have h := cavity_bilinear_abs_bound A (fun j => spinValue (ε j)) (fun j => spinValue (ε j))
    zero_le_one zero_le_one (fun i => (abs_spinValue (ε i)).le) (fun i => (abs_spinValue (ε i)).le)
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := cavityMatrixMass_nonneg A
  simp only [mul_one] at h
  linarith

theorem cavity_logFactor_growth {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor K L C y ε| ≤
      (cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖ ^ 2) := by
  have hK := cavity_quadratic_abs_bound K y
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hy i : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hnorm : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hL' := mul_le_mul_of_nonneg_left hnorm (cavityMatrixMass_nonneg L)
  have hsum := (abs_add_le (cavityQuadratic K y + ∑ i, ∑ j, y i * L i j * spinValue (ε j))
    (cavityQuadratic C (fun j => spinValue (ε j)))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  change |cavityLogFactor K L C y ε| ≤ _ at hsum
  simp only [mul_one] at hL
  nlinarith [cavityMatrixMass_nonneg K, cavityMatrixMass_nonneg C,
    mul_nonneg (cavityMatrixMass_nonneg C) (sq_nonneg ‖y‖)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the two successive tilts with the full cavity factor on
the original leaf/residual/spin prior, with the common root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) :
    (μ.tilted f).prod ν = (μ.prod ν).tilted (fun z => f z.1) := by
  have he : (∫ z : X × Y, Real.exp (f z.1) ∂μ.prod ν) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (fun x => Real.exp (f x)))
  rw [Measure.tilted, Measure.tilted,
    prod_withDensity_left (hf.exp.div_const _).ennreal_ofReal,
    he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianBaseComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the actual Gaussian partition under bounded base-energy changes. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_partition_exp_integrable_ae {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    ∀ᵐ g : ℕ → ℝ ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x + cylinderField (A x) g)) ν := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have hv (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  have he := (gaussian_field_exp_integrable (ν := ν.tilted H)
    (measurable_cylinderFields A) (fun x => cylinderField_law (A x)) hv 1).1.prod_right_ae
  filter_upwards [he] with g hg
  simpa only [one_mul, smul_eq_mul, ← Real.exp_add] using
    (integrable_tilted_iff hH (fun x => Real.exp (1 * cylinderField (A x) g))).mp hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-prior exhaustion with the bounded deterministic cavity energy
left inside the partition. A uniform second moment gives convergence of
the actual expected logarithms. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_bounded_base_exp_integrable {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M : ℝ} (hH : ∀ x, |H x| ≤ M) :
    Integrable (fun x => Real.exp (H x)) ν := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.exp M)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hH x)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω)
      (fun σ => F (ω, σ))) := by
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (measurable_referenceReplicaMean ν (H := H) hH
    (Measurable.ite hS hF measurable_const)).div
      (measurable_referenceReplicaMean ν (H := H) hH
        (Measurable.ite hS measurable_const measurable_const))

lemma cavity_cutoff_replica_eq_cond {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      ∫ σ, F σ ∂cond (Measure.pi (fun _ : Fin 2 => ν.tilted H))
        (univ.pi (fun _ => s)) := by
  let P := Measure.pi (fun _ : Fin 2 => ν.tilted H)
  let S := univ.pi (fun _ : Fin 2 => s)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hnum : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then F σ else 0) = S.indicator F := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  have hden : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then (1 : ℝ) else 0) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  rw [cavityCutoffReplicaMean, referenceReplicaMean_eq_tilted ν H hH,
    referenceReplicaMean_eq_tilted ν H hH, hnum, hden]
  change (∫ σ, S.indicator F σ ∂P) / (∫ σ, S.indicator (fun _ => (1 : ℝ)) σ ∂P) = _
  rw [integral_indicator hS, integral_indicator hS, integral_const]
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_inv, Measure.real, Measure.restrict_apply_univ, mul_one, div_eq_inv_mul]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized spatial cutoff is multiplication of the cavity weight
by its indicator. This is the form used by finite-replica Haar limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma cavity_cutoff_weight_product {X : Type*} (w : X → ℝ) (s : Set X)
    (σ : Fin 2 → X) :
    (∏ i, s.indicator w (σ i)) =
      if ∀ i, σ i ∈ s then ∏ i, w (σ i) else 0 := by
  by_cases h : ∀ i, σ i ∈ s
  · simp only [ite_eq_left h]
    exact Finset.prod_congr rfl (fun i _ => indicator_of_mem (h i) w)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact indicator_of_notMem hi w

theorem cavity_cutoff_replica_indicator {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F := by
  have hz : (referencePartition ν H)^2 ≠ 0 :=
    pow_ne_zero _ (MeasureTheory.integral_exp_pos he).ne'
  have hn : (∫ σ : Fin 2 → X, Real.exp (∑ i, H (σ i)) *
      (if ∀ i, σ i ∈ s then F σ else 0) ∂Measure.pi (fun _ => ν)) =
      cavityWeightNumerator ν (s.indicator (fun x => Real.exp (H x))) F := by
    unfold cavityWeightNumerator
    apply integral_congr_ae
    exact ae_of_all _ fun σ => by
      dsimp only
      rw [cavity_cutoff_weight_product, Real.exp_sum]
      split_ifs <;> simp
  have hd : (∫ σ : Fin 2 → X, Real.exp (∑ i, H (σ i)) *
      (if ∀ i, σ i ∈ s then (1 : ℝ) else 0) ∂Measure.pi (fun _ => ν)) =
      (cavityWeightNormalizer ν (s.indicator (fun x => Real.exp (H x))))^2 := by
    have hf : (fun σ : Fin 2 → X => Real.exp (∑ i, H (σ i)) *
        (if ∀ i, σ i ∈ s then (1 : ℝ) else 0)) =
        fun σ => ∏ i, s.indicator (fun x => Real.exp (H x)) (σ i) := by
      funext σ
      rw [cavity_cutoff_weight_product, Real.exp_sum]
      split_ifs <;> simp
    rw [hf]
    simpa only [cavityWeightNormalizer, Fintype.card_fin] using
      integral_fintype_prod_eq_pow (ι := Fin 2) (μ := ν) (s.indicator (fun x => Real.exp (H x)))
  simp only [cavityCutoffReplicaMean, referenceReplicaMean, hn, hd]
  rw [div_div_div_cancel_right₀ hz]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalGibbsSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original spin/leaf Gibbs law equals the base Gibbs law times the
independent cavity prior, tilted by the exact cavity energy difference. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_base_product_tilt_integrable {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (J : X → ℝ) (hJ : Measurable J) (hi : Integrable (fun x => Real.exp (J x)) μ)
    (V : X × Y → ℝ)
    (hv : Integrable (fun z => Real.exp (J z.1 + V z)) (μ.prod ν)) :
    Integrable (fun z => Real.exp (V z)) ((μ.tilted J).prod ν) := by
  rw [cavity_tilt_prod_left μ ν J hJ]
  have hb : Integrable (fun z : X × Y => Real.exp (J z.1)) (μ.prod ν) := hi.comp_fst ν
  rw [integrable_tilted_iff hb]
  simpa only [smul_eq_mul, ← Real.exp_add] using hv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseCutoffFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factoring a restricted cavity test over the base Gibbs law. The
cutoff remains inside the weight, so its zero convention is preserved. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_reference_tilt_add {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J V : X → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x + V x)) μ)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    referenceReplicaMean μ (fun x => J x + V x) F =
      referenceReplicaMean (μ.tilted J) V F := by
  let := isProbabilityMeasure_tilted hj
  have hv : Integrable (fun x => Real.exp (V x)) (μ.tilted J) := by
    rw [integrable_tilted_iff hj]
    simpa only [smul_eq_mul, ← Real.exp_add] using hfull
  rw [referenceReplicaMean_eq_tilted μ _ hfull,
    referenceReplicaMean_eq_tilted (μ.tilted J) V hv, tilted_tilted hj]
  rfl

lemma cavity_cutoff_tilt_add {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J V : X → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x + V x)) μ)
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean μ (fun x => J x + V x) s F =
      cavityCutoffReplicaMean (μ.tilted J) V s F := by
  unfold cavityCutoffReplicaMean
  rw [cavity_reference_tilt_add μ J V hj hfull,
    cavity_reference_tilt_add μ J V hj hfull]

theorem cavity_base_cutoff_indicator {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [Countable Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (J : X → ℝ) (V : X × Y → ℝ)
    (hj : Integrable (fun x => Real.exp (J x)) μ)
    (hfull : Integrable (fun x => Real.exp (J x.1 + V x)) (μ.prod ν))
    (s : Set (X × Y)) (F : (Fin 2 → X × Y) → ℝ) :
    cavityCutoffReplicaMean (μ.prod ν) (fun x => J x.1 + V x) s F =
      cavityWeightedReplicaMean ((μ.tilted J).prod ν)
        (s.indicator (fun x => Real.exp (V x))) F := by
  let := isProbabilityMeasure_tilted hj
  have hv := cavity_base_product_tilt_integrable μ ν J (measurable_of_countable J) hj V hfull
  rw [cavity_cutoff_tilt_add (μ.prod ν) (fun x => J x.1) V (hj.comp_fst ν) hfull,
    ← cavity_tilt_prod_left μ ν J (measurable_of_countable J)]
  exact cavity_cutoff_replica_indicator ((μ.tilted J).prod ν) V hv s F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseHaarFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independence, in bounded-test form, of the Haar base spectral
orbit and the small compression data in the concrete cavity coupling. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma continuous_cavityConjugate (N : ℕ) :
    Continuous (Function.uncurry (cavityConjugate (N := N))) :=
  ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
    (continuous_subtype_val.comp continuous_fst).matrix_transpose

lemma cavityConjugate_mul {N : ℕ} (U V : Orthogonal N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    cavityConjugate (U * V) J = cavityConjugate U (cavityConjugate V J) := by
  change ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) * J *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)).transpose = _
  simp only [cavityConjugate, Matrix.transpose_mul, Matrix.mul_assoc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityNormalizerRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a denominator regularizer for bounded replica tests. Small
normalizers are isolated as a measurable exceptional event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityWeightNumerator_abs_le_normalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F) {M B : ℝ}
    (_hM : 0 ≤ M) (_hB : 0 ≤ B) (hwb : ∀ x, w x ∈ Icc 0 M)
    (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * cavityWeightNormalizer ν w ^ r := by
  let W := fun σ : Fin r → X => ∏ i, w (σ i)
  have hWM : Measurable W := Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)
  have hW0 σ : 0 ≤ W σ := Finset.prod_nonneg fun i _ => (hwb (σ i)).1
  have hWb σ : |W σ| ≤ M ^ r := by
    rw [abs_of_nonneg (hW0 σ)]
    exact (Finset.prod_le_prod (fun i _ => (hwb (σ i)).1)
      (fun i _ => (hwb (σ i)).2)).trans_eq (by simp)
  have hWI : Integrable W (Measure.pi (fun _ : Fin r => ν)) :=
    integrable_of_measurable_abs_le hWM hWb
  have hWFI : Integrable (fun σ => W σ * F σ) (Measure.pi (fun _ : Fin r => ν)) :=
    hWI.mul_bdd hF.aestronglyMeasurable (ae_of_all _ fun σ => by
      simpa only [Real.norm_eq_abs] using hFb σ)
  change |∫ σ, W σ * F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤ _
  calc
    _ ≤ ∫ σ, |W σ * F σ| ∂Measure.pi (fun _ : Fin r => ν) := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * W σ ∂Measure.pi (fun _ : Fin r => ν) := by
      apply integral_mono hWFI.abs (hWI.const_mul B)
      intro σ
      change |W σ * F σ| ≤ B * W σ
      rw [abs_mul, abs_of_nonneg (hW0 σ)]
      exact (mul_le_mul_of_nonneg_left (hFb σ) (hW0 σ)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [W, cavityWeightNormalizer, Fintype.card_fin] using
        integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) w

lemma cavity_normalized_numerator_bound {A Z B : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / Z ^ r| ≤ B := by
  rw [abs_div, abs_of_nonneg (pow_nonneg hZ r)]
  exact div_le_of_le_mul₀ (pow_nonneg hZ r) hB hA

lemma cavity_regularized_numerator_bound {A Z B δ : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / (Z + δ) ^ r| ≤ B := by
  apply cavity_normalized_numerator_bound (add_nonneg hZ hδ) hB r
  exact hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ (by linarith) r) hB)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStabilizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent rotations inside the base spectral groups preserve the
base interaction and rotate its selected frames. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityBlockRotation_conjugate {m : ℕ} (k : Fin m → ℕ)
    (U : (a : Fin m) → Orthogonal (k a)) (lam : Fin m → ℝ) :
    Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ)) *
      Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) *
      (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).transpose =
      Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) := by
  rw [← Matrix.blockDiagonal'_diagonal (fun a (_ : Fin (k a)) => lam a),
    Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext a
  have hU := (Matrix.mem_orthogonalGroup_iff (Fin (k a)) ℝ).mp (U a).property
  have hD : Matrix.diagonal (fun _ : Fin (k a) => lam a) =
      lam a • (1 : Matrix (Fin (k a)) (Fin (k a)) ℝ) := by
    calc
      _ = Matrix.diagonal (lam a • (fun _ : Fin (k a) => (1 : ℝ))) := by
        congr 1
        funext i
        simp
      _ = _ := by rw [Matrix.diagonal_smul, Matrix.diagonal_one]
  rw [hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

lemma cavityGroupRotation_conjugate {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) (lam : Fin m → ℝ) :
    cavityConjugate (cavityGroupRotation k e U)
      (Matrix.diagonal (fun j => lam (e.symm j).1)) =
      Matrix.diagonal (fun j => lam (e.symm j).1) := by
  have hL : Matrix.diagonal (fun j => lam (e.symm j).1) =
      (Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1)).submatrix
        e.symm e.symm := by
    simpa only [Function.comp_def] using
      (Matrix.submatrix_diagonal_equiv
        (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) e.symm).symm
  rw [hL]
  change (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).submatrix e.symm e.symm *
    (Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1)).submatrix e.symm e.symm *
    (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).transpose.submatrix e.symm e.symm = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, cavityBlockRotation_conjugate]

lemma continuous_cavityGroupRotation {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) : Continuous (cavityGroupRotation k e) := by
  have h : Continuous (fun U : (a : Fin m) → Orthogonal (k a) =>
      Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))) := by
    apply Continuous.matrix_blockDiagonal'
    exact continuous_pi (fun a => continuous_subtype_val.comp (continuous_apply a))
  exact (h.matrix_submatrix e.symm e.symm).subtype_mk _

lemma cavityGroupRotation_frame {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) (a : Fin m) :
    (cavityGroupRotation k e U : Matrix (Fin N) (Fin N) ℝ) * cavityGroupFrame k e a =
      cavityGroupFrame k e a * (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ) := by
  ext i j
  obtain ⟨⟨b, l⟩, rfl⟩ := e.surjective i
  by_cases hba : b = a
  · subst b
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, e.injective.eq_iff, Matrix.blockDiagonal'_apply_eq]
  · have hne : ∀ t : Fin (k a), e ⟨b, l⟩ ≠ e ⟨a, t⟩ := by
      intro t ht
      exact hba (congrArg Sigma.fst (e.injective ht))
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, hne]
    exact Matrix.blockDiagonal'_apply_ne
      (fun c : Fin m => (U c : Matrix (Fin (k c)) (Fin (k c)) ℝ)) l j hba

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupOverlapInvariant
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact preservation of each projected overlap under the independent
rotations inside the base spectral groups. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_bilinear_conjugate {N : ℕ} (V A : Matrix (Fin N) (Fin N) ℝ)
    (x y : Fin N → ℝ) :
    (V.transpose *ᵥ x) ⬝ᵥ (A *ᵥ (V.transpose *ᵥ y)) =
      x ⬝ᵥ ((V * A * V.transpose) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x V, ← Matrix.mulVec_transpose]

lemma projectedOverlap_conjugate {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (σ τ : Spin N) :
    projectedOverlap (matrixRotation V⁻¹) I σ τ = (N : ℝ)⁻¹ *
      ((fun i => spinValue (σ i)) ⬝ᵥ
        (cavityConjugate V (Matrix.diagonal (fun i => if i ∈ I then (1 : ℝ) else 0)) *ᵥ
          (fun i => spinValue (τ i)))) := by
  rw [cavityConjugate, ← cavity_bilinear_conjugate]
  change (N : ℝ)⁻¹ * (∑ i ∈ I, _ * _) = (N : ℝ)⁻¹ *
    (((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ (fun i => spinValue (σ i))) ⬝ᵥ
      (Matrix.diagonal (fun i => if i ∈ I then (1 : ℝ) else 0) *ᵥ
        ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ (fun i => spinValue (τ i)))))
  simp only [dotProduct, Matrix.mulVec_diagonal, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A random cutoff changes bounded replica tests by its discarded
one-replica probability, after averaging over the common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F]
  have h := norm_integral_le_of_norm_le_const
    (μ := cond (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)))
    (f := F) (C := M) (ae_of_all _ (fun σ => by
      simpa only [Real.norm_eq_abs] using hF σ))
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hM measureReal_le_one)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTotalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cutoff is bounded also when its partition integral
is undefined: the existing zero convention then gives zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (s : Set X) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  by_cases hi : Integrable (fun x => Real.exp (H x)) ν
  · exact cavity_cutoff_replica_abs_le ν H hi s (Set.to_countable s).measurableSet F hM hF
  · have hz : referencePartition ν H = 0 := integral_undef hi
    simp only [cavityCutoffReplicaMean, referenceReplicaMean, hz, zero_pow (by decide : 2 ≠ 0),
      div_zero, abs_zero]
    exact hM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projector coordinates give the same Gaussian covariance as the
eigenbasis coordinates, without choosing an eigenbasis measurably. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralProjector_transpose {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    (cavitySpectralProjector V I).transpose = cavitySpectralProjector V I := by
  simp only [cavitySpectralProjector, cavityConjugate, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

lemma cavitySpectralProjector_square {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    cavitySpectralProjector V I * cavitySpectralProjector V I = cavitySpectralProjector V I := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => if i∈I then (1:ℝ) else 0)
  have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
  have hD : D*D=D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> norm_num
  change ((V : Matrix (Fin N) (Fin N) ℝ)*D*(V : Matrix (Fin N) (Fin N) ℝ).transpose)*
    ((V : Matrix (Fin N) (Fin N) ℝ)*D*(V : Matrix (Fin N) (Fin N) ℝ).transpose) = _
  calc
    _ = (V : Matrix (Fin N) (Fin N) ℝ)*D*
        ((V : Matrix (Fin N) (Fin N) ℝ).transpose*(V : Matrix (Fin N) (Fin N) ℝ))*D*
        (V : Matrix (Fin N) (Fin N) ℝ).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc _ D D, hD]; rfl

lemma cavity_projector_coordinate_dot {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (x y : Fin N → ℝ) :
    (cavitySpectralProjector V I *ᵥ x) ⬝ᵥ (cavitySpectralProjector V I *ᵥ y) =
      x ⬝ᵥ (cavitySpectralProjector V I *ᵥ y) := by
  calc
    _ = x ⬝ᵥ (cavitySpectralProjector V I *ᵥ (cavitySpectralProjector V I *ᵥ y)) := by
      rw [Matrix.dotProduct_mulVec x, ← Matrix.mulVec_transpose, cavitySpectralProjector_transpose]
    _ = _ := by rw [Matrix.mulVec_mulVec, cavitySpectralProjector_square]

theorem cavity_projector_coordinate_covariance {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (σ τ : Spin N) :
    (∑ i, cavityProjectorSpinCoordinate (cavitySpectralProjector V I) σ i *
      cavityProjectorSpinCoordinate (cavitySpectralProjector V I) τ i) =
      projectedOverlap (matrixRotation V⁻¹) I σ τ := by
  simp only [cavityProjectorSpinCoordinate, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm, projectedOverlap_conjugate]
  congr 1
  exact cavity_projector_coordinate_dot V I _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cavity reweighting of the original perturbed spin model.
Both Hamiltonians contain the same Gaussian disorder coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_rotation_exp_integrable_ae {N m depth : ℕ}
    (U : Rotation N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) :
    ∀ᵐ z ∂gaussianCoordinates, Integrable
      (fun x => Real.exp (cavityRotationHamiltonian U eig I u z x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  exact cylinder_partition_exp_integrable_ae ν
    (fun x => rotatedEnergy eig U x.1)
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig U σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)))
    (cavityPerturbationCoefficients U I u depth)
    (cavityPerturbationCoefficients_sq_le U I u hu)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCovarianceLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality in law of the entire countable Gaussian field transports
replica observables of every order, including their cutoff normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_field_functional_same_covariance {X : Type*}
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (G : (X → ℝ) → ℝ) (hG : Measurable G) :
    (∫ z, G (fun x => cylinderField (A x) z) ∂gaussianCoordinates) =
      ∫ z, G (fun x => cylinderField (C x) z) ∂gaussianCoordinates := by
  have hA : Measurable (fun z x => cylinderField (A x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (A x))
  have hC : Measurable (fun z x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  rw [← integral_map hA.aemeasurable hG.aestronglyMeasurable,
    cylinder_fields_law_eq A C hcov, integral_map hC.aemeasurable hG.aestronglyMeasurable]

theorem cavity_cutoff_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    (∫ z, cavityCutoffReplicaMean ν (fun x => H x + cylinderField (A x) z) s F ∂gaussianCoordinates) =
      ∫ z, cavityCutoffReplicaMean ν (fun x => H x + cylinderField (C x) z) s F ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => cavityCutoffReplicaMean ν (fun x => H x + w x) s F)
    (measurable_cavityCutoffReplicaMean ν _ hm (fun _ => s)
      (((Set.to_countable s).measurableSet).preimage measurable_snd)
      (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorTensor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor features built directly from labeled spectral projectors.
They give an eigenbasis-free representation of the actual Gaussian
perturbation, with exactly its original covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

lemma cavityProjectorMonomial_cross {N m : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin m → ℕ) (σ τ : Spin N) :
    (∑ w, cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) degree σ w *
      cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) degree τ w) =
      ∏ a, projectedOverlap (matrixRotation V⁻¹) (I a) σ τ ^ degree a := by
  simp only [cavityProjectorMonomial, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (w : Fin (degree a) → (Finset.univ : Finset (Fin N))) =>
    tensorFeature (degree a)
      (fun i : (Finset.univ : Finset (Fin N)) => cavityProjectorSpinCoordinate (cavitySpectralProjector V (I a)) σ (i : Fin N)) w *
    tensorFeature (degree a)
      (fun i : (Finset.univ : Finset (Fin N)) => cavityProjectorSpinCoordinate (cavitySpectralProjector V (I a)) τ (i : Fin N)) w)]
  simp_rw [tensorFeature_cross]
  congr 1
  funext a
  congr 1
  have h := cavity_projector_coordinate_covariance V (I a) σ τ
  exact (Finset.sum_coe_sort Finset.univ _).trans h

lemma cavityProjectorSpinFeature_covariance {N m : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (amp : Fin N → ℝ) (site : ℝ≥0) (mono : Fin N → ℝ≥0) (σ τ : Spin N) :
    (∑ i : CavityProjectorTensorIndex N m degree,
      (tensorVarianceProfile (fun _ => Finset.univ) degree site mono i : ℝ) *
      cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) degree amp σ i *
      cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) degree amp τ i) =
    (site:ℝ) * (∑ j, spinValue (σ j)*spinValue (τ j)) +
      ∑ j, (mono j:ℝ)*amp j^2 * ∏ a, projectedOverlap (matrixRotation V⁻¹) (I a) σ τ ^ degree j a := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, cavityProjectorSpinFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (mono j:ℝ)*amp j^2 * ∑ w,
          cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) (degree j) σ w *
          cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) (degree j) τ w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [cavityProjectorMonomial_cross]

 theorem cavityProjectorPerturbation_cross {N m depth : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityProjectorPerturbation (fun a => cavitySpectralProjector V (I a)) u x)
      (cavityProjectorPerturbation (fun a => cavitySpectralProjector V (I a)) u y) =
    cylinderCross (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth x)
      (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth y) := by
  classical
  let deg := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j => u j)
  let v := fun i => tensorPathProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N)))
    deg depth (fun j => enumeratedTreeDegree m j) (fun _ => 0) i
  let f := fun σ => cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp σ
  rw [cavityProjectorPerturbation, cavityProjectorPerturbation,
    featureCoefficients_diagonal (treeFeatureTag depth x.2) (treeFeatureTag depth y.2)
      (fun i j h => ((treeFeatureTag_cross depth x.2 y.2 i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type, cavityPerturbationCoefficients, cavityPerturbationCoefficients,
    tensorLeafCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth depth x.2 y.2
  · simp only [hi, ite_true, if_true]
    have hprod (j : CavityProjectorTensorIndex N m deg) :
        ((NNReal.sqrt (v i j) : ℝ) * f x.1 j) * ((NNReal.sqrt (v i j) : ℝ) * f y.1 j) =
        (v i j : ℝ) * f x.1 j * f y.1 j := by
      have hs : (NNReal.sqrt (v i j) : ℝ)^2 = (v i j : ℝ) := by
        exact_mod_cast NNReal.sq_sqrt (v i j)
      calc
        _ = (NNReal.sqrt (v i j) : ℝ)^2 * f x.1 j * f y.1 j := by ring
        _ = _ := by rw [hs]
    change (∑ j : CavityProjectorTensorIndex N m deg,
      ((NNReal.sqrt (v i j) : ℝ) * f x.1 j) * ((NNReal.sqrt (v i j) : ℝ) * f y.1 j)) = _
    simp_rw [hprod]
    change (∑ j, (tensorVarianceProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N))) deg
      (varianceIncrement (fun _ => 0) i) (fun j => varianceIncrement
        (monomialPath depth (enumeratedTreeDegree m j)) i) j : ℝ) *
        cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp x.1 j *
        cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp y.1 j) = _
    rw [cavityProjectorSpinFeature_covariance]
    dsimp only [tensorPathProfile]
    rw [spinTensorFeature_covariance]
  · simp only [hi, ite_false, if_false, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorHamiltonian
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base Gibbs law expressed using its labeled projectors.
This makes the law a measurable function of the data in the joint
projector/frame Haar factorization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralProjector_form {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (x : Fin N → ℝ) :
    x ⬝ᵥ (cavitySpectralProjector V I *ᵥ x) =
      ∑ i ∈ I, ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ x) i ^ 2 := by
  rw [cavitySpectralProjector, cavityConjugate, ← cavity_bilinear_conjugate]
  simp only [dotProduct, Matrix.mulVec_diagonal, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, pow_two]

lemma cavityProjectorEnergy_group {N m : ℕ} (g : Fin N → Fin m)
    (V : Orthogonal N) (c : Fin m → ℝ) (σ : Spin N) :
    cavityProjectorEnergy (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) c σ =
      rotatedEnergy (fun i => c (g i)) (matrixRotation V⁻¹) σ := by
  unfold cavityProjectorEnergy rotatedEnergy
  congr 1
  simp_rw [cavitySpectralProjector_form, cavitySpectralGroup, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rfl

lemma cavityProjectorHamiltonian_energy {N m : ℕ} (g : Fin N → Fin m)
    (V : Orthogonal N) (lam v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    cavityProjectorEnergy (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
      (fun a => t*lam a + 2*perturbationScale N*v a) σ =
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) σ := by
  rw [cavityProjectorEnergy_group]
  congr 1
  funext i
  simp [diagonalPerturbedEigenvalues, cavitySpectralGroup]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable, bounded Gibbs observables expressed in the joint
projector and special-frame data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavityProjectorSpinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun Q : Matrix (Fin N) (Fin N) ℝ => cavityProjectorSpinCoordinate Q σ i) := by
  unfold cavityProjectorSpinCoordinate Matrix.mulVec dotProduct
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _

lemma measurable_cavityProjectorMonomial {N m : ℕ} (degree : Fin m → ℕ)
    (σ : Spin N) (w : SpectralTensorIndex
      (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorMonomial Q degree σ w) := by
  unfold cavityProjectorMonomial tensorFeature
  apply Finset.measurable_prod
  intro a _
  apply Finset.measurable_prod
  intro j _
  exact (measurable_cavityProjectorSpinCoordinate σ (w a j)).comp (measurable_pi_apply a)

lemma measurable_cavityProjectorSpinFeature {N m : ℕ} (degree : Fin N → Fin m → ℕ)
    (amp : Fin N → ℝ) (σ : Spin N) (j : CavityProjectorTensorIndex N m degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorSpinFeature Q degree amp σ j) := by
  cases j with
  | inl j => exact measurable_const
  | inr w => exact (measurable_cavityProjectorMonomial (degree w.1) σ w.2).const_mul _

lemma measurable_cavityProjectorField {N m depth : ℕ}
    (u : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : (Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ) =>
      cylinderField (cavityProjectorPerturbation p.1 u x) p.2) := by
  simp only [cavityProjectorPerturbation, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_cavityProjectorSpinFeature _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

lemma measurable_cavityProjectorHamiltonian {N m depth : ℕ}
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) => cavityProjectorHamiltonian p.1.1 c u p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have he : Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorEnergy Q c x.1) := by
    unfold cavityProjectorEnergy Matrix.mulVec dotProduct
    fun_prop
  exact (he.comp measurable_fst).add (measurable_cavityProjectorField u x)

lemma measurable_cavityProjectorHamiltonian_pullback {Ω : Type*} [MeasurableSpace Ω]
    {N m depth : ℕ} (f : Ω → Fin m → Matrix (Fin N) (Fin N) ℝ) (hf : Measurable f)
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) =>
      cavityProjectorHamiltonian (f p.1.1) c u p.1.2 p.2) := by
  let π : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) →
      ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) :=
    fun p => ((f p.1.1,p.1.2),p.2)
  have hπ : Measurable π :=
    ((hf.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd
  have hbase := measurable_cavityProjectorHamiltonian (N := N) (m := m) (depth := depth) c u
  have hcomp := hbase.comp hπ
  exact hcomp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCavity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cavity observable as a measurable function of the
physical labeled projectors, selected frame and small coefficient blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma continuous_cavityFrameCoordinates {N d : ℕ} (σ : Spin N) :
    Continuous (fun S : Matrix (Fin N) (Fin d) ℝ => cavityFrameCoordinates S σ) := by
  unfold cavityFrameCoordinates
  fun_prop

lemma measurable_cavityBlockPotential {Ω : Type*} [MeasurableSpace Ω] {N n d : ℕ}
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (S : Ω → Matrix (Fin N) (Fin d) ℝ) (hS : Measurable S)
    (σ : Spin N) (ε : Spin n) :
    Measurable (fun ω => cavityLogFactor (A ω).1 (A ω).2.1 (A ω).2.2
      (cavityFrameCoordinates (S ω) σ) ε) := by
  have hy := (continuous_cavityFrameCoordinates σ).measurable.comp hS
  unfold cavityLogFactor cavityQuadratic
  fun_prop

lemma cavityProjectorCavityMean_bound {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ σ, |F σ| ≤ C)
    (p : CavityProjectorFrame N m d) :
    ‖cavityProjectorCavityMean T c u t D A F p‖ ≤ C := by
  have hb : ∀ᵐ z ∂gaussianCoordinates, ‖cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
        t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
      {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F‖ ≤ C := by
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact cavity_cutoff_replica_abs_le_all _ _ _ _ hC hF
  simpa only [cavityProjectorCavityMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma measurable_cavityProjectorCavityMean {Ω : Type*} [MeasurableSpace Ω]
    {N n m d depth : ℕ} (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (A : Ω → CavityFactorBlocks d n) (hA : Measurable A)
    (p : Ω → CavityProjectorFrame N m d) (hp : Measurable p)
    (F : Ω → (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun ω => cavityProjectorCavityMean T c u t D (A ω) (F ω) (p ω)) := by
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let H := fun q : (Ω × (ℕ → ℝ)) × X =>
    cavityProjectorHamiltonian (p q.1.1).1 c u q.1.2 q.2.1 +
      t*cavityLogFactor (A q.1.1).1 (A q.1.1).2.1 (A q.1.1).2.2
        (cavityFrameCoordinates (p q.1.1).2 q.2.1.1) q.2.2
  have hH : Measurable H := by
    let π : (Ω × (ℕ → ℝ)) × X →
        (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) := fun q => (q.1,q.2.1)
    have hπ : Measurable π := measurable_fst.prodMk measurable_snd.fst
    have hb := measurable_cavityProjectorHamiltonian_pullback
      (N := N) (m := m) (depth := depth) (fun ω => (p ω).1) hp.fst c u
    have hg := hb.comp hπ
    apply Measurable.add hg
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_cavityBlockPotential A hA (fun ω => (p ω).2) hp.snd x.1.1 x.2).comp
      measurable_fst).const_mul t
  have hs : MeasurableSet {q : (Ω × (ℕ → ℝ)) × X |
      1 + ‖cavityFrameCoordinates (p q.1.1).2 q.2.1.1‖^2 ≤ D} := by
    have hy : Measurable (fun q : (Ω × (ℕ → ℝ)) × X =>
        cavityFrameCoordinates (p q.1.1).2 q.2.1.1) := by
      apply measurable_from_prod_countable_left
      intro x
      exact ((continuous_cavityFrameCoordinates x.1.1).measurable.comp hp.snd).comp
        measurable_fst
    exact measurableSet_le (measurable_const.add (hy.norm.pow_const 2)) measurable_const
  have hG := measurable_cavityCutoffReplicaMean
    ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)) H hH
    (fun q => {x | 1 + ‖cavityFrameCoordinates (p q.1).2 x.1.1‖^2 ≤ D}) hs
    (fun q => F q.1.1 q.2) (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorGibbsHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint averaging of the actual projector-based Gibbs law and its
compression-dependent bounded replica tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalProjectorFrame_action_fst {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) :
    (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).1 =
      fun a => cavitySpectralProjector V
        (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) := by
  funext a
  have hd : (fun j : Fin N => Sum.elim (fun w => if w.1=a then (1:ℝ) else 0)
      (fun j => if a₀ j=a then 1 else 0) (e.symm j)) =
      (fun j => if j ∈ cavitySpectralGroup
        (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a then 1 else 0) := by
    funext j
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h : e.symm j with w | j₀ <;> rfl
  exact congrArg (fun f : Fin N → ℝ => cavityConjugate V (Matrix.diagonal f)) hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCutoffLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The projector realization identifies the full normalized cavity
cutoff law, including its extra finite spins and added potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_projector_extra_cutoff {N n m depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (W : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (s : Set ((Spin N × LabeledLeaf depth) × Spin n))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    let ν : Measure ((Spin N × LabeledLeaf depth) × Spin n) := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)
    (∫ z, cavityCutoffReplicaMean ν
      (fun x => cavityProjectorHamiltonian
        (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z x.1 + W x) s F
      ∂gaussianCoordinates) =
    ∫ z, cavityCutoffReplicaMean ν
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        (cavitySpectralGroup g) u z x.1 + W x) s F ∂gaussianCoordinates := by
  intro ν
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  let H := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    rotatedEnergy eig (matrixRotation V⁻¹) x.1.1 + W x
  let A := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x.1
  let C := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x.1
  have he z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityProjectorHamiltonian (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z x.1 + W x) =
      fun x => H x+cylinderField (A x) z := by
    funext x
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
    dsimp only [H, A, eig]
    ring
  have hc z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityRotationHamiltonian (matrixRotation V⁻¹) eig (cavitySpectralGroup g) u z x.1 + W x) =
      fun x => H x+cylinderField (C x) z := by
    funext x
    dsimp only [cavityRotationHamiltonian, H, C]
    ring
  calc
    _ = ∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (A x) z) s F
        ∂gaussianCoordinates := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => congrArg (fun J => cavityCutoffReplicaMean ν J s F) (he z)
    _ = ∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (C x) z) s F
        ∂gaussianCoordinates := cavity_cutoff_same_covariance ν H A C
      (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x.1 y.1) s F
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => congrArg (fun J => cavityCutoffReplicaMean ν J s F) (hc z).symm

theorem cavity_projector_cavity_cutoff {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d)
    (hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    cavityProjectorCavityMean (N := N) (n := n) (m := m) (d := d) (depth := depth)
      T (fun a => t*lam a+2*perturbationScale N*v a) u t D A F p =
    ∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun j => lam (g j)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x.1 +
        t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
      {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F ∂gaussianCoordinates := by
  unfold cavityProjectorCavityMean
  rw [hp]
  exact cavity_projector_extra_cutoff (N := N) (n := n) (m := m) (depth := depth)
    g V T lam v u t _ _ F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorStabilizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent rotations in each labeled spectral subspace preserve
all base projectors, while rotating the selected cavity axes. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavityGroupRotation_spectralProjector {N m : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (a : Fin m) :
    cavitySpectralProjector (V*cavityGroupRotation k e W)
      (cavitySpectralGroup (fun i => (e.symm i).1) a) =
    cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a) := by
  rw [cavitySpectralProjector, cavitySpectralProjector, cavityConjugate_mul]
  have hmask : (Matrix.diagonal (fun i : Fin N =>
      if i ∈ cavitySpectralGroup (fun i => (e.symm i).1) a then (1 : ℝ) else 0)) =
      Matrix.diagonal (fun i => (fun b => if b=a then (1 : ℝ) else 0) (e.symm i).1) := by
    congr 1
    funext i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hmask, cavityGroupRotation_conjugate k e W (fun b => if b=a then (1 : ℝ) else 0)]

theorem cavity_labeled_stabilizer_average {N m d : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (S : Matrix (Fin N) (Fin d) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (f : CavityProjectorFrame N m d → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ V, f (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*S) ∂μ) =
    ∫ V, ∫ W, f (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*S)) ∂η ∂μ := by
  let : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  let : SecondCountableTopology (Orthogonal N) :=
    (show Topology.IsInducing (Subtype.val : Orthogonal N → Matrix (Fin N) (Fin N) ℝ) from
      Topology.IsInducing.subtypeVal).secondCountableTopology
  let (a : Fin m) : SecondCountableTopology (Orthogonal (k a)) := by
    let : SecondCountableTopology (Matrix (Fin (k a)) (Fin (k a)) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin (k a) → Fin (k a) → ℝ))
    exact (show Topology.IsInducing
      (Subtype.val : Orthogonal (k a) → Matrix (Fin (k a)) (Fin (k a)) ℝ) from
        Topology.IsInducing.subtypeVal).secondCountableTopology
  let h : Orthogonal N → ℝ := fun V => f
    (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*S)
  have hm : Measurable h := by
    apply hf.comp
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro a
      exact ((continuous_cavityConjugate N).comp
        (continuous_id.prodMk continuous_const)).measurable
    · exact (continuous_subtype_val.matrix_mul continuous_const).measurable
  let H := fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
    h (p.1*cavityGroupRotation k e p.2)
  have hrot : Continuous (fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
      p.1*cavityGroupRotation k e p.2) :=
    continuous_fst.mul ((continuous_cavityGroupRotation k e).comp continuous_snd)
  have hi : Integrable H (μ.prod η) := Integrable.of_bound
    (hm.comp hrot.measurable).aestronglyMeasurable C (ae_of_all _ fun p => hb _)
  have hrow W : (∫ V, H (V,W) ∂μ) = ∫ V, h V ∂μ :=
    integral_mul_right_eq_self h (cavityGroupRotation k e W)
  have heq V W : H (V,W) = f
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*S)) := by
    dsimp only [H, h]
    simp only [cavityGroupRotation_spectralProjector]
    rw [show ((V*cavityGroupRotation k e W : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ) =
      (V : Matrix (Fin N) (Fin N) ℝ)*(cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ) from rfl,
      Matrix.mul_assoc]
  calc
    _ = ∫ W, ∫ V, H (V,W) ∂μ ∂η := by simp only [hrow]; simp [h]
    _ = ∫ V, ∫ W, H (V,W) ∂η ∂μ := (integral_integral_swap hi).symm
    _ = _ := by simp only [heq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected columns in spectral groups and their exact spin coordinates.
These are the vectors to which the fresh-frame Gaussian limit applies. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityGroupedSelectedFrame_rotation {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (W : (a : Fin m) → Orthogonal (k a)) :
    (cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A =
    cavityGroupedSelectedFrame k e f (cavityGroupHaarFrames A W) := by
  ext i j
  change ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
    (cavityGroupFrame k e (f j).1*A (f j).1)) i (f j).2 = _
  rw [← Matrix.mul_assoc, cavityGroupRotation_frame, Matrix.mul_assoc]
  rfl

lemma cavityGroupFrame_transpose_mulVec {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m)
    (x : Fin N → ℝ) (j : Fin (k a)) :
    ((cavityGroupFrame k e a).transpose *ᵥ x) j = x (e ⟨a,j⟩) := by
  simp [Matrix.mulVec, dotProduct, cavityGroupFrame]

lemma cavityGroupedSelectedFrame_transpose_mulVec {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ) (x : Fin N → ℝ)
    (j : Fin d) :
    ((cavityGroupedSelectedFrame k e f A).transpose *ᵥ x) j =
      ∑ l, x (e ⟨(f j).1,l⟩)*A (f j).1 l (f j).2 := by
  change (((cavityGroupFrame k e (f j).1*A (f j).1).transpose) *ᵥ x) (f j).2 = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  change (∑ l, A (f j).1 l (f j).2 *
    ((cavityGroupFrame k e (f j).1).transpose *ᵥ x) l) = _
  simp only [cavityGroupFrame_transpose_mulVec]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma cavityGroupedSelectedFrame_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      cavityGroupedSelectedFrame k e f A) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V) A σ := by
  ext j
  change (((V : Matrix (Fin N) (Fin N) ℝ)*
    cavityGroupedSelectedFrame k e f A).transpose *ᵥ (fun i => spinValue (σ i))) j = _
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    cavityGroupedSelectedFrame_transpose_mulVec]
  rfl

lemma cavityGroupedSelectedFrame_rotated_coordinates {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (σ : Spin N) :
    cavityFrameCoordinates ((V : Matrix (Fin N) (Fin N) ℝ)*
      ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
        cavityGroupedSelectedFrame k e f A)) σ =
    cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
      (cavityGroupHaarFrames A W) σ := by
  rw [cavityGroupedSelectedFrame_rotation, cavityGroupedSelectedFrame_coordinates]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedCutoffAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-block Haar cutoff is precisely the fresh-group-frame
observable over the original base Hamiltonian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_grouped_cutoff_average {N n m q d depth : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*cavityGroupedSelectedFrame k e f A) ∂μ) =
    ∫ V, ∫ W, ∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
          (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u z x.1 +
        t*cavityLogFactor B.1 B.2.1 B.2.2
          (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
            (cavityGroupHaarFrames A W) x.1.1) x.2)
      {x | 1+‖cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D} F ∂gaussianCoordinates ∂η ∂μ := by
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let G : CavityProjectorFrame N m d → ℝ := cavityProjectorCavityMean T c u t D B F
  have hFs : Measurable (fun x : CavityProjectorFrame N m d ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F x.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hG : Measurable G := measurable_cavityProjectorCavityMean T c u t D
    (fun _ => B) measurable_const id measurable_id (fun _ => F) hFs
  have hb : ∀ p, ‖G p‖ ≤ M := fun p => cavityProjectorCavityMean_bound T c u t D B F hM hF p
  rw [cavity_labeled_stabilizer_average k e (cavityGroupedSelectedFrame k e f A) μ η G hG M hb]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  let p : CavityProjectorFrame N m d :=
    (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
          cavityGroupedSelectedFrame k e f A))
  have hp : p.1 = fun a => cavitySpectralProjector V
    (cavitySpectralGroup (fun i => (e.symm i).1) a) := rfl
  change cavityProjectorCavityMean T c u t D B F p = _
  rw [cavity_projector_cavity_cutoff (fun i => (e.symm i).1) V T lam v u t D B p hp F]
  simp only [p, cavityGroupedSelectedFrame_rotated_coordinates]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationCutoffWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded spin-only cavity potential factors over the actual
perturbed base Gibbs law, retaining the spatial indicator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_rotation_cutoff_weight {N n m depth : ℕ}
    (V : Rotation N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (W : Spin N × Spin n → ℝ)
    (s : Set ((Spin N × LabeledLeaf depth) × Spin n))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    (∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian V eig I u z x.1 + W (x.1.1,x.2)) s F
        ∂gaussianCoordinates) =
    ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian V eig I u z)).prod (uniformSpinPrior n))
      (s.indicator (fun x => Real.exp (W (x.1.1,x.2)))) F ∂gaussianCoordinates := by
  let μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let ν := μ.prod (uniformSpinPrior n : Measure (Spin n))
  let H : (Spin N × LabeledLeaf depth) × Spin n → ℝ := fun x =>
    rotatedEnergy eig V x.1.1+W (x.1.1,x.2)
  let C : (Spin N × LabeledLeaf depth) × Spin n → ℕ →₀ ℝ := fun x =>
    cavityPerturbationCoefficients V I u depth x.1
  obtain ⟨M,hM⟩ := Finite.exists_le (fun x : Spin N × Spin n => |rotatedEnergy eig V x.1+W x|)
  have hfull : ∀ᵐ z ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x+cylinderField (C x) z)) ν :=
    cylinder_partition_exp_integrable_ae ν H
      (cavity_bounded_base_exp_integrable ν H (fun x => hM (x.1.1,x.2))) C
      (fun x => cavityPerturbationCoefficients_sq_le V I u hu x.1)
  apply integral_congr_ae
  filter_upwards [hfull, cavity_rotation_exp_integrable_ae V T eig I u hu] with z hz hj
  have he : (fun x => H x+cylinderField (C x) z) =
      fun x : (Spin N × LabeledLeaf depth) × Spin n =>
        cavityRotationHamiltonian V eig I u z x.1+W (x.1.1,x.2) := by
    funext x
    dsimp only [H,C,cavityRotationHamiltonian]
    ring
  have hz' : Integrable (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      Real.exp (cavityRotationHamiltonian V eig I u z x.1+W (x.1.1,x.2))) ν :=
    hz.congr (ae_of_all _ fun x => congrArg Real.exp (congrFun he x))
  exact cavity_base_cutoff_indicator μ (uniformSpinPrior n)
    (cavityRotationHamiltonian V eig I u z) (fun x => W (x.1.1,x.2)) hj hz' s F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedWeightedAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh-frame cutoff tests over the actual base Gibbs probability.
The diagonal and Gaussian perturbations stay in that base law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_grouped_weighted_average {N n m q d depth : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t D : ℝ)
    (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*cavityGroupedSelectedFrame k e f A) ∂μ) =
    ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
            (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (e.symm i).1)) u z)).prod (uniformSpinPrior n))
      ({x | 1+‖cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
          Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
            (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
              (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ := by
  rw [cavity_grouped_cutoff_average k e f A μ η T lam v u t D B F hM hF]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  exact cavity_rotation_cutoff_weight (matrixRotation V⁻¹) T
    (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
      (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
    (cavitySpectralGroup (fun i => (e.symm i).1)) u hu
    (fun x => t*cavityLogFactor B.1 B.2.1 B.2.2
      (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1) x.2) _ F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalGroupAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical cavity frame admits the fresh-group Gibbs
representation. No new independent-frame assumption is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalGroupFrame_special {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
      (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)=cavityCanonicalSpecial e :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).2

lemma cavityCanonicalProjectorFrame_grouped {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (V : Orthogonal N) :
    cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e g) =
    (fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv k e g).symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
          (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)) := by
  apply Prod.ext
  · rw [cavityCanonicalProjectorFrame_action_fst]
    funext a
    congr 1
    ext i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
      cavityBaseGroupEquiv_label]
  · rw [cavityCanonicalGroupFrame_special]
    rfl

theorem cavity_canonical_weighted_average {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e g)) ∂μ) =
    let E := cavityBaseGroupEquiv k e g
    let A := cavityCanonicalGroupFrame k e g hk
    ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
            (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (uniformSpinPrior n))
      ({x | 1+‖cavitySelectedSiteProjection (fun j => (g j,j))
        (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
          Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
            (cavitySelectedSiteProjection (fun j => (g j,j))
              (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
              (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ := by
  simp_rw [cavityCanonicalProjectorFrame_grouped k e g hk]
  exact cavity_grouped_weighted_average (cavityBaseGroupDimension k g)
    (cavityBaseGroupEquiv k e g) (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)
    μ η T lam v u hu t D B F hM hF

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorScaling
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature scaling of the actual quadratic cavity factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_smul {d : ℕ} (t : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    cavityQuadratic (t • K) y = t * cavityQuadratic K y := by
  simp only [cavityQuadratic, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, y i * (t*K i j) * y j = t*(y i*K i j*y j) from fun i j => by ring]
  simp only [← Finset.mul_sum]
  ring

lemma cavityLogFactor_smul {d n : ℕ} (t : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin d → ℝ) (ε : Spin n) :
    cavityLogFactor (t • K) (t • L) (t • C) y ε = t * cavityLogFactor K L C y ε := by
  simp only [cavityLogFactor, cavityQuadratic_smul, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, y i * (t*L i j) * spinValue (ε j) =
    t*(y i*L i j*spinValue (ε j)) from fun i j => by ring]
  simp only [← Finset.mul_sum]
  ring

lemma cavity_radial_square_cutoff {α : Type*} (Y : α → ℝ) (hY : ∀ x, 0 ≤ Y x)
    {R : ℝ} (hR : 0 ≤ R) :
    {x | Y x ≤ R} = {x | 1+(Y x)^2 ≤ 1+R^2} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have hy := hY x
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hR hy)]
  · intro h
    nlinarith [hY x]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary fourth moment bound after averaging over the original
Gibbs prior and the independent fresh Haar frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × X =>
      cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  dsimp only [cavitySelectedSiteProjection]
  apply Finset.measurable_sum
  intro l _
  exact (((measurable_pi_apply l).comp ((measurable_pi_apply (e j).1).comp
    ((hv x).comp measurable_fst))).mul
      (((measurable_pi_apply (e j).2).comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply (e j).1).comp
          ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary boundedness and product identities for the restricted
finite-spin factor used in the actual cavity Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityRestrictedFactor_mem {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    cavityRestrictedFactor K L C T B y ε ∈ Icc 0 (Real.exp T) := by
  unfold cavityRestrictedFactor
  split_ifs
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr (min_le_right _ _)⟩
  · exact ⟨le_rfl,(Real.exp_pos _).le⟩

lemma measurable_cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityRestrictedFactor K L C T B p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro ε
  apply Measurable.ite _ _ measurable_const
  · apply measurableSet_le _ measurable_const
    fun_prop
  · exact (((continuous_cavityLogFactor K L C ε).measurable).min measurable_const).exp

lemma measurable_cavityRestrictedFactor_comp {d k : ℕ} {E : Type*} [MeasurableSpace E]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (Y : E → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (ε : E → Spin k) (hε : Measurable ε) :
    Measurable (fun x => cavityRestrictedFactor K L C T B (Y x) (ε x)) := by
  have hp : Measurable (fun x => (Y x,ε x)) := hY.prodMk hε
  change Measurable ((fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ (fun x => (Y x,ε x)))
  exact Measurable.comp (g := fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) (f := fun x => (Y x,ε x))
      (measurable_cavityRestrictedFactor K L C T B) hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded restricted factor as a measurable function of the
original disorder, fresh group rotation, base state and cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityHaarRestrictedWeight e v A₀ K L C T B) := by
  apply measurable_from_prod_countable_left
  intro x
  have hy : Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavitySelectedSiteProjection e (v z.1) (cavityGroupHaarFrames A₀ z.2) x.1) :=
    (measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const))
  exact measurable_cavityRestrictedFactor_comp K L C T B _ hy (fun _ => x.2) measurable_const

lemma cavityHaarRestrictedWeight_mem {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) :
    cavityHaarRestrictedWeight e v A₀ K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRegularizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and boundedness of the regularized replica mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma measurable_cavityRegularizedReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) (δ : ℝ) :
    Measurable (fun ω => cavityRegularizedReplicaMean (ν ω)
      (fun x => w (ω,x)) (fun σ => F (ω,σ)) δ) :=
  (measurable_cavityWeightNumerator ν hν w hw F hF).div
    (((measurable_cavityWeightNormalizer ν hν w hw).add_const δ).pow_const r)

lemma cavityRegularizedReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F)
    {M B δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hwb : ∀ x, w x ∈ Icc 0 M) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityRegularizedReplicaMean ν w F δ| ≤ B :=
  cavity_regularized_numerator_bound
    (cavityWeightNormalizer_mem ν w hw le_rfl hwb).1 hB hδ r
    (cavityWeightNumerator_abs_le_normalizer ν w hw F hF hM hB hwb hFb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProductDisorderWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-disorder integration for normalized restricted weights and
the Gaussian/fresh-frame permutation used by the canonical cavity law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_bounded_disorder_shuffle {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (R : Measure C) [IsProbabilityMeasure R]
    (f : (A × B) × C → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂(P.prod Q).prod R) = ∫ a, ∫ c, ∫ b, f ((a,b),c) ∂Q ∂ R ∂P := by
  have hi := integrable_of_measurable_abs_le (μ := (P.prod Q).prod R) hf hb
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with a
  have hm : Measurable (fun p : B × C => f ((a,p.1),p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact integral_integral_swap (integrable_of_measurable_abs_le (μ := Q.prod R) hm
    (fun p => hb ((a,p.1),p.2)))

lemma cavity_bounded_disorder_dirac_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (b : B)
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R) =
      ∫ a, ∫ d, ∫ c, f (((a,b),c),d) ∂Q ∂ R ∂P := by
  rw [cavity_bounded_disorder_shuffle (P.prod (Measure.dirac b)) Q R f hf hb,
    Measure.prod_dirac]
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  exact integral_map_of_stronglyMeasurable measurable_prodMk_right
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactorIndicator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Above its deterministic spatial bound, the energy cap is inactive.
The resulting factor is exactly the hard spatial restriction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavityRestrictedFactor_eq_indicator {d k : ℕ} {X : Type*}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (Y : X → EuclideanSpace ℝ (Fin d)) (ε : X → Spin k) (x : X) :
    cavityRestrictedFactor K L C T B (Y x) (ε x) =
      {x | ‖Y x‖ ≤ B}.indicator (fun x => Real.exp (cavityLogFactor K L C (Y x) (ε x))) x := by
  have he : 1+‖Y x‖^2 ≤ 1+B^2 ↔ ‖Y x‖ ≤ B := by
    constructor
    · intro h
      exact (sq_le_sq₀ (norm_nonneg _) hB).mp (by linarith)
    · intro h
      have hs := (sq_le_sq₀ (norm_nonneg _) hB).mpr h
      linarith
  unfold cavityRestrictedFactor
  simp only [he]
  by_cases hx : ‖Y x‖ ≤ B
  · have hlog : cavityLogFactor K L C (Y x) (ε x) ≤ T :=
      (le_abs_self _).trans ((cavity_logFactor_growth K L C (Y x) (ε x)).trans
        ((mul_le_mul_of_nonneg_left (he.mpr hx) (cavityFactorSize_nonneg K L C)).trans hT))
    simp only [hx,ite_true, if_true,min_eq_left hlog]
    rw [Set.indicator_of_mem (show x ∈ {x | ‖Y x‖ ≤ B} from hx)]
  · simp only [hx,ite_false, if_false]
    rw [Set.indicator_of_notMem (show x ∉ {x | ‖Y x‖ ≤ B} from hx)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual measurable base spin/leaf Gibbs probability, with its
rotation, cascade weights and Gaussian disorder all retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityRotationProbability_eq_tilted_ae {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (V : Orthogonal N) (T : LabeledTree depth) :
    ∀ᵐ z ∂gaussianCoordinates, cavityRotationProbability eig I u ((V,T),z) =
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) := by
  filter_upwards [cavity_rotation_exp_integrable_ae (matrixRotation V⁻¹) T eig I u hu]
    with z hz
  exact gibbsProbability_eq_tilted _ _ hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable physical group vectors and their covariance in the actual
base Gibbs disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p a => cavityRotationVectors k e p a x) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro j
  exact (measurable_cavityRotation_eval (spinVector x.1) (e ⟨a,j⟩)).comp measurable_fst.fst

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalRestrictedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical cutoff mean, with fixed tree, is exactly the
restricted Haar Gibbs model used in the finite-replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix

namespace InvariantIsing

theorem cavity_canonical_restricted_law {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t : ℝ) (A : CavityFactorBlocks d n)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let E := cavityBaseGroupEquiv k e g
    let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
      (cavitySpectralGroup (fun i => (E.symm i).1)) v t
    let K := t • A.1
    let L := t • A.2.1
    let C := t • A.2.2
    let τ := cavityFactorSize K L C * (1+R^2)
    (∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig
        (cavitySpectralGroup (fun i => (E.symm i).1)) u p.1).prod (uniformSpinPrior n))
      (fun x => cavityHaarRestrictedWeight (fun j => (g j,j))
        (cavityRotationVectors (cavityBaseGroupDimension k g) E)
        (cavityCanonicalGroupFrame k e g hk) K L C τ R (p,x)) F
      ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)) =
    cavityCanonicalGroupCutoffMean k e g hk μ η T lam v u t (1+R^2) A F := by
  intro E eig K L C τ
  let I := cavitySpectralGroup (fun i => (E.symm i).1)
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight (fun j => (g j,j))
    (cavityRotationVectors (depth := depth) (cavityBaseGroupDimension k g) E)
    (cavityCanonicalGroupFrame k e g hk) K L C τ R
  let κ := cavityHaarSpinPriorKernel
    (U := (a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a))
    ν (measurable_cavityRotationProbability eig I u) (uniformSpinPrior n : Measure (Spin n))
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight _ _
    (measurable_cavityRotationVectors _ E) _ K L C τ R
  have hm : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd) 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos τ).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem _ _ _ K L C τ R (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hs := cavity_bounded_disorder_dirac_shuffle μ T gaussianCoordinates η f hm hb
  change _ = ∫ V, ∫ W, ∫ z, _ ∂gaussianCoordinates ∂η ∂μ
  rw [show (∫ p, cavityWeightedReplicaMean ((ν p.1).prod (uniformSpinPrior n))
      (fun x => w (p,x)) F ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)) =
      ∫ p, f p ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η) by
    simp only [f,κ,cavityHaarSpinPriorKernel_apply]]
  rw [hs]
  apply integral_congr_ae
  filter_upwards [] with V
  apply integral_congr_ae
  filter_upwards [] with W
  apply integral_congr_ae
  filter_upwards [cavityRotationProbability_eq_tilted_ae eig I u hu V T] with z hz
  simp only [f,κ,cavityHaarSpinPriorKernel_apply]
  rw [show ν ((V,T),z) = _ from hz]
  congr 1
  funext x
  have he := cavityRestrictedFactor_eq_indicator K L C τ hR (le_refl _)
    (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavitySelectedSiteProjection (fun j => (g j,j))
        (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
        (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e g hk) W) x.1.1)
    Prod.snd x
  change cavityRestrictedFactor K L C τ R
    (cavitySelectedSiteProjection (fun j => (g j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
      (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e g hk) W) x.1.1) x.2 = _
  rw [he]
  rw [cavity_radial_square_cutoff _ (fun x => norm_nonneg _) hR]
  simp only [K,L,C,E,cavityLogFactor_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalGroupFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original full-system cutoff and its actual fresh-group Gibbs
representation have the same limit after deterministic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Matrix Topology

namespace InvariantIsing

theorem cavity_original_group_cutoff_limit_family {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      cavityCanonicalGroupCutoffMean (k j) (e j) a₀ (hk j) (ν j) (η j) (T j)
        lam (v j) (u j) t D A₀ (fun σ => F j (fun i => cavityPairLeafUnswap (σ i))))
      atTop (𝓝 0) := by
  have hh := cavity_haar_cutoff_limit_family N depth hN hNlim g k ek e es B₀ a₀ l w hg hln hw
    μ ν T lam v hv u hu t hD hM F hF A₀ hprob
  apply hh.congr'
  filter_upwards [] with j
  congr 1
  exact cavity_canonical_weighted_average (k j) (e j) a₀ (hk j) (ν j) (η j)
    (T j) lam (v j) (u j) (hu j) t D A₀ (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    hM (fun σ => hF j _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalRestrictedFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original cutoff spin law and the concrete restricted fresh-Haar
law agree asymptotically after coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_original_restricted_haar_limit_family_oai {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (Measure.dirac (T j))).prod gaussianCoordinates).prod (η j)))
      atTop (𝓝 0) := by
  intro E eig τ
  have hh := cavity_original_group_cutoff_limit_family N depth hN hNlim g k ek e es B₀ a₀ hk η
    l w hg hln hw μ ν T lam v hv u hu t (le_add_of_nonneg_right (sq_nonneg R)) hM
    (fun j σ => F j (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
    (fun j σ => hF j _) A hprob
  apply hh.congr'
  filter_upwards [] with j
  have he := cavity_canonical_restricted_law (k j) (e j) a₀ (hk j) (ν j) (η j)
    (T j) lam (v j) (u j) (hu j) t A hR hM (F j) (hF j)
  dsimp only at he
  rw [he]
  rfl

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_original_restricted_haar_limit_family_oai := @OAI.InvariantIsing.cavity_original_restricted_haar_limit_family_oai
