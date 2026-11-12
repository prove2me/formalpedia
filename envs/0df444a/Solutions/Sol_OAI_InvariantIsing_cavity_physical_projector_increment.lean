-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_physical_projector_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:09.36052+00:00
-- url     : https://prove2.me/submissions/fff6f1c0-ce91-4df1-a030-80b159c4e47c

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_capped_energy_increment

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

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-volume algebra for the coupled cavity comparison.  The
spectral coupling and its Gaussian limit are separate source obligations. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    cavityQuadratic (A - B) y = cavityQuadratic A y - cavityQuadratic B y := by
  simp only [cavityQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity exponent difference in the original coordinates. The
retained interaction cancels; only the special and cavity projections
enter the factor. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_dotProduct {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic A x = (1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x)) := by
  simp only [cavityQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma cavityQuadratic_add {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic (A + B) x = cavityQuadratic A x + cavityQuadratic B x := by
  simp only [cavityQuadratic, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma cavityQuadratic_transpose {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cavityQuadratic A.transpose x = cavityQuadratic A x := by
  rw [cavityQuadratic_dotProduct, cavityQuadratic_dotProduct,
    Matrix.dotProduct_transpose_mulVec]

lemma cavityQuadratic_rectangular {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin n) ℝ) (x : Fin r → ℝ) :
    cavityQuadratic (V * K * E.transpose) x =
      (1 / 2 : ℝ) * ((V.transpose *ᵥ x) ⬝ᵥ (K *ᵥ (E.transpose *ᵥ x))) := by
  rw [cavityQuadratic_dotProduct]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem cavityPhysicalChange_factor {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin r → ℝ)
    (ε : Spin n) (hε : E.transpose *ᵥ x = fun j => spinValue (ε j)) :
    cavityQuadratic (cavityPhysicalChange V E K L C) x =
      cavityLogFactor K L C (V.transpose *ᵥ x) ε := by
  simp only [cavityPhysicalChange, cavityQuadratic_add, cavityQuadratic_transpose]
  simp only [cavityQuadratic_rectangular, hε]
  rw [cavityLogFactor, cavityQuadratic_dotProduct, cavityQuadratic_dotProduct]
  have he : ((V.transpose *ᵥ x) ⬝ᵥ (L *ᵥ fun j => spinValue (ε j))) =
      ∑ i, ∑ j, (V.transpose *ᵥ x) i * L i j * spinValue (ε j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [he]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_det_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : G.PosDef) : IsUnit (CFC.sqrt G).det := by
  apply isUnit_iff_ne_zero.mpr
  have he : (CFC.sqrt G).det * (CFC.sqrt G).det = G.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  intro hz
  rw [hz, zero_mul] at he
  exact hG.det_pos.ne' he.symm

theorem cavityNormalizeFrame_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hG : (A.transpose * A).PosDef) :
    (cavityNormalizeFrame A).transpose * cavityNormalizeFrame A = 1 := by
  let G : Matrix (Fin q) (Fin q) ℝ := A.transpose * A
  let S : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hs : S.transpose = S :=
    Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hss : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hu : IsUnit S.det := cavity_sqrt_det_isUnit G hG
  change (A * S⁻¹).transpose * (A * S⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs]
  calc
    S⁻¹ * A.transpose * (A * S⁻¹) = S⁻¹ * G * S⁻¹ := by
      simp only [G, Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hss]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv S hu]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameTransitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the limiting cavity columns by a fixed orthonormal special
frame. This is the reference frame for the continuous complement rule. -/

noncomputable section
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_frame_completion {d n : ℕ}
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ B : Matrix (Fin (d + n)) (Fin d) ℝ,
      B.transpose * B = 1 ∧ E.transpose * B = 0 := by
  let e := EuclideanSpace.basisFun (Fin (d + n)) ℝ
  have hr : Orthonormal ℝ (fun j : Fin n => e (Fin.natAdd d j)) :=
    e.orthonormal.comp _ (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive
    (fun j : Fin n => e (Fin.natAdd d j))
    (fun j : Fin n => WithLp.toLp 2 (fun i => E i j)) hr (cavity_orthonormal_of_gram E hE)
  let B : Matrix (Fin (d + n)) (Fin d) ℝ := fun i j => U (e (Fin.castAdd n j)) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    change (∑ k, U (e (Fin.castAdd n i)) k * U (e (Fin.castAdd n j)) k) =
      if i = j then 1 else 0
    have hh := U.inner_map_map (e (Fin.castAdd n i)) (e (Fin.castAdd n j))
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n i) (Fin.castAdd n j)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fin.castAdd_inj, mul_comm] using hh.trans he
  · ext i j
    change (∑ k, E k i * U (e (Fin.castAdd n j)) k) = 0
    have hh := U.inner_map_map (e (Fin.castAdd n j)) (e (Fin.natAdd d i))
    rw [hU i] at hh
    have hne : Fin.castAdd n j ≠ Fin.natAdd d i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n j) (Fin.natAdd d i)
    rw [ite_eq_right hne] at he
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply] using hh.trans he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavitySpectralStack_gram {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (cavitySpectralStack M).transpose * cavitySpectralStack M = ∑ a, M a := by
  ext i j
  change (∑ k : Fin (m * n),
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 i *
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (CFC.sqrt (M a)).transpose = CFC.sqrt (M a) :=
    Matrix.isHermitian_iff_isSymm.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M a))).isHermitian
  have he := CFC.sqrt_mul_sqrt_self (M a) (hM a).nonneg
  have he' : (CFC.sqrt (M a)).transpose * CFC.sqrt (M a) = M a := by
    rw [hs, he]
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) he'
  exact hentry

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityNormalizeFrame_mul_sqrt {r n : ℕ}
    (X : Matrix (Fin r) (Fin n) ℝ) (hX : (X.transpose * X).PosDef) :
    cavityNormalizeFrame X * CFC.sqrt (X.transpose * X) = X := by
  rw [cavityNormalizeFrame, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (cavity_sqrt_det_isUnit _ hX), Matrix.mul_one]

lemma cavityNormalizeFrame_crossGram {r n : ℕ}
    (X Y : Matrix (Fin r) (Fin n) ℝ) (hXY : X.transpose * Y = 0) :
    (cavityNormalizeFrame X).transpose * cavityNormalizeFrame Y = 0 := by
  simp only [cavityNormalizeFrame, Matrix.transpose_mul]
  calc
    _ = ((CFC.sqrt (X.transpose * X))⁻¹).transpose *
        (X.transpose * Y) * (CFC.sqrt (Y.transpose * Y))⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hXY, Matrix.mul_zero, Matrix.zero_mul]

theorem cavityEigenspaceFrame_gram {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0) :
    (cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X = 1 := by
  classical
  ext i j
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm j).1
  let s := (finProdFinEquiv.symm i).2
  let t := (finProdFinEquiv.symm j).2
  change ((cavityNormalizeFrame (X a)).transpose * cavityNormalizeFrame (X b)) s t =
    if i = j then 1 else 0
  by_cases hab : a = b
  · rw [← hab, cavityNormalizeFrame_gram _ (hX a), Matrix.one_apply]
    have hij : i = j ↔ s = t := by
      constructor
      · intro h; subst j; rfl
      · intro h
        apply (finProdFinEquiv.symm : Fin (m * n) ≃ Fin m × Fin n).injective
        exact Prod.ext hab h
    simp only [hij]
  · rw [cavityNormalizeFrame_crossGram _ _ (hXY a b hab), Matrix.zero_apply]
    have hij : i ≠ j := by
      intro h; subst j; exact hab rfl
    simp only [hij, ite_false, if_false]

theorem cavityEigenspaceFrame_stack {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef) :
    cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) =
      ∑ a, X a := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 *
    CFC.sqrt ((X (finProdFinEquiv.symm k).1).transpose * X (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun A : Matrix (Fin r) (Fin n) ℝ => A i j)
    (cavityNormalizeFrame_mul_sqrt (X a) (hX a))

lemma cavityNormalizeFrame_eigen {r n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (X : Matrix (Fin r) (Fin n) ℝ)
    (lam : ℝ) (hDX : D * X = lam • X) :
    D * cavityNormalizeFrame X = lam • cavityNormalizeFrame X := by
  simp only [cavityNormalizeFrame, ← Matrix.mul_assoc, hDX, Matrix.smul_mul]

theorem cavityEigenspaceFrame_eigen {r m n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hDX : ∀ a, D * X a = lam a • X a) :
    D * cavityEigenspaceFrame X =
      cavityEigenspaceFrame X * cavityRepeatedSpectrum (n := n) lam := by
  ext i j
  have h := congrArg (fun A : Matrix (Fin r) (Fin n) ℝ =>
    A i (finProdFinEquiv.symm j).2)
      (cavityNormalizeFrame_eigen D (X (finProdFinEquiv.symm j).1)
        (lam (finProdFinEquiv.symm j).1) (hDX _))
  change (∑ k, D i k * cavityNormalizeFrame (X (finProdFinEquiv.symm j).1)
    k (finProdFinEquiv.symm j).2) = _ at h
  rw [cavityRepeatedSpectrum, Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, cavityEigenspaceFrame, Matrix.smul_apply, smul_eq_mul,
    mul_comm] using h

theorem cavityEigenspaceFrame_special_perp {r m n d : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * cavitySpectralStack (fun a => (X a).transpose * X a) = 0) :
    (cavityEigenspaceFrame X * B).transpose * (∑ a, X a) = 0 := by
  rw [← cavityEigenspaceFrame_stack X hX, Matrix.transpose_mul]
  calc
    _ = B.transpose * ((cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X) *
        cavitySpectralStack (fun a => (X a).transpose * X a) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [cavityEigenspaceFrame_gram X hX hXY, Matrix.mul_one, hB]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySpectralImage_sum {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) : ∑ a, cavitySpectralImage g A a = A := by
  ext i j
  simp only [Matrix.sum_apply, cavitySpectralImage, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, if_true]

lemma cavitySpectralImage_crossGram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a b : Fin m) (hab : a ≠ b) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A b = 0 := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = b then A k j else 0)) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · simp only [ha, hab, ite_true, if_true, ite_false, if_false, mul_zero]
  · simp only [ha, ite_false, if_false, zero_mul]

lemma cavitySpectralImage_gram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A a =
      A.transpose * Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) * A := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = a then A k j else 0)) =
    ∑ k : Fin r, (∑ t : Fin r,
      A t i * (if t = k then (if g t = a then (1 : ℝ) else 0) else 0)) * A k j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma cavitySpectralImage_eigen {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ) (a : Fin m) :
    Matrix.diagonal (fun i => lam (g i)) * cavitySpectralImage g A a =
      lam a • cavitySpectralImage g A a := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  change lam (g i) * (if g i = a then A i j else 0) =
    lam a * (if g i = a then A i j else 0)
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the cavity directions inside each spectral group. The added
columns are retained eigenvectors supported in the same group. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityGroupLift_support {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (B : Matrix (Fin q) (Fin t) ℝ)
    (i : Fin r) (hi : g i ≠ a) (j : Fin t) : cavityGroupLift g a e B i j = 0 := by
  simp only [cavityGroupLift, hi, dite_false]

lemma cavityGroupLift_gram {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ) :
    (cavityGroupLift g a e B).transpose * cavityGroupLift g a e C = B.transpose * C := by
  classical
  ext i j
  change (∑ k : Fin r, cavityGroupLift g a e B k i * cavityGroupLift g a e C k j) =
    ∑ k : Fin q, B k i * C k j
  calc
    _ = ∑ k : {k : Fin r // g k = a}, B (e k) i * C (e k) j := by
      apply Finset.sum_congr_set {k : Fin r | g k = a}
      · intro k hk
        change g k = a at hk
        simp only [cavityGroupLift, hk, dite_true]
      · intro k hk
        change g k ≠ a at hk
        simp only [cavityGroupLift, hk, dite_false, zero_mul]
    _ = _ := Equiv.sum_comp e (fun k : Fin q => B k i * C k j)

lemma cavityGroupLift_restrict {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (W : Matrix (Fin r) (Fin t) ℝ)
    (hW : ∀ i, g i ≠ a → ∀ j, W i j = 0) :
    cavityGroupLift g a e (fun i j => W (e.symm i) j) = W := by
  ext i j
  by_cases hi : g i = a
  · simp only [cavityGroupLift, hi, dite_true, Equiv.symm_apply_apply]
  · simp only [cavityGroupLift, hi, dite_false, hW i hi j]

lemma cavityNormalizeFrame_spectral_support {r m n : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (i : Fin r) (hi : g i ≠ a) (j : Fin n) :
    cavityNormalizeFrame (cavitySpectralImage g A a) i j = 0 := by
  change (∑ k : Fin n, cavitySpectralImage g A a i k * _) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp only [cavitySpectralImage, hi, ite_false, if_false, zero_mul]

lemma cavity_complement_projection {k n : ℕ}
    (B : Matrix (Fin (k + n)) (Fin k) ℝ) (Y : Matrix (Fin (k + n)) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hY : Y.transpose * Y = 1)
    (hYB : Y.transpose * B = 0) :
    B * B.transpose + Y * Y.transpose = 1 := by
  have hBY : B.transpose * Y = 0 := by
    have h := congrArg Matrix.transpose hYB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B Y).transpose * Matrix.fromCols B Y = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBY, hYB, hY,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n))).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

lemma cavityGroupLift_projection {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ)
    (hBC : B * B.transpose + C * C.transpose = 1) :
    cavityGroupLift g a e B * (cavityGroupLift g a e B).transpose +
      cavityGroupLift g a e C * (cavityGroupLift g a e C).transpose =
        Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  classical
  ext i j
  by_cases hi : g i = a <;> by_cases hj : g j = a
  · have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℝ =>
      M (e ⟨i, hi⟩) (e ⟨j, hj⟩)) hBC
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, Matrix.one_apply, Equiv.apply_eq_iff_eq,
      Subtype.mk.injEq, Matrix.diagonal_apply, ite_true, if_true] using h
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, zero_mul, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_false, zero_mul, Finset.sum_const_zero, add_zero]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, hi, ite_false, if_false]
    · rw [Matrix.diagonal_apply_ne _ hij]

theorem cavityRetainedFrame_exists {r m n k : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin (k + n))
    (hA : ((cavitySpectralImage g A a).transpose * cavitySpectralImage g A a).PosDef) :
    ∃ R : Matrix (Fin r) (Fin k) ℝ,
      R.transpose * R = 1 ∧
      (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose * R = 0 ∧
      (∀ i, g i ≠ a → ∀ j, R i j = 0) ∧
      R * R.transpose + cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  let W := cavityNormalizeFrame (cavitySpectralImage g A a)
  let Y : Matrix (Fin (k + n)) (Fin n) ℝ := fun i j => W (e.symm i) j
  have hW : cavityGroupLift g a e Y = W :=
    cavityGroupLift_restrict g a e W (cavityNormalizeFrame_spectral_support g A a)
  have hY : Y.transpose * Y = 1 := by
    rw [← cavityGroupLift_gram g a e Y Y, hW]
    exact cavityNormalizeFrame_gram _ hA
  obtain ⟨B, hB, hYB⟩ := cavity_frame_completion Y hY
  refine ⟨cavityGroupLift g a e B, ?_, ?_, ?_, ?_⟩
  · rw [cavityGroupLift_gram, hB]
  · change W.transpose * cavityGroupLift g a e B = 0
    rw [← hW, cavityGroupLift_gram, hYB]
  · exact cavityGroupLift_support g a e B
  · change _ + W * W.transpose = _
    rw [← hW]
    exact cavityGroupLift_projection g a e B Y (cavity_complement_projection B Y hB hY hYB)

lemma cavitySpectralSupport_crossGram {r m s t : ℕ}
    (g : Fin r → Fin m) (a b : Fin m) (hab : a ≠ b)
    (V : Matrix (Fin r) (Fin s) ℝ) (W : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0)
    (hW : ∀ i, g i ≠ b → ∀ j, W i j = 0) : V.transpose * W = 0 := by
  ext i j
  change (∑ k, V k i * W k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · have hb : g k ≠ b := fun h => hab (ha.symm.trans h)
    rw [hW k hb j, mul_zero]
  · rw [hV k ha i, zero_mul]

lemma cavitySpectralSupport_eigen {r m t : ℕ}
    (g : Fin r → Fin m) (a : Fin m) (lam : Fin m → ℝ)
    (V : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * V = lam a • V := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  by_cases hi : g i = a
  · rw [hi]; rfl
  · rw [hV i hi j, mul_zero, smul_zero]

lemma cavitySpectralProjectors_sum {r m : ℕ} (g : Fin r → Fin m) :
    (∑ a, Matrix.diagonal (fun i : Fin r => if g i = a then (1 : ℝ) else 0)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true, Matrix.one_apply_eq]
  · simp only [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij,
      Finset.sum_const_zero, Matrix.one_apply_ne hij]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseReplacement
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal and replacement of the small spectral block. The base
matrix is defined without choosing bases in the retained eigenspaces. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityPhysicalChange_sub_special {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    cavityPhysicalChange V E (A - A₀) L C =
      cavityPhysicalChange V E A L C - V * A₀ * V.transpose := by
  simp only [cavityPhysicalChange, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma cavityPhysicalChange_pullback {r s d n : ℕ}
    (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    cavityPhysicalChange (W * B) (W * E) A L C =
      W * cavityPhysicalChange B E A L C * W.transpose := by
  simp only [cavityPhysicalChange, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]

lemma cavityPhysicalChange_reconstruct {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1) :
    cavityPhysicalChange B E (B.transpose * D * B) (B.transpose * D * E)
      (E.transpose * D * E) = D := by
  calc
    _ = (B * B.transpose + E * E.transpose) * D *
        (B * B.transpose + E * E.transpose) := by
      simp only [cavityPhysicalChange, Matrix.transpose_mul, Matrix.transpose_transpose,
        hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      abel
    _ = D := by rw [hBE, Matrix.one_mul, Matrix.mul_one]

theorem cavityBaseReplacement_difference {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    J - cavityBaseReplacement J W D B A₀ =
      cavityPhysicalChange (W * B) (W * E) (B.transpose * D * B - A₀)
        (B.transpose * D * E) (E.transpose * D * E) := by
  rw [cavityPhysicalChange_sub_special, cavityPhysicalChange_pullback,
    cavityPhysicalChange_reconstruct D hD B E hBE, cavityBaseReplacement]
  abel

theorem cavityBaseReplacement_energy_difference {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (hD : D.transpose = D)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hBE : B * B.transpose + E * E.transpose = 1)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (x : Fin r → ℝ) (ε : Spin n)
    (hε : (W * E).transpose *ᵥ x = fun j => spinValue (ε j)) :
    cavityQuadratic J x - cavityQuadratic (cavityBaseReplacement J W D B A₀) x =
      cavityLogFactor (B.transpose * D * B - A₀) (B.transpose * D * E)
        (E.transpose * D * E) ((W * B).transpose *ᵥ x) ε := by
  rw [← cavityQuadratic_sub, cavityBaseReplacement_difference J W D hD B E hBE A₀]
  exact cavityPhysicalChange_factor _ _ _ _ _ x ε hε

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the retained group frames without imposing equal group
sizes. The separate group projector identities give completeness. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavityRetainedStack_gram {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, (R a).transpose * R a = 1)
    (hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0) :
    (cavityRetainedStack k R).transpose * cavityRetainedStack k R = 1 := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  change ((R a).transpose * R b) i j = if (⟨a, i⟩ : Sigma fun a => Fin (k a)) = ⟨b, j⟩ then 1 else 0
  by_cases hab : a = b
  · subst b
    rw [hR, Matrix.one_apply]
    simp
  · rw [hcross a b hab, Matrix.zero_apply]
    have hij : (⟨a, i⟩ : Sigma fun a => Fin (k a)) ≠ ⟨b, j⟩ := fun h => hab (congrArg Sigma.fst h)
    simp only [hij, ite_false, if_false]

theorem cavityRetainedStack_outer {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose =
      ∑ a, R a * (R a).transpose := by
  ext i j
  change (∑ a : Sigma fun a => Fin (k a), R a.1 i a.2 * R a.1 j a.2) = _
  simp only [Fintype.sum_sigma, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityEigenspaceFrame_outer {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) :
    cavityEigenspaceFrame X * (cavityEigenspaceFrame X).transpose =
      ∑ a, cavityNormalizeFrame (X a) * (cavityNormalizeFrame (X a)).transpose := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 * cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
      j (finProdFinEquiv.symm k).2) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]

theorem cavityRetainedStack_complete {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0)) :
    cavityRetainedStack k R * (cavityRetainedStack k R).transpose +
      cavityEigenspaceFrame (cavitySpectralImage g A) *
        (cavityEigenspaceFrame (cavitySpectralImage g A)).transpose = 1 := by
  rw [cavityRetainedStack_outer, cavityEigenspaceFrame_outer, ← Finset.sum_add_distrib]
  simp only [hR]
  exact cavitySpectralProjectors_sum g

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseEigenspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The replaced interaction preserves retained eigenvectors, gives the
special axes their assigned eigenvalues, and annihilates the cavity. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_cavity {r s d n : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (E : Matrix (Fin s) (Fin n) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hJW : J * W = W * D) (hW : W.transpose * W = 1) (hBE : B.transpose * E = 0) :
    cavityBaseReplacement J W D B A₀ * (W * E) = 0 := by
  have hJE : J * (W * E) = W * D * E := by rw [← Matrix.mul_assoc, hJW]
  have hWE : W.transpose * (W * E) = E := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hBB : (W * B).transpose * (W * E) = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWE, hBE]
  rw [cavityBaseReplacement, Matrix.add_mul, Matrix.sub_mul, hJE,
    Matrix.mul_assoc (W * D) W.transpose (W * E), hWE, sub_self, zero_add,
    Matrix.mul_assoc (W * B * A₀) (W * B).transpose (W * E), hBB, Matrix.mul_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseSpectralSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base interaction has an explicit spectral decomposition. Its
retained multiplicities and the assigned special multiplicities add to
the required base counts. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_spectral_sum {r s d : ℕ} {ι : Type*} [Fintype ι]
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin r) ι ℝ) (L : Matrix ι ι ℝ)
    (hJR : J * R = R * L) (hJW : J * W = W * D)
    (hcomplete : R * R.transpose + W * W.transpose = 1) :
    cavityBaseReplacement J W D B A₀ =
      R * L * R.transpose + (W * B) * A₀ * (W * B).transpose := by
  have hJ : J = R * L * R.transpose + W * D * W.transpose := by
    calc
      J = J * (R * R.transpose + W * W.transpose) := by rw [hcomplete, Matrix.mul_one]
      _ = _ := by rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJR, hJW]
  unfold cavityBaseReplacement
  rw [hJ]
  abel

lemma cavityRetainedStack_perp {r m n : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hRX : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0) :
    (cavityRetainedStack k R).transpose * cavityEigenspaceFrame X = 0 := by
  ext ⟨a, i⟩ j
  exact congrArg (fun M : Matrix (Fin (k a)) (Fin n) ℝ =>
    M i (finProdFinEquiv.symm j).2) (hRX a (finProdFinEquiv.symm j).1)

lemma cavityRetainedStack_eigen {r m : ℕ} (g : Fin r → Fin m) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * cavityRetainedStack k R =
      cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) := by
  ext i ⟨a, j⟩
  have h := congrArg (fun M : Matrix (Fin r) (Fin (k a)) ℝ => M i j)
    (cavitySpectralSupport_eigen g a lam (R a) (hR a))
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.diagonal_mul, cavityRetainedStack, Matrix.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem cavityBase_spectral_decomposition {r m n d : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g A)) (cavityRepeatedSpectrum (n := n) lam) B A₀ =
        cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) *
          (cavityRetainedStack k R).transpose +
        (cavityEigenspaceFrame (cavitySpectralImage g A) * B) * A₀ *
          (cavityEigenspaceFrame (cavitySpectralImage g A) * B).transpose := by
  apply cavityBaseReplacement_spectral_sum
  · exact cavityRetainedStack_eigen g lam k R hR
  · exact cavityEigenspaceFrame_eigen _ _ lam (cavitySpectralImage_eigen g A lam)
  · exact cavityRetainedStack_complete g A k R hproj

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReservoirFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orthonormal base frame perpendicular to the physical cavity
coordinates gives an orthogonal eigenbasis of the reservoir. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseFrame_gram {r s d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1) :
    (Matrix.fromCols R (W * B)).transpose * Matrix.fromCols R (W * B) = 1 := by
  have hRV : R.transpose * (W * B) = 0 := by rw [← Matrix.mul_assoc, hRW, Matrix.zero_mul]
  have hVR : (W * B).transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hVV : (W * B).transpose * (W * B) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = B.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.mul_one, hB]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hR, hRV, hVR, hVV,
    Matrix.fromBlocks_one]

lemma cavityBaseFrame_cavity_perp {r s d n : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) ι ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ)
    (hW : W.transpose * W = 1) (hRW : R.transpose * W = 0)
    (hBE : B.transpose * E = 0) :
    (W * E).transpose * Matrix.fromCols R (W * B) = 0 := by
  have hWR : W.transpose * R = 0 := by
    have h := congrArg Matrix.transpose hRW
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hER : (W * E).transpose * R = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hWR, Matrix.mul_zero]
  have hEV : (W * E).transpose * (W * B) = 0 := by
    rw [Matrix.transpose_mul]
    calc
      _ = E.transpose * (W.transpose * W) * B := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hW, Matrix.mul_one, hEB]
  rw [Matrix.mul_fromCols, hER, hEV, Matrix.fromCols_zero]

lemma cavityBaseFrame_spectral_sum {r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix (Fin r) ι ℝ) (V : Matrix (Fin r) (Fin d) ℝ)
    (lam : ι → ℝ) (lam₀ : Fin d → ℝ) :
    Matrix.fromCols R V * Matrix.diagonal (Sum.elim lam lam₀) *
      (Matrix.fromCols R V).transpose =
        R * Matrix.diagonal lam * R.transpose + V * Matrix.diagonal lam₀ * V.transpose := by
  rw [← Matrix.fromBlocks_diagonal, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
  simp only [Matrix.mul_zero, add_zero, zero_add,
    Matrix.fromCols_mul_fromRows]

lemma cavityReservoirRows_conjugate {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ) (L : Matrix ι ι ℝ) :
    (F * L * F.transpose).submatrix (Fin.castAdd n) (Fin.castAdd n) =
      cavityReservoirRows F * L * (cavityReservoirRows F).transpose := by
  ext i j
  rfl

lemma cavityReservoirRows_gram {N n : ℕ} {ι : Type*} [Fintype ι]
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    (cavityReservoirRows F).transpose * cavityReservoirRows F = F.transpose * F := by
  ext i j
  change (∑ k : Fin N, F (k.castAdd n) i * F (k.castAdd n) j) =
    ∑ k : Fin (N + n), F k i * F k j
  rw [Fin.sum_univ_add]
  simp only [hF, zero_mul, Finset.sum_const_zero, add_zero]

lemma cavityReservoirRows_orthogonal {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ)
    (hG : F.transpose * F = 1)
    (hF : ∀ i : Fin n, ∀ j, F (Fin.natAdd N i) j = 0) :
    ∃ U : Orthogonal N, ∀ i j, (U : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows F i (e.symm j) := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j => cavityReservoirRows F i (e.symm j)
  have hA : A.transpose * A = 1 := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ => M (e.symm i) (e.symm j))
      ((cavityReservoirRows_gram F hF).trans hG)
    change (∑ k : Fin N, cavityReservoirRows F k (e.symm i) *
      cavityReservoirRows F k (e.symm j)) = if i = j then 1 else 0
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq] using hh
  exact ⟨⟨A, (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mpr hA⟩, fun _ _ => rfl⟩

lemma cavityPhysicalFrame_lastRows {N n : ℕ} {ι : Type*} [Fintype ι]
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : (show Matrix (Fin (N + n)) (Fin n) ℝ from
      fun i j => U i (Fin.natAdd N j)).transpose * F = 0) :
    ∀ i : Fin n, ∀ j, (U.transpose * F) (Fin.natAdd N i) j = 0 := by
  intro i j
  exact congrArg (fun M : Matrix (Fin n) ι ℝ => M i j) hF

lemma cavityPhysicalFrame_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (U : Orthogonal r) (F : Matrix (Fin r) ι ℝ) :
    ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F).transpose *
      ((U : Matrix (Fin r) (Fin r) ℝ).transpose * F) = F.transpose * F := by
  have hU : (U : Matrix (Fin r) (Fin r) ℝ) *
      (U : Matrix (Fin r) (Fin r) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp U.property
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = F.transpose * ((U : Matrix (Fin r) (Fin r) ℝ) *
        (U : Matrix (Fin r) (Fin r) ℝ).transpose) * F := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single reservoir rotation represents both the base interaction
and its selected special axes, as needed for the fresh-frame law. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityReservoir_spectral_eq {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin N) (F : Matrix (Fin (N + n)) ι ℝ) (lam : ι → ℝ)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j = cavityReservoirRows F i (e.symm j)) :
    cavityReservoirRows F * Matrix.diagonal lam * (cavityReservoirRows F).transpose =
      (V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal (fun j => lam (e.symm j)) *
        (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
  ext i j
  change (∑ k : ι, (∑ t : ι, cavityReservoirRows F i t *
      (if t = k then lam t else 0)) * cavityReservoirRows F j k) =
    ∑ k : Fin N, (∑ t : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) i t *
      (if t = k then lam (e.symm t) else 0)) * (V : Matrix (Fin N) (Fin N) ℝ) j k
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, hV]
  exact (Equiv.sum_comp e.symm (fun k : ι =>
    cavityReservoirRows F i k * lam k * cavityReservoirRows F j k)).symm

lemma cavityCanonicalSpecial_mul {N d : ℕ} {ι : Type*} (e : (ι ⊕ Fin d) ≃ Fin N)
    (V : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (j : Fin d) :
    (V * cavityCanonicalSpecial e) i j = V i (e (Sum.inr j)) := by
  simp only [Matrix.mul_apply, cavityCanonicalSpecial, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-rank overlap errors in cavity coordinates. The retained
coordinates cancel exactly; the error is controlled by the special
projections and the fixed number of added spins. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityCoordinatePairing_abs_le {d : ℕ} (U : Rotation d) (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    |cavityCoordinatePairing U I x y| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have hx : (∑ i ∈ I, (U x i) ^ 2) ≤ ‖x‖ ^ 2 := by
    rw [← U.norm_map x, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)
  have hy : (∑ i ∈ I, (U y i) ^ 2) ≤ ‖y‖ ^ 2 := by
    rw [← U.norm_map y, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ I, |U x i * U y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, ((U x i) ^ 2 + (U y i) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [sq_nonneg (|U x i| - |U y i|), sq_abs (U x i), sq_abs (U y i)]
    _ = ((∑ i ∈ I, (U x i) ^ 2) + ∑ i ∈ I, (U y i) ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

lemma cavity_normalized_overlap_error_sharp {N n : ℕ} (hN : 0 < N)
    (retained fullSmall baseSmall B : ℝ)
    (hsmall : |fullSmall - baseSmall| ≤ B)
    (hbase : |(retained + baseSmall) / N| ≤ 1) :
    |(retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N| ≤
      (B + n) / (N + n : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNn : (0 : ℝ) < N + n := by positivity
  have he : (retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N =
      (fullSmall - baseSmall) / (N + n : ℝ) -
        ((n : ℝ) / (N + n)) * ((retained + baseSmall) / N) := by
    push_cast
    field_simp
    ring
  rw [he]
  calc
    _ ≤ |(fullSmall - baseSmall) / (N + n : ℝ)| +
        |((n : ℝ) / (N + n)) * ((retained + baseSmall) / N)| := abs_sub _ _
    _ ≤ B / (N + n) + (n : ℝ) / (N + n) := by
      rw [abs_div, abs_of_pos hNn, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / (N + n))]
      exact add_le_add (div_le_div_of_nonneg_right hsmall hNn.le)
        ((mul_le_mul_of_nonneg_left hbase (by positivity)).trans_eq (mul_one _))
    _ = (B + n) / (N + n) := (add_div _ _ _).symm

lemma cavity_normalized_overlap_error {N n : ℕ} (hN : 0 < N)
    (retained fullSmall baseSmall B : ℝ) (hB : 0 ≤ B)
    (hsmall : |fullSmall - baseSmall| ≤ B)
    (hbase : |(retained + baseSmall) / N| ≤ 1) :
    |(retained + fullSmall) / (N + n : ℕ) - (retained + baseSmall) / N| ≤
      (B + n) / N := by
  exact (cavity_normalized_overlap_error_sharp (n := n) hN retained fullSmall baseSmall B hsmall hbase).trans
    (div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hN) (le_add_of_nonneg_right (Nat.cast_nonneg n)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionRank
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full rank of the actual spectral compressions, with the eigenvalue
groups arranged in their given consecutive coordinate windows. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityColumns_gram {N n : ℕ} (U : Orthogonal (N + n)) :
    (cavityColumns U).transpose * cavityColumns U = 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin (N + n)) ℝ).mp U.property
  ext i j
  have h := congrArg (fun M : Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
    M (Fin.natAdd N i) (Fin.natAdd N j)) hU
  change (∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    k (Fin.natAdd N i) * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (Fin.natAdd N j)) = if i = j then 1 else 0
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.natAdd_inj] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable special frame used in the actual base interaction.
Its Gram and cavity-orthogonality identities hold for every input frame. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityCompressionGrams_sum {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : ∑ a, cavityCompressionGrams g U a = 1 := by
  unfold cavityCompressionGrams
  simp_rw [cavitySpectralImage_gram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, cavitySpectralProjectors_sum, Matrix.mul_one]
  exact cavityColumns_gram U

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic control of the special coordinates by the unnormalized
spectral images. Only the inverse square-root norms on the good event enter. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_eigenspace_projection_norm {r m n : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame A).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 =
    ∑ a, ‖(WithLp.toLp 2 ((cavityNormalizeFrame (A a)).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin (m * n), (∑ j : Fin r,
      cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j (finProdFinEquiv.symm i).2 * z j) ^ 2) =
    ∑ a, ∑ i : Fin n, (∑ j : Fin r, cavityNormalizeFrame (A a) j i * z j) ^ 2
  calc
    _ = ∑ t : Fin m × Fin n, (∑ j : Fin r,
        cavityNormalizeFrame (A t.1) j t.2 * z j) ^ 2 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp finProdFinEquiv
          (fun i : Fin (m * n) => (∑ j : Fin r,
            cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j
              (finProdFinEquiv.symm i).2 * z j) ^ 2)).symm
    _ = _ := Fintype.sum_prod_type _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialPythagoras
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special coordinates and the physical cavity spins exhaust the
normalized spectral-image coordinates. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_complement_projection_reindex {s d n : ℕ}
    (e : Fin s ≃ Fin (d + n))
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1)
    (hBT : B.transpose * T = 0) :
    B * B.transpose + T * T.transpose = 1 := by
  have hTB : T.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBT
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B T).transpose * Matrix.fromCols B T = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBT, hTB, hT,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    ((finSumFinEquiv : Fin d ⊕ Fin n ≃ Fin (d + n)).trans e.symm)).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

lemma cavity_projection_norm_split {s n : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin s) ι ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hcomplete : B * B.transpose + T * T.transpose = 1)
    (z : EuclideanSpace ℝ (Fin s)) :
    ‖z‖ ^ 2 =
      ‖(WithLp.toLp 2 (B.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ ι)‖ ^ 2 +
      ‖(WithLp.toLp 2 (T.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  have he : z.ofLp ⬝ᵥ ((B * B.transpose + T * T.transpose) *ᵥ z.ofLp) =
      z.ofLp ⬝ᵥ z.ofLp := by rw [hcomplete, Matrix.one_mulVec]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add] at he
  rw [Matrix.dotProduct_mulVec _ B _, Matrix.dotProduct_mulVec _ T _,
    ← Matrix.mulVec_transpose B _, ← Matrix.mulVec_transpose T _] at he
  simpa only [dotProduct, pow_two, PiLp.toLp_apply] using he.symm

lemma cavityColumns_transpose_rotation {N n : ℕ} (U : SpecialOrthogonal (N + n))
    (x : EuclideanSpace ℝ (Fin (N + n))) :
    (cavityColumns (cavitySpecialOrthogonal U)).transpose *ᵥ
      (specialRotation U x).ofLp = fun j => x (Fin.natAdd N j) := by
  have hU : (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (cavitySpecialOrthogonal U).property
  have hx : (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *ᵥ
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *ᵥ x.ofLp) = x.ofLp := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  funext j
  exact congrFun hx (Fin.natAdd N j)

theorem cavity_full_special_pythagoras {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin (N + n)) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame
      (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)))).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 =
      ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 + n := by
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)))
  let T := cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U))
  have hT : T.transpose * T = 1 := by
    have h := cavitySpectralStack_gram (cavityCompressionGrams g (cavitySpecialOrthogonal U))
      (fun a => (hA a).posSemidef)
    exact h.trans (cavityCompressionGrams_sum g (cavitySpecialOrthogonal U))
  have hWT : W * T = cavityColumns (cavitySpecialOrthogonal U) := by
    exact (cavityEigenspaceFrame_stack _ hA).trans (cavitySpectralImage_sum g _)
  have htcoord : T.transpose *ᵥ (W.transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp) =
      fun j => spinValue (σ (Fin.natAdd N j)) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hWT]
    exact cavityColumns_transpose_rotation U (spinVector σ)
  have h := cavity_projection_norm_split B T
    (cavity_complement_projection_reindex e B T hB hT hBT)
    (WithLp.toLp 2 (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp))
  have hy : (WithLp.toLp 2 (B.transpose *ᵥ
      (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) : EuclideanSpace ℝ (Fin d)) =
      cavityFullSpecialCoordinates g B U σ := by
    simp only [cavityFullSpecialCoordinates, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, W]
  have hn : ‖(WithLp.toLp 2 (T.transpose *ᵥ
      (W.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = n := by
    rw [htcoord, EuclideanSpace.real_norm_sq_eq]
    simp only [spinValue_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact h.trans (congrArg₂ (· + ·) (congrArg (fun z => ‖z‖ ^ 2) hy) hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedPairing
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing identities for retained spectral directions and the
pointwise overlap error before taking any Gibbs average. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_masked_pairing_bound {d : ℕ} (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    |∑ i ∈ I, x i * y i| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  exact cavityCoordinatePairing_abs_le (LinearIsometryEquiv.refl ℝ _) I x y

lemma cavity_spectral_pairing_decomposition {r m n k : ℕ}
    (g : Fin r → Fin m) (a : Fin m)
    (R : Matrix (Fin r) (Fin k) ℝ) (W : Matrix (Fin r) (Fin n) ℝ)
    (hproj : R * R.transpose + W * W.transpose =
      Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (x y : Fin r → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => g i = a), x i * y i) =
      ((R.transpose *ᵥ x) ⬝ᵥ (R.transpose *ᵥ y)) +
      ((W.transpose *ᵥ x) ⬝ᵥ (W.transpose *ᵥ y)) := by
  have he := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => x ⬝ᵥ (M *ᵥ y)) hproj
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add] at he
  rw [Matrix.dotProduct_mulVec _ R _, Matrix.dotProduct_mulVec _ W _,
    ← Matrix.mulVec_transpose R _, ← Matrix.mulVec_transpose W _] at he
  simpa only [Matrix.mulVec_diagonal,
    dotProduct, Finset.sum_filter, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
    zero_mul] using he.symm

lemma cavity_normalized_group_pairing_bound {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (x y : EuclideanSpace ℝ (Fin r)) :
    |((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) ⬝ᵥ
      ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp)| ≤
      (‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ x.ofLp) :
          EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 +
        ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ y.ofLp) :
          EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2) / 2 := by
  have hx : ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
      ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ x.ofLp) :
        EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 := by
    rw [cavity_eigenspace_projection_norm]
    exact Finset.single_le_sum (f := fun b =>
      ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X b)).transpose *ᵥ x.ofLp) :
        EuclideanSpace ℝ (Fin n))‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hy : ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
      ‖(WithLp.toLp 2 ((cavityEigenspaceFrame X).transpose *ᵥ y.ofLp) :
        EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 := by
    rw [cavity_eigenspace_projection_norm]
    exact Finset.single_le_sum (f := fun b =>
      ‖(WithLp.toLp 2 ((cavityNormalizeFrame (X b)).transpose *ᵥ y.ofLp) :
        EuclideanSpace ℝ (Fin n))‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have h := cavity_masked_pairing_bound Finset.univ
    (WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp))
    (WithLp.toLp 2 ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp))
  change |((cavityNormalizeFrame (X a)).transpose *ᵥ x.ofLp) ⬝ᵥ
    ((cavityNormalizeFrame (X a)).transpose *ᵥ y.ofLp)| ≤ _ at h
  exact h.trans (by linarith)

theorem cavity_retained_overlap_error {N n m d k : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (a : Fin m)
    (e : Fin (m * n) ≃ Fin (d + n)) (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (R : Matrix (Fin (N + n)) (Fin k) ℝ)
    (hproj : R * R.transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (J : Finset (Fin d)) (σ τ : Spin (N + n))
    (hbase : |(((R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
      (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)) +
      ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N| ≤ 1) :
    |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
      (((R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
        (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)) +
        ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
          cavityFullSpecialCoordinates g B U τ j) / N| ≤
      ((2 * (n : ℝ) + 1) / N) *
        (1 + ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 +
          ‖cavityFullSpecialCoordinates g B U τ‖ ^ 2) := by
  let yσ := cavityFullSpecialCoordinates g B U σ
  let yτ := cavityFullSpecialCoordinates g B U τ
  let retained := (R.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    (R.transpose *ᵥ (specialRotation U (spinVector τ)).ofLp)
  let fullSmall := ((cavityNormalizeFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    ((cavityNormalizeFrame (cavitySpectralImage g
      (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose *ᵥ
        (specialRotation U (spinVector τ)).ofLp)
  let baseSmall := ∑ j ∈ J, yσ j * yτ j
  have hf : |fullSmall| ≤ (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2) / 2 + n := by
    have h := cavity_normalized_group_pairing_bound
      (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) a
      (specialRotation U (spinVector σ)) (specialRotation U (spinVector τ))
    rw [cavity_full_special_pythagoras g e U B hB hBT hA σ,
      cavity_full_special_pythagoras g e U B hB hBT hA τ] at h
    dsimp only [fullSmall, yσ, yτ]
    exact h.trans_eq (by ring)
  have hb : |baseSmall| ≤ (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2) / 2 :=
    cavity_masked_pairing_bound J yσ yτ
  have hsmall : |fullSmall - baseSmall| ≤ ‖yσ‖ ^ 2 + ‖yτ‖ ^ 2 + n := by
    have h := (abs_sub _ _).trans (add_le_add hf hb)
    linarith
  have herr := cavity_normalized_overlap_error (n := n) hN retained fullSmall baseSmall
    (‖yσ‖ ^ 2 + ‖yτ‖ ^ 2 + n) (by positivity) hsmall hbase
  have he : projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ =
      (retained + fullSmall) / (N + n : ℕ) := by
    rw [projectedOverlap, cavitySpectralGroup,
      cavity_spectral_pairing_decomposition g a R _ hproj]
    exact (div_eq_inv_mul _ _).symm
  rw [he]
  apply herr.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hN).le
  nlinarith [sq_nonneg ‖yσ‖, sq_nonneg ‖yτ‖,
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖yσ‖),
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖yτ‖)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedNorm
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special base coordinates have total squared norm
equal to the number of reservoir spins. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_retained_stack_norm {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 ((cavityRetainedStack k R).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ ((a : Fin m) × Fin (k a)))‖ ^ 2 =
      ∑ a, ‖(WithLp.toLp 2 ((R a).transpose *ᵥ z.ofLp) :
        EuclideanSpace ℝ (Fin (k a)))‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Matrix.mulVec,
    Matrix.transpose_apply, cavityRetainedStack, Fintype.sum_sigma]

theorem cavity_retained_special_norm {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (σ : Spin (N + n)) :
    (∑ a, ‖(WithLp.toLp 2 ((R a).transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k a)))‖ ^ 2) +
      ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 = N := by
  have h := cavity_projection_norm_split (cavityRetainedStack k R)
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))))
    (cavityRetainedStack_complete g (cavityColumns (cavitySpecialOrthogonal U)) k R hproj)
    (specialRotation U (spinVector σ))
  rw [(specialRotation U).norm_map, spinVector_norm_sq, cavity_retained_stack_norm,
    cavity_full_special_pythagoras g e U B hB hBT hA σ] at h
  push_cast at h
  linarith

theorem cavity_retained_base_overlap_bound {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (a : Fin m) (J : Finset (Fin d)) (σ τ : Spin (N + n)) :
    |(((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
      ((R a).transpose *ᵥ (specialRotation U (spinVector τ)).ofLp) +
      ∑ j ∈ J, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N| ≤ 1 := by
  let r := fun σ : Spin (N + n) => (WithLp.toLp 2
    ((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) :
      EuclideanSpace ℝ (Fin (k a)))
  let y := fun σ => cavityFullSpecialCoordinates g B U σ
  have hn (σ : Spin (N + n)) : ‖r σ‖ ^ 2 + ‖y σ‖ ^ 2 ≤ N := by
    have ht := cavity_retained_special_norm g e U B hB hBT hA k R hproj σ
    have hs : ‖r σ‖ ^ 2 ≤ ∑ b, ‖(WithLp.toLp 2 ((R b).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k b)))‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖(WithLp.toLp 2 ((R b).transpose *ᵥ
        (specialRotation U (spinVector σ)).ofLp) : EuclideanSpace ℝ (Fin (k b)))‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_univ a)
    dsimp only [y]
    linarith
  have hr := cavity_masked_pairing_bound Finset.univ (r σ) (r τ)
  have hy := cavity_masked_pairing_bound J (y σ) (y τ)
  have hp : |(r σ).ofLp ⬝ᵥ (r τ).ofLp + ∑ j ∈ J, y σ j * y τ j| ≤ N := by
    change |(∑ i, r σ i * r τ i) + ∑ j ∈ J, y σ j * y τ j| ≤ N
    have hh := (abs_add_le _ _).trans (add_le_add hr hy)
    linarith [hn σ, hn τ]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < (N : ℝ) from Nat.cast_pos.mpr hN)]
  exact (div_le_one (Nat.cast_pos.mpr hN)).mpr hp

theorem cavity_retained_base_comparison {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBT : B.transpose * cavitySpectralStack
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a) *
        (cavityNormalizeFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (J : Fin m → Finset (Fin d)) (a : Fin m) (σ τ : Spin (N + n)) :
    |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
      cavityRetainedBaseOverlap g U B k R J a σ τ| ≤
      ((2 * (n : ℝ) + 1) / N) *
        (1 + ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 +
          ‖cavityFullSpecialCoordinates g B U τ‖ ^ 2) := by
  exact cavity_retained_overlap_error hN g a e U B hB hBT hA (R a) (hproj a) (J a) σ τ
    (cavity_retained_base_overlap_bound hN g e U B hB hBT hA k R hproj a (J a) σ τ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical base eigenframe identifies every retained group
overlap with the corresponding projected spin overlap. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_physical_frame_coordinates {N n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι ≃ Fin N) (U : SpecialOrthogonal (N + n))
    (F : Matrix (Fin (N + n)) ι ℝ)
    (hF : ∀ i : Fin n, ∀ j,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F) (Fin.natAdd N i) j = 0)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F)
        i (e.symm j))
    (σ : Spin (N + n)) (j : ι) :
    matrixRotation V⁻¹ (spinVector (fun i => σ (Fin.castAdd n i))) (e j) =
      (F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) j := by
  let P := (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F
  have he : F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp =
      P.transpose *ᵥ (spinVector σ).ofLp := by
    change F.transpose *ᵥ ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *ᵥ
      (spinVector σ).ofLp) = _
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  rw [he]
  change (∑ i : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) i (e j) *
    spinValue (σ (Fin.castAdd n i))) = ∑ i : Fin (N + n), P i j * spinValue (σ i)
  rw [Fin.sum_univ_add]
  simp only [hF, zero_mul, Finset.sum_const_zero, add_zero, hV,
    Equiv.symm_apply_apply, cavityReservoirRows, P]

theorem cavity_base_group_overlap {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (U : SpecialOrthogonal (N + n))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m)
    (hF : ∀ i : Fin n, ∀ j,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        Matrix.fromCols (cavityRetainedStack k R)
          (cavityEigenspaceFrame (cavitySpectralImage g
            (cavityColumns (cavitySpecialOrthogonal U))) * B)) (Fin.natAdd N i) j = 0)
    (V : Orthogonal N)
    (hV : ∀ i j, (V : Matrix (Fin N) (Fin N) ℝ) i j =
      cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        Matrix.fromCols (cavityRetainedStack k R)
          (cavityEigenspaceFrame (cavitySpectralImage g
            (cavityColumns (cavitySpecialOrthogonal U))) * B)) i (e.symm j))
    (a : Fin m) (σ τ : Spin (N + n)) :
    projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a)
      (fun i => σ (Fin.castAdd n i)) (fun i => τ (Fin.castAdd n i)) =
      cavityRetainedBaseOverlap g U B k R
        (fun a => Finset.univ.filter (fun j => a₀ j = a)) a σ τ := by
  let F := Matrix.fromCols (cavityRetainedStack k R)
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) * B)
  let z := fun σ : Spin (N + n) => F.transpose *ᵥ (specialRotation U (spinVector σ)).ofLp
  have hc (σ : Spin (N + n)) (j) :
      matrixRotation V⁻¹ (spinVector (fun i => σ (Fin.castAdd n i))) (e j) = z σ j :=
    cavity_physical_frame_coordinates e U F hF V hV σ j
  have hr (σ : Spin (N + n)) (b : Fin m) (i : Fin (k b)) :
      z σ (Sum.inl ⟨b, i⟩) =
        ((R b).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) i := rfl
  have hy (σ : Spin (N + n)) (i : Fin d) :
      z σ (Sum.inr i) = cavityFullSpecialCoordinates g B U σ i := rfl
  rw [projectedOverlap, cavityBaseGroup, Finset.sum_filter]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply, hc, Fintype.sum_sum_type, Fintype.sum_sigma,
    Sum.elim_inl, Sum.elim_inr, hr, hy]
  simp only [Finset.sum_ite_irrel]
  rw [cavityRetainedBaseOverlap, Finset.sum_filter, div_eq_inv_mul]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, dotProduct]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltTransport
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized quadratic tilts commute with the Gaussian factor map. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X → Y) (hF : Measurable F)
    (f : Y → ℝ) (hf : Measurable f) :
    (μ.tilted (f ∘ F)).map F = (μ.map F).tilted f := by
  ext s hs
  rw [Measure.map_apply hF hs, tilted_apply_eq_ofReal_integral' _ (hF hs),
    tilted_apply_eq_ofReal_integral' _ hs,
    integral_map hF.aemeasurable hf.exp.aestronglyMeasurable,
    setIntegral_map hs ((hf.exp.div_const _).aestronglyMeasurable) hF.aemeasurable]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinSplit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact product prior obtained by separating the cavity sites.
The leaf coordinate is preserved by the split. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_spin_split_prior (N n : ℕ) :
    MeasurePreserving (cavitySpinSplit N n)
      (uniformSpinPrior (N+n) : Measure (Spin (N+n)))
      ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  have hp : (cavitySpinSplit N n) ⁻¹' {p} = {(cavitySpinSplit N n).symm p} := by
    ext σ
    exact (cavitySpinSplit N n).eq_symm_apply.symm
  rw [hp, ← singleton_prod_singleton, Measure.prod_prod]
  change (PMF.uniformOfFintype (Spin (N+n))).toMeasure {_} =
    (PMF.uniformOfFintype (Spin N)).toMeasure {_} *
      (PMF.uniformOfFintype (Spin n)).toMeasure {_}
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (cavitySpinSplit N n), Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv] <;> simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffMap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff replica tests commute with the exact split of the uniform
spin law into its base and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_spin_pair_leaf_prior (N n depth : ℕ) (T : LabeledTree depth) :
    MeasurePreserving (fun x : Spin (N+n) × LabeledLeaf depth =>
      (cavitySpinSplit N n x.1,x.2))
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) :=
  (cavity_spin_split_prior N n).prod (MeasurePreserving.id (labeledLeafLaw depth T))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseRestrictedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted base/cavity test in the exact product coordinates:
the shared cascade leaf stays with the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_pair_leaf_swap_preserving (N n depth : ℕ) (T : LabeledTree depth) :
    MeasurePreserving (cavityPairLeafSwap (N := N) (n := n) (depth := depth))
      (((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T))
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)) := by
  have h₁ := measurePreserving_prodAssoc (uniformSpinPrior N : Measure (Spin N))
    (uniformSpinPrior n : Measure (Spin n)) (labeledLeafLaw depth T)
  have h₂ := (MeasurePreserving.id (uniformSpinPrior N : Measure (Spin N))).prod
    (Measure.measurePreserving_swap (μ := (uniformSpinPrior n : Measure (Spin n)))
      (ν := labeledLeafLaw depth T))
  have h₃ := (measurePreserving_prodAssoc (uniformSpinPrior N : Measure (Spin N))
    (labeledLeafLaw depth T) (uniformSpinPrior n : Measure (Spin n))).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoupledProjectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical overlap comparison uses the same frame as the entire
family of labeled spectral projectors, including repeated eigenvalues. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_coupled_labeled_projectors {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n)) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef) :
    ∃ V : Orthogonal N,
      (∀ (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ),
        cavityPhysicalBase g lam B (Matrix.diagonal lam₀) (cavitySpecialOrthogonal U) =
          (V : Matrix (Fin N) (Fin N) ℝ) *
            Matrix.diagonal (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)) *
            (V : Matrix (Fin N) (Fin N) ℝ).transpose) ∧
      cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U) =
        cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) ∧
      cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e ∧
      ∀ a σ τ,
        |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
          projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a)
            (fun i => σ (Fin.castAdd n i)) (fun i => τ (Fin.castAdd n i))| ≤
        ((2 * (n : ℝ) + 1) / N) *
          (1 + ‖cavityFullSpecialCoordinates g
              (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U σ‖ ^ 2 +
            ‖cavityFullSpecialCoordinates g
              (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U τ‖ ^ 2) := by
  classical
  let O := cavitySpecialOrthogonal U
  let A := cavityColumns O
  let X := cavitySpectralImage g A
  let W := cavityEigenspaceFrame X
  let B₁ := B (cavityCompressionGrams g O)
  let T := cavitySpectralStack (cavityCompressionGrams g O)
  choose R hRG hRX hRS hRP using fun a => cavityRetainedFrame_exists g A a (ek a) (hA a)
  have hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0 := by
    intro a b hab
    exact cavitySpectralSupport_crossGram g a b hab (R a) (R b) (hRS a) (hRS b)
  have hperp : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      have h := congrArg Matrix.transpose (hRX a)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
    · exact cavitySpectralSupport_crossGram g a b hab (R a) _ (hRS a)
        (cavityNormalizeFrame_spectral_support g A b)
  let S := cavityRetainedStack k R
  let F := Matrix.fromCols S (W * B₁)
  let P := (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F
  have hWG : W.transpose * W = 1 :=
    cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A)
  have hSG : S.transpose * S = 1 := cavityRetainedStack_gram k R hRG hcross
  have hSW : S.transpose * W = 0 := cavityRetainedStack_perp k R X hperp
  have hWT : W * T = A :=
    (cavityEigenspaceFrame_stack X hA).trans (cavitySpectralImage_sum g A)
  have hFG : F.transpose * F = 1 := cavityBaseFrame_gram S W B₁ hSG hWG hSW hB
  have hPG : P.transpose * P = 1 := (cavityPhysicalFrame_gram O F).trans hFG
  have hPF : ∀ i : Fin n, ∀ j, P (Fin.natAdd N i) j = 0 := by
    apply cavityPhysicalFrame_lastRows (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) F
    change A.transpose * F = 0
    rw [← hWT]
    exact cavityBaseFrame_cavity_perp S W B₁ T hWG hSW hBT
  obtain ⟨V, hV⟩ := cavityReservoirRows_orthogonal e P hPG hPF
  have hSpectrum (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ) :
      cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
    let Λ := Matrix.diagonal (Sum.elim (fun v : (b : Fin m) × Fin (k b) => lam v.1) lam₀)
    have hJ : cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
        (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) =
        F * Λ * F.transpose := by
      rw [cavityBase_spectral_decomposition g A lam k R hRS hRP]
      exact (cavityBaseFrame_spectral_sum S (W * B₁) (fun v => lam v.1) lam₀).symm
    have hJP : (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
          (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) *
        (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) = P * Λ * P.transpose := by
      rw [hJ]
      simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    change ((O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
        (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) *
      (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
        (Fin.castAdd n) (Fin.castAdd n) = _
    rw [hJP, cavityReservoirRows_conjugate]
    exact cavityReservoir_spectral_eq e P _ V hV
  have hSpecial : cavityPhysicalSpecial g B O =
      (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
    ext i j
    rw [cavityCanonicalSpecial_mul, hV]
    simp only [Equiv.symm_apply_apply]
    rfl
  refine ⟨V, hSpectrum, ?_, hSpecial, ?_⟩
  · apply Prod.ext
    · funext a
      exact hSpectrum (fun b => if b=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0)
    · exact hSpecial
  · intro a σ τ
    rw [cavity_base_group_overlap g U B₁ k R e a₀ hPF V hV a σ τ]
    exact cavity_retained_base_comparison hN g es U B₁ hB hBT hA k R hRP
      (fun a => Finset.univ.filter (fun j => a₀ j = a)) a σ τ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained-projector coupling supplies the geometric error
needed for every bounded replica test on a fixed special-coordinate cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityGeometricWeight_one_le {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (x : Spin N × Spin n) : 1 ≤ cavityGeometricWeight g B U x :=
  le_add_of_nonneg_right (sq_nonneg _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic energies in physical coordinates and after deleting the
annihilated cavity rows and columns. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_conjugate {r d : ℕ}
    (U : Matrix (Fin r) (Fin d) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin d → ℝ) :
    cavityQuadratic (U.transpose * A * U) x = cavityQuadratic A (U *ᵥ x) := by
  rw [cavityQuadratic_dotProduct, cavityQuadratic_dotProduct,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

lemma cavityQuadratic_first_block {N n : ℕ}
    (A : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)
    (hrow : ∀ j i, A (Fin.natAdd N j) i = 0)
    (hcol : ∀ i j, A i (Fin.natAdd N j) = 0)
    (x : Fin (N+n) → ℝ) :
    cavityQuadratic A x =
      cavityQuadratic (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
        (fun i => x (Fin.castAdd n i)) := by
  simp only [cavityQuadratic, Fin.sum_univ_add, hrow, hcol, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, Matrix.submatrix_apply]

lemma cavityQuadratic_first_block_of_symmetric {N n : ℕ}
    (A : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) (hA : A.transpose = A)
    (hcol : ∀ i j, A i (Fin.natAdd N j) = 0) (x : Fin (N+n) → ℝ) :
    cavityQuadratic A x =
      cavityQuadratic (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
        (fun i => x (Fin.castAdd n i)) := by
  apply cavityQuadratic_first_block A _ hcol x
  intro j i
  rw [← hA]
  exact hcol i j

lemma cavityQuadratic_diagonal {d : ℕ} (a x : Fin d → ℝ) :
    cavityQuadratic (Matrix.diagonal a) x = (1 / 2 : ℝ) * ∑ i, a i * (x i)^2 := by
  rw [cavityQuadratic_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cavity_rotatedEnergy_matrix {N : ℕ} (eig : Fin N → ℝ)
    (U : Orthogonal N) (σ : Spin N) :
    rotatedEnergy eig (matrixRotation U) σ =
      cavityQuadratic ((U : Matrix (Fin N) (Fin N) ℝ).transpose *
        Matrix.diagonal eig * (U : Matrix (Fin N) (Fin N) ℝ))
          (fun i => spinValue (σ i)) := by
  rw [cavityQuadratic_conjugate, cavityQuadratic_diagonal]
  rfl

lemma cavityQuadratic_inverse_rotation {N : ℕ} (eig : Fin N → ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityQuadratic ((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal eig *
      (V : Matrix (Fin N) (Fin N) ℝ).transpose) (fun i => spinValue (σ i)) =
      rotatedEnergy eig (matrixRotation V⁻¹) σ := by
  rw [cavity_rotatedEnergy_matrix]
  rfl

lemma cavityBaseReplacement_transpose {r s d : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J.transpose = J) (hD : D.transpose = D) (hA₀ : A₀.transpose = A₀) :
    (cavityBaseReplacement J W D B A₀).transpose = cavityBaseReplacement J W D B A₀ := by
  simp only [cavityBaseReplacement, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose, hJ, hD, hA₀, Matrix.mul_assoc]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance equality transports the logarithm of an added cavity
weight while retaining the Gaussian field inside the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_log_partition_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) (H : X → ℝ) (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    (∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (A x) z) ∂ν) ∂gaussianCoordinates) =
    ∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (C x) z) ∂ν) ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => Real.exp (H p.2+p.1 p.2)) := by
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)).exp
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => Real.log (∫ x, Real.exp (H x+w x) ∂ν))
    hm.stronglyMeasurable.integral_prod_right'.measurable.log

theorem cavity_log_weight_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    (∫ z, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (A x) z)) ∂gaussianCoordinates) =
    ∫ z, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) z)) ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hw : Measurable (fun p : (X → ℝ) × X => Real.exp (W p.2)) :=
    ((measurable_of_countable W).comp measurable_snd).exp
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => Real.log (∫ x, Real.exp (W x) ∂ν.tilted (fun x => H x+w x)))
    (measurable_random_tilted_integral measurable_const hm hw).log

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogMap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of a logarithmic cavity weight through the split
spin/leaf coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_pair_leaf_base_partition {N n depth : ℕ} (T : LabeledTree depth)
    (H : Spin N × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (x.1.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T := by
  have hp := cavity_pair_leaf_swap_preserving N n depth T
  have hi := integral_map
    (μ := ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
      (labeledLeafLaw depth T)) hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      Real.exp (H x.1))).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  have he := integral_fun_fst
    (μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (ν := (uniformSpinPrior n : Measure (Spin n))) (fun x => Real.exp (H x))
  rw [he] at hi
  simpa only [probReal_univ, one_smul, Function.comp_def, cavityPairLeafSwap] using hi.symm

lemma cavity_pair_leaf_full_partition {N n depth : ℕ} (T : LabeledTree depth)
    (H : Spin (N+n) × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (cavityJoinedSpin x.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T := by
  have hp := cavity_spin_pair_leaf_prior N n depth T
  have hi := integral_map
    (μ := labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
    hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      Real.exp (H (cavityJoinedSpin x.1,x.2)))).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  have he (σ : Spin (N+n)) : cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [cavityJoinedSpin, cavitySpinSplit]
  simpa only [Function.comp_def, he] using hi

lemma cavity_log_weight_map {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [Countable Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : MeasurePreserving f μ ν)
    (H W : Y → ℝ) :
    Real.log (∫ x, Real.exp (W (f x)) ∂μ.tilted (H ∘ f)) =
      Real.log (∫ y, Real.exp (W y) ∂ν.tilted H) := by
  have ht : (μ.tilted (H ∘ f)).map f = ν.tilted H := by
    rw [cavity_tilt_map μ f hf.measurable H (measurable_of_countable H), hf.map_eq]
  have hi := integral_map (μ := μ.tilted (H ∘ f)) hf.measurable.aemeasurable
    ((measurable_of_countable W).exp.aestronglyMeasurable)
  rw [ht] at hi
  exact congrArg Real.log hi.symm

lemma cavity_log_weight_pair_leaf {N n depth : ℕ} (T : LabeledTree depth)
    (H W : (Spin N × LabeledLeaf depth) × Spin n → ℝ) :
    Real.log (∫ x, Real.exp (W (cavityPairLeafSwap x))
      ∂(((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)).tilted (H ∘ cavityPairLeafSwap)) =
    Real.log (∫ x, Real.exp (W x)
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted H) :=
  cavity_log_weight_map _ _ _ (cavity_pair_leaf_swap_preserving N n depth T) H W

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full special coordinates are already coordinates of the base
spin: the special frame has zero rows at all cavity sites. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_physical_special_coordinates {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (U : SpecialOrthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin N) (ε : Spin n) :
    (cavityFullSpecialCoordinates g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavityJoinedSpin (σ,ε))).ofLp =
      (cavityPhysicalSpecial g B (cavitySpecialOrthogonal U)).transpose *ᵥ
        (fun i => spinValue (σ i)) := by
  let O := cavitySpecialOrthogonal U
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns O))
  let B₁ := B (cavityCompressionGrams g O)
  let Q := (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (W * B₁)
  have hp : (cavityColumns O).transpose * (W * B₁) = 0 := by
    have h := cavityEigenspaceFrame_special_perp
      (cavitySpectralImage g (cavityColumns O)) hA
      (cavitySpectralImage_crossGram g (cavityColumns O)) B₁ hBT
    rw [cavitySpectralImage_sum] at h
    have ht := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
  have hQ : ∀ i : Fin n, ∀ j, Q (Fin.natAdd N i) j = 0 :=
    cavityPhysicalFrame_lastRows (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) (W * B₁) hp
  have htrans : (W * B₁).transpose *
      (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) = Q.transpose := by
    simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose]
  funext j
  change ((W * B₁).transpose *ᵥ
    ((O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) *ᵥ
      (fun i => spinValue (cavityJoinedSpin (σ,ε) i)))) j = _
  rw [Matrix.mulVec_mulVec, htrans]
  change (∑ i, Q i j * spinValue (cavityJoinedSpin (σ,ε) i)) =
    ∑ i, Q (Fin.castAdd n i) j * spinValue (σ i)
  simp only [Fin.sum_univ_add, hQ, zero_mul, Finset.sum_const_zero, add_zero,
    cavityJoinedSpin, Fin.append_left]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalEnergy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact original-spin energy difference is the finite random-block
cavity factor. All spectral-image and cavity-coordinate identities are
proved for the actual orthogonal matrix. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_physical_energy_difference {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (e : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin N) (ε : Spin n) :
    let O := cavitySpecialOrthogonal U
    let B₁ := B (cavityCompressionGrams g O)
    let D := cavityRepeatedSpectrum (n := n) lam
    let T := cavitySpectralStack (cavityCompressionGrams g O)
    rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin (σ,ε)) -
      cavityQuadratic (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O)
        (fun i => spinValue (σ i)) =
      cavityLogFactor (B₁.transpose * D * B₁ - Matrix.diagonal lam₀)
        (B₁.transpose * D * T) (T.transpose * D * T)
        (cavityFullSpecialCoordinates g B₁ U (cavityJoinedSpin (σ,ε))).ofLp ε := by
  intro O B₁ D T
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns O))
  let J := Matrix.diagonal (fun i => lam (g i))
  let R := cavityBaseReplacement J W D B₁ (Matrix.diagonal lam₀)
  let A := (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * R *
    (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)
  let x := (specialRotation U (spinVector (cavityJoinedSpin (σ,ε)))).ofLp
  have hWG : W.transpose * W = 1 :=
    cavityEigenspaceFrame_gram _ hA (cavitySpectralImage_crossGram g (cavityColumns O))
  have hJW : J * W = W * D :=
    cavityEigenspaceFrame_eigen _ _ lam (cavitySpectralImage_eigen g (cavityColumns O) lam)
  have hWT : W * T = cavityColumns O :=
    (cavityEigenspaceFrame_stack _ hA).trans (cavitySpectralImage_sum g (cavityColumns O))
  have hT : T.transpose * T = 1 :=
    (cavitySpectralStack_gram _ (fun a => (hA a).posSemidef)).trans
      (cavityCompressionGrams_sum g O)
  have hcomplete : B₁ * B₁.transpose + T * T.transpose = 1 :=
    cavity_complement_projection_reindex e B₁ T hB hT hBT
  have hR : R.transpose = R :=
    cavityBaseReplacement_transpose J W D B₁ (Matrix.diagonal lam₀)
      (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _)
  have hAs : A.transpose = A := by
    simp only [A, Matrix.transpose_mul, Matrix.transpose_transpose, hR, Matrix.mul_assoc]
  have hRc : R * cavityColumns O = 0 := by
    rw [← hWT]
    exact cavityBaseReplacement_cavity J W D B₁ T _ hJW hWG hBT
  have hAc : ∀ i j, A i (Fin.natAdd N j) = 0 := by
    intro i j
    dsimp only [A]
    rw [Matrix.mul_assoc]
    change (∑ k, (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) k i *
      (R * cavityColumns O) k j) = 0
    rw [hRc]
    simp
  have hb := cavityQuadratic_first_block_of_symmetric A hAs hAc
    (fun i => spinValue (cavityJoinedSpin (σ,ε) i))
  have hx : x = (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) *ᵥ
      (fun i => spinValue (cavityJoinedSpin (σ,ε) i)) := rfl
  have hbase : cavityQuadratic R x =
      cavityQuadratic (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O)
        (fun i => spinValue (σ i)) := by
    rw [hx, ← cavityQuadratic_conjugate]
    simpa only [A, R, J, W, D, B₁, cavityPhysicalBase, cavityJoinedSpin,
      Fin.append_left] using hb
  have hcoord : (W * T).transpose *ᵥ x = fun j => spinValue (ε j) := by
    rw [hWT]
    simpa only [x, cavityJoinedSpin, spinVector_apply, Fin.append_right] using
      cavityColumns_transpose_rotation U (spinVector (cavityJoinedSpin (σ,ε)))
  have hdiff := cavityBaseReplacement_energy_difference J W D
    (Matrix.diagonal_transpose _) B₁ T hcomplete (Matrix.diagonal lam₀) x ε hcoord
  rw [hbase] at hdiff
  convert (config := {transparency := .instances, preTransparency := .instances}) hdiff using 1
  · rw [cavityQuadratic_diagonal]
    rfl
  · rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped logarithmic cavity factor in physical projector
coordinates, including the vanishing quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_projector_capped_log {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t cap δ : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d)
    (hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) :
    cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p =
    ∫ z, Real.log (∫ x, Real.exp
      (min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
        δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2))
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x.1)) ∂gaussianCoordinates := by
  let ν := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
    (uniformSpinPrior n : Measure (Spin n))
  let H := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) x.1.1
  let B := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x.1
  let C := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x.1
  let W := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2)
  have he z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityProjectorHamiltonian p.1 (fun a => t*lam a+2*perturbationScale N*v a) u z x.1) =
      fun x => H x+cylinderField (B x) z := by
    funext x
    rw [hp]
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
  unfold cavityProjectorCappedLog
  simp_rw [he]
  exact cavity_log_weight_same_covariance ν H W B C
    (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x.1 y.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalLogIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual geometric pressure increment dominates the capped
projector cavity logarithm, with the explicit vanishing quadratic error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_capped_increment {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) (B G) (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let eig₀ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
    let J := cavityBaseGroup k e a₀
    let ν := ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
      (labeledLeafLaw depth T)
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
      2*cavityCovarianceRate n (2*n+1) N
    ∃ V : Orthogonal N,
      p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) ∧
      cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
        u t cap δ A p ≤
      (∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z (cavityJoinedSpin x.1,x.2)) ∂ν) ∂gaussianCoordinates) -
      ∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (matrixRotation V⁻¹) (diagonalPerturbedEigenvalues eig₀ J v t)
          J u z (x.1.1,x.2)) ∂ν) ∂gaussianCoordinates := by
  intro G A p eig₀ J ν δ
  obtain ⟨V, hSpectrum, hProj, hSpecial, herr₀⟩ :=
    cavity_coupled_labeled_projectors hN g k ek e es U a₀ B hB hBT hA
  refine ⟨V, hProj, ?_⟩
  let w := cavityGeometricWeight g (B G) U
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2*(n : ℝ)+1)/N*(w x+w z) := by
    have h := herr₀ a (cavityJoinedSpin x) (cavityJoinedSpin z)
    simp only [cavityJoinedSpin, Fin.append_left] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w, cavityGeometricWeight, G, cavityJoinedSpin]
    linarith
  have hc := cavity_finite_capped_energy_increment hN (specialRotation U) (matrixRotation V⁻¹)
    (cavitySpectralGroup g) J (fun i => lam (g i)) eig₀ v hv u hu t cap hcap ν w
    (cavityGeometricWeight_one_le g (B G) U) (by positivity) herr
  dsimp only at hc
  have hp : p.1 = fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) := by
    rw [show p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) from hProj]
    exact cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hI : cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) = J := rfl
  have hEig : (fun j => lam (Sum.elim (fun w => w.1) a₀ (e.symm j))) = eig₀ := by
    funext j
    dsimp only [eig₀]
    cases e.symm j <;> rfl
  have hw (x : Spin N × Spin n) :
      w x = 1+‖cavityFrameCoordinates p.2 x.1‖^2 := by
    dsimp only [w, cavityGeometricWeight]
    rw [← WithLp.toLp_ofLp 2 (cavityFullSpecialCoordinates g (B G) U (cavityJoinedSpin x)),
      cavity_physical_special_coordinates g U B hBT hA]
    rfl
  have he (x : Spin N × Spin n) :
      rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin x) -
        rotatedEnergy eig₀ (matrixRotation V⁻¹) x.1 =
      cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1) x.2 := by
    have h := cavity_physical_energy_difference g es U lam (fun j => lam (a₀ j)) B
      hB hBT hA x.1 x.2
    dsimp only at h
    rw [hSpectrum, cavityQuadratic_inverse_rotation,
      cavity_physical_special_coordinates g U B hBT hA] at h
    exact h
  have hlog : cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p =
      ∫ z, Real.log (∫ x, Real.exp
        (min (t*(rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin x.1) -
          rotatedEnergy eig₀ (matrixRotation V⁻¹) x.1.1)) cap - δ*w x.1)
        ∂ν.tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues eig₀ J v t) J u z (x.1.1,x.2))) ∂gaussianCoordinates := by
    rw [cavity_projector_capped_log _ V T lam v u t cap δ A p hp]
    rw [hI, hEig]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      have hm := cavity_log_weight_pair_leaf T
        (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues eig₀ J v t) J u z x.1)
        (fun x => min (t*cavityLogFactor A.1 A.2.1 A.2.2
          (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
            δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2))
      simpa only [Function.comp_def, cavityPairLeafSwap, he, hw, ν] using hm.symm
  rw [hlog]
  exact hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base logarithmic partition function in the same physical
projector variables as the capped cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_projector_log_partition {N m depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ) :
    cavityProjectorLogPartition T (fun a => t*lam a+2*perturbationScale N*v a) u
      (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) =
    ∫ z, Real.log (∫ x, Real.exp
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        (cavitySpectralGroup g) u z x)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      ∂gaussianCoordinates := by
  let H := fun x : Spin N × LabeledLeaf depth =>
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) x.1
  let A := fun x : Spin N × LabeledLeaf depth =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x
  let C := fun x : Spin N × LabeledLeaf depth =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x
  have he z : (fun x : Spin N × LabeledLeaf depth => cavityProjectorHamiltonian
      (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
      (fun a => t*lam a+2*perturbationScale N*v a) u z x) =
      fun x => H x+cylinderField (A x) z := by
    funext x
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
  unfold cavityProjectorLogPartition
  simp_rw [he]
  exact cavity_log_partition_same_covariance _ H A C
    (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x y)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalProjectorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An additive lower bound for the literal full-system log partition,
written entirely in the physical projector and compression data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_projector_increment_oai {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) (B G) (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
      2*cavityCovarianceRate n (2*n+1) N
    cavityProjectorCappedLog T c u t cap δ A p + cavityProjectorLogPartition T c u p.1 ≤
      ∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x)
        ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        ∂gaussianCoordinates := by
  intro G A p c δ
  obtain ⟨V,hV,hc⟩ := cavity_physical_capped_increment hN g k ek e es U lam a₀ B
    hB hBT hA T v hv u hu t cap hcap
  let g₀ : Fin N → Fin m := fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)
  let eig₀ : Fin N → ℝ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
  have hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g₀ a) := by
    rw [show p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) from hV]
    exact cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hEig : (fun j => lam (g₀ j)) = eig₀ := by
    funext j
    dsimp only [g₀,eig₀]
    cases e.symm j <;> rfl
  have hb := cavity_projector_log_partition g₀ V T lam v u t
  rw [hEig, ← hp] at hb
  have hfull z := cavity_pair_leaf_full_partition (N := N) (n := n) T
    (cavityRotationHamiltonian (specialRotation U)
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u z)
  have hbase z := cavity_pair_leaf_base_partition (n := n) T
    (cavityRotationHamiltonian (matrixRotation V⁻¹)
      (diagonalPerturbedEigenvalues eig₀ (cavityBaseGroup k e a₀) v t)
      (cavityBaseGroup k e a₀) u z)
  change cavityProjectorCappedLog T c u t cap δ A p ≤
    (∫ z, Real.log (∫ x, Real.exp (cavityRotationHamiltonian (specialRotation U)
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u z (cavityJoinedSpin x.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n : Measure (Spin n))).prod
        (labeledLeafLaw depth T)) ∂gaussianCoordinates) -
    ∫ z, Real.log (∫ x, Real.exp (cavityRotationHamiltonian (matrixRotation V⁻¹)
      (diagonalPerturbedEigenvalues eig₀ (cavityBaseGroup k e a₀) v t)
      (cavityBaseGroup k e a₀) u z (x.1.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n : Measure (Spin n))).prod
        (labeledLeafLaw depth T)) ∂gaussianCoordinates at hc
  simp_rw [hfull, hbase] at hc
  have hJ : cavitySpectralGroup g₀ = cavityBaseGroup k e a₀ := rfl
  rw [hJ] at hb
  rw [← hb] at hc
  linarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_physical_projector_increment_oai := @OAI.InvariantIsing.cavity_physical_projector_increment_oai
