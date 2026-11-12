-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_orientation_tensor_probability_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:35.684372+00:00
-- url     : https://prove2.me/submissions/6c3fd15f-9884-4cb1-b9b7-312fcf17c08c

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

lemma gaussian_pullback_measurePreserving {ι : Type*} (tag : ι → ℕ)
    (ht : Function.Injective tag) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i => g (tag i)) gaussianCoordinates
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp ht).map_fun_eq_infinitePi_map (fun _ => by fun_prop)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

/-- Injective Gaussian reindexing identifies the entire countable
spin/leaf field law with the flat tensor model. -/
theorem tensorNamespacedFields_law {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) := by
  let Φ := fun (G : TensorGaussianKey I degree → ℝ) (x : Spin N × LabeledLeaf n) =>
    ∑ i : Fin (n + 1), ∑ a : SpinTensorIndex I degree,
      (NNReal.sqrt (v i a) : ℝ) * spinTensorFeature U I degree amplitude x.1 a *
        G (i, (labeledAddress n x.2).take i, a)
  have hmΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro x
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun a _ =>
      (measurable_pi_apply (i.1, (labeledAddress n x.2).take i, a)).const_mul _
  have he : (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q : TensorGaussianKey I degree => g (Encodable.encode q)) := by
    funext g x
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hn : (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q => g (tensorNamespaceTag I degree q)) := by
    funext g x
    rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hp := gaussian_pullback_measurePreserving
    (Encodable.encode : TensorGaussianKey I degree → ℕ) Encodable.encode_injective
  have hq := gaussian_pullback_measurePreserving
    (tensorNamespaceTag I degree) (tensorNamespaceTag_injective I degree)
  rw [he, hn, ← Measure.map_map hmΦ hp.measurable, ← Measure.map_map hmΦ hq.measurable,
    hp.map_eq, hq.map_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The SO correction changes only coordinate signs in the spectral
basis, so every physical projected overlap and quadratic energy agrees. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityOrientationLift_eval {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i =
      (if i=(⟨0,hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)*
        matrixRotation U x i := by
  change ((cavityOrientationSign hN U*(U : Matrix (Fin N) (Fin N) ℝ))*ᵥ x) i = _
  rw [← Matrix.mulVec_mulVec]
  simp only [cavityOrientationSign, Matrix.mulVec_diagonal]
  rfl

lemma cavityOrientationLift_product {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x y : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i *
      specialRotation (cavityOrientationLift hN U) y i =
        matrixRotation U x i * matrixRotation U y i := by
  rw [cavityOrientationLift_eval, cavityOrientationLift_eval]
  split_ifs
  · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
  · ring

lemma cavityOrientationLift_overlap {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap (specialRotation (cavityOrientationLift hN U)) I σ τ =
      projectedOverlap (matrixRotation U) I σ τ := by
  unfold projectedOverlap
  simp_rw [cavityOrientationLift_product]

lemma cavityOrientationLift_energy {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (eig : Fin N → ℝ) (σ : Spin N) :
    rotatedEnergy eig (specialRotation (cavityOrientationLift hN U)) σ =
      rotatedEnergy eig (matrixRotation U) σ := by
  unfold rotatedEnergy
  simp_rw [pow_two, cavityOrientationLift_product]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProbabilityCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian covariance determines the law of the everywhere defined
Gibbs probability, including its zero-partition convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_gibbs_probability_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    gaussianCoordinates.map (fun z => gibbsProbability ν (fun x => H x+cylinderField (A x) z)) =
      gaussianCoordinates.map (fun z => gibbsProbability ν (fun x => H x+cylinderField (C x) z)) := by
  let G : (X → ℝ) → Measure X := fun w => gibbsProbability ν (fun x => H x+w x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_gibbsProbability (ν := fun _ => ν) measurable_const hm
  have hA : Measurable (fun z x => cylinderField (A x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (A x))
  have hC : Measurable (fun z x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  have hh := congrArg (fun μ : Measure (X → ℝ) => μ.map G) (cylinder_fields_law_eq A C hcov)
  simpa only [Measure.map_map hG hA, Measure.map_map hG hC, Function.comp_def, G] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTensorProbabilityLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base Gibbs probability has the same Gaussian law as the
namespaced tensor realization used by the proved GG and Ward estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem tensorLeaf_gibbsProbability_law {N m k depth : ℕ}
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0)
    (T : LabeledTree depth) (H : Spin N × LabeledLeaf depth → ℝ) :
    gaussianCoordinates.map (fun z => gibbsProbability
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => H x+cylinderField (tensorLeafCoefficients U I degree amp depth v x) z)) =
    gaussianCoordinates.map (fun z => gibbsProbability
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => H x+cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z)) := by
  let X := Spin N × LabeledLeaf depth
  let ν : Measure X := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let G : (X → ℝ) → Measure X := fun f => gibbsProbability ν (fun x => H x+f x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_gibbsProbability (ν := fun _ => ν) measurable_const hm
  have hA : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hC : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hh := congrArg (fun μ : Measure (X → ℝ) => μ.map G)
    (tensorNamespacedFields_law U I degree amp depth v)
  simpa only [Measure.map_map hG hA, Measure.map_map hG hC, Function.comp_def, G] using hh

theorem cavity_rotation_tensor_probability_law {N m depth : ℕ}
    (U : SpecialOrthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u
      (((cavitySpecialOrthogonal U)⁻¹,T),z)) =
    gaussianCoordinates.map (fun z => tensorNamespacedReference eig (fun _ => 0) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j)) depth
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) ((U,T),z)) := by
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j : Fin N => u j)
  let v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0 := fun i => tensorPathProfile I degree depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i
  have hh := tensorLeaf_gibbsProbability_law (specialRotation U) I degree amp v T
    (fun x => rotatedEnergy eig (specialRotation U) x.1)
  have hr : matrixRotation (cavitySpecialOrthogonal U) = specialRotation U := rfl
  simp only [cavityRotationProbability, inv_inv, hr, tensorNamespacedReference]
  unfold cavityRotationHamiltonian tensorNamespacedHamiltonian
  simp only [fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [cavityPerturbationCoefficients, degree, amp, v] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orienting the eigenbasis preserves the whole random Gibbs probability,
and identifies it with the published-input tensor realization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityOrientationLift_perturbation_covariance {N m depth : ℕ}
    (hN : 0 < N) (U : Orthogonal N) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN U)) I u depth x)
      (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN U)) I u depth y) =
    cylinderCross (cavityPerturbationCoefficients (matrixRotation U) I u depth x)
      (cavityPerturbationCoefficients (matrixRotation U) I u depth y) := by
  simp only [cavityPerturbationCoefficients_cross, cavityWeightedKernel,
    cavityPerturbationKernel, cavityOrientationLift_overlap]

theorem cavity_orientation_probability_law {N m depth : ℕ} (hN : 0 < N)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u ((V,T),z)) =
      gaussianCoordinates.map (fun z => cavityRotationProbability eig I u
        (((cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹))⁻¹,T),z)) := by
  have hh := cavity_gibbs_probability_same_covariance
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1)
    (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth)
    (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN V⁻¹)) I u depth)
    (fun x y => (cavityOrientationLift_perturbation_covariance hN V⁻¹ I u x y).symm)
  simp only [cavityRotationProbability, inv_inv]
  unfold cavityRotationHamiltonian
  simp only [show matrixRotation (cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹)) =
    specialRotation (cavityOrientationLift hN V⁻¹) from rfl, cavityOrientationLift_energy]
  exact hh

theorem cavity_orientation_tensor_probability_law_oai {N m depth : ℕ} (hN : 0 < N)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u ((V,T),z)) =
      gaussianCoordinates.map (fun z => tensorNamespacedReference eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
        ((cavityOrientationLift hN V⁻¹,T),z)) :=
  (cavity_orientation_probability_law hN V T eig I u).trans
    (cavity_rotation_tensor_probability_law (cavityOrientationLift hN V⁻¹) T eig I u)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_orientation_tensor_probability_law_oai := @OAI.InvariantIsing.cavity_orientation_tensor_probability_law_oai
