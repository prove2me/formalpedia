-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:35:09.060873+00:00
-- url     : https://prove2.me/submissions/ca8e7df1-b8e3-4cb1-8926-ecc6130c7d72
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
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_labeled_moment
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_restricted_gibbs_regularized_match

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

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


lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)


lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

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
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma forestVertexDepth_edgeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n γ i) = i := by
  have h := nodeAddress_nodeAt_length n γ i.succ
  rw [nodeAt_succ,nodeAddress_length_some] at h
  exact Nat.add_right_cancel h

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

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

lemma cavity_one_sub_pow_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (r : ℕ) :
    1 - t ^ r ≤ r * (1 - t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : t ^ r ≤ 1 := pow_le_one₀ ht ht1
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma cavity_normalized_numerator_bound {A Z B : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / Z ^ r| ≤ B := by
  rw [abs_div, abs_of_nonneg (pow_nonneg hZ r)]
  exact div_le_of_le_mul₀ (pow_nonneg hZ r) hB hA

lemma cavity_regularized_numerator_bound {A Z B δ : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / (Z + δ) ^ r| ≤ B := by
  apply cavity_normalized_numerator_bound (add_nonneg hZ hδ) hB r
  exact hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ (by linarith) r) hB)

lemma cavity_normalizer_regularization_error {A Z B δ a : ℝ}
    (ha : 0 < a) (haZ : a ≤ Z) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) :
    |A / Z ^ r - A / (Z + δ) ^ r| ≤ B * r * δ / a := by
  have hZ : 0 < Z := ha.trans_le haZ
  have hZd : 0 < Z + δ := by linarith
  let t := Z / (Z + δ)
  have ht : 0 ≤ t := div_nonneg hZ.le hZd.le
  have ht1 : t ≤ 1 := (div_le_one hZd).mpr (by linarith)
  have htp : 0 ≤ 1 - t ^ r := sub_nonneg.mpr (pow_le_one₀ ht ht1)
  have he : A / Z ^ r - A / (Z + δ) ^ r = A / Z ^ r * (1 - t ^ r) := by
    dsimp [t]
    rw [div_pow]
    field_simp [ne_of_gt hZ, ne_of_gt hZd]
  have hsub : 1 - t = δ / (Z + δ) := by
    dsimp [t]
    field_simp [ne_of_gt hZd]
    ring
  calc
    _ = |A / Z ^ r| * (1 - t ^ r) := by rw [he, abs_mul, abs_of_nonneg htp]
    _ ≤ B * (r * (1 - t)) :=
      mul_le_mul (cavity_normalized_numerator_bound hZ.le hB r hA)
        (cavity_one_sub_pow_le ht ht1 r) htp hB
    _ = B * r * (δ / (Z + δ)) := by rw [hsub]; ring
    _ ≤ B * r * (δ / a) := mul_le_mul_of_nonneg_left
      (div_le_div₀ hδ le_rfl ha (by linarith)) (mul_nonneg hB (Nat.cast_nonneg r))
    _ = _ := by ring

theorem cavity_normalizer_regularization_mean_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A Z : Ω → ℝ) (hA : Measurable A) (hZ : Measurable Z)
    {B δ a : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ha : 0 < a) (r : ℕ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hAZ : ∀ ω, |A ω| ≤ B * Z ω ^ r) :
    |∫ ω, (A ω / Z ω ^ r - A ω / (Z ω + δ) ^ r) ∂P| ≤
      B * r * δ / a + 2 * B * P.real {ω | Z ω < a} := by
  let D := fun ω => A ω / Z ω ^ r - A ω / (Z ω + δ) ^ r
  let c := B * r * δ / a
  let E := {ω | Z ω < a}
  have hE : MeasurableSet E := measurableSet_lt hZ measurable_const
  have hD : Measurable D := (hA.div (hZ.pow_const r)).sub
    (hA.div ((hZ.add_const δ).pow_const r))
  have hb ω : |D ω| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by
      have h1 := cavity_normalized_numerator_bound (hZ0 ω) hB r (hAZ ω)
      have h2 := cavity_regularized_numerator_bound (hZ0 ω) hB hδ r (hAZ ω)
      linarith)
  have hi : Integrable D P := integrable_of_measurable_abs_le hD hb
  have hc : 0 ≤ c := by positivity
  have hind : Integrable (E.indicator (fun _ => 2 * B)) P := (integrable_const _).indicator hE
  calc
    _ ≤ ∫ ω, |D ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (c + E.indicator (fun _ => 2 * B) ω) ∂P := by
      apply integral_mono hi.abs ((integrable_const c).add hind)
      intro ω
      change |D ω| ≤ c + E.indicator (fun _ => 2 * B) ω
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        linarith [hb ω]
      · rw [indicator_of_notMem hω, add_zero]
        exact cavity_normalizer_regularization_error ha (le_of_not_gt hω) hB hδ r (hAZ ω)
    _ = _ := by
      rw [integral_add (integrable_const c) hind, integral_const, integral_indicator_const _ hE]
      simp only [probReal_univ, smul_eq_mul]
      dsimp [c, E]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cutoff weight is bounded below whenever the discarded prior mass
is at most one half. The exceptional event is controlled by its mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_cutoff_normalizer_lower {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (s : Set X) (hs : MeasurableSet s)
    (w : X → ℝ) (hw : Measurable w) {c M : ℝ} (hc : 0 ≤ c)
    (hwb : ∀ x ∈ s, w x ∈ Icc c M) :
    c * (1 - ν.real sᶜ) ≤ cavityWeightNormalizer ν (s.indicator w) := by
  have hwi : Integrable (s.indicator w) ν := by
    apply integrable_of_measurable_abs_le (hw.indicator hs) (c := max M 0)
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, abs_of_nonneg (hc.trans (hwb x hx).1)]
      exact (hwb x hx).2.trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, abs_zero]
      exact le_max_right _ _
  have hlow := integral_mono ((integrable_const c).indicator hs) hwi (fun x => by
    change s.indicator (fun _ => c) x ≤ s.indicator w x
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using (hwb x hx).1
    · simp only [indicator_of_notMem hx, le_refl])
  rw [integral_indicator_const c hs, smul_eq_mul] at hlow
  change c * (1 - ν.real sᶜ) ≤ ∫ x, s.indicator w x ∂ν
  calc
    _ = ν.real s * c := by rw [measureReal_compl hs, probReal_univ]; ring
    _ ≤ _ := hlow

lemma cavity_cutoff_normalizer_half {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (s : Set X) (hs : MeasurableSet s)
    (w : X → ℝ) (hw : Measurable w) {c M : ℝ} (hc : 0 ≤ c)
    (hwb : ∀ x ∈ s, w x ∈ Icc c M) (htail : ν.real sᶜ ≤ 1 / 2) :
    c / 2 ≤ cavityWeightNormalizer ν (s.indicator w) := by
  have h := cavity_cutoff_normalizer_lower ν s hs w hw hc hwb
  nlinarith

lemma cavity_small_normalizer_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z t : Ω → ℝ)
    (hZ : Measurable Z) (_ht : Measurable t) (hti : Integrable t P) (ht0 : ∀ ω, 0 ≤ t ω)
    {a : ℝ} (hlow : ∀ ω, t ω ≤ 1 / 2 → a ≤ Z ω) :
    P.real {ω | Z ω < a} ≤ 2 * ∫ ω, t ω ∂P := by
  let E := {ω | Z ω < a}
  have hE : MeasurableSet E := measurableSet_lt hZ measurable_const
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hle := integral_mono hi (hti.const_mul 2) (fun ω => by
    change E.indicator (fun _ => (1 : ℝ)) ω ≤ 2 * t ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      have hlarge : 1 / 2 < t ω := by
        by_contra hh
        exact (not_le_of_gt hω) (hlow ω (le_of_not_gt hh))
      linarith
    · rw [indicator_of_notMem hω]
      exact mul_nonneg (by norm_num) (ht0 ω))
  simpa only [integral_indicator_const _ hE, smul_eq_mul, mul_one, integral_const_mul] using hle

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedRegularizationError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative denominator-removal bound for the restricted weights.
The prior tail controls the exceptional small-normalizer event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_bounded_regularization_mean_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (t : Ω → ℝ) (ht : Measurable t) (hti : Integrable t P) (ht0 : ∀ ω, 0 ≤ t ω)
    {M B δ a : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ha : 0 < a)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B)
    (hlow : ∀ ω, t ω ≤ 1/2 → a ≤ cavityWeightNormalizer (ν ω) (fun x => w (ω,x))) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω) (fun x => w (ω,x))
        (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
        (fun σ => F (ω,σ)) ∂P| ≤ B * r * δ / a + 4 * B * ∫ ω, t ω ∂P := by
  let Z ω := cavityWeightNormalizer (ν ω) (fun x => w (ω,x))
  let A ω := cavityWeightNumerator (ν ω) (fun x => w (ω,x)) (fun σ => F (ω,σ))
  have hZ : Measurable Z := measurable_cavityWeightNormalizer ν hν w hw
  have hA : Measurable A := measurable_cavityWeightNumerator ν hν w hw F hF
  have hZ0 ω : 0 ≤ Z ω :=
    (cavityWeightNormalizer_mem (ν ω) _ (hw.comp measurable_prodMk_left) le_rfl (hwb ω)).1
  have hAZ ω : |A ω| ≤ B * Z ω^r :=
    cavityWeightNumerator_abs_le_normalizer (ν ω) _ (hw.comp measurable_prodMk_left)
      _ (hF.comp measurable_prodMk_left) hM hB (hwb ω) (hFb ω)
  have hi : Integrable (fun ω => A ω / Z ω^r) P :=
    integrable_of_measurable_abs_le (hA.div (hZ.pow_const r))
      (fun ω => cavity_normalized_numerator_bound (hZ0 ω) hB r (hAZ ω))
  have hiδ : Integrable (fun ω => A ω / (Z ω + δ)^r) P :=
    integrable_of_measurable_abs_le (hA.div ((hZ.add_const δ).pow_const r))
      (fun ω => cavity_regularized_numerator_bound (hZ0 ω) hB hδ r (hAZ ω))
  have he := cavity_normalizer_regularization_mean_error P A Z hA hZ hB hδ ha r hZ0 hAZ
  have hp := cavity_small_normalizer_probability P Z t hZ ht hti ht0 hlow
  change |(∫ ω, A ω / (Z ω + δ)^r ∂P) - ∫ ω, A ω / Z ω^r ∂P| ≤ _
  rw [abs_sub_comm, ← integral_sub hi hiδ]
  exact he.trans (by nlinarith)

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
attribute [-instance] _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
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

lemma cavityRotationMatrix_apply {n : ℕ} (U : Rotation n)
    (x : EuclideanSpace ℝ (Fin n)) : matrixRotation (cavityRotationMatrix U) x = U x := by
  have h := U.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis x
  ext i
  exact congrFun h i

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySphereAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular averaging for the moments of fresh Haar frame coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_matrixRotation_mul_apply {n : ℕ} (U V : Orthogonal n)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixRotation (U * V) x = matrixRotation U (matrixRotation V x) := by
  ext i
  change (((U : Matrix (Fin n) (Fin n) ℝ) * (V : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x.ofLp) i =
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((V : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma cavity_unit_vector_transitive {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : Orthogonal n, matrixRotation U v = w := by
  have ho (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
      Orthonormal ℝ (fun _ : Fin 1 => x) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, hx]
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _ (ho v hv) (ho w hw)
  exact ⟨cavityRotationMatrix U, (cavityRotationMatrix_apply U v).trans (hU 0)⟩

lemma continuous_cavityRotationAction (n : ℕ) :
    Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) => matrixRotation p.1 p.2) := by
  change Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) =>
    WithLp.toLp 2 ((p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ p.2.ofLp))
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

lemma cavity_sphere_average_independent {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u w : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) =
      ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
  obtain ⟨V, hV⟩ := cavity_unit_vector_transitive u w hu hw
  rw [← hV]
  simp_rw [← cavity_matrixRotation_mul_apply]
  exact (integral_mul_right_eq_self (μ := μ)
    (fun U : Orthogonal n => |⟪v, matrixRotation U u⟫| ^ p) V).symm

theorem cavity_sphere_radial_average {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U x⟫| ^ p ∂μ) =
      ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  by_cases hx : x = 0
  · subst x
    by_cases hp : p = 0 <;> simp [hp]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let w := ‖x‖⁻¹ • x
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
  have hxw : x = ‖x‖ • w := by simp [w, smul_smul, hn]
  calc
    _ = ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
      conv_lhs => rw [hxw]
      simp_rw [map_smul, real_inner_smul_right, abs_mul, abs_norm, mul_pow]
      rw [integral_const_mul]
    _ = _ := by rw [cavity_sphere_average_independent μ v w u hw hu p]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRadialMoments
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-explicit Gaussian radial moments used to bound moments of
uniform spherical projections. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace InvariantIsing

lemma cavityGaussianAbsMoment_nonneg (p : ℕ) : 0 ≤ cavityGaussianAbsMoment p :=
  integral_nonneg (fun z => pow_nonneg (abs_nonneg z) p)

lemma cavityGaussianAbsMoment_two : cavityGaussianAbsMoment 2 = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [cavityGaussianAbsMoment, id_eq, integral_id_gaussianReal,
    sub_zero, sq_abs, NNReal.coe_one] using h

lemma cavity_gaussian_norm_pow_integrable (n p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) (stdGaussian _) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) p (by simp)).integrable_norm_pow'

lemma cavity_gaussian_inner_abs_moment {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ‖v‖ ^ p * cavityGaussianAbsMoment p := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ v
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [L, innerSL_apply_norm, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (by simp)
  calc
    _ = ∫ z : ℝ, |z| ^ p ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map L :=
      (integral_map L.continuous.aemeasurable (by fun_prop)).symm
    _ = ∫ z : ℝ, |z| ^ p ∂(gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by rw [hm]
    _ = ‖v‖ ^ p * cavityGaussianAbsMoment p := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [abs_mul, abs_norm, mul_pow, integral_const_mul, cavityGaussianAbsMoment]

lemma cavity_gaussian_norm_sq_integral (n : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 ∂stdGaussian _) = n := by
  have hcoord (i : Fin n) :
      (∫ z : EuclideanSpace ℝ (Fin n), z i ^ 2 ∂stdGaussian _) = 1 := by
    have h := cavity_gaussian_inner_abs_moment (EuclideanSpace.basisFun (Fin n) ℝ i) 2
    simpa only [EuclideanSpace.basisFun_inner, sq_abs,
      OrthonormalBasis.norm_eq_one, one_pow, one_mul, cavityGaussianAbsMoment_two] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · intro i _
    simpa only [innerSL_apply_apply, EuclideanSpace.basisFun_inner, Real.norm_eq_abs, sq_abs] using
      (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 (by simp)).integrable_norm_pow'

lemma cavity_gaussian_radial_moment_lower (n k : ℕ) :
    (n : ℝ) ^ k ≤ ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _ := by
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2)
      (stdGaussian _) := cavity_gaussian_norm_pow_integrable n 2
  have hik : Integrable (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖ ^ 2) ^ k)
      (stdGaussian _) := by
    simpa only [← pow_mul] using cavity_gaussian_norm_pow_integrable n (2 * k)
  have h := (convexOn_pow k (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun z => sq_nonneg ‖z‖)) hi hik
  simpa only [cavity_gaussian_norm_sq_integral, ← pow_mul] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySphereMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform even moments of Haar projections. Gaussian angular averaging
gives a bound with the dimension in the denominator. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_gaussian_angular_moment {n : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  let F := fun U : Orthogonal n => fun z : EuclideanSpace ℝ (Fin n) =>
    |⟪v, matrixRotation U z⟫| ^ p
  have hF : Continuous (Function.uncurry F) :=
    (continuous_const.inner (continuous_cavityRotationAction n)).abs.pow p
  have hb (U : Orthogonal n) (z : EuclideanSpace ℝ (Fin n)) :
      |F U z| ≤ ‖v‖ ^ p * ‖z‖ ^ p := by
    dsimp [F]
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [(matrixRotation U).norm_map] using abs_real_inner_le_norm v (matrixRotation U z)) p
  have hi : Integrable (Function.uncurry F) (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
    apply (((cavity_gaussian_norm_pow_integrable n p).const_mul (‖v‖ ^ p)).comp_snd μ).mono'
      hF.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change |F z.1 z.2| ≤ ‖v‖ ^ p * ‖z.2‖ ^ p
      exact hb z.1 z.2)
  have hrot (U : Orthogonal n) :
      (∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    calc
      _ = ∫ z, |⟪v, z⟫| ^ p
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map (matrixRotation U) :=
        (integral_map (matrixRotation U).continuous.aemeasurable (by fun_prop)).symm
      _ = _ := by rw [stdGaussian_map]
  calc
    _ = ∫ U, ∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ∂μ := by
      simp_rw [hrot]
      simp
    _ = ∫ z, ∫ U, F U z ∂μ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      integral_integral_swap hi
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p *
        (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ (fun z => cavity_sphere_radial_average μ v u z hu p))
    _ = _ := integral_mul_const _ _

theorem cavity_sphere_even_moment_bound {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (k : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ) ≤
      cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) / (n : ℝ) ^ k := by
  have hp : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hn) k
  apply (le_div_iff₀ hp).mpr
  have hnon : 0 ≤ ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
    integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)
  calc
    _ = (n : ℝ) ^ k * ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ := mul_comm _ _
    _ ≤ (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
      mul_le_mul_of_nonneg_right (cavity_gaussian_radial_moment_lower n k) hnon
    _ = cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) := by
      rw [← cavity_gaussian_angular_moment μ v u hu, cavity_gaussian_inner_abs_moment, mul_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianEnvelope
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial-exponential moments for the finite Gaussian marks
after the quadratic tilt. Only the norm of the covariance factor matters. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_standardGaussian_exp_norm_integrable (d : ℕ) (c : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (c * ‖z‖)) (stdGaussian _) := by
  obtain ⟨a, ha, hi⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian (EuclideanSpace ℝ (Fin d)))
  let b := c^2 / (4 * a)
  have hb : 4 * a * b = c^2 := mul_div_cancel₀ _ (by positivity)
  apply (hi.const_mul (Real.exp b)).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs := sq_nonneg (2 * a * ‖z‖ - c)
    nlinarith

lemma cavity_polynomial_exp_bound (p : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    r^p * Real.exp (c * r) ≤ Real.exp ((p + c) * r) := by
  have he : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hp := pow_le_pow_left₀ hr he p
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (c * r)).le
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hm
  simpa only [add_mul] using hm

theorem cavity_gaussian_linear_polynomial_exp_bound {d q : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin q))
    {M c : ℝ} (_hM : 0 ≤ M) (hL : ‖L‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) ∧
    (∫ z : EuclideanSpace ℝ (Fin d), ‖L z‖^p * Real.exp (c * ‖L z‖) ∂stdGaussian _) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), Real.exp (((p : ℝ) + c) * M * ‖z‖) ∂stdGaussian _ := by
  have hi := cavity_standardGaussian_exp_norm_integrable d (((p : ℝ) + c) * M)
  have hb z : ‖L z‖^p * Real.exp (c * ‖L z‖) ≤ Real.exp (((p : ℝ) + c) * M * ‖z‖) := by
    have hn : ‖L z‖ ≤ M * ‖z‖ := (L.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
    apply (cavity_polynomial_exp_bound p c ‖L z‖ (norm_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (add_nonneg (Nat.cast_nonneg p) hc)]
  have hif : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) := by
    apply hi.mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb z
  exact ⟨hif, integral_mono hif hi hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform moments of the remaining linear cavity tilt. The estimate uses
only the one-replica exponential radial moment after the quadratic tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma cavity_linear_envelope_bounds (p : ℕ) {c r v : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hv : |v| ≤ c * (1 + r)) :
    |v| ≤ c * cavityLinearMomentEnvelope p c r ∧
    Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r ∧
    r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hve := abs_le.mp hv
  have hexp : Real.exp r ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin : |v| ≤ c * cavityLinearMomentEnvelope p c r :=
    hv.trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using (Real.add_one_le_exp r).trans hexp) hc)
  have hev : Real.exp v ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hneg : Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : r^p * Real.exp v ≤ Real.exp ((p : ℝ) * r + v) := by
    have h := cavity_polynomial_exp_bound p 0 r hr
    simp only [zero_mul, Real.exp_zero, mul_one, add_zero] at h
    calc
      _ ≤ Real.exp ((p : ℝ) * r) * Real.exp v :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hprod1 : r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hprod2 : (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    apply (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr p) (Real.exp_pos _).le) hprod 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hneg2 : Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact ⟨hlin, hev, hneg, hprod1, hprod2, hneg2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearGaussianMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A covariance bound gives a step-independent moment bound for the
remaining cavity tilt, including singular Gaussian covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_linear_envelope {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => cavityLinearMomentEnvelope p c ‖y‖)
      (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖y‖
      ∂multivariateGaussian 0 S) ≤ cavityGaussianLinearMomentBound d p c M := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hL : ‖L‖ ≤ Real.sqrt M := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, CFC.norm_sqrt S hS.nonneg]
    exact Real.sqrt_le_sqrt hSM
  have ha : 0 ≤ (2 : ℝ) * p + 2 * c + 1 := by positivity
  have hG := cavity_gaussian_linear_polynomial_exp_bound L (Real.sqrt_nonneg M) hL ha 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hG
  have hi := hG.1.const_mul (Real.exp (2 * c))
  have he (z : EuclideanSpace ℝ (Fin d)) :
      cavityLinearMomentEnvelope p c ‖L z‖ =
        Real.exp (2 * c) * Real.exp ((2 * p + 2 * c + 1) * ‖L z‖) := Real.exp_add _ _
  have his : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      cavityLinearMomentEnvelope p c ‖y‖) (multivariateGaussian 0 S) := by
    rw [multivariateGaussian, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) (by fun_prop)]
    simpa only [zero_add, Function.comp_def, cavityLinearMomentEnvelope, Real.exp_add, L] using hi
  refine ⟨his, ?_⟩
  rw [multivariateGaussian, integral_map (by fun_prop) (by unfold cavityLinearMomentEnvelope; fun_prop)]
  simp only [zero_add]
  change (∫ z : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖L z‖ ∂stdGaussian _) ≤ _
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hG.2 (Real.exp_pos _).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianSum
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sums of independent Gaussian increments used in the cavity path. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_gaussian_sum_law {ι : Type*} [Fintype ι] {d : ℕ}
    (S : ι → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef) :
    (Measure.pi (fun i => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i))).map
        (fun z => ∑ i, z i) = multivariateGaussian 0 (∑ i, S i) := by
  have hsum : (∑ i, S i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun i _ => hS i)
  apply Measure.ext_of_charFun
  rw [charFun_map_sum_pi_eq_prod]
  funext x
  simp only [Finset.prod_apply, charFun_multivariateGaussian, hS, hsum, inner_zero_right,
    Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  have hquad : x ⬝ᵥ (∑ i, S i) *ᵥ x = ∑ i, x ⬝ᵥ S i *ᵥ x := by
    simp only [Matrix.sum_mulVec, dotProduct_sum]
  rw [hquad]
  simp only [Complex.ofReal_sum, Finset.sum_div, Finset.sum_neg_distrib]

theorem cavity_gaussian_add_law {d : ℕ}
    (S T : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).prod
      (multivariateGaussian 0 T)).map (fun p => p.1 + p.2) =
      multivariateGaussian 0 (S + T) := by
  apply Measure.ext_of_charFun
  rw [charFun_map_add_prod_eq_mul]
  funext x
  simp only [Pi.mul_apply, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hT, charFun_multivariateGaussian (hS.add hT),
    inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  rw [Matrix.add_mulVec, dotProduct_add]
  push_cast
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOneReplicaPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sampled innovation path has independent Gaussian increments.
This is the marginal needed by the remaining linear-tilt moment bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_edgeAt_injective (n : ℕ) (γ : LabeledLeaf n) :
    Function.Injective (edgeAt n γ) := by
  intro i j hij
  apply Fin.ext
  simpa only [forestVertexDepth_edgeAt] using congrArg (forestVertexDepth n) hij

lemma cavity_selected_path_law {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (γ : LabeledLeaf n) :
    (Measure.infinitePi (fun v : ForestVertex n =>
      (μ (forestVertexDepth n v) : Measure A))).map (fun g i => g (edgeAt n γ i)) =
      Measure.pi (fun i : Fin n => (μ i : Measure A)) := by
  have hi : iIndepFun (fun v (g : ForestVertex n → A) => g v)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (cavity_edgeAt_injective n γ)
  have he := hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (edgeAt n γ i)).aemeasurable)
  simpa only [Measure.infinitePi_map_eval, forestVertexDepth_edgeAt] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityContinuousReplicaTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential replica tilts on the continuous leaf/residual state space.
Finite-product identities do not require a countable configuration space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma cavity_exp_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (∫ x, Real.exp (H x) ∂ν)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin] using
    integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x))

lemma cavity_continuous_replica_tilt {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  let := isProbabilityMeasure_tilted he
  have hZ : 0 < ∫ x, Real.exp (H x) ∂ν := integral_exp_pos he
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs),
    cavity_exp_replica_partition, Measure.restrict_pi_pi]
  have hh (σ : Fin r → X) : Real.exp (∑ i, H (σ i)) /
      (∫ x, Real.exp (H x) ∂ν)^r =
        ∏ i, Real.exp (H (σ i)) / (∫ x, Real.exp (H x) ∂ν) := by
    rw [Real.exp_sum, Finset.prod_div_distrib]
    simp
  simp_rw [hh]
  rw [integral_fintype_prod_eq_prod
    (fun (_ : Fin r) x => Real.exp (H x) / (∫ y, Real.exp (H y) ∂ν))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
    div_nonneg (Real.exp_pos _).le hZ.le))]
  congr 1
  funext i
  exact (tilted_apply_eq_ofReal_integral' H (hs i)).symm

lemma cavityWeightedReplicaMean_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ}
    (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (fun x => Real.exp (H x)) F =
      ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← cavity_continuous_replica_tilt ν H he r, integral_tilted_eq_div,
    cavity_exp_replica_partition]
  simp only [cavityWeightedReplicaMean, cavityWeightNormalizer,
    cavityWeightNumerator, Real.exp_sum]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar resolvent bounds, including the extension at zero.
The comparison uses any alphabet point above the compressed eigenvalue. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityScalarResolvent_denominator_pos (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 ≤ x) :
    0 < 1 + x * (finiteR ρ eig hρ hρsum x - α) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · have hgap : 0 < finiteInverse ρ eig hρ hρsum x - α :=
      sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))
    have he : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
        x * (finiteInverse ρ eig hρ hρsum x - α) := by
      simp only [finiteR, ite_eq_left hx]
      field_simp [hx.ne']
      ring
    rw [he]
    exact mul_pos hx hgap

lemma cavityScalarResolvent_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    cavityScalarResolvent ρ eig hρ hρsum α x =
      (finiteInverse ρ eig hρ hρsum x - α)⁻¹ := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hden : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
      x * (finiteInverse ρ eig hρ hρsum x - α) := by
    simp only [finiteR, ite_eq_left hx]
    field_simp [hx.ne']
    ring
  rw [cavityScalarResolvent, hden, div_mul_eq_div_div, div_self hx.ne', one_div]

lemma continuousOn_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a) :
    ContinuousOn (cavityScalarResolvent ρ eig hρ hρsum α) (Ici 0) := by
  apply continuousOn_id.div
    (continuousOn_const.add (continuousOn_id.mul
      ((continuous_finiteR ρ eig hρ hρsum).continuousOn.sub continuousOn_const)))
  intro x hx
  exact (cavityScalarResolvent_denominator_pos ρ eig hρ hρsum a hα hx).ne'

lemma hasDerivAt_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    HasDerivAt (cavityScalarResolvent ρ eig hρ hρsum α)
      (1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2)) x := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hM := (finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum
    (finiteInverse_spec ρ eig hρ hρsum hx).1).ne'
  have hd := ((hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx).hasDerivAt.sub_const α).inv hg
  have he : (fun y => (finiteInverse ρ eig hρ hρsum y - α)⁻¹) =ᶠ[𝓝 x]
      cavityScalarResolvent ρ eig hρ hρsum α := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (cavityScalarResolvent_pos_eq ρ eig hρ hρsum a hα hy).symm
  convert hd.congr_of_eventuallyEq he.symm using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hM, hg]

lemma cavityScalarResolvent_derivative_bound (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    0 ≤ 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ∧
    1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ≤ (ρ a)⁻¹ := by
  classical
  let b := finiteInverse ρ eig hρ hρsum x
  let M := finiteSecondResolvent ρ eig b
  have hs : ∀ j, eig j < b := (finiteInverse_spec ρ eig hρ hρsum hx).1
  have hM : 0 < M := finiteSecondResolvent_pos (fun j => (hρ j).le) hρsum hs
  have hga : 0 < b - eig a := sub_pos.mpr (hs a)
  have hg : 0 < b - α := sub_pos.mpr (hα.trans_lt (hs a))
  have hpart : ρ a / (b - eig a)^2 ≤ M := by
    exact Finset.single_le_sum (f := fun j => ρ j / (b - eig j)^2)
      (fun j _ => div_nonneg (hρ j).le (sq_nonneg _)) (Finset.mem_univ a)
  have hsq : (b - eig a)^2 ≤ (b - α)^2 := by nlinarith
  have hprod : ρ a ≤ M * (b - α)^2 := by
    calc
      ρ a = (ρ a / (b - eig a)^2) * (b - eig a)^2 := by field_simp
      _ ≤ M * (b - eig a)^2 := mul_le_mul_of_nonneg_right hpart (sq_nonneg _)
      _ ≤ M * (b - α)^2 := mul_le_mul_of_nonneg_left hsq hM.le
  refine ⟨by positivity, ?_⟩
  simpa only [one_div, M, b] using one_div_le_one_div_of_le (hρ a) hprod

theorem cavityScalarResolvent_lipschitz (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) :
    |cavityScalarResolvent ρ eig hρ hρsum α y - cavityScalarResolvent ρ eig hρ hρsum α x| ≤
      (ρ a)⁻¹ * (y - x) := by
  rcases hy.eq_or_lt with rfl | hxy
  · simp
  let D := fun z => 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum z) *
    (finiteInverse ρ eig hρ hρsum z - α)^2)
  obtain ⟨z, hz, hd⟩ := exists_hasDerivAt_eq_slope
    (cavityScalarResolvent ρ eig hρ hρsum α) D hxy
    ((continuousOn_cavityScalarResolvent ρ eig hρ hρsum a hα).mono
      (fun t ht => hx.trans ht.1))
    (fun t ht => hasDerivAt_cavityScalarResolvent ρ eig hρ hρsum a hα (hx.trans_lt ht.1))
  have hbound := cavityScalarResolvent_derivative_bound ρ eig hρ hρsum a hα (hx.trans_lt hz.1)
  have he : cavityScalarResolvent ρ eig hρ hρsum α y -
      cavityScalarResolvent ρ eig hρ hρsum α x = D z * (y - x) :=
    ((eq_div_iff (sub_pos.mpr hxy).ne').mp hd).symm
  rw [he, abs_mul, abs_of_nonneg hbound.1, abs_of_pos (sub_pos.mpr hxy)]
  exact mul_le_mul_of_nonneg_right hbound.2 (sub_pos.mpr hxy).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCovariancePartitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common root, all positive levels, and the residual have total
covariance mass one. This estimate is independent of the number of steps. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_covariance_partition_bound {d n : ℕ}
    (T : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (q x : Fin (n + 1) → ℝ) (b : Fin n → ℝ) {C : ℝ}
    (hT0 : T 0 = 0)
    (hT : ∀ u v, 0 ≤ u → u ≤ v → ‖T v - T u‖ ≤ C * (v - u))
    (hG : ‖G‖ ≤ C) (hq : Monotone q) (hq0 : 0 ≤ q 0)
    (hx : ∀ i, 0 ≤ x i)
    (hb : ∀ i, 0 < b i)
    (hgap : ∀ i, x i.castSucc - x i.succ = b i * (q i.succ - q i.castSucc))
    (hlast : x (Fin.last n) = 1 - q (Fin.last n)) :
    ‖q 0 • G + (∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))) +
      T (x (Fin.last n))‖ ≤ C := by
  have hqstep (i : Fin n) : 0 ≤ q i.succ - q i.castSucc :=
    sub_nonneg.mpr (hq (Fin.castSucc_le_succ i))
  have hstep (i : Fin n) :
      ‖(b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ ≤ C * (q i.succ - q i.castSucc) := by
    have horder : x i.succ ≤ x i.castSucc := by
      have := mul_nonneg (hb i).le (hqstep i)
      linarith [hgap i]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hb i))]
    calc
      _ ≤ (b i)⁻¹ * (C * (x i.castSucc - x i.succ)) :=
        mul_le_mul_of_nonneg_left (hT _ _ (hx i.succ) horder) (inv_pos.mpr (hb i)).le
      _ = C * (q i.succ - q i.castSucc) := by rw [hgap i]; field_simp [(hb i).ne']
  have hroot : ‖q 0 • G‖ ≤ C * q 0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hG hq0
  have htail : ‖T (x (Fin.last n))‖ ≤ C * (1 - q (Fin.last n)) := by
    simpa only [hT0, sub_zero, hlast] using hT 0 (x (Fin.last n)) le_rfl (hx _)
  have htel : (∑ i : Fin n, (q i.succ - q i.castSucc)) = q (Fin.last n) - q 0 := by
    rw [Finset.sum_sub_distrib]
    have h0 := Fin.sum_univ_succ q
    have h1 := Fin.sum_univ_castSucc q
    linarith
  calc
    _ ≤ ‖q 0 • G‖ + ‖∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ +
        ‖T (x (Fin.last n))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * q 0 + (∑ i : Fin n, C * (q i.succ - q i.castSucc)) + C * (1 - q (Fin.last n)) := by
      exact add_le_add (add_le_add hroot ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hstep i)))) htail
    _ = C := by rw [← Finset.mul_sum, htel]; ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySoftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous cutoffs for finite-replica passage. Their removal costs
only the discarded mass, including the zero-normalizer convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_normalized_cutoff_algebra {A F Z B : ℝ} (r : ℕ)
    (hZ : Z ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B)
    (hA : |A| ≤ B * Z ^ r) (hAF : |A - F| ≤ B * (1 - Z ^ r)) :
    |A / Z ^ r - F| ≤ 2 * B * r * (1 - Z) := by
  have hp : Z ^ r ≤ 1 := pow_le_one₀ hZ.1 hZ.2
  have hnp : 0 ≤ 1 - Z ^ r := sub_nonneg.mpr hp
  have hb := cavity_normalized_numerator_bound hZ.1 hB r hA
  have he : A / Z ^ r - A = A / Z ^ r * (1 - Z ^ r) := by
    by_cases hz : Z ^ r = 0
    · have ha : A = 0 := abs_nonpos_iff.mp (by simpa only [hz, mul_zero] using hA)
      simp only [ha, zero_div, sub_self, zero_mul]
    · field_simp
  calc
    _ ≤ |A / Z ^ r - A| + |A - F| := abs_sub_le _ _ _
    _ = |A / Z ^ r| * (1 - Z ^ r) + |A - F| := by
      rw [he, abs_mul, abs_of_nonneg hnp]
    _ ≤ B * (1 - Z ^ r) + B * (1 - Z ^ r) :=
      add_le_add (mul_le_mul_of_nonneg_right hb hnp) hAF
    _ = 2 * B * (1 - Z ^ r) := by ring
    _ ≤ 2 * B * (r * (1 - Z)) := mul_le_mul_of_nonneg_left
      (cavity_one_sub_pow_le hZ.1 hZ.2 r) (by positivity)
    _ = _ := by ring

theorem cavity_soft_cutoff_replica_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    (hwb : ∀ x, w x ∈ Icc (0 : ℝ) 1) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν w F - ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤
      2 * B * r * (1 - cavityWeightNormalizer ν w) := by
  let P := Measure.pi (fun _ : Fin r => ν)
  let V := fun σ : Fin r → X => ∏ i, w (σ i)
  have hVm : Measurable V := Finset.measurable_prod _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hV0 σ : 0 ≤ V σ := Finset.prod_nonneg (fun i _ => (hwb (σ i)).1)
  have hV1 σ : V σ ≤ 1 := by
    exact (Finset.prod_le_prod (fun i _ => (hwb (σ i)).1)
      (fun i _ => (hwb (σ i)).2)).trans_eq (by simp)
  have hiV : Integrable V P := integrable_of_measurable_abs_le hVm
    (fun σ => by rw [abs_of_nonneg (hV0 σ)]; exact hV1 σ)
  have hiF : Integrable F P := integrable_of_measurable_abs_le hF hFb
  have hiVF : Integrable (fun σ => V σ * F σ) P := hiV.mul_bdd hF.aestronglyMeasurable
    (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hFb σ))
  have hvi : (∫ σ, V σ ∂P) = cavityWeightNormalizer ν w ^ r := by
    simpa only [P, V, cavityWeightNormalizer, Fintype.card_fin] using
      integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) w
  apply cavity_normalized_cutoff_algebra r
    (cavityWeightNormalizer_mem ν w hw (by norm_num) hwb) hB
    (cavityWeightNumerator_abs_le_normalizer ν w hw F hF (by norm_num) hB hwb hFb)
  change |(∫ σ, V σ * F σ ∂P) - ∫ σ, F σ ∂P| ≤ _
  rw [← integral_sub hiVF hiF]
  calc
    _ ≤ ∫ σ, |V σ * F σ - F σ| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * (1 - V σ) ∂P := by
      apply integral_mono (hiVF.sub hiF).abs (((integrable_const 1).sub hiV).const_mul B)
      intro σ
      change |V σ * F σ - F σ| ≤ B * (1 - V σ)
      rw [← sub_one_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr (hV1 σ)), neg_sub]
      exact (mul_le_mul_of_nonneg_left (hFb σ) (sub_nonneg.mpr (hV1 σ))).trans_eq (mul_comm _ _)
    _ = B * (1 - cavityWeightNormalizer ν w ^ r) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hiV, integral_const, hvi]
      simp only [probReal_univ, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffFloorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The order of the two remaining limits: choose a large spatial radius,
then a small denominator floor, then pass to the system-size limit. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_cutoff_floor_comparison
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (u v : ℕ → ℝ → ℕ → ℝ) (a e : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ j, 0 < a j) (he : Tendsto e atTop (𝓝 0))
    (hfu : ∀ j δ, 0 < δ → ∀ n, |f j n - u j δ n| ≤ C*δ/a j + e j)
    (hvg : ∀ j δ, 0 < δ → ∀ n, |v j δ n - g n| ≤ C*δ/a j + e j)
    (huv : ∀ j δ, 0 < δ → Tendsto (fun n => u j δ n - v j δ n) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop, |f j n - g n| < ε := by
  intro ε hε
  filter_upwards [he.eventually (Iio_mem_nhds (show (0 : ℝ) < ε/6 by positivity))] with j hj
  have haj := ha j
  let δ := ε*a j/(12*(C+1))
  have hδ : 0 < δ := by dsimp only [δ] <;> positivity
  have hsmall : C*δ/a j ≤ ε/12 := by
    have heq : C*δ/a j = (ε/12)*(C/(C+1)) := by
      dsimp only [δ]
      field_simp [haj.ne', show C+1 ≠ 0 by linarith]
    rw [heq]
    have hc : C/(C+1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)
  filter_upwards [(huv j δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε/3 by positivity))] with n hn
  rw [Real.dist_eq,sub_zero] at hn
  have h₁ := hfu j δ hδ n
  have h₂ := hvg j δ hδ n
  have htri := abs_sub_le (f j n) (u j δ n) (g n)
  have htri' := abs_sub_le (u j δ n) (v j δ n) (g n)
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDeficitGap
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a gap in the finite overlap support, the deficit is affine with
slope equal to minus the mass below the gap. Endpoints may be atoms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma deficit_antitone_argument (p : OverlapPath) : Antitone (deficit p) := by
  intro a b hab
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_mono (p.integrable_complement_max b) (p.integrable_complement_max a)
  intro s
  exact sub_le_sub_left (max_le_max_left (p s) hab) 1

lemma deficit_lower_of_ae_le (p : OverlapPath) {M r : ℝ}
    (hM : ∀ᵐ s ∂pathMeasure, p s ≤ M) (hr : r ≤ M) :
    1 - M ≤ deficit p r := by
  rw [deficit_eq_integral]
  calc
    1 - M = ∫ _s : ℝ, (1 - M) ∂pathMeasure := by simp
    _ ≤ ∫ s, 1 - max (p s) r ∂pathMeasure := by
      apply integral_mono_ae (integrable_const _) (p.integrable_complement_max r)
      filter_upwards [hM] with s hs
      exact sub_le_sub_left (max_le hs hr) 1

theorem deficit_affine_on_gap (p : OverlapPath) {a b : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    {r : ℝ} (hr : r ∈ Icc a b) :
    deficit p r = deficit p a - pathMeasure.real {s | p s ≤ a} * (r - a) := by
  let A : Set ℝ := {s | p s ≤ a}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  have he : (fun s => (1 - max (p s) r) - (1 - max (p s) a)) =ᵐ[pathMeasure]
      A.indicator (fun _ => a - r) := by
    filter_upwards [hgap] with s hs
    by_cases hsa : p s ≤ a
    · rw [max_eq_right (hsa.trans hr.1), max_eq_right hsa,
        indicator_of_mem (show s ∈ A from hsa)]
      ring
    · have hbs : b ≤ p s := hs.resolve_left hsa
      rw [max_eq_left (hr.2.trans hbs), max_eq_left (hr.1.trans (hr.2.trans hbs)),
        indicator_of_notMem (show s ∉ A from hsa)]
      ring
  have hi : deficit p r - deficit p a = pathMeasure.real A * (a - r) := by
    rw [deficit_eq_integral, deficit_eq_integral,
      ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max a),
      integral_congr_ae he, integral_indicator_const (a - r) hA]
    rfl
  change deficit p r = deficit p a - pathMeasure.real A * (r - a)
  linarith

end InvariantIsing

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

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalSpectralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precision assumptions in the rooted Gaussian calculation follow
from the actual upper spectral gap when the base matrix is diagonal. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma finiteInverse_antitone_pos {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    finiteInverse ρ eig hρ hsum x ≤ finiteInverse ρ eig hρ hsum y := by
  have hx := hy.trans_le hyx
  by_contra! h
  have hh := finiteResolvent_strictAnti (fun a => (hρ a).le) hsum
    (finiteInverse_spec ρ eig hρ hsum hy).1 h
  rw [(finiteInverse_spec ρ eig hρ hsum hx).2,
    (finiteInverse_spec ρ eig hρ hsum hy).2] at hh
  exact (not_lt_of_ge hyx) hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

lemma finite_overlap_ae_bounds {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    ∀ᵐ s ∂pathMeasure, q 0 ≤ p s ∧ p s ≤ q (Fin.last n) := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  exact ⟨hq (Fin.zero_le _), hq (Fin.le_last _)⟩

lemma finite_overlap_deficit_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) {r : ℝ} (hr : r ≤ q (Fin.last n)) :
    0 < deficit p r := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.2)
  exact (sub_pos.mpr htop).trans_le (deficit_lower_of_ae_le p hbound hr)

theorem finite_overlap_cumulative_mass {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (j : Fin (n + 1)) :
    pathMeasure.real {s | p s ≤ q j} = cut j.succ := by
  have he : {s | p s ≤ q j} =ᵐ[pathMeasure] Iic (cut j.succ) := by
    filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
    obtain ⟨k, hk⟩ := hs
    apply propext
    change p s ≤ q j ↔ s ≤ cut j.succ
    rw [hp k s hk]
    by_cases hkj : k ≤ j
    · exact iff_of_true (hq.monotone hkj)
        (hk.2.le.trans (hcut.monotone (by simpa using hkj)))
    · have hjk : j < k := lt_of_not_ge hkj
      have hindex : j.succ ≤ k.castSucc := by
        change j.val + 1 ≤ k.val
        exact hjk
      exact iff_of_false (not_le.mpr (hq hjk))
        (not_le.mpr ((hcut.monotone hindex).trans_lt hk.1))
  have hb : cut j.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hfirst]
      exact hcut.monotone (Fin.zero_le _)
    · rw [← hlast]
      exact hcut.monotone (Fin.le_last _)
  rw [measureReal_def, measure_congr he]
  change (IsingPerceptron.unitUniform (Iic (cut j.succ))).toReal = cut j.succ
  rw [IsingPerceptron.unitUniform_Iic hb, ENNReal.toReal_ofReal hb.1]

theorem finite_overlap_value_gap {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    ∀ᵐ s ∂pathMeasure, p s ≤ q i.castSucc ∨ q i.succ ≤ p s := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  by_cases hji : j ≤ i.castSucc
  · exact Or.inl (hq hji)
  · change ¬j.val ≤ i.val at hji
    exact Or.inr (hq (by change i.val + 1 ≤ j.val; omega))

/-- The actual finite-level deficit increment, including the atoms at
both neighboring overlap values. -/
theorem finite_overlap_deficit_increment {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) {r : ℝ} (hr : r ∈ Icc (q i.castSucc) (q i.succ)) :
    deficit p r = deficit p (q i.castSucc) -
      cut i.succ.castSucc * (r - q i.castSucc) := by
  rw [deficit_affine_on_gap p
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i) hr,
    finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal ordinary residual covariance is the remaining tail of
the field-density integral; it is not an additional cascade level. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma deficit_eq_one_sub_of_ae_le (p : OverlapPath) {r : ℝ}
    (hr : ∀ᵐ s ∂pathMeasure, p s ≤ r) : deficit p r = 1 - r := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] (fun _ => 0) :=
    hr.mono (fun _ hs => max_eq_right (sub_nonpos.mpr hs))
  rw [deficit, integral_congr_ae he, integral_zero, sub_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavityFiniteCovariance_diagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance rho lam hrho hsum g x =
      Matrix.diagonal (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹) := by
  unfold cavityFiniteCovariance
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [he, Matrix.diagonal_mul_diagonal]
  have hg (i : Fin d) : finiteInverse rho lam hrho hsum x - lam (g i) ≠ 0 :=
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))).ne'
  simp [hg]

lemma cavityFiniteCovariance_posDef (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  exact Matrix.PosDef.diagonal (fun i => inv_pos.mpr
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))))

lemma cavityFiniteCovariance_sub_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply sub_nonneg.mpr
  exact inv_anti₀ (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum
    (hy.trans_le hyx)).1 (g i)))
    (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)

lemma cavityFiniteCovariance_root_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x q₀ : ℝ} (hx : 0 < x) (hq₀ : 0 ≤ q₀) :
    (q₀ • ((1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) •
      (cavityFiniteCovariance rho lam hrho hsum g x *
        cavityFiniteCovariance rho lam hrho hsum g x))).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx, Matrix.diagonal_mul_diagonal]
  have hM : 0 < finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x) :=
    finiteSecondResolvent_pos (fun a => (hrho a).le) hsum
      (finiteInverse_spec rho lam hrho hsum hx).1
  exact ((Matrix.PosSemidef.diagonal (fun i => mul_self_nonneg _)).smul
    (one_div_nonneg.mpr hM.le)).smul hq₀

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

lemma cavityFiniteLevel_castSucc {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n i = i.castSucc := by
  apply Fin.ext
  exact min_eq_left i.isLt.le

lemma cavityFiniteLevel_succ {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n (i + 1) = i.succ := by
  apply Fin.ext
  exact min_eq_left i.isLt

lemma cavityFiniteDeficitPath_antitone {n : ℕ} (p : OverlapPath)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) : Antitone (cavityFiniteDeficitPath p q) :=
  (deficit_antitone_argument p).comp_monotone (hq.comp (cavityFiniteLevel_monotone n))

lemma cavityFiniteDeficitPath_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : ℕ) : 0 < cavityFiniteDeficitPath p q i :=
  finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop (hq (Fin.le_last _))

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariancePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hfirst hlast hq hp htop in
lemma cavityFiniteCovariancePath_posDef (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).PosDef :=
  cavityFiniteCovariance_posDef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFinitePriorBound
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total ordinary covariance of the finite labeled cavity prior is
bounded independently of the number of levels. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

variable {m d n : ℕ}

lemma cavityFiniteCovariance_eq_scalar_diagonal
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance ρ eig hρ hsum g x =
      Matrix.diagonal (fun j => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) x) := by
  rw [cavityFiniteCovariance_diagonal ρ eig hρ hsum g hx]
  congr 1
  funext j
  exact (cavityScalarResolvent_pos_eq ρ eig hρ hsum (g j) le_rfl hx).symm

lemma cavityFiniteCovariance_root_eq_diagonal
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) :
    (1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x)) •
      (cavityFiniteCovariance ρ eig hρ hsum g x *
        cavityFiniteCovariance ρ eig hρ hsum g x) =
    Matrix.diagonal (fun j => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x) *
        (finiteInverse ρ eig hρ hsum x - eig (g j))^2)) := by
  rw [cavityFiniteCovariance_diagonal ρ eig hρ hsum g hx, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_smul]
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, one_div, pow_two, mul_inv]

theorem cavity_finite_prior_covariance_bound
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    ‖(cavityFiniteRootCovariance ρ eig hρ hsum g p q +
      ∑ i : Fin n, cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q i) +
      cavityFiniteCovariancePath ρ eig hρ hsum g p q n‖ ≤ ∑ a, (ρ a)⁻¹ := by
  let T := fun x => Matrix.diagonal
    (fun j : Fin d => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) x)
  let x := fun i : Fin (n + 1) => deficit p (q i)
  let G := Matrix.diagonal (fun j : Fin d => 1 /
    (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum (x 0)) *
      (finiteInverse ρ eig hρ hsum (x 0) - eig (g j))^2))
  let C := ∑ a, (ρ a)⁻¹
  have hC (a : Fin m) : (ρ a)⁻¹ ≤ C :=
    Finset.single_le_sum (fun i _ => inv_nonneg.mpr (hρ i).le) (Finset.mem_univ a)
  have hCn : 0 ≤ C := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hρ i).le)
  have hx (i : Fin (n + 1)) : 0 < x i :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last i))
  have hT0 : T 0 = 0 := by simp [T, cavityScalarResolvent]
  have hT : ∀ u v, 0 ≤ u → u ≤ v → ‖T v - T u‖ ≤ C * (v - u) := by
    intro u v hu huv
    rw [show T v - T u = Matrix.diagonal
      (fun j => cavityScalarResolvent ρ eig hρ hsum (eig (g j)) v -
        cavityScalarResolvent ρ eig hρ hsum (eig (g j)) u) from
        Matrix.diagonal_sub _ _, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hCn (sub_nonneg.mpr huv))).mpr
    intro j
    exact (cavityScalarResolvent_lipschitz ρ eig hρ hsum (g j) le_rfl hu huv).trans
      (mul_le_mul_of_nonneg_right (hC (g j)) (sub_nonneg.mpr huv))
  have hG : ‖G‖ ≤ C := by
    rw [show G = Matrix.diagonal _ from rfl, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hCn).mpr
    intro j
    have h := cavityScalarResolvent_derivative_bound ρ eig hρ hsum (g j) le_rfl (hx 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (hC (g j))
  have hb (i : Fin n) : 0 < cut i.succ.castSucc := by
    rw [← hfirst]
    exact hcut (by change 0 < i.val + 1; omega)
  have hgap (i : Fin n) : x i.castSucc - x i.succ =
      cut i.succ.castSucc * (q i.succ - q i.castSucc) := by
    have h := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
      (r := q i.succ) ⟨hq.monotone (Fin.castSucc_le_succ i), le_rfl⟩
    dsimp only [x]
    linarith
  have hlastx : x (Fin.last n) = 1 - q (Fin.last n) :=
    deficit_eq_one_sub_of_ae_le p
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  have bound := cavity_covariance_partition_bound T G q x
    (fun i => cut i.succ.castSucc) hT0 hT hG hq.monotone
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 (fun i => (hx i).le) hb hgap hlastx
  have hpath (i : ℕ) : cavityFiniteCovariancePath ρ eig hρ hsum g p q i =
      T (x (cavityFiniteLevel n i)) :=
    cavityFiniteCovariance_eq_scalar_diagonal ρ eig hρ hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)
  have hroot : cavityFiniteRootCovariance ρ eig hρ hsum g p q = q 0 • G := by
    dsimp only [cavityFiniteRootCovariance, cavityFiniteCovariancePath]
    rw [show cavityFiniteDeficitPath p q 0 = x 0 by simp [cavityFiniteDeficitPath, x]]
    rw [cavityFiniteCovariance_root_eq_diagonal ρ eig hρ hsum g (hx 0)]
  have he (i : Fin n) : cut ⟨i.val + 1, by omega⟩ = cut i.succ.castSucc :=
    congrArg cut (Fin.ext rfl)
  rw [hroot]
  simpa only [cavityFiniteNoiseCovariance, hpath, cavityFiniteLevel_castSucc,
    cavityFiniteLevel_succ, cavityFiniteLevel_last, chainExponent_apply cut,
    Fin.isLt, he] using bound

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cavity model in a fixed measurable state space:
the tree, Gaussian root and forest are disorder; the leaf, ordinary
residual and Ising spin form the configuration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma measurable_cavityLabeledField {d : ℕ} (n : ℕ) :
    Measurable (fun p : CavityLabeledDisorder d n × LabeledLeaf n =>
      cavityLabeledField n p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro α
  change Measurable (fun ω : CavityLabeledDisorder d n =>
    ω.2.1 + ∑ i : Fin n, ω.2.2 (edgeAt n α i))
  exact measurable_snd.fst.add (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply (edgeAt n α i)).comp measurable_snd.snd)

lemma measurable_cavityLabeledEndpoint {d k : ℕ} (n : ℕ) :
    Measurable (cavityLabeledEndpoint (d := d) (k := k) n) := by
  have ha : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      (p.1, p.2.1.1)) := measurable_fst.prodMk measurable_snd.fst.fst
  have hf : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1) := (measurable_cavityLabeledField (d := d) n).comp ha
  have hr : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.1.2) := measurable_snd.fst.snd
  have hy : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1 + p.2.1.2) := hf.add hr
  have hs : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.2) := measurable_snd.snd
  exact hy.prodMk hs

lemma measurable_cavityLabeledPotential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) : Measurable (cavityLabeledPotential n K L C) := by
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityLogFactor K L C p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro ε
    exact (continuous_cavityLogFactor K L C ε).measurable
  exact hm.comp (measurable_cavityLabeledEndpoint n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPriorEndpointLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed labeled path, its common Gaussian root, and its independent
ordinary residual have the full unweighted endpoint covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_forest_leaf_sum_law {d : ℕ} (n : ℕ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (α : LabeledLeaf n) :
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))).map
      (fun g => ∑ i : Fin n, g (edgeAt n α i)) =
    multivariateGaussian 0 (∑ i : Fin n, S i) := by
  have hsel := cavity_selected_path_law n (cavityGaussianMarks S) α
  have hm : Measurable (fun z : Fin n → EuclideanSpace ℝ (Fin d) => ∑ i, z i) := by fun_prop
  have he := congrArg (fun μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) =>
    μ.map (fun z => ∑ i, z i)) hsel
  rw [Measure.map_map hm (by fun_prop)] at he
  exact he.trans (cavity_gaussian_sum_law (fun i : Fin n => S i) (fun i => hS i))

lemma cavity_root_forest_leaf_law {d : ℕ} (n : ℕ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hS : ∀ i, (S i).PosSemidef) (α : LabeledLeaf n) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).map
      (fun z => z.1 + ∑ i : Fin n, z.2 (edgeAt n α i)) =
    multivariateGaussian 0 (S₀ + ∑ i : Fin n, S i) := by
  let PG := Measure.infinitePi (fun v : ForestVertex n =>
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))
  let f := fun g : ForestVertex n → EuclideanSpace ℝ (Fin d) => ∑ i : Fin n, g (edgeAt n α i)
  have hf : Measurable f := by unfold f; fun_prop
  have he := Measure.map_prod_map (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀)
    PG measurable_id hf
  rw [Measure.map_id, cavity_forest_leaf_sum_law n S hS α] at he
  change ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod PG).map
    ((fun p => p.1 + p.2) ∘ Prod.map id f) = _
  rw [← Measure.map_map (by fun_prop) (measurable_id.prodMap hf), ← he]
  exact cavity_gaussian_add_law S₀ _ hS₀ (Matrix.posSemidef_sum Finset.univ (fun i _ => hS i))

lemma cavity_prior_endpoint_law {d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (α : LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)).map
      (fun z => (z.1.1 + ∑ i : Fin n, z.1.2 (edgeAt n α i)) + z.2) =
    multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  let PS := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  let f := fun z : EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d)) =>
    z.1 + ∑ i : Fin n, z.2 (edgeAt n α i)
  have hf : Measurable f := by unfold f; fun_prop
  have he := Measure.map_prod_map PS (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)
    hf measurable_id
  rw [Measure.map_id, cavity_root_forest_leaf_law n S₀ S hS₀ hS α] at he
  change (PS.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)).map
    ((fun p => p.1 + p.2) ∘ Prod.map f id) = _
  rw [← Measure.map_map (by fun_prop) (hf.prodMap measurable_id), ← he]
  exact cavity_gaussian_add_law _ R (hS₀.add (Matrix.posSemidef_sum Finset.univ (fun i _ => hS i))) hR

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledPriorLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full unweighted labeled cavity prior has a Gaussian endpoint law.
This controls its ordinary moments without assumptions on individual forests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma cavity_prior_endpoint_mixture_lintegral {d : ℕ} (n : ℕ)
    (T : LabeledTree n) (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sg, ∫⁻ α, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
      ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂ν
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n =>
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))) =
    ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  let PS := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  have hm : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) =>
      f ((p.1.1 + ∑ i : Fin n, p.1.2 (edgeAt n p.2.1 i)) + p.2.2)) := by
    have he := (measurable_cavityLabeledEndpoint (d := d) (k := 0) n).fst.comp
      (show Measurable (fun p :
        (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
          (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) =>
        ((T, p.1), (p.2, (fun _ : Fin 0 => false)))) from by fun_prop)
    exact hf.comp he
  have hinner : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × LabeledLeaf n =>
      ∫⁻ z, f ((p.1.1 + ∑ i : Fin n, p.1.2 (edgeAt n p.2 i)) + z)
        ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have hmp : Measurable (fun p :
        ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × LabeledLeaf n) ×
          EuclideanSpace ℝ (Fin d) =>
        f ((p.1.1.1 + ∑ i : Fin n, p.1.1.2 (edgeAt n p.1.2 i)) + p.2)) :=
      hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact hmp.lintegral_prod_right'
  rw [lintegral_lintegral_swap hinner.aemeasurable]
  have he (α : LabeledLeaf n) :
      (∫⁻ sg, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
        ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂PS) =
      ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
    have hmap := cavity_prior_endpoint_law n S₀ R S hS₀ hR hS α
    rw [← hmap, lintegral_map hf (by fun_prop)]
    have hmz : Measurable (fun z :
        (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
          EuclideanSpace ℝ (Fin d) =>
        f ((z.1.1 + ∑ i : Fin n, z.1.2 (edgeAt n α i)) + z.2)) :=
      hf.comp (by fun_prop)
    exact (lintegral_prod _ hmz.aemeasurable).symm
  calc
    _ = ∫⁻ _α, ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) ∂ν :=
      lintegral_congr (fun α => he α)
    _ = _ := by simp


theorem cavity_labeled_prior_endpoint_law {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((cavityLabeledDisorderLaw n b S₀ S) ⊗ₘ (cavityLabeledPriorKernel n R π)).map
      (fun p => (cavityLabeledEndpoint n p).1) =
    multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      f ((cavityLabeledEndpoint n p).1)) :=
    hf.comp (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst
  rw [lintegral_map hf (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst,
    Measure.lintegral_compProd hm]
  have hinner (T : LabeledTree n) :
      (∫⁻ sg, ∫⁻ x, f ((cavityLabeledEndpoint n ((T, sg), x)).1)
        ∂cavityLabeledPriorKernel n R π (T, sg)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))) =
      ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
    have hx (sg : EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) :
        Measurable (fun x : CavityLabeledState d k n =>
          f ((cavityLabeledEndpoint n ((T, sg), x)).1)) :=
      hm.comp (measurable_const.prodMk measurable_id)
    have he sg :
        (∫⁻ x, f ((cavityLabeledEndpoint n ((T, sg), x)).1)
          ∂cavityLabeledPriorKernel n R π (T, sg)) =
        ∫⁻ α, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
          ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂labeledLeafLaw n T := by
      rw [cavityLabeledPriorKernel_apply, lintegral_prod _ (hx sg).aemeasurable]
      simp only [cavityLabeledEndpoint, cavityLabeledField, lintegral_const,
        measure_univ, mul_one]
      rw [lintegral_prod _]
      exact (hf.comp ((measurable_cavityLabeledEndpoint (d := d) (k := 0) n).fst.comp
        (show Measurable (fun p : LabeledLeaf n × EuclideanSpace ℝ (Fin d) =>
          ((T, sg), (p, (fun _ : Fin 0 => false)))) from by fun_prop))).aemeasurable
    simp_rw [he]
    exact cavity_prior_endpoint_mixture_lintegral n T (labeledLeafLaw n T)
      S₀ R S hS₀ hR hS f hf
  unfold cavityLabeledDisorderLaw
  rw [lintegral_prod _]
  · simp_rw [hinner]
    simp
  · exact (hm.lintegral_kernel_prod_right' (κ := cavityLabeledPriorKernel n R π)).aemeasurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary fourth moments of the actual labeled prior follow from
its Gaussian endpoint law, uniformly in the number of cascade levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_fourth_moment_bound {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    {M : ℝ} (hSM : ‖S‖ ≤ M) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖^4) (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), ‖y‖^4 ∂multivariateGaussian 0 S) ≤
      cavityGaussianLinearMomentBound d 4 0 M := by
  have hi : Integrable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖^4)
      (multivariateGaussian 0 S) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)
        4 (by norm_num)).integrable_norm_pow'
  have he := cavity_gaussian_linear_envelope S hS hSM (le_refl (0 : ℝ)) 4
  refine ⟨hi, (integral_mono hi he.1 fun y => ?_).trans he.2⟩
  have hb := (cavity_linear_envelope_bounds 4 (le_refl (0 : ℝ)) (norm_nonneg y)
    (show |(0 : ℝ)| ≤ 0 * (1 + ‖y‖) by simp)).2.2.2.1
  simpa only [Real.exp_zero, mul_one] using hb

theorem cavity_prior_fourth_moment_of_gaussian_law {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (E : Ω × X → EuclideanSpace ℝ (Fin d)) (hE : Measurable E)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (P ⊗ₘ κ).map E = multivariateGaussian 0 S) {M : ℝ} (hM : ‖S‖ ≤ M) :
    (∀ᵐ ω ∂P, Integrable (fun x => ‖E (ω, x)‖^4) (κ ω)) ∧
    Integrable (fun ω => ∫ x, ‖E (ω, x)‖^4 ∂κ ω) P ∧
    (∫ ω, ∫ x, ‖E (ω, x)‖^4 ∂κ ω ∂P) ≤ cavityGaussianLinearMomentBound d 4 0 M := by
  have hG := cavity_gaussian_fourth_moment_bound S hS hM
  have hi : Integrable (fun p => ‖E p‖^4) (P ⊗ₘ κ) := by
    have ht := hG.1
    rw [← hLaw] at ht
    exact (integrable_map_measure (by fun_prop) hE.aemeasurable).mp ht
  have hp := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  refine ⟨hp.1, ?_, ?_⟩
  · simpa only [norm_pow, norm_norm] using hp.2
  · have heq : (∫ ω, ∫ x, ‖E (ω, x)‖^4 ∂κ ω ∂P) =
        ∫ y : EuclideanSpace ℝ (Fin d), ‖y‖^4 ∂multivariateGaussian 0 S := by
      rw [← Measure.integral_compProd hi, ← hLaw, integral_map hE.aemeasurable (by fun_prop)]
    exact heq.le.trans hG.2

theorem cavity_labeled_prior_fourth_moment {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] {M : ℝ}
    (hM : ‖(S₀ + ∑ i : Fin n, S i) + R‖ ≤ M) :
    (∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω, x)).1‖^4)
        (cavityLabeledPriorKernel n R π ω)) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω) (cavityLabeledDisorderLaw n b S₀ S) ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω ∂cavityLabeledDisorderLaw n b S₀ S) ≤
        cavityGaussianLinearMomentBound d 4 0 M := by
  have hpos : ((S₀ + ∑ i : Fin n, S i) + R).PosSemidef :=
    (hS₀.add (Matrix.posSemidef_sum (Finset.univ : Finset (Fin n)) fun i _ => hS i)).add hR
  exact cavity_prior_fourth_moment_of_gaussian_law
    (Ω := CavityLabeledDisorder d n) (X := CavityLabeledState d k n) (d := d)
    (cavityLabeledDisorderLaw n b S₀ S) (cavityLabeledPriorKernel n R π)
    (fun p => (cavityLabeledEndpoint n p).1) (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst
    ((S₀ + ∑ i : Fin n, S i) + R)
    hpos
    (cavity_labeled_prior_endpoint_law n b S₀ R S hS₀ hR hS π) hM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFinitePriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary fourth moments for the actual finite spectral cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_prior_fourth_moment {m d n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let P := cavityLabeledDisorderLaw n (chainExponent cut)
      (cavityFiniteRootCovariance ρ eig hρ hsum g p q)
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q)
    (∀ᵐ ω ∂P, Integrable (fun x => ‖(cavityLabeledEndpoint n (ω, x)).1‖^4)
      (cavityLabeledPriorKernel n R π ω)) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω) P ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω ∂P) ≤
        cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹) := by
  intro R P
  have hroot : (cavityFiniteRootCovariance ρ eig hρ hsum g p q).PosSemidef :=
    cavityFiniteCovariance_root_posSemidef ρ eig hρ hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop 0)
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  exact cavity_labeled_prior_fourth_moment n (chainExponent cut)
    (cavityFiniteRootCovariance ρ eig hρ hsum g p q) R
    (cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q)
    hroot
    (cavityFiniteCovariancePath_posDef ρ eig hρ hsum g p cut hfirst hlast q hq hp htop n).posSemidef
    (cavityFiniteNoiseCovariance_posSemidef ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop)
    π (cavity_finite_prior_covariance_bound ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma cavityUniformLevel_on_cell (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityUniformLevel n s = i := by
  apply Fin.ext
  change min n ⌊(n + 1 : ℕ) * s⌋₊ = i.val
  rw [floor_on_uniformCell n i hs, min_eq_right (Nat.le_of_lt_succ i.isLt)]

lemma cavityStrictUniformPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityStrictUniformPath p n s = cavityStrictUniformLevels p n i := by
  change cavityStrictUniformLevels p n (cavityUniformLevel n s) = _
  rw [cavityUniformLevel_on_cell n i hs]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCapIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and separate-expectation cap errors for bounded replica
tests under the full cavity Gibbs tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_replicaMean_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    {B : ℝ} (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    Integrable (fun ω => cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
      (fun σ => F (ω,σ))) P := by
  have hm : Measurable (fun ω => cavityWeightedReplicaMean (ν ω)
      (fun x => Real.exp (H (ω,x))) (fun σ => F (ω,σ))) :=
    (measurable_cavityWeightNumerator ν hν _ hH.exp F hF).div
      ((measurable_cavityWeightNormalizer ν hν _ hH.exp).pow_const r)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  filter_upwards [he] with ω hω
  rw [cavityWeightedReplicaMean_exp (ν ω) (fun x => H (ω,x)) hω]
  let := isProbabilityMeasure_tilted hω
  have hb := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => (ν ω).tilted (fun x => H (ω,x))))
    (f := fun σ => F (ω,σ)) (C := B)
    (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hFb ω σ))
  simpa only [probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial tightness from the second moment of the full tilted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma cavity_square_tail_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (R : X → ℝ)
    (hi : Integrable (fun x => R x ^ 2) ν) {A : ℝ} (hA : 0 < A) :
    ν.real {x | A < |R x|} ≤ (∫ x, R x ^ 2 ∂ν) / A ^ 2 := by
  have hs : {x | A < |R x|} ⊆ {x | A ^ 2 ≤ R x ^ 2} := by
    intro x hx
    change A ^ 2 ≤ R x ^ 2
    have h := pow_le_pow_left₀ hA.le (le_of_lt hx) 2
    simpa only [sq_abs] using h
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all ν fun x => sq_nonneg (R x)) hi (A ^ 2)
  have ht := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) hs) (sq_nonneg A)
  nlinarith

theorem cavity_random_tilted_square_tail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H) (hR : Measurable R)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^2)
      ((ν ω).tilted (fun x => H (ω,x))))
    (hmi : Integrable (fun ω => ∫ x, R (ω,x)^2
      ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {M A : ℝ} (hA : 0 < A)
    (hM : (∫ ω, ∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ M) :
    (∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real {x | A < |R (ω,x)|} ∂P) ≤
      M / A^2 := by
  classical
  let Z := fun ω => ∫ x, (if A < |R (ω,x)| then (1 : ℝ) else 0)
    ∂(ν ω).tilted (fun x => H (ω,x))
  have hs : MeasurableSet {p : Ω × X | A < |R p|} :=
    measurableSet_lt measurable_const hR.abs
  have hZ ω : Z ω = ((ν ω).tilted (fun x => H (ω,x))).real {x | A < |R (ω,x)|} := by
    change (∫ x, {x | A < |R (ω,x)|}.indicator (fun _ => (1 : ℝ)) x
      ∂(ν ω).tilted (fun x => H (ω,x))) = _
    exact integral_indicator_one (hs.preimage measurable_prodMk_left)
  have hmZ : Measurable Z := measurable_random_tilted_integral hν hH
    (Measurable.ite hs measurable_const measurable_const)
  have hiZ : Integrable Z P := Integrable.of_bound hmZ.aestronglyMeasurable 1 (by
    filter_upwards [he] with ω hω
    let := isProbabilityMeasure_tilted hω
    have hb := norm_integral_le_of_norm_le_const (μ := (ν ω).tilted (fun x => H (ω,x)))
      (f := fun x => if A < |R (ω,x)| then (1 : ℝ) else 0) (C := 1)
      (ae_of_all _ fun x => by split_ifs <;> norm_num)
    simpa only [probReal_univ, mul_one] using hb)
  have hb : ∀ᵐ ω ∂P, Z ω ≤
      (∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) / A^2 := by
    filter_upwards [he, hi] with ω heω hiω
    let := isProbabilityMeasure_tilted heω
    rw [hZ]
    exact cavity_square_tail_le _ _ hiω hA
  have hh := integral_mono_ae hiZ (hmi.div_const (A^2)) hb
  simp only [hZ, integral_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hM (sq_nonneg A))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteTiltedTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite spectral cavity laws are uniformly tight, including
when their strict overlap discretization has increasing depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_labeled_square_tail {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] {A : ℝ} (hA : 0 < A) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    (∫ ω, ((cavityLabeledPriorKernel n R π ω).tilted
      (fun x => cavityLabeledPotential n K L C (ω,x))).real
        {x | A < ‖(cavityLabeledEndpoint n (ω,x)).1‖} ∂P) ≤
      cavityGaussianLinearMomentBound d 2 (cavityMatrixMass L + cavityMatrixMass C)
        (ρ a)⁻¹ / A^2 := by
  intro K R S S₀ P
  have h := cavity_finite_labeled_moment ρ eig hρ hsum B hB g a ha
    p cut hcut hfirst hlast q hq hp htop L C π 2
  have ht := cavity_random_tilted_square_tail P (cavityLabeledPriorKernel n R π)
    (cavityLabeledPriorKernel n R π).measurable (cavityLabeledPotential n K L C)
    (fun z => ‖(cavityLabeledEndpoint n z).1‖)
    (measurable_cavityLabeledPotential n K L C)
    ((measurable_cavityLabeledEndpoint n).fst.norm)
    (h.1.mono fun _ hx => hx.1) (h.1.mono fun _ hx => hx.2) h.2.1 hA h.2.2
  simpa only [abs_norm] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModelNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and the literal product-prior formula for the finite
cavity numerator used in extra-replica normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityLabeledReplicaTest {m r d k n : ℕ}
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledReplicaTest (d := d) B F) := by
  have hl : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).1.1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).fst.fst
  have hs : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).2) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).snd
  exact F.continuous.measurable.comp (((measurable_of_countable B).comp hl).prodMk hs)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPriorFourthTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prior tails required for removing the spatially restricted denominator
floor. The available physical and finite-cascade fourth moments suffice. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_fourth_tail_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (R : X → ℝ)
    (hi : Integrable (fun x => R x^4) ν) {a : ℝ} (ha : 0 < a) :
    ν.real {x | a < |R x|} ≤ (∫ x, R x^4 ∂ν) / a^4 := by
  have hs : {x | a < |R x|} ⊆ {x | a^4 ≤ R x^4} := by
    intro x hx
    change a^4 ≤ R x^4
    simpa only [pow_abs, abs_of_nonneg (by positivity : 0 ≤ R x^4)] using
      pow_le_pow_left₀ ha.le hx.le 4
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all ν fun x => by positivity : ∀ᵐ x ∂ν, 0 ≤ R x^4) hi (a^4)
  have ht := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) hs) (pow_nonneg ha.le 4)
  nlinarith

lemma measurable_cavityPriorTail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (R : Ω × X → ℝ) (hR : Measurable R) (a : ℝ) :
    Measurable (fun ω => (ν ω).real {x | a < |R (ω,x)|}) := by
  have hs : MeasurableSet {p : Ω × X | a < |R p|} :=
    measurableSet_lt measurable_const hR.abs
  have he ω : (∫ x, (if a < |R (ω,x)| then (1:ℝ) else 0) ∂ν ω) =
      (ν ω).real {x | a < |R (ω,x)|} := by
    have hsω : MeasurableSet {x | a < |R (ω,x)|} := hs.preimage measurable_prodMk_left
    simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
      (integral_indicator_one (μ := ν ω) hsω)
  have hm := measurable_cavityWeightNormalizer ν hν
    (fun p : Ω × X => if a < |R p| then (1:ℝ) else 0)
    (Measurable.ite hs measurable_const measurable_const)
  simpa only [cavityWeightNormalizer, he] using hm

theorem cavity_random_prior_fourth_tail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (R : Ω × X → ℝ) (hR : Measurable R)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω,x)^4 ∂ν ω) P)
    {M a : ℝ} (ha : 0 < a)
    (hM : (∫ ω, ∫ x, R (ω,x)^4 ∂ν ω ∂P) ≤ M) :
    (∫ ω, (ν ω).real {x | a < |R (ω,x)|} ∂P) ≤ M/a^4 := by
  have hiT : Integrable (fun ω => (ν ω).real {x | a < |R (ω,x)|}) P :=
    integrable_of_measurable_abs_le (measurable_cavityPriorTail ν hν R hR a)
      (c := 1) (fun _ => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hh := integral_mono_ae hiT (hmi.div_const (a^4))
    (hi.mono fun ω hω => cavity_fourth_tail_le (ν ω) (fun x => R (ω,x)) hω ha)
  rw [integral_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hM (pow_nonneg ha.le 4))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting an exponential Gibbs weight commutes with normalizing its
full tilt, including when the restricted normalizer is zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityWeightedReplicaMean_mul_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (fun x => w x * Real.exp (H x)) F =
      cavityWeightedReplicaMean (ν.tilted H) w F := by
  have hn : cavityWeightNumerator (ν.tilted H) w F =
      cavityWeightNumerator ν (fun x => w x * Real.exp (H x)) F /
        (∫ x, Real.exp (H x) ∂ν)^r := by
    unfold cavityWeightNumerator
    rw [← cavity_continuous_replica_tilt ν H he r, integral_tilted_eq_div,
      cavity_exp_replica_partition]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with σ
    rw [Real.exp_sum, Finset.prod_mul_distrib]
    ring
  have hz : cavityWeightNormalizer (ν.tilted H) w =
      cavityWeightNormalizer ν (fun x => w x * Real.exp (H x)) /
        (∫ x, Real.exp (H x) ∂ν) := by
    unfold cavityWeightNormalizer
    rw [integral_tilted_eq_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  rw [cavityWeightedReplicaMean, cavityWeightedReplicaMean, hn, hz, div_pow,
    div_div_div_cancel_right₀ (pow_ne_zero r (integral_exp_pos he).ne')]

lemma cavityWeightedReplicaMean_indicator_exp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (s : Set X)
    {r : ℕ} (F : (Fin r → X) → ℝ) :
    cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F =
      cavityWeightedReplicaMean (ν.tilted H) (s.indicator (fun _ => 1)) F := by
  convert cavityWeightedReplicaMean_mul_exp ν H he (s.indicator (fun _ => 1)) F using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem cavity_restricted_replica_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (s : Set X) (hs : MeasurableSet s)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F -
      cavityWeightedReplicaMean ν (fun x => Real.exp (H x)) F| ≤
        2 * B * r * (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted he
  rw [cavityWeightedReplicaMean_indicator_exp ν H he,
    cavityWeightedReplicaMean_exp ν H he]
  have hb x : s.indicator (fun _ => (1 : ℝ)) x ∈ Icc 0 1 := by
    by_cases hx : x ∈ s <;> simp [hx]
  have hh := cavity_soft_cutoff_replica_error (ν.tilted H)
    (s.indicator (fun _ => 1)) (measurable_const.indicator hs) hb F hF hB hFb
  have hz : cavityWeightNormalizer (ν.tilted H) (s.indicator (fun _ => (1 : ℝ))) =
      (ν.tilted H).real s := integral_indicator_one hs
  simpa only [hz, measureReal_compl hs, probReal_univ] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTailIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail probabilities as measurable disorder averages and as the
one-coordinate marginal of the physical two-replica Gibbs test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_random_tilted_tail_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1}) :
    Integrable (fun ω => ((ν ω).tilted (fun x => H (ω,x))).real (s ω)) P := by
  classical
  let Z := fun ω => ∫ x, (s ω).indicator (fun _ => (1 : ℝ)) x
    ∂(ν ω).tilted (fun x => H (ω,x))
  have hZ ω : Z ω = ((ν ω).tilted (fun x => H (ω,x))).real (s ω) :=
    integral_indicator_one (hs.preimage measurable_prodMk_left)
  have hm : Measurable Z := measurable_random_tilted_integral hν hH
    (Measurable.ite hs measurable_const measurable_const)
  have hi : Integrable Z P := Integrable.of_bound hm.aestronglyMeasurable 1 (by
    apply ae_of_all
    intro ω
    rw [hZ, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one)
  exact hi.congr (ae_of_all _ hZ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatially restricted Gibbs tests: separate quantitative control of
the denominator floor and of the discarded full-Gibbs mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_restricted_regularization_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-A) / 2) + 4 * B * ∫ ω, (ν ω).real (s ω)ᶜ ∂P := by
  classical
  let w := fun p : Ω × X => if p.2 ∈ s p.1 then Real.exp (H p) else 0
  have hw : Measurable w := Measurable.ite hs hH.exp measurable_const
  have hwb ω x : w (ω,x) ∈ Icc 0 (Real.exp A) := by
    by_cases hx : x ∈ s ω
    · simp only [w,hx,ite_true, if_true]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound ω x hx))⟩
    · simp only [w,hx,ite_false, if_false]
      exact ⟨le_rfl,(Real.exp_pos _).le⟩
  let t := fun ω => (ν ω).real (s ω)ᶜ
  have hsm ω : MeasurableSet (s ω) := hs.preimage measurable_prodMk_left
  have htval ω : (∫ x, (if x ∉ s ω then (1 : ℝ) else 0) ∂ν ω) = t ω := by
    simpa only [Set.indicator, Set.mem_compl_iff, Pi.one_apply] using
      (integral_indicator_one (μ := ν ω) (hsm ω).compl)
  have ht : Measurable t := by
    have hh := measurable_cavityWeightNormalizer ν hν
      (fun p : Ω × X => if p.2 ∉ s p.1 then (1 : ℝ) else 0)
      (Measurable.ite hs.compl measurable_const measurable_const)
    simpa only [cavityWeightNormalizer, htval] using hh
  have hti : Integrable t P := integrable_of_measurable_abs_le ht (c := 1)
    (fun ω => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hlow ω (hω : t ω ≤ 1/2) :
      Real.exp (-A) / 2 ≤ cavityWeightNormalizer (ν ω) (fun x => w (ω,x)) := by
    exact cavity_cutoff_normalizer_half (ν ω) (s ω) (hsm ω)
      (fun x => Real.exp (H (ω,x))) (hH.comp measurable_prodMk_left).exp
      (Real.exp_pos _).le (fun x hx =>
        ⟨Real.exp_le_exp.mpr (abs_le.mp (hbound ω x hx)).1,
          Real.exp_le_exp.mpr (abs_le.mp (hbound ω x hx)).2⟩) hω
  exact cavity_bounded_regularization_mean_error P ν hν w hw F hF t ht hti
    (fun _ => measureReal_nonneg) (Real.exp_pos A).le hB hδ (by positivity) hwb hFb hlow

theorem cavity_restricted_replica_expectation_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B : ℝ} (hB : 0 ≤ B) (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A)
    (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityWeightedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real (s ω)ᶜ ∂P := by
  classical
  let w := fun p : Ω × X => if p.2 ∈ s p.1 then Real.exp (H p) else 0
  have hw : Measurable w := Measurable.ite hs hH.exp measurable_const
  have hwb ω x : w (ω,x) ∈ Icc 0 (Real.exp A) := by
    by_cases hx : x ∈ s ω
    · simp only [w,hx,ite_true, if_true]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound ω x hx))⟩
    · simp only [w,hx,ite_false, if_false]
      exact ⟨le_rfl,(Real.exp_pos _).le⟩
  have hm := measurable_cavityRegularizedReplicaMean ν hν w hw F hF 0
  have hb ω : |cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
      (fun σ => F (ω,σ))| ≤ B := by
    have hh := cavityRegularizedReplicaMean_abs_le (ν ω) (fun x => w (ω,x))
      (hw.comp measurable_prodMk_left) (fun σ => F (ω,σ))
      (hF.comp measurable_prodMk_left) (Real.exp_pos A).le hB (show (0:ℝ) ≤ 0 from le_rfl)
      (hwb ω) (hFb ω)
    change |cavityWeightNumerator (ν ω) (fun x => w (ω,x)) (fun σ => F (ω,σ)) /
      cavityWeightNormalizer (ν ω) (fun x => w (ω,x)) ^ r| ≤ B
    simpa only [cavityRegularizedReplicaMean, add_zero] using hh
  have hiW : Integrable (fun ω => cavityWeightedReplicaMean (ν ω)
      (fun x => w (ω,x)) (fun σ => F (ω,σ))) P := by
    apply integrable_of_measurable_abs_le _ hb
    simpa only [cavityRegularizedReplicaMean, add_zero, cavityWeightedReplicaMean] using hm
  have hiF := cavity_exp_replicaMean_integrable P ν hν H hH F hF he hFb
  have hiT := cavity_random_tilted_tail_integrable P ν hν H hH
    (fun ω => (s ω)ᶜ) hs.compl
  change |(∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
    (fun σ => F (ω,σ)) ∂P) - _| ≤ _
  rw [← integral_sub hiW hiF]
  apply abs_integral_le_integral_abs.trans
  refine (integral_mono_ae (hiW.sub hiF).abs (hiT.const_mul (2*B*r)) ?_).trans_eq ?_
  · filter_upwards [he] with ω hω
    exact cavity_restricted_replica_error (ν ω) _ hω (s ω)
      (hs.preimage measurable_prodMk_left) _ (hF.comp measurable_prodMk_left) hB (hFb ω)
  · rw [integral_const_mul]

theorem cavity_restricted_regularized_full_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-A) / 2) + 4 * B * (∫ ω, (ν ω).real (s ω)ᶜ ∂P) +
        2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real (s ω)ᶜ ∂P := by
  have h₁ := cavity_restricted_regularization_error P ν hν H hH s hs F hF hB hδ hbound hFb
  have h₂ := cavity_restricted_replica_expectation_error P ν hν H hH he s hs F hF hB hbound hFb
  exact (abs_sub_le _ (∫ ω, cavityWeightedReplicaMean (ν ω)
    ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P) _).trans
      (add_le_add h₁ h₂)

theorem cavity_radial_restricted_regularized_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H) (hR : Measurable R)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {D B a δ : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hg : ∀ ω x, |H (ω,x)| ≤ D * (1 + R (ω,x)^2))
    (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ({x | |R (ω,x)| ≤ a}.indicator (fun x => Real.exp (H (ω,x))))
        (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-D * (1+a^2)) / 2) +
        4 * B * (∫ ω, (ν ω).real {x | a < |R (ω,x)|} ∂P) +
        2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real
          {x | a < |R (ω,x)|} ∂P := by
  have hg' ω x (hx : x ∈ {x | |R (ω,x)| ≤ a}) : |H (ω,x)| ≤ D*(1+a^2) := by
    have hp := pow_le_pow_left₀ (abs_nonneg (R (ω,x))) hx 2
    rw [sq_abs] at hp
    exact (hg ω x).trans (mul_le_mul_of_nonneg_left (by linarith :
      1 + R (ω,x)^2 ≤ 1+a^2) hD)
  have hh := cavity_restricted_regularized_full_error P ν hν H hH he
    (fun ω => {x | |R (ω,x)| ≤ a}) (measurableSet_le hR.abs measurable_const)
    F hF hB hδ hg' hFb
  simpa only [Set.compl_ofPred, not_le, neg_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactorIndicator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRestrictedError
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff-removal errors for the finite spectral cavity law, controlled
by uniform prior and full-Gibbs moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix Matrix.Norms.L2Operator BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_error {m d N n k r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B₀ : Matrix (Fin (m*N)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (O : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (T : ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ) :
    let K := B₀.transpose * cavityRepeatedSpectrum (n := N) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n) n
    let Q := cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    cavityFactorSize K L C * (1+B^2) ≤ T →
    |(∫ ω, cavityRegularizedReplicaMean (cavityLabeledPriorKernel n R π ω)
        (fun x => cavityLabeledRestrictedWeight n K L C T B (ω,x))
        (fun σ => cavityLabeledReplicaTest O F (ω,σ)) δ ∂Q) -
      ∫ ω, cavityWeightedReplicaMean (cavityLabeledPriorKernel n R π ω)
        (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (fun σ => cavityLabeledReplicaTest O F (ω,σ)) ∂Q| ≤
      ‖F‖ * r * δ / (Real.exp (-cavityFactorSize K L C * (1+B^2)) / 2) +
        4 * ‖F‖ * (cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹) / B^4) +
        2 * ‖F‖ * r * (cavityGaussianLinearMomentBound d 2
          (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ / B^2) := by
  intro K R Q hT
  let η := cavityLabeledPriorKernel n R π
  let H := cavityLabeledPotential n K L C
  let Z := fun z : CavityLabeledDisorder d n × CavityLabeledState d k n =>
    ‖(cavityLabeledEndpoint n z).1‖
  let V := cavityLabeledReplicaTest (d := d) O F
  have hH : Measurable H := measurable_cavityLabeledPotential n K L C
  have hZ : Measurable Z := (measurable_cavityLabeledEndpoint n).fst.norm
  have hV : Measurable V := measurable_cavityLabeledReplicaTest O F
  have hm := cavity_finite_labeled_moment ρ eig hρ hsum B₀ hB₀ g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π 2
  have hp := cavity_finite_prior_fourth_moment ρ eig hρ hsum g
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 π
  have ht := cavity_random_prior_fourth_tail Q (fun ω => η ω) η.measurable Z hZ
    hp.1 hp.2.1 hB hp.2.2
  have hsq := cavity_finite_labeled_square_tail ρ eig hρ hsum B₀ hB₀ g a ha
    (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π hB
  have he := cavity_radial_restricted_regularized_error Q (fun ω => η ω) η.measurable
    H Z hH hZ (hm.1.mono fun _ h => h.1) V hV (a := B)
    (cavityFactorSize_nonneg K L C) (norm_nonneg F) hδ
    (fun ω x => cavity_logFactor_growth K L C _ _)
    (fun ω σ => (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _))
  have hw ω : {x | |Z (ω,x)| ≤ B}.indicator (fun x => Real.exp (H (ω,x))) =
      fun x => cavityLabeledRestrictedWeight n K L C T B (ω,x) := by
    funext x
    simpa only [Z,abs_norm,H,cavityLabeledPotential,cavityLabeledRestrictedWeight,
      Function.comp_apply] using
      (cavityRestrictedFactor_eq_indicator K L C T hB.le hT
        (fun x => (cavityLabeledEndpoint n (ω,x)).1)
        (fun x => (cavityLabeledEndpoint n (ω,x)).2) x).symm
  rw [show -cavityFactorSize K L C * (1+B^2) = -(cavityFactorSize K L C * (1+B^2)) by ring] at he
  simp only [hw] at he
  have hsq' : (∫ ω, ((η ω).tilted (fun x => H (ω,x))).real
      {x | B < |Z (ω,x)|} ∂Q) ≤ cavityGaussianLinearMomentBound d 2
        (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ / B^2 := by
    simpa only [Z,abs_norm,H,η,R,Q,K] using hsq
  have hout := he.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 4*‖F‖)))
    (mul_le_mul_of_nonneg_left hsq' (by positivity : 0 ≤ 2*‖F‖*r)))
  simpa only [η,H,V,neg_mul] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedHaarMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform ordinary fourth moments for the actual selected Haar axes.
These are the physical-side moments used to remove the normalizer floor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators RealInnerProductSpace

namespace InvariantIsing

lemma cavity_sphere_fourth_moment_of_norm {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    {C : ℝ} (hv : ‖v‖^2 ≤ C * n) :
    (∫ U, |⟪v, matrixRotation U u⟫|^4 ∂μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hr : ‖v‖^2 / (n : ℝ) ≤ C := (div_le_iff₀ hn').mpr hv
  have h := cavity_sphere_even_moment_bound hn μ v u hu 2
  norm_num only [Nat.reduceMul] at h
  calc
    _ ≤ cavityGaussianAbsMoment 4 * ‖v‖^4 / (n : ℝ)^2 := h
    _ = cavityGaussianAbsMoment 4 * (‖v‖^2 / (n : ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hn'.le) hr 2)
      (cavityGaussianAbsMoment_nonneg 4)

lemma cavity_selected_site_inner {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (U : (a : Fin m) → Orthogonal (N a)) (j : Fin d) :
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) () j =
      ⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫ := by
  simp only [cavitySelectedSiteProjection, PiLp.toLp_apply, cavityGroupHaarFrames,
    Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    matrixRotation_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem cavity_selected_haar_fourth_moment {m q d : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ}
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a) :
    (∫ U, ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  let Y := fun U : (a : Fin m) → Orthogonal (N a) =>
    cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hu (j : Fin d) : ‖(WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ = 1 :=
    (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
  have hcoord (U) (j : Fin d) : |Y U j| ≤ ‖(WithLp.toLp 2 (v (e j).1) :
      EuclideanSpace ℝ (Fin (N (e j).1)))‖ := by
    dsimp only [Y]
    rw [cavity_selected_site_inner]
    simpa only [(matrixRotation _).norm_map, hu j, mul_one] using
      abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
        (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
  have hm (j : Fin d) : Measurable (fun U : Orthogonal (N (e j).1) =>
      |⟪(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1))),
        matrixRotation U (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2))⟫|^4) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      matrixRotation_apply]
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul_const
    apply Finset.measurable_sum
    intro l _
    exact (((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      measurable_subtype_coe)).mul_const _)
  have hcm (j : Fin d) : Measurable (fun U => |Y U j|^4) := by
    simpa only [Y, cavity_selected_site_inner, Function.comp_def] using
      (hm j).comp (measurable_pi_apply (e j).1)
  have hci (j : Fin d) : Integrable (fun U => |Y U j|^4) (Measure.pi μ) := by
    apply Integrable.of_bound (hcm j).aestronglyMeasurable
      (‖(WithLp.toLp 2 (v (e j).1) : EuclideanSpace ℝ (Fin (N (e j).1)))‖^4)
    apply ae_of_all
    intro U
    change ‖|Y U j|^4‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hcoord U j) 4
  have hb (j : Fin d) : (∫ U, |Y U j|^4 ∂Measure.pi μ) ≤ cavityGaussianAbsMoment 4 * C^2 := by
    have h := cavity_sphere_fourth_moment_of_norm (hN (e j).1) (μ (e j).1)
      (WithLp.toLp 2 (v (e j).1)) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)) (hu j) (hv (e j).1)
    have he := (measurePreserving_eval μ (e j).1).hasLaw.integral_comp (hm j).aestronglyMeasurable
    simpa only [Y, cavity_selected_site_inner, Function.comp_def, Function.eval] using he.le.trans h
  have hpoint (U) : ‖Y U‖^4 ≤ (d : ℝ) * ∑ j, |Y U j|^4 := by
    have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
      (f := fun j : Fin d => (Y U j)^2) (fun _ _ => sq_nonneg _) 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, EuclideanSpace.real_norm_sq_eq]
    simpa only [Nat.reduceAdd, pow_one, Finset.card_univ, Fintype.card_fin, pow_mul,
      sq_abs] using h
  calc
    _ ≤ ∫ U, (d : ℝ) * ∑ j, |Y U j|^4 ∂Measure.pi μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun U => pow_nonneg (norm_nonneg _) _))
        ((integrable_finsetSum _ fun j _ => hci j).const_mul d) (ae_of_all _ hpoint)
    _ = (d : ℝ) * ∑ j, ∫ U, |Y U j|^4 ∂Measure.pi μ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ => hci j]
    _ ≤ (d : ℝ) * ∑ _j : Fin d, cavityGaussianAbsMoment 4 * C^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hb j) (Nat.cast_nonneg d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
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

lemma cavity_selected_site_fourth_bound {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (U : (a : Fin m) → Orthogonal (N a)) :
    ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ≤ ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2 := by
  let Y := cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hb (j : Fin d) : (Y j)^2 ≤ C * ∑ a, (N a : ℝ) := by
    have hu := (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
    have hi := abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
      (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
    rw [(matrixRotation _).norm_map, hu, mul_one] at hi
    have hsq : (Y j)^2 ≤ ‖(WithLp.toLp 2 (v (e j).1) :
        EuclideanSpace ℝ (Fin (N (e j).1)))‖^2 := by
      simpa only [Y, cavity_selected_site_inner, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) hi 2
    exact (hsq.trans (hv _)).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => Nat.cast_nonneg (N a)) (Finset.mem_univ (e j).1)) hC)
  have hs : ‖Y‖^2 ≤ (d : ℝ) * (C * ∑ a, (N a : ℝ)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  simpa only [← pow_mul, Nat.reduceMul, Y] using pow_le_pow_left₀ (sq_nonneg ‖Y‖) hs 2

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

theorem cavity_haar_prior_fourth_moment {m q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hvM : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ ω x a, ‖(WithLp.toLp 2 (v ω a x) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let R := fun (p : Ω × ((a : Fin m) → Orthogonal (N a))) (x : X × Spin k) =>
      ‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^4
    (∀ p, Integrable (R p) ((ν p.1).prod π)) ∧
    Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) ∧
    (∫ p, ∫ x, R p x ∂(ν p.1).prod π ∂P.prod (Measure.pi μ)) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  intro R
  let D := ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2
  have hbound p x : ‖R p x‖ ≤ D := by
    simp only [R, norm_pow, norm_norm]
    exact cavity_selected_site_fourth_bound e (fun a => v p.1 a x.1) A₀ hA₀ hC (hv p.1 x.1) p.2
  have hR : Measurable (Function.uncurry R) :=
    ((measurable_cavitySelectedSiteProjection e v hvM A₀).comp
      (measurable_fst.prodMk measurable_snd.fst)).norm.pow_const 4
  have hi p : Integrable (R p) ((ν p.1).prod π) :=
    Integrable.of_bound ((hR.comp measurable_prodMk_left).aestronglyMeasurable) D
      (ae_of_all _ (hbound p))
  let νK : Kernel Ω X := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  let κ : Kernel (Ω × ((a : Fin m) → Orthogonal (N a))) (X × Spin k) :=
    (Kernel.comap νK Prod.fst measurable_fst).prod (Kernel.const _ π)
  have hm : Measurable (fun p => ∫ x, R p x ∂(ν p.1).prod π) := by
    simpa only [κ, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
      νK, Kernel.coe_mk, Function.uncurry_apply_pair] using
      (hR.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hmi : Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable D (ae_of_all _ fun p =>
      by simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := (ν p.1).prod π) (ae_of_all _ (hbound p)))
  refine ⟨hi, hmi, ?_⟩
  rw [integral_prod _ hmi]
  have hn p : 0 ≤ ∫ x, R p x ∂(ν p.1).prod π :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hpω (ω : Ω) : (∫ U, ∫ x, R (ω,U) x ∂(ν ω).prod π ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
    have hiω : Integrable (fun p : ((a : Fin m) → Orthogonal (N a)) × (X × Spin k) =>
        R (ω, p.1) p.2) ((Measure.pi μ).prod ((ν ω).prod π)) :=
      Integrable.of_bound ((hR.comp ((measurable_const.prodMk measurable_fst).prodMk
          measurable_snd)).aestronglyMeasurable) D
        (ae_of_all _ fun p => hbound (ω,p.1) p.2)
    rw [integral_integral_swap hiω]
    have hb x : (∫ U, R (ω,U) x ∂Measure.pi μ) ≤
        (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 :=
      cavity_selected_haar_fourth_moment hN μ e (fun a => v ω a x.1) A₀ hA₀ (hv ω x.1)
    have hi := integral_mono_of_nonneg (μ := (ν ω).prod π)
      (ae_of_all _ fun x => integral_nonneg (fun U => pow_nonneg (norm_nonneg _) 4))
      (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hb)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have ht := integral_mono_of_nonneg (μ := P)
    (ae_of_all _ fun ω => integral_nonneg (fun U => hn (ω,U)))
    (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hpω)
  simpa only [integral_const, probReal_univ, one_smul] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySampledBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral arrays and finite blocks sampled from the same original
Gibbs configurations, with their disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavitySampledGroupBlock {m r : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω]
    (B : Ω → X → X → SpectralEntry (m + 1))
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) (σ : Fin r → X) :
    Measurable (fun ω => cavitySampledGroupBlock B ω σ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.castSucc).comp (hB (σ i) (σ j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable physical cavity model, with original disorder and fresh
Haar frames outside the replica prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityHaarSpinPotential {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (cavityHaarSpinPotential e v A₀ K L C) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
    cavityLogFactor K L C (cavitySelectedSiteProjection e (v z.1)
      (cavityGroupHaarFrames A₀ z.2) x.1) x.2)
  exact (continuous_cavityLogFactor K L C x.2).measurable.comp
    ((measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const)))

lemma measurable_cavityHaarSpinReplicaTest {m r k : ℕ} {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityHaarSpinReplicaTest (U := U) B F) := by
  apply measurable_from_prod_countable_left
  intro σ
  change Measurable (fun z : Ω × U => F (B z.1 (fun i => (σ i).1), fun i => (σ i).2))
  exact F.continuous.measurable.comp
    (((hB (fun i => (σ i).1)).comp measurable_fst).prodMk
      (show Measurable (fun _ : Ω × U => fun i => (σ i).2) from measurable_const))

lemma cavityHaarSpinReplicaTest_bound {m r k : ℕ} {Ω X U : Type*}
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : (Ω × U) × (Fin r → X × Spin k)) :
    |cavityHaarSpinReplicaTest B F p| ≤ ‖F‖ := by
  exact (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedFloor
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical Haar prior supplies the quantitative denominator-floor
error. No inverse partition moment or full tilted Haar moment is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_floor_error {m q d k r : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hvM : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ ω x a, ‖(WithLp.toLp 2 (v ω a x) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C₀ * N a)
    (O : Ω → (Fin r → X) → SpectralBlock m r)
    (hO : ∀ σ, Measurable (fun ω => O ω σ))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    |(∫ p, cavityRegularizedReplicaMean ((ν p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x))
        (cavityProjectedSpinTest (O p.1) F) δ ∂P.prod (Measure.pi μ)) -
      ∫ p, cavityWeightedReplicaMean ((ν p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x))
        (cavityProjectedSpinTest (O p.1) F) ∂P.prod (Measure.pi μ)| ≤
      ‖F‖ * r * δ / (Real.exp (-cavityFactorSize K L C * (1+B^2)) / 2) +
        4 * ‖F‖ * ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 / B^4) := by
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N a)) ν hν π
  let Y := fun z : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k) =>
    cavitySelectedSiteProjection e (v z.1.1) (cavityGroupHaarFrames A₀ z.1.2) z.2.1
  let R := fun z => ‖Y z‖
  let H := cavityHaarSpinPotential e v A₀ K L C
  let s := fun p => {x | ‖Y (p,x)‖ ≤ B}
  let G := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N a)) O F
  have hY : Measurable Y := (measurable_cavitySelectedSiteProjection e v hvM A₀).comp
    (measurable_fst.prodMk measurable_snd.fst)
  have hH : Measurable H := measurable_cavityHaarSpinPotential e v hvM A₀ K L C
  have hG : Measurable G := measurable_cavityHaarSpinReplicaTest O hO F
  have hw p x : (s p).indicator (fun x => Real.exp (H (p,x))) x =
      cavityHaarRestrictedWeight e v A₀ K L C T B (p,x) :=
    (cavityRestrictedFactor_eq_indicator K L C T hB.le hT
      (fun x => Y (p,x)) Prod.snd x).symm
  have hg p x (hx : x ∈ s p) : |H (p,x)| ≤ cavityFactorSize K L C * (1+B^2) := by
    have hp := (sq_le_sq₀ (norm_nonneg (Y (p,x))) hB.le).mpr hx
    exact (cavity_logFactor_growth K L C (Y (p,x)) x.2).trans
      (mul_le_mul_of_nonneg_left (by linarith) (cavityFactorSize_nonneg K L C))
  have hf := cavity_restricted_regularization_error (P.prod (Measure.pi μ))
    (fun p => κ p) κ.measurable H hH s (measurableSet_le hY.norm measurable_const)
    G hG (norm_nonneg F) hδ hg (fun p σ => cavityHaarSpinReplicaTest_bound O F (p,σ))
  have hm := cavity_haar_prior_fourth_moment P ν hν hN μ e v hvM A₀ hA₀ hC₀ hv π
  have hm' : (∀ p, Integrable (fun x => R (p,x)^4) (κ p)) ∧
      Integrable (fun p => ∫ x, R (p,x)^4 ∂κ p) (P.prod (Measure.pi μ)) ∧
      (∫ p, ∫ x, R (p,x)^4 ∂κ p ∂P.prod (Measure.pi μ)) ≤
        (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 := by
    simpa only [R,Y,κ,cavityHaarSpinPriorKernel_apply] using hm
  have ht := cavity_random_prior_fourth_tail (P.prod (Measure.pi μ))
    (fun p => κ p) κ.measurable R hY.norm (ae_of_all _ hm'.1) hm'.2.1 hB hm'.2.2
  have ht' : (∫ p, (κ p).real (s p)ᶜ ∂P.prod (Measure.pi μ)) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 / B^4 := by
    simpa only [R,s,abs_norm,Set.compl_ofPred,not_le] using ht
  have hwfun p : (s p).indicator (fun x => Real.exp (H (p,x))) =
      fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x) := funext (hw p)
  simp only [hwfun] at hf
  have hout := hf.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ 4 * ‖F‖)))
  simpa only [κ,cavityHaarSpinPriorKernel_apply,G,cavityHaarSpinReplicaTest,neg_mul] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-disorder integration for physical Haar spin numerators. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_group_gram_diagonal_norm {m : ℕ} {N : Fin m → ℕ}
    (hN : ∀ a, 0 < N a) (v : (a : Fin m) → Fin (N a) → ℝ) {C : ℝ}
    (hv : ∀ a, |cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0| ≤ C) :
    ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a := by
  intro a
  have hn : 0 < (N a : ℝ) := Nat.cast_pos.mpr (hN a)
  have h := (le_abs_self _).trans (hv a)
  have he : cavityGroupReplicaGram (fun a (_ : Fin 1) => v a) a 0 0 =
      ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 / (N a : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [cavityGroupReplicaGram, pow_two]
  rw [he] at h
  exact (div_le_iff₀ hn).mp h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarFiniteCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Haar restricted Gibbs test approaches the full finite
spectral cavity test as the cutoff grows after the system-size limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_finite_cutoff_comparison_oai {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
    {N₀ : ℕ} (B₀ : Matrix (Fin (m*N₀)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (hK : K = B₀.transpose * cavityRepeatedSpectrum (n := N₀) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i)))
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let Qf := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let Of := fun n => cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
          (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
          ∂(P n).prod (Measure.pi (μ n))) -
        ∫ ω, cavityWeightedReplicaMean (η n ω)
          (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
          (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n| < ε := by
  intro p τ η Qf Of
  let f j n := ∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod π)
    (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
    (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin)
    ∂(P n).prod (Measure.pi (μ n))
  let u j δ n := ∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
    (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
    (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin) δ
    ∂(P n).prod (Measure.pi (μ n))
  let v j δ n := ∫ ω, cavityRegularizedReplicaMean (η n ω)
    (fun x => cavityLabeledRestrictedWeight n K L Cspin (τ j) (b j) (ω,x))
    (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) δ ∂Qf n
  let z n := ∫ ω, cavityWeightedReplicaMean (η n ω)
    (fun x => Real.exp (cavityLabeledPotential n K L Cspin (ω,x)))
    (fun σ => cavityLabeledReplicaTest (Of n) Fspin (ω,σ)) ∂Qf n
  let M₁ := (dim : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2
  let M₂ := cavityGaussianLinearMomentBound dim 4 0 (∑ a, (ρ a)⁻¹)
  let M₃ := cavityGaussianLinearMomentBound dim 2
    (cavityMatrixMass L + cavityMatrixMass Cspin) (ρ a)⁻¹
  let E j := |4 * ‖Fspin‖ * (M₁ / (b j)^4)| +
    |4 * ‖Fspin‖ * (M₂ / (b j)^4) + 2 * ‖Fspin‖ * r * (M₃ / (b j)^2)|
  have hnorm n ω x a :
      ‖(WithLp.toLp 2 (v₀ n ω a x) : EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C * N n a :=
    cavity_group_gram_diagonal_norm (hNpos n) (fun a => v₀ n ω a x)
      (fun a => hv 1 n (ω,fun _ => x) a 0 0) a
  have hu j δ (hδ : 0 < δ) n : |f j n - u j δ n| ≤
      (‖Fspin‖ * r) * δ / (Real.exp (-τ j)/2) + E j := by
    have hh := cavity_haar_restricted_floor_error (P n) (ν n) (hν n) (hNpos n) (μ n)
      e (v₀ n) (hvM n) (A₀ n) (hA₀ n) hC (hnorm n)
      (cavitySampledGroupBlock (B n)) (measurable_cavitySampledGroupBlock (B n) (hB n))
      K L Cspin π (τ j) (hb j) hδ.le (le_refl _) Fspin
    rw [abs_sub_comm] at hh
    have hh' : |f j n-u j δ n| ≤ (‖Fspin‖*r)*δ/(Real.exp (-τ j)/2) +
        4*‖Fspin‖*(M₁/(b j)^4) := by
      simpa only [f,u,τ,M₁,neg_mul] using hh
    apply hh'.trans
    dsimp only [E]
    linarith [le_abs_self (4*‖Fspin‖*(M₁/(b j)^4)),
      abs_nonneg (4*‖Fspin‖*(M₂/(b j)^4)+2*‖Fspin‖*r*(M₃/(b j)^2))]
  have hvz j δ (hδ : 0 < δ) n : |v j δ n-z n| ≤
      (‖Fspin‖ * r) * δ / (Real.exp (-τ j)/2) + E j := by
    have hh := cavity_finite_restricted_error ρ eig hρ hρsum B₀ hB₀ g a ha p L Cspin π
      (Of n) Fspin (τ j) (hb j) hδ.le
    simp only [← hK] at hh
    have hh' := hh (le_refl _)
    have hh'' : |v j δ n-z n| ≤ (‖Fspin‖*r)*δ/(Real.exp (-τ j)/2) +
        4*‖Fspin‖*(M₂/(b j)^4) + 2*‖Fspin‖*r*(M₃/(b j)^2) := by
      simpa only [v,z,η,Qf,M₂,M₃,τ,neg_mul] using hh'
    apply hh''.trans
    dsimp only [E]
    linarith [abs_nonneg (4*‖Fspin‖*(M₁/(b j)^4)),
      le_abs_self (4*‖Fspin‖*(M₂/(b j)^4)+2*‖Fspin‖*r*(M₃/(b j)^2))]
  have huv j δ (hδ : 0 < δ) : Tendsto (fun n => u j δ n-v j δ n) atTop (𝓝 0) := by
    exact cavity_haar_restricted_gibbs_regularized_match N hN μ A₀ hA₀ Ω X P ν hν B hB
      hGram v₀ hvM C hv ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG
      d hd0 hd hE hP hn hoff hdiag g e he heg K L Cspin (τ j) δ hδ π Fspin
      (hb j).le (hnull j)
  have hinv : Tendsto (fun j => (b j)⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero.comp hblim
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have ht := (((hinv.pow 4).const_mul (4*‖Fspin‖*M₁)).abs).add
      ((((hinv.pow 4).const_mul (4*‖Fspin‖*M₂)).add
        ((hinv.pow 2).const_mul (2*‖Fspin‖*r*M₃))).abs)
    simpa only [E,div_eq_mul_inv,inv_pow,mul_assoc,zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,abs_zero] using ht
  exact cavity_cutoff_floor_comparison f z u v (fun j => Real.exp (-τ j)/2) E
    (mul_nonneg (norm_nonneg Fspin) (Nat.cast_nonneg r)) (fun _ => by positivity)
    hE0 hu hvz huv

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison_oai.{u_1, u_2} := @OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison_oai.{u_1, u_2}
