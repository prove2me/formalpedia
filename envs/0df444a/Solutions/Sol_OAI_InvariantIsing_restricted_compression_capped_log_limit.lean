-- Prove2me | solution 1 for OAI.InvariantIsing.restricted_compression_capped_log_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:05:29.290183+00:00
-- url     : https://prove2.me/submissions/e351f887-29b4-4fe8-9ce9-126802ffc520

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_gibbs_numerator_match
import Theorems.Thm_OAI_InvariantIsing_restricted_compression_log_limit

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
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



lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he



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

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWeightedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial approximation of reciprocal normalizers in bounded
replica tests. Extra-replica mixed moments determine the limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

lemma cavity_weighted_comp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Integrable (fun ω => A ω * f (Z ω)) P := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hzs : Measurable (fun ω => (⟨Z ω, hZb ω⟩ : Icc a b)) := hZ.subtype_mk
  have hm : Measurable (fun ω => f (Z ω)) := hf.domRestrict.measurable.comp hzs
  apply Integrable.of_bound (hA.mul hm).aestronglyMeasurable (B * C)
  exact ae_of_all _ fun ω => by
    change ‖A ω * f (Z ω)‖ ≤ B * C
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hAb ω) (hC _ (hZb ω)) (norm_nonneg _) ((abs_nonneg _).trans (hAb ω))

lemma cavity_weighted_polynomial_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B) (p : ℝ[X]) :
    (∫ ω, A ω * p.eval (Z ω) ∂P) =
      ∑ k ∈ p.support, p.coeff k * ∫ ω, A ω * Z ω ^ k ∂P := by
  have he (ω : Ω) : A ω * p.eval (Z ω) =
      ∑ k ∈ p.support, p.coeff k * (A ω * Z ω ^ k) := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ =>
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb
      (fun x => x ^ k) (continuous_pow k).continuousOn).const_mul (p.coeff k))]
  simp only [integral_const_mul]

lemma cavity_weighted_approx_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B η : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    |(∫ ω, A ω * f (Z ω) ∂P) - ∫ ω, A ω * g (Z ω) ∂P| ≤ B * η := by
  rw [← integral_sub (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb f hf)
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb g hg), ← Real.norm_eq_abs]
  have ht := norm_integral_le_of_norm_le_const (μ := P) (C := B * η)
    (f := fun ω => A ω * f (Z ω) - A ω * g (Z ω)) (ae_of_all _ fun ω => by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hAb ω) (hfg _ (hZb ω)) (abs_nonneg _) ((abs_nonneg _).trans (hAb ω)))
  simpa only [probReal_univ, mul_one] using ht

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

lemma cavityWeightNumerator_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) {r : ℕ}
    (F : (Fin r → X) → ℝ) {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hw : ∀ x, |w x| ≤ M) (hF : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * M ^ r := by
  have hp (σ : Fin r → X) : |∏ i, w (σ i)| ≤ M ^ r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ : Fin r, M := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        (fun i _ => hw (σ i))
      _ = _ := by simp
  have ht := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => ν))
    (f := fun σ => (∏ i, w (σ i)) * F σ) (C := B * M ^ r)
    (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hp σ) (hF σ) (abs_nonneg _) (pow_nonneg hM r)).trans_eq (mul_comm _ _))
  simpa only [cavityWeightNumerator, Real.norm_eq_abs, probReal_univ, mul_one] using ht

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform second moment of the negative log normalizer permits
removing the positive floor after the finite-replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_floor_bound {z δ M R : ℝ} (hz : 0 < z) (hzM : z ≤ M)
    (_hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) :
    0 ≤ Real.log (z + δ) - Real.log z ∧
      Real.log (z + δ) - Real.log z ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * (max (-Real.log z) 0) ^ 2 / R := by
  have hzδ : 0 < z + δ := add_pos_of_pos_of_nonneg hz hδ
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hL : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith [_hM])
  refine ⟨sub_nonneg.mpr (Real.log_le_log hz (by linarith)), ?_⟩
  have hsec : Real.log (z + δ) - Real.log z ≤ δ / z := by
    rw [← Real.log_div hzδ.ne' hz.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hzδ hz)).trans_eq
    field_simp
    ring
  by_cases hsmall : -Real.log z ≤ R
  · have hzr : Real.exp (-R) ≤ z := by
      conv_rhs => rw [← Real.exp_log hz]
      exact Real.exp_le_exp.mpr (by linarith)
    have hd : δ / z ≤ δ * Real.exp R := by
      have hh := div_le_div_of_nonneg_left hδ (Real.exp_pos (-R)) hzr
      simpa only [div_eq_mul_inv, Real.exp_neg, inv_inv] using hh
    exact (hsec.trans hd).trans (le_add_of_nonneg_right (by positivity))
  · have hy : max (-Real.log z) 0 = -Real.log z := max_eq_left (by linarith)
    rw [hy]
    have hY : -Real.log z ≤ (-Real.log z) ^ 2 / R := by
      apply (le_div_iff₀ hR0).mpr
      nlinarith
    have h1 : 1 ≤ (-Real.log z) ^ 2 / R := (by linarith : 1 ≤ -Real.log z).trans hY
    have hu : Real.log (z + δ) - Real.log z ≤ Real.log (M + 1) + -Real.log z := by
      have hh := Real.log_le_log hzδ (show z + δ ≤ M + 1 by linarith)
      linarith
    calc
      _ ≤ Real.log (M + 1) + -Real.log z := hu
      _ ≤ Real.log (M + 1) * ((-Real.log z) ^ 2 / R) + ((-Real.log z) ^ 2 / R) :=
        add_le_add (by nlinarith) hY
      _ = (1 + Real.log (M + 1)) * (-Real.log z) ^ 2 / R := by ring
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδ (Real.exp_pos R).le)

lemma cavity_log_floor_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M K δ R : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P)
    (hK : (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) ≤ K) :
    0 ≤ (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ∧
      (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * K / R := by
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hbound ω := cavity_log_floor_bound (hZ0 ω) (hZM ω) hM hδ hδ1 hR
  have him : Integrable (fun ω => δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R) P :=
    (integrable_const _).add ((hi.const_mul L).div_const R)
  have hie : Integrable (fun ω => Real.log (Z ω + δ) - Real.log (Z ω)) P :=
    him.mono' ((hZ.add_const δ).log.sub hZ.log).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
        exact (hbound ω).2)
  refine ⟨integral_nonneg (fun ω => (hbound ω).1), ?_⟩
  calc
    _ ≤ ∫ ω, δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R ∂P :=
      integral_mono hie him (fun ω => (hbound ω).2)
    _ = δ * Real.exp R + L * (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) / R := by
      rw [integral_add (integrable_const _) ((hi.const_mul L).div_const R)]
      simp only [integral_div, integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK hL) hR0.le)

lemma cavity_log_floor_uniform {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : (n : ℕ) → Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {M K : ℝ} (hZ0 : ∀ n ω, 0 < Z n ω) (hZM : ∀ n ω, Z n ω ≤ M)
    (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hi : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hK : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ ∈ Icc (0 : ℝ) δ₀, ∀ n,
      0 ≤ (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) ∧
        (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) < ε := by
  intro ε hε
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  let R := 1 + 4 * L * K / ε
  have hR : 1 ≤ R := le_add_of_nonneg_right (div_nonneg (by positivity) hε.le)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRmul : R * ε = ε + 4 * L * K := by
    dsimp only [R]
    field_simp
  have htail : L * K / R < ε / 4 := by
    apply (div_lt_iff₀ hR0).mpr
    nlinarith
  refine ⟨min 1 (ε / (4 * Real.exp R)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro δ hδ n
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hδe : δ * Real.exp R ≤ ε / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * Real.exp R by positivity)).mp
      (hδ.2.trans (min_le_right _ _))
    nlinarith
  have hh := cavity_log_floor_integral_bound (P n) (Z n) (hZ n) (hZ0 n) (hZM n)
    hM hδ.1 hδ1 hR (hi n) (hK n)
  refine ⟨hh.1, hh.2.trans_lt ?_⟩
  change δ * Real.exp R + L * K / R < ε
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The negative logarithm of a capped cavity weight is controlled by
the original energy moments, uniformly in the cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_capped_log_negative_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (hiH : Integrable H ν) {T : ℝ} (hT : 0 ≤ T) :
    max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0 ≤ ∫ x, |H x| ∂ν := by
  have him : Integrable (fun x => min (H x) T) ν := by
    apply (hiH.abs.add (integrable_const |T|)).mono'
      (hH.min measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      change |min (H x) T| ≤ |H x| + |T|
      apply abs_le.mpr
      constructor
      · exact le_min (by linarith [neg_abs_le (H x), abs_nonneg T])
          (by linarith [neg_abs_le T, abs_nonneg (H x)])
      · exact (min_le_left _ _).trans (by linarith [le_abs_self (H x), abs_nonneg T]))
  have hie : Integrable (fun x => Real.exp (min (H x) T)) ν := by
    apply Integrable.of_bound ((hH.min measurable_const).exp).aestronglyMeasurable (Real.exp T)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hz := integral_exp_pos hie
  have hj : (∫ x, min (H x) T ∂ν) ≤ Real.log (∫ x, Real.exp (min (H x) T) ∂ν) :=
    (Real.le_log_iff_exp_le hz).mpr (exp_integral_le_partition him hie)
  have hl : -(∫ x, |H x| ∂ν) ≤ ∫ x, min (H x) T ∂ν := by
    rw [← integral_neg]
    apply integral_mono hiH.abs.neg him
    intro x
    exact le_min (neg_abs_le _) ((neg_nonpos.mpr (abs_nonneg _)).trans hT)
  exact max_le (by linarith) (integral_nonneg fun _ => abs_nonneg _)

lemma cavity_capped_log_negative_sq_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ)
    (hH : Measurable H) (hiH : Integrable H ν)
    (hiH2 : Integrable (fun x => |H x| ^ 2) ν)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (_hC : 0 ≤ C) (hT : 0 ≤ T) (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hl := cavity_capped_log_negative_bound ν H hH hiH hT
  have hj := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun x => abs_nonneg (H x))) hiH.abs hiH2
  have hp : (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤ ∫ x, |H x|^2 ∂ν := by
    exact (pow_le_pow_left₀ (le_max_right _ _) hl 2).trans hj
  have hu : (∫ x, |H x|^2 ∂ν) ≤ 2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
    have hb := integral_mono hiH2 ((integrable_const 1).add hiR4 |>.const_mul (2 * C ^ 2))
      (fun x => by
        change |H x| ^ 2 ≤ 2 * C ^ 2 * (1 + R x ^ 4)
        have hs := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
        nlinarith [sq_nonneg (R x ^ 2 - 1), sq_nonneg C])
    simpa only [integral_const_mul, Pi.add_apply, integral_add (integrable_const 1) hiR4,
      integral_const, probReal_univ, one_smul] using hb
  exact hp.trans hu

theorem cavity_capped_log_negative_sq_of_growth {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ) (hH : Measurable H)
    (hiR4 : Integrable (fun x => R x ^ 4) ν)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : ∀ x, |H x| ≤ C * (1 + R x ^ 2)) :
    (max (-Real.log (∫ x, Real.exp (min (H x) T) ∂ν)) 0)^2 ≤
      2 * C ^ 2 * (1 + ∫ x, R x ^ 4 ∂ν) := by
  have hs x : |H x|^2 ≤ 2 * C^2 * (1 + R x^4) := by
    have hh := pow_le_pow_left₀ (abs_nonneg (H x)) (hbound x) 2
    nlinarith [sq_nonneg (R x^2 - 1), sq_nonneg C]
  have hiH : Integrable H ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C)).mono' hH.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      change |H x| ≤ 2 * C * (1 + R x^4)
      have hh := mul_le_mul_of_nonneg_left
        (show 1 + R x^2 ≤ 2 * (1 + R x^4) by nlinarith [sq_nonneg (R x^2 - 1)]) hC
      nlinarith [hbound x]
  have hiH2 : Integrable (fun x => |H x|^2) ν := by
    apply (((integrable_const 1).add hiR4).const_mul (2 * C^2)).mono'
      (hH.abs.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hs x
  exact cavity_capped_log_negative_sq_bound ν H R hH hiH hiH2 hiR4 hC hT hbound

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalGroupAverage
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

lemma cavityCanonicalGroupFrame_gram {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) (a : Fin m) :
    (cavityCanonicalGroupFrame k e g hk a).transpose*cavityCanonicalGroupFrame k e g hk a=1 :=
  (Classical.choose_spec (cavity_canonical_group_frames k e g hk)).1 a

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityUnflooredLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the positive floor after the bounded finite-replica passage.
Only the second moment of the negative logarithm is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_integrable_of_negative_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    Integrable (fun ω => Real.log (Z ω)) P := by
  apply ((integrable_const (1 + |Real.log M|)).add hi).mono' hZ.log.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change |Real.log (Z ω)| ≤ 1 + |Real.log M| + (max (-Real.log (Z ω)) 0)^2
    have hy := le_max_left (-Real.log (Z ω)) 0
    have hs := sq_nonneg (max (-Real.log (Z ω)) 0 - 1)
    have hu := Real.log_le_log (hZ0 ω) (hZM ω)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (max (-Real.log (Z ω)) 0), abs_nonneg (Real.log M),
      le_abs_self (Real.log M)]

lemma cavity_floored_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ) :
    Integrable (fun ω => Real.log (Z ω + δ)) P := by
  apply integrable_of_measurable_abs_le ((hZ.add_const δ).log)
    (c := |Real.log δ| + |Real.log (M + δ)|)
  intro ω
  have hl := Real.log_le_log hδ (show δ ≤ Z ω + δ by linarith [hZ0 ω])
  have hu := Real.log_le_log (show 0 < Z ω + δ by linarith [hZ0 ω])
    (show Z ω + δ ≤ M + δ by linarith [hZM ω])
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log (M + δ)),
    abs_nonneg (Real.log δ), abs_nonneg (Real.log (M + δ))]

lemma cavity_log_floor_mean_difference {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    |(∫ ω, Real.log (Z ω + δ) ∂P) - ∫ ω, Real.log (Z ω) ∂P| =
      ∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P := by
  rw [← integral_sub (cavity_floored_log_integrable P Z hZ hZ0 hZM hδ)
    (cavity_log_integrable_of_negative_sq P Z hZ hZ0 hZM hi)]
  exact abs_of_nonneg (integral_nonneg (fun ω => sub_nonneg.mpr
    (Real.log_le_log (hZ0 ω) (by linarith))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matching replica moments compare two varying models directly.
This applies to the physical system and a refining finite cascade without
postulating a limiting random probability measure for either model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

theorem cavity_moving_weighted_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : ∀ n, Measurable (W n)) (hD : ∀ n, Measurable (D n))
    {a b B : ℝ} (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc a b) (hWb : ∀ n ω, W n ω ∈ Icc a b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ n ω, |D n ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, A n ω * Z n ω ^ k ∂P n) - ∫ ω, D n ω * W n ω ^ k ∂Q n) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => (∫ ω, A n ω * f (Z n ω) ∂P n) -
      ∫ ω, D n ω * f (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (3 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηb : B * η < ε / 3 := by
    have he : 3 * (B + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf η hη
  have ht : Tendsto (fun n => (∫ ω, A n ω * p.eval (Z n ω) ∂P n) -
      ∫ ω, D n ω * p.eval (W n ω) ∂Q n) atTop (𝓝 0) := by
    simp_rw [cavity_weighted_polynomial_integral (P _) (Z _) (A _) (hZ _) (hA _)
        (hZb _) (hAb _) p,
      cavity_weighted_polynomial_integral (Q _) (W _) (D _) (hW _) (hD _)
        (hWb _) (hDb _) p, ← Finset.sum_sub_distrib, ← mul_sub]
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum p.support (fun k _ => (hmom k).const_mul (p.coeff k))
  have hclose := ht.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h1 := cavity_weighted_approx_error (P n) (Z n) (A n) (hZ n) (hA n)
    (hZb n) (hAb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have h2 := cavity_weighted_approx_error (Q n) (W n) (D n) (hW n) (hD n)
    (hWb n) (hDb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have htri := abs_sub_le (∫ ω, A n ω * f (Z n ω) ∂P n)
    (∫ ω, A n ω * p.eval (Z n ω) ∂P n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, A n ω * p.eval (Z n ω) ∂P n)
    (∫ ω, D n ω * p.eval (W n ω) ∂Q n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  rw [abs_sub_comm] at h1
  linarith

theorem cavity_moving_floored_log
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M δ : ℝ} (hδ : 0 < δ)
    (hZb : ∀ n ω, Z n ω ∈ Icc 0 M) (hWb : ∀ n ω, W n ω ∈ Icc 0 M)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, Z n ω ^ k ∂P n) - ∫ ω, W n ω ^ k ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω + δ) ∂P n) -
      ∫ ω, Real.log (W n ω + δ) ∂Q n) atTop (𝓝 0) := by
  have hf : ContinuousOn (fun z : ℝ => Real.log (z + δ)) (Icc 0 M) :=
    (continuousOn_id.add continuousOn_const).log
      (fun z hz => (add_pos_of_nonneg_of_pos hz.1 hδ).ne')
  simpa only [one_mul] using cavity_moving_weighted_moments P Q Z (fun _ _ => 1)
    W (fun _ _ => 1) hZ (fun _ => measurable_const) hW (fun _ => measurable_const)
    (B := 1) zero_le_one hZb hWb (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (by simpa only [one_mul] using hmom) _ hf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingCappedReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capped spin-replica normalization from ordinary fourth moments and
finite-prefix numerator limits, as supplied by the physical Haar comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_capped_negative_log_mean_bound_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω, x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω, x)^4 ∂ν ω) P)
    {D M T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hg : ∀ ω x, |H (ω, x)| ≤ D * (1 + R (ω, x)^2))
    (hM : (∫ ω, ∫ x, R (ω, x)^4 ∂ν ω ∂P) ≤ M) :
    Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P ∧
    (∫ ω, (max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ∂P) ≤
      2 * D^2 * (1 + M) := by
  have hb : ∀ᵐ ω ∂P, (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ≤
      2 * D^2 * (1 + ∫ x, R (ω, x)^4 ∂ν ω) := by
    filter_upwards [hi] with ω hω
    exact cavity_capped_log_negative_sq_of_growth (ν ω) (fun x => H (ω, x))
      (fun x => R (ω, x)) (hH.comp measurable_prodMk_left) hω hD hT (hg ω)
  have hZ : Measurable (fun ω => ∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) :=
    measurable_cavityWeightNormalizer ν hν _ ((hH.min measurable_const).exp)
  have he := ((integrable_const 1).add hmi).const_mul (2 * D^2)
  have hN : Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P := by
    apply he.mono' ((hZ.log.neg.max measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    change |(max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hω
  refine ⟨hN, ?_⟩
  have hh := integral_mono_ae hN he hb
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const 1) hmi,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM) (by positivity))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Floor removal when both random normalizers vary. This is the form
needed for the finite system and its refining cascade approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_unfloored_log
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hfloors : ∀ δ > 0, Tendsto (fun n =>
      (∫ ω, Real.log (Z n ω + δ) ∂P n) - ∫ ω, Real.log (W n ω + δ) ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, he₁⟩ := cavity_log_floor_uniform P Z hZ hZ0 hZM hM hK0 hiZ hKZ
    (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, he₂⟩ := cavity_log_floor_uniform Q W hW hW0 hWM hM hK0 hiW hKW
    (ε / 3) (by positivity)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hclose := (hfloors δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h₁ := (he₁ δ ⟨hδ.le, min_le_left _ _⟩ n).2
  have h₂ := (he₂ δ ⟨hδ.le, min_le_right _ _⟩ n).2
  rw [← cavity_log_floor_mean_difference (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ (hiZ n),
    abs_sub_comm] at h₁
  rw [← cavity_log_floor_mean_difference (Q n) (W n) (hW n) (hW0 n) (hWM n) hδ (hiW n)] at h₂
  have htri := abs_sub_le (∫ ω, Real.log (Z n ω) ∂P n)
    (∫ ω, Real.log (Z n ω + δ) ∂P n) (∫ ω, Real.log (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, Real.log (Z n ω + δ) ∂P n)
    (∫ ω, Real.log (W n ω + δ) ∂Q n) (∫ ω, Real.log (W n ω) ∂Q n)
  linarith

theorem cavity_moving_log_of_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, Z n ω ^ k ∂P n) - ∫ ω, W n ω ^ k ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_unfloored_log P Q Z W hZ hW hM hK0 hZ0 hW0 hZM hWM hiZ hiW hKZ hKW
  intro δ hδ
  exact cavity_moving_floored_log P Q Z W hZ hW hδ
    (fun n ω => ⟨(hZ0 n ω).le, hZM n ω⟩) (fun n ω => ⟨(hW0 n ω).le, hWM n ω⟩) hmom

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingCappedLogAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capped logarithmic comparison with almost-sure prior moments,
as provided by the labeled finite-cascade construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_moving_capped_log_ae
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ) (G S : (n : ℕ) → Ξ n × Y n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hiR : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => R n (ω, x)^4) (ν n ω))
    (hiS : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => S n (ω, x)^4) (ρ n ω))
    (hmiR : ∀ n, Integrable (fun ω => ∫ x, R n (ω, x)^4 ∂ν n ω) (P n))
    (hmiS : ∀ n, Integrable (fun ω => ∫ x, S n (ω, x)^4 ∂ρ n ω) (Q n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω, x)| ≤ D * (1 + R n (ω, x)^2))
    (hgG : ∀ n ω x, |G n (ω, x)| ≤ D * (1 + S n (ω, x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω, x)^4 ∂ν n ω ∂P n) ≤ M)
    (hMS : ∀ n, (∫ ω, ∫ x, S n (ω, x)^4 ∂ρ n ω ∂Q n) ≤ M)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin k → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : Fin k → Y n,
        (∏ i, Real.exp (min (G n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ρ n ω) ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω, x)) T) ∂ρ n ω) ∂Q n)
        atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω, x)) T) ∂ρ n ω
  have hw n : Measurable (fun p => Real.exp (min (H n p) T)) :=
    ((hH n).min measurable_const).exp
  have hv n : Measurable (fun p => Real.exp (min (G n p) T)) :=
    ((hG n).min measurable_const).exp
  have hwb n ω x : Real.exp (min (H n (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hvb n ω x : Real.exp (min (G n (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hZ n : Measurable (Z n) := measurable_cavityWeightNormalizer (ν n) (hν n) _ (hw n)
  have hW n : Measurable (W n) := measurable_cavityWeightNormalizer (ρ n) (hρ n) _ (hv n)
  have hZn n := cavity_capped_negative_log_mean_bound_ae (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hiR n) (hmiR n) hD hT (hgH n) (hMR n)
  have hWn n := cavity_capped_negative_log_mean_bound_ae (Q n) (ρ n) (hρ n) (G n) (S n)
    (hG n) (hiS n) (hmiS n) hD hT (hgG n) (hMS n)
  apply cavity_moving_log_of_moments P Q Z W hZ hW
    (M := Real.exp T) (K := 2 * D^2 * (1 + M)) (Real.one_le_exp hT) (by positivity)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hw n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hwb n ω x).2)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hv n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hvb n ω x).2)
  · exact fun n ω => (cavityWeightNormalizer_mem (ν n ω) _
      ((hw n).comp measurable_prodMk_left) le_rfl (hwb n ω)).2
  · exact fun n ω => (cavityWeightNormalizer_mem (ρ n ω) _
      ((hv n).comp measurable_prodMk_left) le_rfl (hvb n ω)).2
  · exact fun n => (hZn n).1
  · exact fun n => (hWn n).1
  · exact fun n => (hZn n).2
  · exact fun n => (hWn n).2
  · intro k
    have hp n ω : Z n ω ^ k = ∫ ξ : Fin k → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ν n ω) := by
      simpa only [Z, Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν n ω)
          (fun x => Real.exp (min (H n (ω, x)) T))).symm
    have hq n ω : W n ω ^ k = ∫ ξ : Fin k → Y n,
        (∏ i, Real.exp (min (G n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ρ n ω) := by
      simpa only [W, Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ρ n ω)
          (fun x => Real.exp (min (G n (ω, x)) T))).symm
    simpa only [hp, hq] using hmom k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCappedLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic capped comparison for the actual Haar and finite
cavity models, with both ordinary fourth moments discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_finite_capped_log_comparison {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) : EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (hT : 0 ≤ T) :
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (uniformCut n) (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
        (cavityStrictUniformLevels p n) n) π
    let H := fun n => cavityHaarSpinPotential e (v n) (A₀ n) K L C
    let G := fun n => cavityLabeledPotential n K L C
    (∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin j → X n × Spin k,
        (∏ i, Real.exp (min (H n (ω,ξ i)) T))
          ∂Measure.pi (fun _ => (ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, ∫ ξ : Fin j → CavityLabeledState d k n,
        (∏ i, Real.exp (min (G n (ω,ξ i)) T))
          ∂Measure.pi (fun _ => η n ω) ∂Q n) atTop (𝓝 0)) →
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂(ν n ω.1).prod π)
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂η n ω) ∂Q n)
      atTop (𝓝 0) := by
  intro Q η H G hraw
  let ν₁ n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a)) (ν n) (hν n) π
  let R n (s : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) :=
    ‖cavitySelectedSiteProjection e (v n s.1.1) (cavityGroupHaarFrames (A₀ n) s.1.2) s.2.1‖
  let S n (s : CavityLabeledDisorder d n × CavityLabeledState d k n) :=
    ‖(cavityLabeledEndpoint n s).1‖
  let M₁ := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  let M₂ := cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹)
  have hR₀ n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n) e (v n)
    (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hR n : (∀ ω, Integrable (fun x => R n (ω,x)^4) (ν₁ n ω)) ∧
      Integrable (fun ω => ∫ x, R n (ω,x)^4 ∂ν₁ n ω) ((P n).prod (Measure.pi (μ n))) ∧
      (∫ ω, ∫ x, R n (ω,x)^4 ∂ν₁ n ω ∂(P n).prod (Measure.pi (μ n))) ≤ M₁ := by
    simpa only [R, ν₁, cavityHaarSpinPriorKernel_apply, M₁] using hR₀ n
  have hM₁ : 0 ≤ M₁ := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hS n := cavity_finite_prior_fourth_moment ρ eig hρ hsum g (cavityStrictUniformPath p n)
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (cavityStrictUniformLevels p n) (cavityStrictUniformLevels_strict p n)
    (cavityStrictUniformPath_on_cell p n) (cavityStrictUniformLevels_mem p n (Fin.last n)).2 π
  have out := cavity_moving_capped_log_ae (fun n => (P n).prod (Measure.pi (μ n))) Q
    (fun n => ν₁ n) (fun n => (ν₁ n).measurable) (fun n => η n) (fun n => (η n).measurable)
    H R G S (fun n => measurable_cavityHaarSpinPotential e (v n) (hvM n) (A₀ n) K L C)
    (fun n => measurable_cavityLabeledPotential n K L C)
    (fun n => ae_of_all _ (hR n).1) (fun n => (hS n).1)
    (fun n => (hR n).2.1) (fun n => (hS n).2.1)
    (D := cavityFactorSize K L C) (M := max M₁ M₂) (cavityFactorSize_nonneg K L C)
    (hM₁.trans (le_max_left _ _)) hT
    (fun n ω x => cavity_logFactor_growth K L C _ _)
    (fun n ω x => cavity_logFactor_growth K L C _ _)
    (fun n => (hR n).2.2.trans (le_max_left _ _))
    (fun n => (hS n).2.2.trans (le_max_right _ _))
    (by simpa only [ν₁, cavityHaarSpinPriorKernel_apply] using hraw)
  simpa only [ν₁, cavityHaarSpinPriorKernel_apply] using out

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame covariance is the physical projected overlap divided
by the finite spectral-group mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityPhysicalReplicaVectors_gram {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j =
      projectedOverlap U (I a) (σ i) (σ j) / ((d a : ℝ) / N) := by
  have hs : (∑ k, U (spinVector (σ i)) (e a k) * U (spinVector (σ j)) (e a k)) =
      ∑ k ∈ I a, U (spinVector (σ i)) k * U (spinVector (σ j)) k := by
    exact ((e a).sum_comp (fun k : ↥(I a) =>
      U (spinVector (σ i)) k * U (spinVector (σ j)) k)).trans
        ((I a).sum_coe_sort (fun k : Fin N => U (spinVector (σ i)) k * U (spinVector (σ j)) k))
  simp only [cavityGroupReplicaGram, cavityPhysicalReplicaVectors, hs, projectedOverlap]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  by_cases hd : d a = 0
  · simp [hd]
  · have hd' : (d a : ℝ) ≠ 0 := by exact_mod_cast hd
    field_simp

lemma cavityPhysicalReplicaVectors_gram_bound {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (c : ℝ) (hc : 0 < c) (hd : ∀ a, c ≤ (d a : ℝ) / N) :
    ∀ a i j, |cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j| ≤ 1 / c := by
  intro a i j
  rw [cavityPhysicalReplicaVectors_gram hN, abs_div,
    abs_of_pos (lt_of_lt_of_le hc (hd a))]
  exact div_le_div₀ (by positivity) (projectedOverlap_abs_le_one U (I a) (σ i) (σ j))
    hc (hd a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vectors used by the fresh group frames have exactly the
physical projected-overlap covariance divided by the group density. -/

noncomputable section
open IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityGroupSetEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupSetEquiv k e a) j : Fin N)=e ⟨a,j⟩ := rfl

lemma cavityGroupSpinCoordinates_physical {N m r : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N) (σ : Fin r → Spin N) :
    (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) =
    cavityPhysicalReplicaVectors (matrixRotation V⁻¹)
      (cavitySpectralGroup (fun i => (e.symm i).1)) k (cavityGroupSetEquiv k e) σ := by
  funext a i j
  rw [cavityPhysicalReplicaVectors, cavityGroupSetEquiv_apply]
  rfl

lemma cavityGroupSpinCoordinates_gram {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j =
      projectedOverlap (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1) a) (σ i) (σ j) / ((k a : ℝ)/N) := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram hN _ _ _ _ _ a i j

lemma cavityGroupSpinCoordinates_covariance {N m r depth : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N × LabeledLeaf depth) (q : ℕ) :
    cavityGroupReplicaCovariance q
      (cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i).1)) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (fun i j => spectralJointEntry (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) depth (σ i) (σ j)) := by
  unfold cavitySpectralBlockCovariance
  congr 1
  funext a i j
  rw [cavityGroupSpinCoordinates_gram hN, spectralJointEntry_spectral]

lemma cavityGroupSpinCoordinates_gram_bound {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) {c : ℝ} (hc : 0 < c)
    (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j|
      ≤ 1/c := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram_bound hN _ _ _ _ _ c hc hk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
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

lemma cavity_haar_spin_numerator_integral {m q d k r : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightNumerator ((ν ω).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C ((ω,U),x)) T))
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ p, cavityWeightNumerator ((ν p.1).prod π)
      (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C (p,x)) T))
      (cavityProjectedSpinTest (B p.1) F) ∂P.prod (Measure.pi μ) := by
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N a)) ν hν π
  have hm := measurable_cavityWeightNumerator κ κ.measurable
    (fun p => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C p) T))
    (((measurable_cavityHaarSpinPotential e v hv A₀ K L C).min measurable_const).exp)
    (cavityHaarSpinReplicaTest B F) (measurable_cavityHaarSpinReplicaTest B hB F)
  have hb (p : Ω × ((a : Fin m) → Orthogonal (N a))) :
      |cavityWeightNumerator (κ p)
        (fun x => Real.exp (min (cavityHaarSpinPotential e v A₀ K L C (p,x)) T))
        (fun σ => cavityHaarSpinReplicaTest B F (p,σ))| ≤ ‖F‖ * (Real.exp T)^r :=
    cavityWeightNumerator_abs_le (κ p) _ _ (Real.exp_pos T).le (norm_nonneg F)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
      (fun σ => cavityHaarSpinReplicaTest_bound B F (p,σ))
  have hi := Integrable.of_bound (μ := P.prod (Measure.pi μ)) hm.aestronglyMeasurable
    (‖F‖ * (Real.exp T)^r) (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  simpa only [κ, cavityHaarSpinPriorKernel_apply, cavityHaarSpinReplicaTest] using
    (integral_prod _ hi).symm

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarGibbsCappedLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capped logarithmic limits for the actual fresh-Haar Gibbs model,
from the spectral/GG limit and the derived ordinary moment bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_gibbs_capped_log_match {m q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (hNpos : ∀ k a, 0 < N k a)
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
    (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ r k (x : Ω k × (ℕ → X k)) j i l, |cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ r k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (cavitySampledEntryArray (B k) x)))
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
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) (hT : 0 ≤ T)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun k => cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
        (cavityStrictUniformLevels p k))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
        (uniformCut k) (cavityStrictUniformLevels p k))
    let η := fun k => cavityLabeledPriorKernel k
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
        (cavityStrictUniformLevels p k) k) π
    Tendsto (fun k =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityHaarSpinPotential e (v₀ k) (A₀ k) K L Cspin (ω,x)) T)
        ∂(ν k ω.1).prod π) ∂(P k).prod (Measure.pi (μ k))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential k K L Cspin (ω,x)) T)
        ∂η k ω) ∂Qf k) atTop (𝓝 0) := by
  intro p Qf η
  have hnorm k ω x : ∀ a, ‖(WithLp.toLp 2 (v₀ k ω a x) :
      EuclideanSpace ℝ (Fin (N k a)))‖^2 ≤ C * N k a :=
    cavity_group_gram_diagonal_norm (hNpos k) (fun a => v₀ k ω a x)
      (fun a => hv 1 k (ω,fun _ => x) a 0 0)
  have hcomp := cavity_finite_capped_log_comparison N hNpos μ Ω X P ν hν e v₀ hvM
    A₀ hA₀ hC hnorm ρ eig hρ hρsum g p K L Cspin π T hT
  let F j : SpectralBlock m j × (Fin j → Spin kspin) →ᵇ ℝ :=
    BoundedContinuousFunction.const _ 1
  have hraw (j : ℕ) := cavity_haar_gibbs_numerator_match (r := j)
    N hN μ A₀ hA₀ Ω X P ν hν B hB hGram v₀ hvM C (hv j)
    ρs ρ eig hρs hρ hρlim hρsum (hcov j) Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn
    hoff hdiag g e he heg K L Cspin T π (F j)
  have hnum (j k : ℕ) := cavity_haar_spin_numerator_integral (P k) (ν k) (hν k)
    (μ k) e (v₀ k) (hvM k) (A₀ k) (cavitySampledGroupBlock (B k))
    (fun σ => measurable_cavitySampledGroupBlock (B k) (hB k) σ)
    K L Cspin π T (F j)
  apply hcomp
  intro j
  apply (hraw j).congr'
  filter_upwards [] with k
  have hnk := hnum j k
  dsimp only [cavityHaarSpinPotential] at hnk
  rw [hnk]
  simp only [F, cavityWeightNumerator, cavityProjectedSpinTest,
    cavityLabeledCappedNumerator, cavityLabeledReplicaTest,
    BoundedContinuousFunction.const_apply', mul_one]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationArray
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral array of the concrete base rotation/Gaussian Gibbs
law. The same rotation supplies its overlaps and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityRotationEntry_gram {N m depth : ℕ} (I : Fin m → Finset (Fin N))
    (p : ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)) :
    SpectralGram (cavitySampledEntryArray (cavityRotationEntry I) p) := by
  intro a r
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_tree] using
      treeOverlap_posSemidef depth (fun i : Fin r => (p.2 i).2)
  · simpa only [spectralCoordinateArray, cavitySampledEntryArray,
      cavityRotationEntry, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (matrixRotation p.1.1.1⁻¹) (I j)
        (fun i : Fin r => (p.2 i).1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma cavityRotationVectors_gram_bound {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)))
    {c : ℝ} (hc : 0 < c) (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i)) a i j| ≤ 1/c :=
  cavityGroupSpinCoordinates_gram_bound hN k e p.1.1.1
    (fun i => (p.2 i).1) hc hk

lemma cavityRotationVectors_covariance {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth))) (q : ℕ) :
    cavityGroupReplicaCovariance q (cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i))) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (spectralBlockView (m+1) r (cavitySampledEntryArray
        (cavityRotationEntry (cavitySpectralGroup (fun i => (e.symm i).1))) p)) :=
  cavityGroupSpinCoordinates_covariance hN k e p.1.1.1 (fun i => p.2 i) q

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPhysicalLogLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capped logarithmic convergence with the actual base-system Gibbs
kernel and physical spectral-group coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem restricted_physical_capped_log_limit
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin kspin)) (hC : C.Nonempty) (hN : ∀ n, 0 < N n)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ n a, 0 < dims n a)
    (hdims : ∀ a, Tendsto (fun n => dims n a) atTop atTop)
    (E : (n : ℕ) → ((a : Fin m) × Fin (dims n a)) ≃ Fin (N n))
    (μ : (n : ℕ) → Measure (Orthogonal (N n))) [∀ n, IsProbabilityMeasure (μ n)]
    (θ : (n : ℕ) → Measure (LabeledTree (depth n))) [∀ n, IsProbabilityMeasure (θ n)]
    (μG : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (dims n a)))
    [∀ n a, IsProbabilityMeasure (μG n a)] [∀ n a, (μG n a).IsMulRightInvariant]
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (dims n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    (eigN : (n : ℕ) → Fin (N n) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hcG : ∀ n a, c ≤ (dims n a : ℝ)/N n)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρlim : Tendsto (fun n a => (dims n a : ℝ)/N n) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun n => restrictedRotationArrayLaw (S n) (hS n) (μ n) (θ n) (eigN n)
      (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n)) atTop (𝓝 Q₀))
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
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) (hT : 0 ≤ T) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun r => cavityLabeledDisorderLaw r (chainExponent (uniformCut r))
      (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r))
      (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (uniformCut r) (cavityStrictUniformLevels p r))
    let η := fun r => cavityLabeledPriorKernel r
      (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r) r) (restrictedSpinPrior C hC)
    Tendsto (fun r =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityHaarSpinPotential e (cavityRotationVectors (dims r) (E r)) (A₀ r) K L Cspin (ω,x)) T)
        ∂((restrictedRotationProbability (S r) (hS r) (eigN r)
          (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r) ω.1).prod (restrictedSpinPrior C hC)))
        ∂(((μ r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential r K L Cspin (ω,x)) T)
        ∂η r ω) ∂Qf r) atTop (𝓝 0) := by
  intro p Qf η
  let I r := cavitySpectralGroup (fun i => ((E r).symm i).1)
  let Ω r := (Orthogonal (N r) × LabeledTree (depth r)) × (ℕ → ℝ)
  let X r := Spin (N r) × LabeledLeaf (depth r)
  let P r := ((μ r).prod (θ r)).prod gaussianCoordinates
  let ν r := restrictedRotationProbability (depth := depth r) (S r) (hS r) (eigN r) (I r) (u r)
  let B r := cavityRotationEntry (depth := depth r) (I r)
  let Q r := restrictedRotationArrayLaw (S r) (hS r) (μ r) (θ r) (eigN r) (I r) (u r)
  have hρs r a : 0 < (dims r a : ℝ)/N r :=
    div_pos (Nat.cast_pos.mpr (hgroups r a)) (Nat.cast_pos.mpr (hN r))
  exact cavity_haar_gibbs_capped_log_match dims hdims hgroups μG A₀ hA₀ Ω X P ν
    (fun r => measurable_restrictedRotationProbability (S r) (hS r) _ _ _) B
    (fun r => measurable_cavityRotationEntry (I r))
    (fun r => cavityRotationEntry_gram (I r))
    (fun r => cavityRotationVectors (dims r) (E r))
    (fun r => measurable_cavityRotationVectors (dims r) (E r)) (1/c)
    (div_nonneg zero_le_one hc.le)
    (fun s r x => cavityRotationVectors_gram_bound (r := s) (hN r) (dims r) (E r) x hc (hcG r))
    (fun r a => (dims r a : ℝ)/N r) ρ eig hρs hρ hρlim hρsum
    (fun s r x => cavityRotationVectors_covariance (r := s) (hN r) (dims r) (E r) x q)
    Q Q₀ (fun _ => rfl) hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    K L Cspin T hT (restrictedSpinPrior C hC)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCanonicalLogLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral/GG logarithmic limit in the canonical coordinates of the
physical pressure increment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem restricted_canonical_capped_log_limit {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
    (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
    (μ : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun r => restrictedRotationArrayLaw (S r) (hS r) (μ r) (θ r)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)) (v r) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1))
      (u r)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (d₀ : Fin (m+1) → ℝ) (hd0 : ∀ j, 0≤d₀ j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ)=d₀ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0≤(x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ t, |Φ t|≤B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ=0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l=0)
    (A : CavityFactorBlocks d n) (cap : ℝ) (hcap : 0 ≤ cap) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun r => cavityLabeledDisorderLaw r (chainExponent (uniformCut r))
      (cavityFiniteRootCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r))
      (cavityFiniteNoiseCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (uniformCut r) (cavityStrictUniformLevels p r))
    let η := fun r => cavityLabeledPriorKernel r
      (cavityFiniteCovariancePath ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r) r) (restrictedSpinPrior C hC)
    Tendsto (fun r =>
      (∫ ω, restrictedCanonicalHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap 0 A ω
        ∂(((μ r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential r A.1 A.2.1 A.2.2 (ω,x)) cap)
        ∂η r ω) ∂Qf r) atTop (𝓝 0) := by
  intro p Qf η
  let dims := fun r => cavityBaseGroupDimension (k r) a₀
  let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
  let frames := fun r => cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r)
  let eig := fun r => diagonalPerturbedEigenvalues (fun i => lam ((E r).symm i).1)
    (cavitySpectralGroup (fun i => ((E r).symm i).1)) (v r) 1
  have hinj : Function.Injective (fun j : Fin d => (a₀ j,j)) := by
    intro i j hij
    exact congrArg Prod.snd hij
  have h := restricted_physical_capped_log_limit N depth S hS C hC hN dims hgroups hdims E μ θ μG frames
    (fun r a => cavityCanonicalGroupFrame_gram (k r) (e r) a₀ (hk r) a) eig u hc hfrac
    ρ lam hρ hρsum hρlim Q₀ hlim hgg hG d₀ hd0 hd hE hP hn hoff hdiag
    a₀ (fun j => (a₀ j,j)) hinj (fun _ => rfl) A.1 A.2.1 A.2.2 cap hcap
  simpa only [restrictedCanonicalHaarLog, restrictedHaarLogObservable, cavityHaarSpinPotential,
    one_mul, zero_mul, sub_zero, dims, E, frames, eig, p, Qf, η] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCompressionCappedLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual random-compression pressure integrand converges to the
finite cascade logarithm, including its vanishing geometric penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem restricted_compression_capped_log_limit_oai {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (hN : ∀ r, 0<N r) (hNlim : Tendsto N atTop atTop)
    (g : (r : ℕ) → Fin (N r+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (hk : ∀ r a, d ≤ k r a)
    (hgroups : ∀ r a, 0 < cavityBaseGroupDimension (k r) a₀ a)
    (hdims : ∀ a, Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ a) atTop atTop)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n))) [∀ r, IsProbabilityMeasure (μ r)]
    (ν : (r : ℕ) → Measure (Orthogonal (N r))) [∀ r, IsProbabilityMeasure (ν r)]
    (θ : (r : ℕ) → Measure (LabeledTree (depth r))) [∀ r, IsProbabilityMeasure (θ r)]
    (μG : (r : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k r) a₀ a)))
    [∀ r a, IsProbabilityMeasure (μG r a)] [∀ r a, (μG r a).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hfrac : ∀ r a, c ≤ (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun r => restrictedRotationArrayLaw (S r) (hS r) (ν r) (θ r)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1)) (v r) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1))
      (u r)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (d₀ : Fin (m+1) → ℝ) (hd0 : ∀ j, 0≤d₀ j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ)=d₀ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0≤(x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ t, |Φ t|≤B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ=0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l=0)
    (A : CavityFactorBlocks d n)
    (hprob : ∀ ε>0, Tendsto (fun r => (μ r).real {U | ε < cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A}) atTop (𝓝 0))
    (cap : ℝ) (hcap : 0 ≤ cap) :
    let AR := fun r U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams (g r) U)
    let δ := fun r => cavityDeterministicRate n m (2*(2*n+1)) (N r)+
      2*cavityCovarianceRate n (2*n+1) (N r)
    let p := spectralSpinQuantilePath Q₀ hP hn
    let Qf := fun r => cavityLabeledDisorderLaw r (chainExponent (uniformCut r))
      (cavityFiniteRootCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r))
      (cavityFiniteNoiseCovariance ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (uniformCut r) (cavityStrictUniformLevels p r))
    let η := fun r => cavityLabeledPriorKernel r
      (cavityFiniteCovariancePath ρ lam hρ hρsum a₀ (cavityStrictUniformPath p r)
        (cavityStrictUniformLevels p r) r) (restrictedSpinPrior C hC)
    Tendsto (fun r =>
      (∫ ω, restrictedRandomHaarLog (S r) (hS r) C hC (k r) (e r) a₀ (hk r) lam (v r) (u r) 1 cap (δ r) (AR r) ω
        ∂((μ r).prod (((ν r).prod (θ r)).prod gaussianCoordinates)).prod (Measure.pi (μG r))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential r A.1 A.2.1 A.2.2 (ω,x)) cap)
        ∂η r ω) ∂Qf r) atTop (𝓝 0) := by
  intro AR δ p Qf η
  have hc₀ := restricted_compression_log_limit N depth S hS C hC hN hNlim g k e es B₀ a₀ hk hgroups
    μ ν θ μG lam v u hc hfrac A hprob cap hcap
  have hf := restricted_canonical_capped_log_limit N depth S hS C hC hN k e a₀ hk hgroups hdims
    ν θ μG lam v u hc hfrac ρ hρ hρsum hρlim Q₀ hlim hgg hG d₀ hd0 hd hE hP hn
    hoff hdiag A cap hcap
  have ht := hc₀.add hf
  simpa only [sub_add_sub_cancel, add_zero] using ht

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.restricted_compression_capped_log_limit_oai := @OAI.InvariantIsing.restricted_compression_capped_log_limit_oai
