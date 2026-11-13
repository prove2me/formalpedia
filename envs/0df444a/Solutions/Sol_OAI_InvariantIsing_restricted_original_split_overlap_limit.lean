-- Prove2me | solution 1 for OAI.InvariantIsing.restricted_original_split_overlap_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:06:52.7972+00:00
-- url     : https://prove2.me/submissions/81fd6586-9ae2-4cb9-ba34-8876154135af

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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_original_integrability
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_finite_cutoff_comparison
import Theorems.Thm_OAI_InvariantIsing_integral_priorCavityLabeledDepthMean
import Theorems.Thm_OAI_InvariantIsing_restricted_cavity_full_depth_test_evaluation
import Theorems.Thm_OAI_InvariantIsing_restricted_original_full_haar_comparison

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The noncommuting resolvent identities in the quadratic cavity tilt.
These finite matrix statements include the zero-dimensional convention. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_inverse_pushThrough {d : ℕ} (C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - C * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * C = C * R := by
  calc
    J * C = J * C * ((1 - K * C) * R) := by rw [hR, mul_one]
    _ = (J * (1 - C * K)) * C * R := by noncomm_ring
    _ = C * R := by rw [hJ, one_mul]

private lemma cavity_inverse_difference {d : ℕ}
    (B C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - B * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * B - C * R = J * (B - C) * R := by
  calc
    J * B - C * R = J * B * ((1 - K * C) * R) - (J * (1 - B * K)) * C * R := by
      rw [hR, hJ, mul_one, one_mul]
    _ = J * (B - C) * R := by noncomm_ring

lemma cavityResolvent_pushThrough {d : ℕ} (K C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K C = C * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  exact cavity_inverse_pushThrough C K _ _
    (Matrix.nonsing_inv_mul _ hC) (Matrix.mul_nonsing_inv _ hR)

/-- Equation `cav:q-resolvent-difference`, with the matrix factors in their
required order. No commutation hypothesis is used. -/
theorem cavityResolvent_difference {d : ℕ} (K B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : IsUnit (1 - B * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  rw [cavityResolvent_pushThrough K C hC]
  exact cavity_inverse_difference B C K _ _
    (Matrix.nonsing_inv_mul _ hB) (Matrix.mul_nonsing_inv _ hR)

theorem cavityResolvent_difference_symmetric {d : ℕ}
    (K B C : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hC : C.transpose = C)
    (hBdet : IsUnit (1 - B * K).det) (hCdet : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * ((1 - C * K)⁻¹).transpose := by
  rw [cavityResolvent_difference K B C hBdet hCdet]
  congr 1
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hK, hC]

/-- The quadratic tilt replaces the original spectral block by the full
block in its resolvent, exactly as in `cav:q-transform`. -/
theorem cavityResolvent_spectral_transform {d : ℕ}
    (A A0 : Matrix (Fin d) (Fin d) ℝ) (b : ℝ)
    (h0 : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0).det)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det) :
    cavityResolvent (A - A0) ((b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0)⁻¹) =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let D0 := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have hD0 : IsUnit D0.det := h0
  have hD : IsUnit D.det := hA
  have hd : D = D0 - (A - A0) := by dsimp only [D, D0]; abel
  have hf : 1 - D0⁻¹ * (A - A0) = D0⁻¹ * D := by
    rw [hd]
    calc
      _ = D0⁻¹ * D0 - D0⁻¹ * (A - A0) := by rw [Matrix.nonsing_inv_mul D0 hD0]
      _ = _ := (mul_sub D0⁻¹ D0 (A - A0)).symm
  have hi : (1 - D0⁻¹ * (A - A0))⁻¹ = D⁻¹ * D0 := by
    apply Matrix.inv_eq_right_inv
    rw [hf]
    calc
      (D0⁻¹ * D) * (D⁻¹ * D0) = D0⁻¹ * (D * D⁻¹) * D0 := by simp only [mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv D hD, mul_one, Matrix.nonsing_inv_mul D0 hD0]
  change (1 - D0⁻¹ * (A - A0))⁻¹ * D0⁻¹ = D⁻¹
  rw [hi, mul_assoc, Matrix.mul_nonsing_inv D0 hD0, mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional algebra in `cav:q-factor` and the backward
quadratic recursion.  The factors retain their order: neither the two
covariances nor the quadratic coefficient need commute. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_quadratic_factor {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    1 - (P - C) * cavityBackwardQuadratic K C =
      (1 - P * K) * (1 - C * K)⁻¹ := by
  unfold cavityBackwardQuadratic
  calc
    1 - (P - C) * (K * (1 - C * K)⁻¹) =
        (1 - C * K) * (1 - C * K)⁻¹ -
          (P - C) * (K * (1 - C * K)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hC]
    _ = (1 - P * K) * (1 - C * K)⁻¹ := by noncomm_ring

theorem cavity_quadratic_step_isUnit {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    IsUnit (1 - (P - C) * cavityBackwardQuadratic K C).det := by
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  exact hP.mul (Matrix.isUnit_nonsing_inv_det _ hC)

theorem cavityBackwardQuadratic_transpose {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.transpose = H)
    (hHdet : IsUnit (1 - H * K).det) :
    (cavityBackwardQuadratic K H).transpose = cavityBackwardQuadratic K H := by
  have hKH : IsUnit (1 - K * H).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  unfold cavityBackwardQuadratic
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hH, hK]
  exact cavityResolvent_pushThrough H K hKH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square completion for an arbitrary positive definite real precision
matrix, expressed against the standard finite-dimensional Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_eigenbasis_action {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (i : Fin d) :
    Q.toEuclideanLin (hQ.eigenvectorBasis i) =
      hQ.eigenvalues i • hQ.eigenvectorBasis i := by
  ext j
  exact congrFun (hQ.mulVec_eigenvectorBasis i) j

lemma cavity_eigenbasis_coordinate {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.eigenvectorBasis.repr (Q.toEuclideanLin x) i =
      hQ.eigenvalues i * hQ.eigenvectorBasis.repr x i := by
  rw [hQ.eigenvectorBasis.repr_apply_apply, hQ.eigenvectorBasis.repr_apply_apply,
    ← Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ (hQ.eigenvectorBasis i) x,
    cavity_eigenbasis_action Q hQ i, real_inner_smul_left]

lemma cavity_eigenbasis_quadratic {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Q.toEuclideanLin x⟫ =
      ∑ i, hQ.eigenvalues i * (hQ.eigenvectorBasis.repr x i) ^ 2 := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner x (Q.toEuclideanLin x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) x, ← hQ.eigenvectorBasis.repr_apply_apply,
    ← hQ.eigenvectorBasis.repr_apply_apply, cavity_eigenbasis_coordinate]
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultivariateGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic integral for the actual multivariate Gaussian law.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_covariance_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hs : (CFC.sqrt S).transpose = CFC.sqrt S := by
    have hs' : (CFC.sqrt S).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg S)
    exact Matrix.isHermitian_iff_isSymm.mp hs'.isHermitian
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine precision homotopy in `cav:q-precision`.  Since the
eigenvectors of its fixed symmetric coefficient do not change, path
nonsingularity rules out eigenvalues at or above one directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_precision_eigenvalues_lt_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) (i : Fin d) :
    hM.eigenvalues i < 1 := by
  by_contra! hEig
  have hEigenPos : 0 < hM.eigenvalues i := lt_of_lt_of_le zero_lt_one hEig
  let t := (hM.eigenvalues i)⁻¹
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(inv_pos.mpr hEigenPos).le, ?_⟩
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hEig
  have hz : (1 - t • M) *ᵥ (fun j => hM.eigenvectorBasis i j) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hM.mulVec_eigenvectorBasis, smul_smul]
    simp [t, inv_mul_cancel₀ hEigenPos.ne']
  have hinj : Function.Injective (1 - t • M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hpath t ht))
  have hvzero : (fun j => hM.eigenvectorBasis i j) = 0 := by
    apply hinj
    simpa only [Matrix.mulVec_zero] using hz
  apply hM.eigenvectorBasis.orthonormal.ne_zero i
  ext j
  exact congrFun hvzero j

lemma cavity_precision_inner_pos {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hEig : ∀ i, hM.eigenvalues i < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) :
    0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ := by
  have he : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ =
      ∑ i, (1 - hM.eigenvalues i) * (hM.eigenvectorBasis.repr x i) ^ 2 := by
    simp only [map_sub, map_one, sub_apply,
      one_apply_eq_self, inner_sub_right, real_inner_self_eq_norm_sq]
    have hq : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) M x⟫ =
        ∑ i, hM.eigenvalues i * (hM.eigenvectorBasis.repr x i) ^ 2 :=
      cavity_eigenbasis_quadratic M hM x
    rw [hq]
    have hn : ‖x‖ ^ 2 = ∑ i, (hM.eigenvectorBasis.repr x i) ^ 2 := by
      simpa only [hM.eigenvectorBasis.repr_apply_apply] using
        (hM.eigenvectorBasis.sum_sq_inner_right x).symm
    rw [hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  obtain ⟨i, hi⟩ : ∃ i, hM.eigenvectorBasis.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply hM.eigenvectorBasis.repr.injective
    ext i
    simpa only [map_zero, PiLp.zero_apply] using h i
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sub_pos.mpr (hEig j)).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (sub_pos.mpr (hEig i)) (sq_pos_of_ne_zero hi)⟩

/-- The source's precision-continuation argument specialized to its actual
affine path. No continuity-of-eigenvalues input is needed. -/
theorem cavity_precision_posDef_of_path {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) :
    (1 - M).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_one.sub hM, ?_⟩
  intro v hv
  have hx : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
    intro h
    apply hv
    ext i
    exact congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  have hp := cavity_precision_inner_pos M hM
    (cavity_precision_eigenvalues_lt_one M hM hpath) (WithLp.toLp 2 v) hx
  simpa only [Matrix.inner_toEuclideanCLM, PiLp.toLp_apply, star_trivial] using hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-gap comparison for the diagonal covariances in the
finite-alphabet cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_inverse_gap {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    (Matrix.diagonal (fun i => (s i)⁻¹) - K).PosDef := by
  have hd : (Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply sub_nonneg.mpr
    simpa only [one_div] using one_div_le_one_div_of_le (hs i) (hsp i)
  have he : Matrix.diagonal (fun i => (s i)⁻¹) - K =
      (Matrix.diagonal (fun i => (p i)⁻¹) - K) +
        Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [he]
  exact hgap.add_posSemidef hd

lemma cavity_diagonal_gap_isUnit {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    IsUnit (1 - Matrix.diagonal s * K).det := by
  have hg := cavity_diagonal_inverse_gap K p s hs hsp hgap
  have he : 1 - Matrix.diagonal s * K =
      Matrix.diagonal s * (Matrix.diagonal (fun i => (s i)⁻¹) - K) := by
    rw [mul_sub, Matrix.diagonal_mul_diagonal]
    have hone : Matrix.diagonal (fun i => s i * (s i)⁻¹) = 1 := by
      simp [funext fun i => mul_inv_cancel₀ (hs i).ne']
    rw [hone]
  rw [he, Matrix.det_mul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (Matrix.PosDef.diagonal hs).det_pos.ne'
  · exact isUnit_iff_ne_zero.mpr hg.det_pos.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStepPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision positivity for a finite-alphabet covariance step.  The
upper covariance is positive diagonal; the lower one is either positive
diagonal or zero, as at the terminal endpoint of the cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_interpolation_isUnit {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (p c : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i) (hcp : ∀ i, c i ≤ p i)
    (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (1 - Matrix.diagonal (fun i => c i + t * (p i - c i)) * K).det := by
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_mul, add_zero]
    rcases hc with hc | hc
    · have hz : c = 0 := funext hc
      simp [hz]
    · exact cavity_diagonal_gap_isUnit K p c hc hcp hgap
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  apply cavity_diagonal_gap_isUnit K p _ _ _ hgap
  · intro i
    have hpi := hp i
    have hci := hc0 i
    nlinarith [mul_pos htpos hpi, mul_nonneg (sub_nonneg.mpr ht.2) hci]
  · intro i
    have hi := hcp i
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hi)]

/-- Positivity of `I-Bᵀ K_i B` from the actual diagonal covariance
ordering and the upper spectral gap.  `B Bᵀ = P-C` may be singular. -/
theorem cavity_step_precision_posDef {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hB : Matrix.diagonal p - Matrix.diagonal c = B * B.transpose) :
    (cavityFactorPrecision (cavityBackwardQuadratic K (Matrix.diagonal c)) B).PosDef := by
  let P := Matrix.diagonal p
  let C := Matrix.diagonal c
  let L := cavityBackwardQuadratic K C
  have hC : IsUnit (1 - C * K).det := by
    simpa only [C, zero_mul, add_zero] using
      cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap 0 (by constructor <;> norm_num)
  have hL : L.transpose = L := by
    exact cavityBackwardQuadratic_transpose K C hK (by simp [C]) hC
  have hM : (B.transpose * L * B).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change (B.transpose * L * B).transpose = B.transpose * L * B
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hL, mul_assoc]
  apply cavity_precision_posDef_of_path (B.transpose * L * B) hM
  intro t ht
  let S := C + t • (P - C)
  have hS : IsUnit (1 - S * K).det := by
    have he : S = Matrix.diagonal (fun i => c i + t * (p i - c i)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [S, C, P]
      · simp [S, C, P, Matrix.diagonal_apply_ne _ hij]
    rw [he]
    exact cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap t ht
  have hstep := cavity_quadratic_step_isUnit K S C hS hC
  have hSC : S - C = t • (P - C) := by dsimp only [S]; abel
  rw [hSC] at hstep
  have hdet : (1 - t • (B.transpose * L * B)).det =
      (1 - (t • (P - C)) * L).det := by
    calc
      _ = (1 - (t • (B.transpose * L)) * B).det := by rw [Matrix.smul_mul]
      _ = (1 - B * (t • (B.transpose * L))).det := Matrix.det_one_sub_mul_comm _ _
      _ = _ := by
        rw [Matrix.mul_smul, ← mul_assoc, ← hB, Matrix.smul_mul]
  rw [hdet]
  exact hstep

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling the covariance step by its positive cascade exponent. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_scaled_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 ≤ ζ) :
    (Real.sqrt ζ • CFC.sqrt S) * (Real.sqrt ζ • CFC.sqrt S).transpose = ζ • S := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hζ, cavity_covariance_sqrt_factor S hS]

lemma cavity_scaled_factor_precision {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    cavityFactorPrecision K (Real.sqrt ζ • B) = cavityFactorPrecision (ζ • K) B := by
  simp only [cavityFactorPrecision, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hζ]

/-- The exact precision required by the Gaussian law, obtained from the
diagonal covariance ordering, including zero covariance increments. -/
theorem cavity_scaled_step_precision {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hΔ : Matrix.diagonal p - Matrix.diagonal c = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic K (Matrix.diagonal c))
      (CFC.sqrt S)).PosDef := by
  rw [← cavity_scaled_factor_precision _ _ ζ hζ]
  apply cavity_step_precision_posDef K (Real.sqrt ζ • CFC.sqrt S) hK
    p c hp hc0 hcp hc hgap
  rw [cavity_scaled_sqrt_factor S hS ζ hζ]
  exact hΔ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper spectral gap supplies the diagonal inverse-gap hypothesis
used by the quadratic cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_upper_spectral_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (L b : ℝ) (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (hb : L < b) : (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosDef := by
  have hp : ((b - L) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hb)
  have he : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      (b - L) • (1 : Matrix (Fin d) (Fin d) ℝ) + (L • 1 - A) := by module
  rw [he]
  exact hp.add_posSemidef hA

lemma cavity_resolvent_diagonal_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (eig : Fin d → ℝ) (L b : ℝ)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) (hb : L < b) :
    (Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig)).PosDef := by
  have he : Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig) = b • (1 : Matrix (Fin d) (Fin d) ℝ) - A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [inv_inv, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact cavity_upper_spectral_gap A L b hA hb

/-- The residual endpoint has lower covariance zero. -/
theorem cavity_resolvent_terminal_precision {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (eig : Fin d → ℝ) (L b : ℝ)
    (hK : (A - Matrix.diagonal eig).transpose = A - Matrix.diagonal eig)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (heig : ∀ i, eig i ≤ L) (hb : L < b)
    (hB : Matrix.diagonal (fun i => (b - eig i)⁻¹) = B * B.transpose) :
    (cavityFactorPrecision (A - Matrix.diagonal eig) B).PosDef := by
  have hp : ∀ i, 0 < (b - eig i)⁻¹ := fun i =>
    inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) hb))
  have h := cavity_step_precision_posDef (A - Matrix.diagonal eig) B hK
    (fun i => (b - eig i)⁻¹) (fun _ => 0) hp (by intro i; exact le_rfl)
    (by intro i; exact (hp i).le) (Or.inl (by intro i; rfl))
    (cavity_resolvent_diagonal_gap A eig L b hA hb) (by simpa using hB)
  simpa only [Matrix.diagonal_zero, cavityBackwardQuadratic_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavityRDerivative_eq_deriv (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    cavityRDerivative rho lam hrho hsum x = deriv (finiteR rho lam hrho hsum) x := by
  let b := finiteInverse rho lam hrho hsum x
  let M := finiteSecondResolvent rho lam b
  have hspec := finiteInverse_spec rho lam hrho hsum hx
  have hM : M ≠ 0 := (finiteSecondResolvent_pos (fun a => (hrho a).le) hsum hspec.1).ne'
  have hgap (a : ι) : b - lam a ≠ 0 := (sub_pos.mpr (hspec.1 a)).ne'
  have hterm (a : ι) : projectedResolventDerivative rho lam hrho hsum a x *
      (lam a - finiteR rho lam hrho hsum x) ^ 2 =
        ((rho a / (b - lam a) ^ 2) / x ^ 2 -
          (2 / x) * (rho a / (b - lam a)) + rho a) / M := by
    simp only [projectedResolventDerivative, finiteR, ite_eq_left hx]
    change rho a / (M * (b - lam a) ^ 2) * (lam a - (b - 1 / x)) ^ 2 = _
    field_simp [hM, hgap a, hx.ne']
    ring
  calc
    cavityRDerivative rho lam hrho hsum x =
        (M / x ^ 2 - (2 / x) * x + 1) / M := by
      unfold cavityRDerivative
      simp_rw [hterm]
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, hsum]
      change (M / x ^ 2 - (2 / x) * finiteResolvent rho lam b + 1) / M = _
      rw [hspec.2]
    _ = -1 / M + 1 / x ^ 2 := by field_simp [hM, hx.ne'] <;> ring
    _ = deriv (finiteR rho lam hrho hsum) x :=
      (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt.deriv.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix covariance identities of `cav:q-innovations`.  These
identities apply also to zero covariance increments. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- The covariance increment transforms by the resolvent difference.
This multiplication form does not require a nonzero cascade exponent. -/
theorem cavity_innovation_covariance_mul {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    ζ • ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) =
      cavityResolvent K P - cavityResolvent K C := by
  rw [cavityResolvent_difference_symmetric K P C hK hC hPdet hCdet, hΔ]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

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

lemma cavity_sqrt_scalar_identity {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) :
    CFC.sqrt (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) = Real.sqrt ρ • 1 := by
  apply CFC.sqrt_unique
    (hb := (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg ρ)).nonneg)
  rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt hρ]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Schur field identity identifies the covariance of each projected
quadratic innovation with a scalar increment. This is the finite matrix
step in the identification of the cavity field path. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_projected_resolvent_difference {d n : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC : ℝ)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * (cavityResolvent K P - cavityResolvent K C) * L =
      (rP - rC) • 1 := by
  calc
    _ = L.transpose * cavityResolvent K P * L -
        L.transpose * cavityResolvent K C * L := by rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (C₀ + L.transpose * cavityResolvent K P * L) -
        (C₀ + L.transpose * cavityResolvent K C * L) := by abel
    _ = (rP - rC) • 1 := by rw [hP, hC, sub_smul]

/-- The independent innovation covariance from `cav:q-innovations`,
after projection to the cavity sites, is a scalar resolvent difference. -/
theorem cavity_projected_innovation_covariance {d n : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC ζ : ℝ) (hζ : ζ ≠ 0)
    (hK : K.transpose = K) (hCsym : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((rP - rC) / ζ) • 1 := by
  have hcov : (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose =
      ζ⁻¹ • (cavityResolvent K P - cavityResolvent K C) := by
    rw [← cavity_innovation_covariance_mul K P C S ζ hK hCsym hPdet hCdet hΔ,
      smul_smul, inv_mul_cancel₀ hζ, one_smul]
  rw [hcov, Matrix.mul_smul, Matrix.smul_mul,
    cavity_projected_resolvent_difference K P C L C₀ rP rC hP hC, smul_smul]
  congr 1
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Schur-complement evaluation in `cav:compression` and
`cav:scalar-field`. All block inverses are ordinary nonsingular inverses. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_block_inverse_bottom {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (hM : IsUnit (Matrix.fromBlocks A B C D).det) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let := Matrix.invertibleOfIsUnitDet A hA
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks A B C D) hM
  let := Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.toBlocks_fromBlocks₂₂] using
    congrArg Matrix.toBlocks₂₂ (Matrix.invOf_fromBlocks₁₁_eq A B C D)

lemma cavity_block_shift {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
        Matrix.fromBlocks A L L.transpose C =
      Matrix.fromBlocks (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks, Matrix.smul_apply]

/-- Compressing the full resolvent onto the cavity block gives the inverse
of the Schur complement; no commutation of the special blocks is needed. -/
theorem cavity_schur_resolvent_compression {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ =
        (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ := by
  rw [cavity_block_shift] at hM ⊢
  simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
    cavity_block_inverse_bottom (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) hA hM

/-- The scalar compression `x I` forces the cavity field to be
`(b - 1/x) I`, the finite identity `cav:scalar-field`. -/
theorem cavity_schur_scalar_field {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b x : ℝ) (hx : x ≠ 0)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1) :
    C + L.transpose * (b • 1 - A)⁻¹ * L = (b - x⁻¹) • 1 := by
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  let E := b • (1 : Matrix (Fin n) (Fin n) ℝ) - C
  let := Matrix.invertibleOfIsUnitDet D hA
  have hMD : IsUnit (Matrix.fromBlocks D (-L) (-L.transpose) E).det := by
    simpa only [D, E, cavity_block_shift] using hM
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks D (-L) (-L.transpose) E) hMD
  let := Matrix.invertibleOfFromBlocks₁₁Invertible D (-L) (-L.transpose) E
  have hS : IsUnit (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L).det := by
    simpa only [D, E, Matrix.invOf_eq_nonsing_inv, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] using
        Matrix.isUnit_det_of_invertible (E - (-L.transpose) * ⅟D * (-L))
  let := Matrix.invertibleOfIsUnitDet _ hS
  have hi : (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ = x • 1 := by
    rw [← cavity_schur_resolvent_compression A L C b hA hM]
    exact hcompression
  have hscalar : (x • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = x⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hx, one_smul]
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) hi
  rw [Matrix.inv_inv_of_invertible, hscalar] at hs
  rw [sub_smul]
  calc
    C + L.transpose * (b • 1 - A)⁻¹ * L =
        b • 1 - (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L) := by abel
    _ = b • 1 - x⁻¹ • 1 := by rw [hs]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special/cavity block matrix and its continuous limit. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

theorem cavityLimitingStack_gram {m n : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityLimitingStack (n := n) ρ =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have he : cavityLimitingStack (n := n) ρ =
      cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    ext i j
    simp only [cavityLimitingStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [he, cavitySpectralStack_gram _ (fun a => Matrix.PosSemidef.one.smul (hρ a)),
    ← Finset.sum_smul, hsum, one_smul]

theorem cavityLimitingStack_cavity_block {m n : ℕ} (ρ lam : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) ρ = (∑ a, ρ a * lam a) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  change (∑ k : Fin (m * n), (∑ t : Fin (m * n),
    cavityLimitingStack (n := n) ρ t i *
      (if t = k then lam (finProdFinEquiv.symm t).1 else 0)) *
      cavityLimitingStack (n := n) ρ k j) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [cavityLimitingStack, Equiv.symm_apply_apply]
  change (∑ a : Fin m, ∑ b : Fin n,
    Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
      (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
    (∑ a, ρ a * lam a) * (if i = j then 1 else 0)
  have hs (a : Fin m) :
      (∑ b : Fin n, Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
        (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
      (ρ a * lam a) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      rw [mul_right_comm, Real.mul_self_sqrt (hρ a)]
    · have hji : j ≠ i := Ne.symm hij
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp [hij, hji]
  simp_rw [hs]
  exact (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent compression for the actual finite repeated spectrum. The
complete special/cavity basis gives the Schur compression directly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_basis_gram {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) :
    (Matrix.fromCols B E).transpose * Matrix.fromCols B E = 1 := by
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using h
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    hB, hE, hBE, hEB, Matrix.fromBlocks_one]

private lemma cavity_complete_basis_blocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) :
    (Matrix.fromCols B E).transpose * D * Matrix.fromCols B E =
      cavitySpecialBlocks D B E := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  rfl

/-- The resolvent of the full special/cavity block is the same complete
orthogonal compression of the original spectral resolvent. -/
theorem cavity_complete_blocks_inverse {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1)
    (hD : IsUnit (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E)⁻¹ = cavitySpecialBlocks (b • 1 - D)⁻¹ B E := by
  let Q := Matrix.fromCols B E
  have hQ : Q.transpose * Q = 1 := cavity_complete_basis_gram B E hB hE hBE
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hshift : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, cavity_complete_basis_blocks]
  rw [hshift, ← cavity_complete_basis_blocks]
  apply Matrix.inv_eq_right_inv
  calc
    (Q.transpose * (b • 1 - D) * Q) * (Q.transpose * (b • 1 - D)⁻¹ * Q) =
        Q.transpose * (b • 1 - D) * (Q * Q.transpose) * (b • 1 - D)⁻¹ * Q := by
      simp only [Matrix.mul_assoc]
    _ = Q.transpose * ((b • 1 - D) * (b • 1 - D)⁻¹) * Q := by
      rw [hQQ, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hD, Matrix.mul_one, hQ]

private lemma cavityRepeatedSpectrum_shift {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        Matrix.diagonal (fun i => b - lam (finProdFinEquiv.symm i).1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

private lemma cavityRepeatedSpectrum_inverse_mul {m n : ℕ}
    (lam : Fin m → ℝ) (b : ℝ) (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam) *
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) = 1 := by
  rw [cavityRepeatedSpectrum_shift]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum, hb]
  · simp [cavityRepeatedSpectrum, hij]

lemma cavityRepeatedSpectrum_resolvent {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ)
    (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam)⁻¹ =
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) := by
  exact Matrix.inv_eq_right_inv (cavityRepeatedSpectrum_inverse_mul lam b hb)

/-- Exact `cav:compression`: the limiting cavity columns produce the
scalar finite-law Stieltjes transform, for every complete complement. -/
theorem cavity_limiting_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (hb : ∀ a, b - lam a ≠ 0) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ =
      (∑ a, rho a / (b - lam a)) • 1 := by
  have hD := Matrix.isUnit_det_of_right_inverse
    (cavityRepeatedSpectrum_inverse_mul (n := n) lam b hb)
  rw [cavity_complete_blocks_inverse _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete hD,
    cavityRepeatedSpectrum_resolvent lam b hb]
  change (cavityLimitingStack (n := n) rho).transpose *
    cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) *
      cavityLimitingStack (n := n) rho = _
  simpa only [div_eq_mul_inv] using
    cavityLimitingStack_cavity_block rho (fun a => (b - lam a)⁻¹) hrho

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicities in the cavity Schur determinant and the finite
spectral inverse used to evaluate the scalar cavity field. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_conjugate_det {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s]
    (X : Matrix r r ℝ) (Q : Matrix r s ℝ)
    (hQ : Q.transpose * Q = 1) (hQQ : Q * Q.transpose = 1) :
    (Q.transpose * X * Q).det = X.det := by
  have hleft : Q.transpose * X * Q = 1 + Q.transpose * ((X - 1) * Q) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hQ]
    rw [← Matrix.mul_assoc]
    abel
  have hright : 1 + ((X - 1) * Q) * Q.transpose = X := by
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    abel
  rw [hleft, Matrix.det_one_add_mul_comm, hright]

/-- Determinants are preserved by the complete special/cavity basis,
even though its two index types need not be definitionally equal. -/
theorem cavity_complete_blocks_determinant {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E).det =
        (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det := by
  let Q := Matrix.fromCols B E
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : Q.transpose * Q = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
      hB, hE, hBE, hEB, Matrix.fromBlocks_one]
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hblock : Q.transpose * D * Q = cavitySpecialBlocks D B E := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    rfl
  have heq : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, hblock]
  rw [heq]
  exact cavity_complete_conjugate_det _ Q hQ hQQ

lemma cavityRepeatedSpectrum_shift_eq {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        cavityRepeatedSpectrum (n := n) (fun a => b - lam a) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

/-- Every eigenvalue in the full limiting block occurs once for each
cavity coordinate. -/
theorem cavityRepeatedSpectrum_determinant {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).det = ∏ a, (b - lam a) ^ n := by
  rw [cavityRepeatedSpectrum_shift_eq, cavityRepeatedSpectrum, Matrix.det_diagonal]
  rw [← Equiv.prod_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem cavity_limiting_blocks_determinant {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det = ∏ a, (b - lam a) ^ n := by
  rw [cavity_complete_blocks_determinant _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete,
    cavityRepeatedSpectrum_determinant]

/-- The actual inverse-transform argument realizes the compression `x I`
without assuming a separate scalar resolvent identity. -/
theorem cavity_finiteInverse_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    ((finiteInverse rho lam hrho hsum x •
        (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ = x • 1 := by
  have hs := finiteInverse_spec rho lam hrho hsum hx
  rw [cavity_limiting_blocks_compression rho lam _ (fun a => (hrho a).le)
    hsum B hB hBE hcomplete (fun a => ne_of_gt (sub_pos.mpr (hs.1 a)))]
  exact congrArg (fun y : ℝ => y • (1 : Matrix (Fin n) (Fin n) ℝ)) hs.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurFiniteR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Schur field of the actual limiting cavity block is the
finite spectral R-transform, including its prescribed value at zero. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_compressed_shift_posDef {r d : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hD : (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).PosDef) :
    (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B).PosDef := by
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => B.transpose *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  have h := hD.conjTranspose_mul_mul_same hBinj
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using h

private lemma cavitySpecialBlocks_symmetric_fromBlocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (hD : D.transpose = D) :
    cavitySpecialBlocks D B E = Matrix.fromBlocks (B.transpose * D * B)
      (B.transpose * D * E) (B.transpose * D * E).transpose (E.transpose * D * E) := by
  unfold cavitySpecialBlocks
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD]
  simp only [Matrix.mul_assoc]

/-- The source field identity at its true finite-law inverse argument.
Both required determinant hypotheses are derived from spectral positivity. -/
theorem cavity_limiting_field_eq_finiteR {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let b := finiteInverse rho lam hrho hsum x
    E.transpose * D * E + (B.transpose * D * E).transpose *
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B)⁻¹ *
        (B.transpose * D * E) = finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let b := finiteInverse rho lam hrho hsum x
  let A := B.transpose * D * B
  let L := B.transpose * D * E
  let C := E.transpose * D * E
  have hb : ∀ a, lam a < b := (finiteInverse_spec rho lam hrho hsum hx).1
  have hDsym : D.transpose = D := Matrix.diagonal_transpose _
  have hD : (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) - D).PosDef := by
    rw [show D = cavityRepeatedSpectrum (n := n) lam from rfl,
      cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb (finProdFinEquiv.symm i).1))
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    isUnit_iff_ne_zero.mpr (cavity_compressed_shift_posDef D B b hB hD).det_pos.ne'
  have hblocks : Matrix.fromBlocks A L L.transpose C = cavitySpecialBlocks D B E :=
    (cavitySpecialBlocks_symmetric_fromBlocks D B E hDsym).symm
  have hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det := by
    rw [hblocks]
    change IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det
    rw [cavity_limiting_blocks_determinant rho lam b (fun a => (hrho a).le)
      hsum B hB hBE hcomplete]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero n (ne_of_gt (sub_pos.mpr (hb a)))))
  have hcomp : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1 := by
    rw [hblocks]
    exact cavity_finiteInverse_blocks_compression rho lam hrho hsum B hB hBE hcomplete x hx
  have hf := cavity_schur_scalar_field A L C b x hx.ne' hA hM hcomp
  simpa only [finiteR, ite_eq_left hx, one_div, A, L, C, D, E, b] using hf

theorem cavity_limiting_cavityBlock_eq_finiteR_zero {m n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    (cavityLimitingStack (n := n) rho).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho = finiteR rho lam hrho hsum 0 • 1 := by
  simpa only [finiteR, lt_self_iff_false, ite_false, if_false] using
    cavityLimitingStack_cavity_block rho lam (fun a => (hrho a).le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The projected root covariance for the actual finite spectral cavity
blocks. All determinant conditions follow from the positive spectral gap. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
open Filter

namespace InvariantIsing

private lemma cavity_finite_base_shift_isUnit {m d : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i))).det := by
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact isUnit_iff_ne_zero.mpr
    (Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (g i)))).det_pos.ne'

private lemma cavity_finite_compressed_shift_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).det := by
  have hBinj : Function.Injective B.mulVec := by
    intro u v huv
    have he := congrArg (fun w => B.transpose *ᵥ w) huv
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using he
  have hp : (finiteInverse rho lam hrho hsum x •
      (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
        cavityRepeatedSpectrum (n := n) lam).PosDef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (finProdFinEquiv.symm i).1))
  have hc := hp.conjTranspose_mul_mul_same hBinj
  have he : (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using hc
  exact isUnit_iff_ne_zero.mpr he.det_pos.ne'

/-- The finite cavity tilt is invertible at every positive deficit. -/
lemma cavity_finite_tilt_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    IsUnit (1 - H * (A - A₀)).det := by
  dsimp only
  let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let b := finiteInverse rho lam hrho hsum x
  have h₀ : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det :=
    cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx
  have he : 1 - (b • 1 - A₀)⁻¹ * (A - A₀) =
      (b • 1 - A₀)⁻¹ * (b • 1 - A) := by
    calc
      _ = (b • 1 - A₀)⁻¹ * (b • 1 - A₀) - (b • 1 - A₀)⁻¹ * (A - A₀) := by
        rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by noncomm_ring
  change IsUnit (1 - (b • 1 - A₀)⁻¹ * (A - A₀)).det
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul hA

/-- The projected resolvent of the finite cavity tilt has the prescribed
finite-law scalar field value. -/
lemma cavity_finite_projected_resolvent {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L =
      finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  rw [cavityResolvent_spectral_transform _ _ _
    (cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx)
    (cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx)]
  exact cavity_limiting_field_eq_finiteR rho lam hrho hsum B hB hBE hcomplete x hx

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar projections of the innovations and the ordinary residual for
the actual finite spectral cavity blocks. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_finite_projected_innovation {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x y ζ : ℝ) (hx : 0 < x) (hy : 0 < y) (hζ : ζ ≠ 0)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hΔ : (finiteInverse rho lam hrho hsum x • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ -
      (finiteInverse rho lam hrho hsum y • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ = ζ • S) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let K := A - A₀
    let P := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let C := (finiteInverse rho lam hrho hsum y • 1 - A₀)⁻¹
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum y) / ζ) • 1 := by
  intro D E A A₀ L K P C
  have hK : K.transpose = K := by
    dsimp only [K, A, A₀, D, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hC : C.transpose = C := by
    simp only [C, A₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose]
  exact cavity_projected_innovation_covariance K P C S L (E.transpose * D * E)
    (finiteR rho lam hrho hsum x) (finiteR rho lam hrho hsum y) ζ hζ hK hC
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g x hx)
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g y hy) hΔ
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx)
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g y hy)

theorem cavity_finite_projected_residual {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    L.transpose * cavityResolvent (A - A₀) H * L =
      (finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum 0) • 1 := by
  intro D E A A₀ L H
  have hp := cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx
  change E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L = _ at hp
  rw [cavity_limiting_cavityBlock_eq_finiteR_zero rho lam hrho hsum] at hp
  rw [sub_smul]
  exact eq_sub_of_add_eq' hp

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

lemma finiteInverse_strict_antitone_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    finiteInverse rho lam hrho hsum x < finiteInverse rho lam hrho hsum y := by
  apply lt_of_le_of_ne (finiteInverse_antitone_pos rho lam hrho hsum hy hyx.le)
  intro he
  have h := congrArg (finiteResolvent rho lam) he
  rw [(finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).2,
    (finiteInverse_spec rho lam hrho hsum hy).2] at h
  exact hyx.ne h.symm

lemma cavityFiniteCovariance_sub_posDef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosDef.diagonal
  intro i
  apply sub_pos.mpr
  simpa only [one_div] using one_div_lt_one_div_of_lt
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).1 (g i)))
    (sub_lt_sub_right (finiteInverse_strict_antitone_pos rho lam hrho hsum hy hyx) _)

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

theorem cavityFiniteCovariance_step_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x y ζ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hζ : 0 ≤ ζ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hΔ : cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y = ζ • S) :
    (cavityFactorPrecision
      (ζ • cavityBackwardQuadratic (A - Matrix.diagonal (fun i => lam (g i)))
        (cavityFiniteCovariance rho lam hrho hsum g y)) (CFC.sqrt S)).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hy]
  apply cavity_scaled_step_precision _ S hK hS ζ hζ
    (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹)
    (fun i => (finiteInverse rho lam hrho hsum y - lam (g i))⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))).le
  · intro i
    exact inv_anti₀ (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
      (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))
  · exact cavity_resolvent_diagonal_gap A (fun i => lam (g i)) (lam a)
      (finiteInverse rho lam hrho hsum x) hA
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 a)
  · simpa only [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
      cavityFiniteCovariance_diagonal rho lam hrho hsum g hy] using hΔ

theorem cavityFiniteCovariance_terminal_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι) (ha : ∀ i, lam (g i) ≤ lam a)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (cavityFactorPrecision (A - Matrix.diagonal (fun i => lam (g i)))
      (CFC.sqrt (cavityFiniteCovariance rho lam hrho hsum g x))).PosDef := by
  apply cavity_resolvent_terminal_precision A _ (fun i => lam (g i)) (lam a)
    (finiteInverse rho lam hrho hsum x) hK hA ha
    ((finiteInverse_spec rho lam hrho hsum hx).1 a)
  rw [cavity_covariance_sqrt_factor _ (cavityFiniteCovariance_posDef rho lam hrho hsum g hx).posSemidef,
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]

lemma cavity_finite_spectral_upper {m n : ℕ}
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ i, lam i ≤ lam a)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1) :
    (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosSemidef := by
  have hD : (lam a • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).PosSemidef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (ha _))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using
    hD.conjTranspose_mul_mul_same B

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

theorem hasDerivAt_deficit_on_gap (p : OverlapPath) {a b r : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s) (hr : r ∈ Ioo a b) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ a}) r := by
  have hd : HasDerivAt
      (fun t => deficit p a - pathMeasure.real {s | p s ≤ a} * (t - a))
      (-pathMeasure.real {s | p s ≤ a}) r := by
    convert! (((hasDerivAt_id r).sub_const a).const_mul
      (pathMeasure.real {s | p s ≤ a})).const_sub (deficit p a) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  exact deficit_affine_on_gap p hgap ⟨ht.1.le, ht.2.le⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldIncrement
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field increments prescribed by the quadratic cavity
calculation are exactly the integrals defining the manuscript field path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma continuousAt_deriv_finiteR_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (deriv (finiteR rho lam hrho hsum)) x := by
  have h1 := (hasStrictDerivAt_finiteInverseDerivative rho lam hrho hsum hx).hasDerivAt.continuousAt
  have h2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
    continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx.ne')
  apply (h1.add h2).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (hasStrictDerivAt_finiteR rho lam hrho hsum hy).hasDerivAt.deriv

/-- Positive-level covariance increments; no assumption about endpoint
atoms is needed, only that the open interval is a gap in the support. -/
theorem integral_finiteR_deriv_deficit_gap (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {a b : ℝ} (hab : a < b)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    (hpos : 0 < deficit p b) (hmass : pathMeasure.real {s | p s ≤ a} ≠ 0) :
    (∫ r in a..b, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p a) -
        finiteR rho lam hrho hsum (deficit p b)) / pathMeasure.real {s | p s ≤ a} := by
  let R := finiteR rho lam hrho hsum
  let ζ := pathMeasure.real {s | p s ≤ a}
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => deriv R (deficit p r)) (Icc a b) := by
    intro r hr
    exact ((continuousAt_deriv_finiteR_pos rho lam hrho hsum (hp r hr)).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun r => deriv R (deficit p r)) volume a b :=
    ((uIcc_of_le hab.le).symm ▸ hc).intervalIntegrable
  have hcomp : ContinuousOn (fun r => R (deficit p r)) (Icc a b) := by
    intro r hr
    exact (((hasStrictDerivAt_finiteR rho lam hrho hsum (hp r hr)).hasDerivAt.continuousAt).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun r => R (deficit p r))
      ((-ζ) * deriv R (deficit p r)) r := by
    intro r hr
    have hR := (hasStrictDerivAt_finiteR rho lam hrho hsum
      (hp r ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    rw [← hR.deriv] at hR
    convert! hR.comp r hD using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [R, ζ]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcomp hd
    (hi.const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in a..b, deriv R (deficit p r)) * ζ = R (deficit p a) - R (deficit p b)
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the root and all positive-level field covariance
increments for the finite trial quantile used in the cavity argument. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finite_overlap_field_increment (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (∫ r in q i.castSucc..q i.succ, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  have hmass := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
  have hc : 0 < cut i.castSucc.succ := by
    rw [← hfirst]
    apply hcut
    exact Fin.succ_pos _
  have hm : pathMeasure.real {s | p s ≤ q i.castSucc} ≠ 0 := by
    rw [hmass]
    exact hc.ne'
  have h := integral_finiteR_deriv_deficit_gap rho lam hrho hsum p
    (hq (Fin.castSucc_lt_succ (i := i)))
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
    (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))) hm
  rwa [hmass] at h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true, if_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false, if_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true, if_true] using hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteFieldVariance
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar variances in the published field marking input coincide
with the finite spectral cavity covariance increments. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_height_sub (h : FieldStep) (i : Fin h.depth) :
    (fieldStepVariance h i : ℝ) = h.height i.succ - h.height i.castSucc := by
  rw [fieldStepVariance, dite_eq_left i.isLt]
  have hg : (scalarFieldIncrements h).get
      ⟨i, by simpa only [scalarFieldIncrements_length] using i.isLt⟩ =
      ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
    exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
      NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) _
  rw [hg]
  change (fieldIncrement h i.succ).2 = _
  simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero,
    dite_false, Nat.add_sub_cancel]
  rfl

variable {ι : Type*} [Fintype ι]

theorem cavityFieldStep_variance (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (fieldStepVariance
      (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i : ℝ) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  rw [fieldStepVariance_eq_height_sub
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i]
  change cavityFieldPrimitive rho lam hrho hsum p (q i.succ) -
    cavityFieldPrimitive rho lam hrho hsum p (q i.castSucc) = _
  rw [cavityFieldPrimitive_sub]
  calc
    _ = ∫ r in q i.castSucc..q i.succ,
        deriv (finiteR rho lam hrho hsum) (deficit p r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le
        (hq (Fin.castSucc_lt_succ (i := i))).le
      intro r hr
      exact cavityRDerivative_eq_deriv rho lam hrho hsum
        (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
          (hr.2.le.trans (hq.monotone (Fin.le_last _))))
    _ = _ := finite_overlap_field_increment rho lam hrho hsum p cut hcut
      hfirst hlast q hq hp htop i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
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

lemma cavityFiniteDeficitPath_step {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    cavityFiniteDeficitPath p q i - cavityFiniteDeficitPath p q (i + 1) =
      chainExponent cut i * (q i.succ - q i.castSucc) := by
  have he := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
    ⟨(hq (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut i.isLt]
  have hc : cut i.succ.castSucc = cut ⟨i + 1, by omega⟩ := congrArg cut (Fin.ext rfl)
  rw [hc] at he
  linarith

lemma cavityFiniteDeficitPath_step_strict {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) : cavityFiniteDeficitPath p q (i + 1) < cavityFiniteDeficitPath p q i := by
  have hc : 0 < chainExponent cut i := by
    rw [chainExponent_apply cut i.isLt, ← hfirst]
    apply hcut
    change 0 < i.val + 1
    omega
  apply sub_pos.mp
  rw [cavityFiniteDeficitPath_step p cut hcut hfirst hlast q hq hp i]
  exact mul_pos hc (sub_pos.mpr (hq (Fin.castSucc_lt_succ (i := i))))

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

lemma field_chainExponent_pos (h : FieldStep) (i : ℕ) : 0 < chainExponent h.cut i :=
  finite_chainExponent_pos h.cut h.ordered_cut h.first i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationPrefix
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic innovation change preserves shared Gaussian prefixes.
This is the deterministic part of transporting common-level spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix Classical

namespace InvariantIsing

lemma cavityCommonMarkDepth_measurable {d : ℕ} (n : ℕ) :
    Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n => cavityCommonMarkDepth n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [cavityCommonMarkDepth]
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    · have ht : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) ×
          NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) => (p.1.2.2, p.2.2.2)) := by fun_prop
      exact (ih.comp ht).add_const 1
    · exact measurable_const

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianMarkDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Non-atomic Gaussian coordinates identify branching in the retained
quadratic cascade. Common-level tests survive its innovation transport. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Classical Matrix

namespace InvariantIsing

lemma cavity_multivariateGaussian_nullSingleton {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (j : Fin d) (hj : 0 < S j j) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S) := by
  have hv : (S j j).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hj)
  let _ := nullSingletonClass_gaussianReal (μ := 0) hv
  constructor
  intro x
  have hp := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d)))
    hS (i := j)).map_eq
  have hz : (0 : EuclideanSpace ℝ (Fin d)) j = 0 := rfl
  rw [hz] at hp
  have hn : (gaussianReal 0 (S j j).toNNReal) {x j} = 0 := measure_singleton _
  rw [← hp, Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn
  apply measure_mono_null _ hn
  intro y hy
  exact congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) hy

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

lemma cavityFiniteCovariancePath_symmetric (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).transpose =
      cavityFiniteCovariancePath rho lam hrho hsum g p q i := by
  simp only [cavityFiniteCovariancePath, cavityFiniteCovariance,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.diagonal_transpose]

include hcut hfirst in
lemma cavityFiniteNoiseCovariance_delta (i : ℕ) :
    cavityFiniteCovariancePath rho lam hrho hsum g p q i -
      cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1) =
        chainExponent cut i • cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i := by
  rw [cavityFiniteNoiseCovariance, smul_smul,
    mul_inv_cancel₀ (finite_chainExponent_pos cut hcut hfirst i).ne', one_smul]

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posDef (i : Fin n) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosDef := by
  apply Matrix.PosDef.smul
  · exact cavityFiniteCovariance_sub_posDef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_step_strict p cut hcut hfirst hlast q hq hp i)
  · exact inv_pos.mpr (finite_chainExponent_pos cut hcut hfirst i)

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_atomless (hd : 0 < d) (i : ℕ) (hi : i < n) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i)) := by
  have hs := cavityFiniteNoiseCovariance_posDef rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop ⟨i, hi⟩
  exact cavity_multivariateGaussian_nullSingleton _ hs.posSemidef ⟨0, hd⟩ hs.diag_pos

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialPythagoras
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionLimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The limiting frame extracted from the concrete compression has the
orthogonality and completeness used in the finite spectral cavity model. -/

noncomputable section
open Filter
open scoped Matrix Topology

namespace InvariantIsing

lemma cavitySpectralStack_scalar_eq {m n : ℕ} (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) :
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      cavityLimitingStack (n := n) ρ := by
  ext i j
  simp only [cavitySpectralStack, cavityLimitingStack,
    cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

lemma cavityCompressionLimitFrame_gram {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityCompressionLimitFrame e B₀ = 1 := by
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i * B₀ k j)
  exact he.trans (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB₀)

lemma cavityCompressionLimitFrame_perp {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityLimitingStack (n := n) ρ = 0 := by
  have ht := congrArg Matrix.transpose hEB
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
  rw [← cavitySpectralStack_scalar_eq ρ hρ]
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i *
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) (e.symm k) j)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, cavityCompressionLimitFrame,
    Equiv.symm_apply_apply, cavityReindexedStack, Matrix.zero_apply] using
      he.trans (congrArg (fun A : Matrix (Fin d) (Fin n) ℝ => A i j) ht)

theorem cavityCompressionLimitFrame_complete {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    cavityCompressionLimitFrame e B₀ * (cavityCompressionLimitFrame e B₀).transpose +
      cavityLimitingStack (n := n) ρ * (cavityLimitingStack (n := n) ρ).transpose = 1 :=
  cavity_complement_projection_reindex e _ _ (cavityCompressionLimitFrame_gram e B₀ hB₀)
    (cavityLimitingStack_gram ρ hρ hsum) (cavityCompressionLimitFrame_perp e B₀ ρ hρ hEB)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sequence of increasing cutoff radii can avoid every boundary
atom of a countable family of limiting replica laws. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace InvariantIsing

lemma cavity_radius_atoms_countable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (R : X → ℝ) (hR : Measurable R) :
    Set.Countable {B : ℝ | μ {x | R x=B} ≠ 0} := by
  have hm B : MeasurableSet {x | R x=B} := measurableSet_eq_fun hR measurable_const
  have hd : Pairwise (fun B C : ℝ => Disjoint {x | R x=B} {x | R x=C}) := by
    intro B C hBC
    exact Set.disjoint_left.mpr (fun x hx hy => hBC (hx.symm.trans hy))
  simpa only [pos_iff_ne_zero] using Measure.countable_meas_pos_of_disjoint_iUnion hm hd

theorem cavity_common_null_cutoff_radii {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, SFinite (μ n)]
    (R : (n : ℕ) → X n → ℝ) (hR : ∀ n, Measurable (R n)) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, (j : ℝ)+1 < B j ∧ B j < (j : ℝ)+2 ∧
        ∀ n, μ n {x | R n x=B j}=0 := by
  let S : Set ℝ := ⋃ n, {B : ℝ | μ n {x | R n x=B} ≠ 0}
  have hS : S.Countable := Set.countable_iUnion (fun n => cavity_radius_atoms_countable (μ n) (R n) (hR n))
  have hex (j : ℕ) : ∃ B ∈ Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2), B ∉ S := by
    have he := measure_sdiff_null (s := Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2)) (hS.measure_zero volume)
    have hp : 0 < volume (Set.Ioo ((j : ℝ)+1) ((j : ℝ)+2) \ S) := by
      rw [he,Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨B,hB⟩ := nonempty_of_measure_ne_zero hp.ne'
    exact ⟨B,hB.1,hB.2⟩
  choose B hB hBS using hex
  refine ⟨B, ?_, fun j => ⟨(hB j).1,(hB j).2,?_⟩⟩
  · apply tendsto_atTop.mpr
    intro b
    obtain ⟨n,hn⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop n] with j hj
    have hnj : (n : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith [(hB j).1]
  · intro n
    by_contra hn
    exact hBS j (Set.mem_iUnion_of_mem n hn)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common depths alone are preserved by the same-root quadratic innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityRootedDepthTest {d k n : ℕ} (a : ℕ → ℝ) :
    Measurable (cavityRootedDepthTest (d := d) (k := k) (n := n) a) := by
  have hc : Measurable (fun σ : ℕ → CavitySpinState d k n =>
      cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) :=
    (cavityCommonMarkDepth_measurable n).comp
      (show Measurable (fun σ : ℕ → CavitySpinState d k n =>
        ((σ 0).1.2.1, (σ 1).1.2.1)) from by fun_prop)
  exact (measurable_of_countable a).comp hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded common-depth observable disintegrated over root and forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityRootedDepthTest_abs_le {d k n : ℕ} (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) (σ : ℕ → CavitySpinState d k n) :
    |cavityRootedDepthTest a σ| ≤ B := by
  simpa only [cavityRootedDepthTest, abs_mul, abs_spinValue, mul_one, one_mul] using
    ha (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

theorem cavity_rooted_depth_test_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [IsProbabilityMeasure P] (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)) =
      ∫ ω, cavityRootedDepthTestMean n K R L C π a ω ∂P := by
  have hi := integrable_of_measurable_abs_le
    (μ := (probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)
    (measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a)
    (cavityRootedDepthTest_abs_le a ha)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  simpa only [Kernel.const_apply, probabilityReplicaKernel, Kernel.coe_mk,
    cavityRootedDepthTestMean] using
    Kernel.integral_comp hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous spectral-block observable used to read the physical
spin overlap from the finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma sum_cavityCanonicalCoordinate {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∑ a, cavityCanonicalCoordinate rho lam hrho hsum p a t) = t := by
  simp only [cavityCanonicalCoordinate, Set.projIcc_of_mem zero_le_one ht]
  rw [← intervalIntegral.integral_finsetSum
    (fun a _ => spectralPathDensity_intervalIntegrable rho lam hrho hsum p a ht)]
  simp only [spectralPathDensity, sum_projectedResolventDerivative,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous ordinary-overlap observable, without a spin insertion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing


lemma cavityOverlapObservable_finite {m k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (σ : Fin 2 → LabeledLeaf n) (ε : Fin 2 → Spin k) :
    cavityOverlapObservable (m := m) Φ hΦ
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, ε) =
      Φ (q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1)))) := by
  change Φ (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) = _
  have hs : (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) =
      q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1))) := by
    simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, Fin.zero_ne_one,
      ↓reduceIte, cavityCanonicalLabel]
    exact sum_cavityCanonicalCoordinate rho lam hrho hsum p (hq _)
  rw [hs]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximum selected-coordinate norm gives exactly the simultaneous
spatial restriction of every replica. A common divergent sequence of
radii avoids the boundaries of all the limiting replica laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavityReplicaRadius {m r q d : ℕ} {L : Type*} [TopologicalSpace L]
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    Continuous (cavityReplicaRadius (L := L) J) :=
  (J.continuous.comp continuous_snd).norm

theorem cavity_replica_common_null_radii {m q d : ℕ}
    (L : ℕ → Type*) [∀ r, TopologicalSpace (L r)]
    [∀ r, MeasurableSpace (L r)] [∀ r, BorelSpace (L r)]
    (Q : (r : ℕ) → ProbabilityMeasure
      (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (J : (r : ℕ) → EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, 0 < B j ∧ ∀ r,
        (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
          {p | cavityReplicaRadius (J r) p = B j} = 0 := by
  obtain ⟨B,hlim,hB⟩ := cavity_common_null_cutoff_radii
    (fun r => (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))))
    (fun r => cavityReplicaRadius (J r))
    (fun r => (continuous_cavityReplicaRadius (J r)).measurable)
  refine ⟨B,hlim,fun j => ⟨?_,(hB j).2.2⟩⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith [(hB j).1]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalSpinObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the physical spectral components recovers the ordinary spin
overlap. Thus the scalar test needed by self-consistency has no frame dependence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma sum_projectedOverlap_groups {N m : ℕ} (g : Fin N → Fin m)
    (U : Rotation N) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (cavitySpectralGroup g a) σ τ) =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  calc
    _ = (N : ℝ)⁻¹ * ∑ a, ∑ i, if g i = a then
        U (spinVector σ) i * U (spinVector τ) i else 0 := by
      simp only [projectedOverlap,cavitySpectralGroup,Finset.sum_filter,Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ∑ i, U (spinVector σ) i * U (spinVector τ) i := by
      congr 1
      rw [Finset.sum_comm]
      simp
    _ = projectedOverlap U Finset.univ σ τ := by simp only [projectedOverlap]
    _ = _ := projectedOverlap_univ U σ τ

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalOverlapCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual base-system spectral coordinates recover its ordinary
spin-overlap law under the fresh-Haar cutoff comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_physical_overlap_observable {N m depth k : ℕ}
    (g : Fin N → Fin m)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (σ : Fin 2 → (Spin N × LabeledLeaf depth) × Spin k) :
    cavityProjectedSpinTest
      (cavitySampledGroupBlock (cavityRotationEntry (cavitySpectralGroup g)) p)
      (cavityOverlapObservable Φ hΦ) σ =
      Φ ((N : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1.1 i) * spinValue ((σ 1).1.1 i)) := by
  simp only [cavityProjectedSpinTest,cavityOverlapObservable,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,cavitySampledGroupBlock,cavityRotationEntry,spectralJointEntry_spectral]
  rw [sum_projectedOverlap_groups]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralCutoffRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single deterministic cutoff sequence avoids the Gaussian-mixture
boundaries for every replica count in the spectral limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_spectral_common_cutoff_radii {m q d : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m+1))) (ρ : Fin m → ℝ)
    (e : Fin d → Fin m × Fin q) :
    ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧ ∀ j, 0 < b j ∧ ∀ r,
      (cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r) : Measure
        (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
        {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0 :=
  cavity_replica_common_null_radii (fun r => SpectralBlock m r)
    (fun r => cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r))
    (fun _ => cavitySelectedGroupProjection e)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorLabeledOverlapObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing
lemma prior_cavity_labeled_overlap_observable {m d k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (ω : CavityLabeledDisorder d n) :
    cavityWeightedReplicaMean (cavityLabeledPriorKernel n R π ω)
      (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ)) =
      priorCavityLabeledDepthMean n K R L C π (fun i => Φ (q (cavityFiniteLevel n i))) ω := by
  have htest (ξ : Fin 2 → CavityLabeledState d k n) :
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ) =
        Φ (q (cavityFiniteLevel n (labeledCommonDepth n (ξ 0).1.1 (ξ 1).1.1))) :=
    cavityOverlapObservable_finite rho lam hrho hsum p q hq Φ hΦ _ _
  simp only [cavityWeightedReplicaMean, cavityWeightNumerator, cavityWeightNormalizer,
    priorCavityLabeledDepthMean, referenceReplicaMean, referencePartition, Real.exp_sum, htest]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFiniteDepthTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral quadratic cavity has the original common-overlap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_depth_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ σ, cavityRootedDepthTest (fun i => Φ (q (fieldDepthLevel h i))) σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT))
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, Φ (p t) ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  let x := cavityFiniteDeficitPath p q
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hxm : Antitone x := cavityFiniteDeficitPath_antitone p q hq.monotone
  have hK : K.transpose = K := by
    dsimp only [K, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hH (i : ℕ) : (H i).transpose = H i :=
    cavityFiniteCovariancePath_symmetric rho lam hrho hsum g p q i
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop i
  have hS₀ : S₀.PosSemidef :=
    cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g (hx 0) (hq0 0)
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_finite_tilt_isUnit rho lam hrho hsum B hB g (x i) (hx i)
  have hΔ (i : ℕ) : H i - H (i + 1) = chainExponent cut i • S i :=
    cavityFiniteNoiseCovariance_delta rho lam hrho hsum g p cut hcut hfirst q i
  have hA := cavity_finite_spectral_upper lam a ha B hB
  have hQ (i : ℕ) : (cavityFactorPrecision
      (chainExponent cut i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef :=
    cavityFiniteCovariance_step_precision rho lam hrho hsum g _ a hK hA
      (hx (i + 1)) (hxm (Nat.le_succ i)) (finite_chainExponent_pos cut hcut hfirst i).le
      (S i) (hS i) (hΔ i)
  have hR : (H n).PosSemidef :=
    (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast q hq hp htop n).posSemidef
  have hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef :=
    cavityFiniteCovariance_terminal_precision rho lam hrho hsum g _ a (fun i => ha (g i)) hK hA (hx n)
  have hAtom (i : ℕ) (hi : i < n) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)) :=
    cavityFiniteNoiseCovariance_atomless rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop hd i hi
  have hcov (i : ℕ) (hi : i < n) :
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1 := by
    let k : Fin n := ⟨i, hi⟩
    have he := cavity_finite_projected_innovation rho lam hrho hsum B hB hBE hcomplete g
      (x i) (x (i + 1)) (chainExponent cut i) (hx i) (hx (i + 1))
      (finite_chainExponent_pos cut hcut hfirst i).ne' (S i) (hΔ i)
    change L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L = _ at he
    rw [he]
    have hv := cavityFieldStep_variance rho lam hrho hsum p cut hcut hfirst hlast
      q hq hq0 hp htop k
    change (fieldStepVariance h i : ℝ) = _ at hv
    rw [hv]
    simp only [x, cavityFiniteDeficitPath, show i = (k : ℕ) from rfl,
      cavityFiniteLevel_castSucc, cavityFiniteLevel_succ]
    rw [chainExponent_apply cut k.isLt]
    rfl
  have hnonneg : 0 ≤ finiteR rho lam hrho hsum (x n) - c := by
    apply sub_nonneg.mpr
    have hc : c = ∑ a, rho a * lam a := by simp [c, finiteR]
    rw [hc]
    exact mean_le_finiteR rho lam hrho hsum (hx n)
  let v : ℝ≥0 := (finiteR rho lam hrho hsum (x n) - c).toNNReal
  have hres : L.transpose * cavityResolvent K (H n) * L = (v : ℝ) • 1 := by
    rw [show (v : ℝ) = finiteR rho lam hrho hsum (x n) - c from Real.coe_toNNReal _ hnonneg]
    exact cavity_finite_projected_residual rho lam hrho hsum B hB hBE hcomplete g (x n) (hx n)
  have he := restricted_cavity_full_depth_test_evaluation hpub hN T hT h K H S S₀ hS₀ L c hK hH hS
    (fun i => field_chainExponent_pos h i) hdet hΔ hQ hR hQR hAtom v hcov hres
    (fun i => Φ (q (fieldDepthLevel h i))) (fun i => hΦ _)
  apply he.trans
  apply integral_congr_ae
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with t ht
  obtain ⟨i, hi⟩ := ht
  have hindex : fieldLevelIndex h t = i := fieldLevelIndex_on_cell h i hi
  rw [hindex]
  have hlev : fieldDepthLevel h i.val = i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  rw [hlev, hp i t hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFiniteModelDepth
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-depth preservation in the actual normalized finite spectral model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_model_depth_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ ω, priorCavityLabeledDepthMean n K (H n) L (c • 1) (restrictedSpinPrior T hT)
      (fun i => Φ (q (fieldDepthLevel h i))) ω
      ∂cavityLabeledDisorderLaw n (chainExponent cut) S₀ S) =
      ∫ t, Φ (p t) ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  have hI := cavity_finite_original_integrability rho lam hrho hsum B hB g a ha
    p cut hcut hfirst hlast q hq hp htop L (c • 1) (restrictedSpinPrior T hT)
  have hAtom (i : ℕ) (hi : i < n) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)) :=
    cavityFiniteNoiseCovariance_atomless rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop hd i hi
  rw [integral_priorCavityLabeledDepthMean n (chainExponent cut) K (H n) S₀ S L (c • 1) (restrictedSpinPrior T hT)
    (chainExponent_admissible hcut hfirst hlast) hAtom hI]
  rw [← cavity_rooted_depth_test_disintegration n K (H n) L (c • 1)
    (restrictedSpinPrior T hT) _ _ (fun i => hΦ (q (fieldDepthLevel h i)))]
  exact restricted_cavity_finite_depth_test hpub hd hN T hT rho lam hrho hsum B hB hBE hcomplete
    g a ha p cut hcut hfirst hlast q hq hp htop Φ hΦ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedStrictFiniteOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized overlap distribution for the strict finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_finite_normalized_overlap_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ) (hΦc : Continuous Φ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ ω, cavityWeightedReplicaMean
      (cavityLabeledPriorKernel n (H n) (restrictedSpinPrior T hT) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦc) (ω,ξ))
      ∂cavityLabeledDisorderLaw n (chainExponent cut) S₀ S) =
      ∫ t, Φ (p t) ∂pathMeasure := by
  intro H S S₀ K L c
  have hqmem := fun i => finite_overlap_value_mem_unit p cut hcut q hp i
  simp_rw [prior_cavity_labeled_overlap_observable rho lam hrho hsum p q hqmem K (H n) L
    (c • 1) (restrictedSpinPrior T hT) Φ hΦc]
  exact restricted_cavity_finite_model_depth_test hpub hd hN T hT rho lam hrho hsum B hB hBE hcomplete
    g a ha p cut hcut hfirst hlast q hq hp htop Φ hΦ

theorem restricted_strict_finite_overlap_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (Φ : ℝ → ℝ) (hΦc : Continuous Φ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let q := cavityStrictUniformLevels p n
    let p' := cavityStrictUniformPath p n
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p' q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p' (uniformCut n) q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p' q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ ω, cavityWeightedReplicaMean
      (cavityLabeledPriorKernel n (H n) (restrictedSpinPrior T hT) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p' q)
        (cavityOverlapObservable Φ hΦc) (ω,ξ))
      ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n)) S₀ S) =
      ∫ t, Φ (p' t)
        ∂pathMeasure := by
  exact restricted_finite_normalized_overlap_test hpub hd hN T hT rho lam hrho hsum B hB hBE hcomplete
    g a ha (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (fun i s hs => cavityStrictUniformPath_on_cell p n i hs)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 Φ hΦc hΦ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarFiniteOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical restricted Haar overlap test converges to the
unmodified common-level law of the finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem restricted_haar_finite_overlap_cutoff (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m q dim kspin : ℕ}
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
    (hNpos : ∀ n a, 0 < N n a) (hC : 0 ≤ C)
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (T : Finset (Spin kspin)) (hT : T.Nonempty)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean ((ν n ω.1).prod (restrictedSpinPrior T hT))
          (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1)
            (cavityOverlapObservable Φ hΦ)) ∂(P n).prod (Measure.pi (μ n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) ∂pathMeasure| < ε := by
  intro p K L Cspin τ
  have hh := cavity_haar_finite_cutoff_comparison N hN μ A₀ hA₀ Ω X P ν hν B hB
    hGram v₀ hvM C hv ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG
    d hd0 hd hE hP hn hoff hdiag g e he heg K L Cspin (restrictedSpinPrior T hT)
    (cavityOverlapObservable Φ hΦ) hNpos hC B₀ hB₀ a ha rfl b hb hblim hnull
  dsimp only at hh
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  filter_upwards [hj] with n hn'
  have hf := restricted_strict_finite_overlap_test hpub hdim hkspin T hT ρ eig hρ hρsum B₀ hB₀
    hBE hcomplete g a ha p Φ hΦ (n := n) hΦb
  dsimp only at hf
  rw [hf] at hn'
  exact hn'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPhysicalOverlapCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual eigenbasis/Gaussian disorder and the ordinary spin overlap
specialize the finite-cavity scalar-field identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem restricted_physical_overlap_cutoff (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (S : (n : ℕ) → Finset (Spin (N n))) (hS : ∀ n, (S n).Nonempty)
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
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (T : Finset (Spin kspin)) (hT : T.Nonempty)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean
          ((restrictedRotationProbability (S n) (hS n) (eigN n)
            (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n) ω.1).prod
            (restrictedSpinPrior T hT))
          (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors (dims n) (E n))
            (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1)))
          ∂(((μ n).prod (θ n)).prod gaussianCoordinates).prod (Measure.pi (μG n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) ∂pathMeasure| < ε := by
  intro p K L Cspin τ
  let I n := cavitySpectralGroup (fun i => ((E n).symm i).1)
  let Ω n := (Orthogonal (N n) × LabeledTree (depth n)) × (ℕ → ℝ)
  let X n := Spin (N n) × LabeledLeaf (depth n)
  let P n := ((μ n).prod (θ n)).prod gaussianCoordinates
  let ν n := restrictedRotationProbability (S n) (hS n) (depth := depth n) (eigN n) (I n) (u n)
  let B n := cavityRotationEntry (depth := depth n) (I n)
  let Q n := restrictedRotationArrayLaw (S n) (hS n) (μ n) (θ n) (eigN n) (I n) (u n)
  have hρs n a : 0 < (dims n a : ℝ)/N n :=
    div_pos (Nat.cast_pos.mpr (hgroups n a)) (Nat.cast_pos.mpr (hN n))
  have hh := restricted_haar_finite_overlap_cutoff hpub dims hdims μG A₀ hA₀ Ω X P ν
    (fun n => measurable_restrictedRotationProbability _ _ _ _ _) B
    (fun n => measurable_cavityRotationEntry (I n))
    (fun n => cavityRotationEntry_gram (I n))
    (fun n => cavityRotationVectors (dims n) (E n))
    (fun n => measurable_cavityRotationVectors (dims n) (E n)) (1/c)
    (fun s n x => cavityRotationVectors_gram_bound (r := s) (hN n) (dims n) (E n) x hc (hcG n))
    (fun n a => (dims n a : ℝ)/N n) ρ eig hρs hρ hρlim hρsum
    (fun s n x => cavityRotationVectors_covariance (r := s) (hN n) (dims n) (E n) x q)
    Q Q₀ (fun _ => rfl) hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    hgroups (div_nonneg zero_le_one hc.le) hdim hkspin T hT B₀ hB₀ hBE hcomplete a ha Φ hΦ hΦb
    b hb hblim hnull
  dsimp only at hh
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  filter_upwards [hj] with n hn'
  have htest (ω : Ω n × ((a : Fin m) → Orthogonal (dims n a))) : cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1)
      (cavityOverlapObservable Φ hΦ) =
      (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))) := by
    funext σ
    exact cavity_physical_overlap_observable (fun i => ((E n).symm i).1) ω.1 Φ hΦ σ
  simpa only [htest] using hn'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedOriginalOverlapLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full model, including the original random tree and both
perturbations, has the scalar-field two-spin limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem restricted_original_split_overlap_limit_oai (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    {M₀ : ℝ} (hmean : ∀ j (T : LabeledTree (depth j)), restrictedCavityFullDisorderTest
      (cavityProductSlice (S j) Cset) (cavityProductSlice_nonempty (S j) (hS j) Cset hCset)
      ((μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))) T
      (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
      (cavitySpectralGroup (g j)) (u j)
      (cavityProjectionAxesTest (cavitySpectralGroup (g j)) (Fin.natAdd (N j))) ≤ M₀)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A : CavityFactorBlocks d n)
    (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => restrictedRotationArrayLaw (S j) (hS j) (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (Φ : ℝ →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r =>
      (∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset) ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r) -
      ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
  let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
    (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) 1
  let B := cavityCompressionLimitFrame es B₀
  let F := fun j (σ : Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) =>
    Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  have hF j σ : |F j σ| ≤ ‖Φ‖ := by
    simpa only [F,abs_mul,abs_spinValue,mul_one,one_mul,Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  obtain ⟨b,hblim,hb⟩ := cavity_spectral_common_cutoff_radii Q₀ ρ (fun i : Fin d => (a₀ i,i))
  have hbpos j := (hb j).1
  have hnull j r := (hb j).2 r
  have hfinite := restricted_physical_overlap_cutoff hpub N depth hN S hS
    (fun j => cavityBaseGroupDimension (k j) a₀) hgroups hdims E ν θ μG
    (fun j => cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (fun j a => cavityCanonicalGroupFrame_gram (k j) (e j) a₀ (hk j) a)
    eig u hc hcG ρ lam hρ hρsum hρlim Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a₀ (fun i => (a₀ i,i)) (fun i j hij => congrArg Prod.snd hij) (fun _ => rfl)
    hd hn Cset hCset B (cavityCompressionLimitFrame_gram es B₀ hB₀)
    (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
    (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
    a ha Φ Φ.continuous (fun x => by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm x)
    b hbpos hblim hnull
  have horig := restricted_original_full_haar_comparison N depth S hS Cset hCset hN hNlim g k ek e es B₀ a₀ hk
    (fun j => Measure.pi (μG j)) l w hg hln hw μ ν θ lam v hv u hu 1 hmean good hgood hp hL hbound
    (norm_nonneg Φ) F hF A hprob b hbpos hblim
  dsimp only at hfinite horig
  rw [hA] at horig
  simp only [one_smul] at horig
  let cut := fun j r => ∫ ω, cavityWeightedReplicaMean
    ((restrictedRotationProbability (S r) (hS r) (eig r) (cavitySpectralGroup (fun i => ((E r).symm i).1))
      (u r) ω.1).prod (restrictedSpinPrior Cset hCset))
    (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
      (cavityRotationVectors (cavityBaseGroupDimension (k r) a₀) (E r))
      (cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r))
      A.1 A.2.1 A.2.2 (cavityFactorSize A.1 A.2.1 A.2.2*(1+(b j)^2)) (b j) (ω,x)) (F r)
    ∂(((ν r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))
  let full := fun r => ∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset)
    ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
    (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
    (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r
  let scalar := fun r => ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hjO,hjF⟩ := ((horig (ε/2) (by positivity)).and
    (hfinite (ε/2) (by positivity))).exists
  filter_upwards [hjO,hjF] with r hrO hrF
  have hrO' : |full r-cut j r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrO
  have hrF' : |cut j r-scalar r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrF
  rw [Real.dist_eq,sub_zero]
  exact (abs_sub_le (full r) (cut j r) (scalar r)).trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.restricted_original_split_overlap_limit_oai := @OAI.InvariantIsing.restricted_original_split_overlap_limit_oai
