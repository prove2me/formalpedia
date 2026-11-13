-- Prove2me | solution 1 for OAI.InvariantIsing.random_pressure_limit_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:03:46.840003+00:00
-- url     : https://prove2.me/submissions/93684ea1-247e-46c3-806a-49afd61641f4

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
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
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved
import Theorems.Thm_OAI_InvariantIsing_haarPolynomialMoment_log_bound
import Theorems.Thm_OAI_InvariantIsing_panchenkoTalagrandFieldPair_proved
import Theorems.Thm_OAI_InvariantIsing_selected_spectral_pressure_tendsto

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
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

/-- Equation (6.6), pointwise in the rotation and independent of the field. -/
lemma abs_rotatedPressure_sub_le {N : ℕ} (hN : 0 < N)
    (eig κ : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) :
    |rotatedPressure eig U c - rotatedPressure κ U c| ≤ δ / 2 := by
  have h := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)
    (δ * N / 2) (fun σ => by
      simpa only [add_sub_add_right_eq_sub] using abs_rotatedEnergy_sub_le eig κ U δ hδ σ)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ = (N : ℝ)⁻¹ * |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) -
        logPartition (fun σ => rotatedEnergy κ U σ + fieldEnergy c σ)| := by
      rw [rotatedPressure, rotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (δ * N / 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = δ / 2 := by field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureLipschitz
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frobenius continuity of Haar pressure

The Lipschitz constant is independent of dimension and of a deterministic
magnetic field. This is the finite-volume estimate required to apply the
published SO(N) concentration input.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma specialRotation_spin_dist_sq_le {N : ℕ} (U V : SpecialOrthogonal N)
    (σ : Spin N) :
    (∑ i, (specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i) ^ 2) ≤
      (N : ℝ) * frobeniusDistance U V ^ 2 := by
  have he (i : Fin N) : specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i =
      ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j -
        (V : Matrix (Fin N) (Fin N) ℝ) i j) * spinValue (σ j) := by
    simp only [specialRotation_apply, spinVector_apply, sub_mul, Finset.sum_sub_distrib]
  have hrow (i : Fin N) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (U : Matrix (Fin N) (Fin N) ℝ) i j -
      (V : Matrix (Fin N) (Fin N) ℝ) i j) (fun j => spinValue (σ j))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Finset.sum_mul] at hsum
  simp_rw [he]
  rw [frobeniusDistance, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  nlinarith

lemma abs_rotatedEnergy_sub_rotation_le {N : ℕ} (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (K : ℝ) (hK : 0 ≤ K)
    (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ| ≤
      K * N * frobeniusDistance U V := by
  let x := specialRotation U (spinVector σ)
  let y := specialRotation V (spinVector σ)
  let d := frobeniusDistance U V
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hx : ∑ i, x i ^ 2 = N := rotated_spin_sq_sum _ _
  have hy : ∑ i, y i ^ 2 = N := rotated_spin_sq_sum _ _
  have hm : (∑ i, (x i - y i) ^ 2) ≤ (N : ℝ) * d ^ 2 :=
    specialRotation_spin_dist_sq_le U V σ
  have hp : (∑ i, (x i + y i) ^ 2) ≤ 4 * (N : ℝ) := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (x i + y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2 by
        nlinarith [sq_nonneg (x i - y i)])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy] at hi
    linarith
  have hw : (∑ i, (eig i * (x i - y i)) ^ 2) ≤
      K ^ 2 * ∑ i, (x i - y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    have hb : eig i ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (heig i)
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => eig i * (x i - y i)) (fun i => x i + y i)
  have hs : (∑ i, (eig i * (x i - y i)) * (x i + y i)) ^ 2 ≤
      (2 * K * (N : ℝ) * d) ^ 2 := by
    calc
      _ ≤ (∑ i, (eig i * (x i - y i)) ^ 2) * ∑ i, (x i + y i) ^ 2 := hcs
      _ ≤ (K ^ 2 * ∑ i, (x i - y i) ^ 2) * (4 * (N : ℝ)) :=
        mul_le_mul hw hp (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ ≤ (K ^ 2 * ((N : ℝ) * d ^ 2)) * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
          (by positivity)
      _ = _ := by ring
  have ha : |∑ i, (eig i * (x i - y i)) * (x i + y i)| ≤
      2 * K * (N : ℝ) * d := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  have he : rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ =
      (1 / 2 : ℝ) * ∑ i, (eig i * (x i - y i)) * (x i + y i) := by
    rw [rotatedEnergy, rotatedEnergy, ← mul_sub, ← Finset.sum_sub_distrib]
    change (1 / 2 : ℝ) * (∑ i, (eig i * x i ^ 2 - eig i * y i ^ 2)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_eq (by dsimp [d] <;> ring)

lemma abs_rotatedPressure_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U V : SpecialOrthogonal N) (c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedPressure eig (specialRotation U) c -
      rotatedPressure eig (specialRotation V) c| ≤ K * frobeniusDistance U V := by
  have h := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)
    (K * N * frobeniusDistance U V) (fun σ => by
      simpa only [add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig σ)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ = (N : ℝ)⁻¹ * |logPartition (fun σ =>
        rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) -
        logPartition (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)| := by
      rw [rotatedPressure, rotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (K * N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = K * frobeniusDistance U V := by field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_Concentration
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar concentration for Ising pressure

Frobenius Lipschitz continuity and measurability give concentration of the
Ising pressure about a median.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma measurable_rotatedPressure {N : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c) := by
  have hE (σ : Spin N) : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul
        (eig i)).const_mul (1 / 2 : ℝ)).add_const _
  unfold rotatedPressure logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log.const_mul (N : ℝ)⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_AlmostSure
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Almost-sure concentration without independence across dimensions

A countable Borel–Cantelli argument upgrades Haar tails to almost-sure
concentration of the pressure about its medians.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace InvariantIsing

/-- Summable exponential tails imply almost-sure convergence to zero. No
independence between the random variables is required. -/
lemma ae_tendsto_zero_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, μ.real {ω | ε ≤ |f n ω|} ≤ C * Real.exp (-a * (n : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have hb (k : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ¬ (1 / (k + 1 : ℝ) ≤ |f n ω|) := by
    have hk : 0 < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨C, a, hC, ha, ht⟩ := htail _ hk
    have hsum : Summable (fun n : ℕ => C * Real.exp (-a * (n : ℝ))) := by
      simp_rw [mul_comm (-a), Real.exp_nat_mul]
      exact (summable_geometric_of_lt_one (Real.exp_pos (-a)).le
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))).mul_left C
    let q : ℕ → ℝ≥0 := fun n => NNReal.mk (C * Real.exp (-a * (n : ℝ)))
      (mul_nonneg hC (Real.exp_pos _).le)
    have hq : Summable q := (NNReal.summable_coe (f := q)).mp hsum
    have hfinite : (∑' n, (q n : ENNReal)) ≠ ∞ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
    have hbound (n : ℕ) : μ {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|} ≤ (q n : ENNReal) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|})]
      change ENNReal.ofReal (μ.real {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|}) ≤ _
      simpa only [q, ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC (Real.exp_pos _).le)] using
        ENNReal.ofReal_le_ofReal (ht n)
    exact ae_eventually_notMem (s := fun n => {ω | 1 / (k + 1 : ℝ) ≤ |f n ω|})
      (ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum hbound))
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Real.dist_eq, sub_zero] using lt_trans (lt_of_not_ge (hN n hn)) hk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_MedianMean
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relating the deterministic medians and means in the concentration step. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma abs_median_le_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (m B : ℝ)
    (hB : ∀ ω, |f ω| ≤ B)
    (hl : (1 / 2 : ℝ) ≤ μ.real {ω | f ω ≤ m})
    (hu : (1 / 2 : ℝ) ≤ μ.real {ω | m ≤ f ω}) : |m| ≤ B := by
  apply abs_le.mpr
  constructor
  · by_contra h
    have hm : m < -B := lt_of_not_ge h
    have he : {ω | f ω ≤ m} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      change f ω ≤ m at hω
      have hf := (abs_le.mp (hB ω)).1
      linarith
    rw [he] at hl
    norm_num at hl
  · by_contra h
    have hm : B < m := lt_of_not_ge h
    have he : {ω | m ≤ f ω} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      change m ≤ f ω at hω
      have hf := (abs_le.mp (hB ω)).2
      linarith
    rw [he] at hu
    norm_num at hu

/-- A bounded deviation has mean at most r plus its bound times the r-tail. -/
lemma abs_integral_sub_le_deviation_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) (m B r : ℝ) (hr : 0 ≤ r)
    (hB : ∀ ω, |f ω - m| ≤ B) :
    |(∫ ω, f ω ∂μ) - m| ≤ r + B * μ.real {ω | r ≤ |f ω - m|} := by
  let A : Set Ω := {ω | r ≤ |f ω - m|}
  have hA : MeasurableSet A := measurableSet_le measurable_const (hf.sub_const m).abs
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have hupper : Integrable (fun ω => r + B * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const r).add (hiA.const_mul B)
  have he (ω : Ω) : |f ω - m| ≤ r + B * A.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      linarith [hB ω]
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact (lt_of_not_ge hω).le
  calc
    _ = |∫ ω, f ω - m ∂μ| := by rw [integral_sub hfi (integrable_const m)]; simp
    _ ≤ ∫ ω, |f ω - m| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => f ω - m)
    _ ≤ ∫ ω, r + B * A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_mono (hfi.sub (integrable_const m)).abs hupper he
    _ = r + B * μ.real A := by
      rw [integral_add (integrable_const r) (hiA.const_mul B), integral_const_mul,
        integral_indicator_const 1 hA]
      simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure concentration of the actual pressure about its expectation. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma rotatedPressure_zero {N : ℕ} (U : Rotation N) (c : Fin N → ℝ) :
    rotatedPressure (fun _ => 0) U c = noninteractingPressure c := by
  simp [rotatedPressure, rotatedEnergy, noninteractingPressure]

lemma abs_pressure_sub_noninteracting_le {N : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedPressure eig U c - noninteractingPressure c| ≤ K / 2 := by
  simpa only [sub_zero, rotatedPressure_zero] using
    abs_rotatedPressure_sub_le hN eig (fun _ => 0) U c K (fun i => by simpa using heig i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCountComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pressure comparison from the fractions of changed axes in the two
endpoint eigenspaces. This is the analytic part of manuscript Lemma gen:counts. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_countPressure {N : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c) := by
  exact measurable_rotatedPressure eig c

lemma integrable_countPressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig c : Fin N → ℝ) (K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    Integrable (fun U => rotatedPressure eig (specialRotation U) c) μ := by
  apply (integrable_const (K / 2 + |noninteractingPressure c|)).mono'
    (measurable_countPressure eig c).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs]
  have hb := abs_pressure_sub_noninteracting_le hN eig c (specialRotation U) K heig
  have ha := abs_add_le (rotatedPressure eig (specialRotation U) c - noninteractingPressure c)
    (noninteractingPressure c)
  rw [sub_add_cancel] at ha
  exact ha.trans (add_le_add hb le_rfl)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete base-rotation array is exactly the namespaced tensor
array after orienting its inverse eigenbasis. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityOrientedBaseLaw_preserving {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) :
    MeasurePreserving (fun V => cavityOrientationLift hN V⁻¹) μ (cavityOrientedBaseLaw hN μ) :=
  ⟨(measurable_cavityOrientationLift hN).comp measurable_inv, rfl⟩

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An all-size version of the oriented physical law. The zero-dimensional
case is only a harmless placeholder for sequences indexed by all naturals. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_oriented_pressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) (eig c : Fin N → ℝ) :
    (∫ U, rotatedPressure eig (specialRotation U) c ∂cavityOrientedBaseLaw hN μ) =
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ := by
  calc
    _ = ∫ V, rotatedPressure eig
        (specialRotation (cavityOrientationLift hN V⁻¹)) c ∂μ :=
      ((cavityOrientedBaseLaw_preserving hN μ).hasLaw.integral_comp
        (measurable_rotatedPressure eig c).aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun V => by
        simp only [rotatedPressure, cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ProbabilityMedian
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of a median for every real probability law, including laws with atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem probability_real_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ m : ℝ, (1/2:ℝ) ≤ ν.real (Iic m) ∧ (1/2:ℝ) ≤ ν.real (Ici m) := by
  let F := cdf ν
  let S : Set ℝ := {x | (1/2:ℝ) ≤ F x}
  have htop : ∃ x : ℝ, (1/2:ℝ) < F x := by
    have h := (tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))
    exact h.exists
  have hbot : ∃ x : ℝ, F x < (1/2:ℝ) := by
    have h := (tendsto_cdf_atBot ν).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    exact h.exists
  obtain ⟨b,hb⟩ := hbot
  have hne : S.Nonempty := by obtain ⟨x,hx⟩ := htop; exact ⟨x,hx.le⟩
  have hbb : BddBelow S := by
    refine ⟨b,?_⟩
    intro x hx
    by_contra h
    have hm := (monotone_cdf ν) (le_of_not_ge h)
    change (1/2:ℝ) ≤ F x at hx
    exact (not_le_of_gt hb) (hx.trans hm)
  let m := sInf S
  have hright (x : ℝ) (hx : m < x) : (1/2:ℝ) ≤ F x := by
    obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hne hx
    exact hy.trans ((monotone_cdf ν) hyx.le)
  have hleft (x : ℝ) (hx : x < m) : F x < (1/2:ℝ) := by
    by_contra h
    have hxS : x ∈ S := le_of_not_gt h
    exact (not_le_of_gt hx) (csInf_le hbb hxS)
  have hfm : (1/2:ℝ) ≤ F m := by
    apply ge_of_tendsto ((F.right_continuous m).mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hfl : Function.leftLim F m ≤ (1/2:ℝ) := by
    apply le_of_tendsto (F.mono.tendsto_leftLim m)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  refine ⟨m,?_,?_⟩
  · simpa only [F,cdf_eq_real] using hfm
  · have he : ν (Ici m) = ENNReal.ofReal (1-Function.leftLim F m) := by
      rw [← measure_cdf ν]
      exact (cdf ν).measure_Ici (tendsto_cdf_atTop ν) m
    rw [Measure.real,he,ENNReal.toReal_ofReal (by linarith)]
    linarith

theorem measurable_median {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m} ∧ (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω} := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨m,hm1,hm2⟩ := probability_real_median (μ.map f)
  refine ⟨m,?_,?_⟩
  · rw [map_measureReal_apply hf measurableSet_Iic] at hm1
    exact hm1
  · rw [map_measureReal_apply hf measurableSet_Ici] at hm2
    exact hm2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMedianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of two Gaussian tails about a center to tails about any median. -/
noncomputable section
open MeasureTheory Set
namespace InvariantIsing

theorem gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (c m k : ℝ) (hk : 0 < k)
    (hm1 : (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m})
    (hm2 : (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω})
    (hplus : ∀ r > 0, μ.real {ω | r ≤ f ω-c} ≤ Real.exp (-k*r^2))
    (hminus : ∀ r > 0, μ.real {ω | r ≤ c-f ω} ≤ Real.exp (-k*r^2))
    {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |f ω-m|} ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
  let a := Real.sqrt (2/k)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (by norm_num) hk)
  have ha2 : a^2 = 2/k := Real.sq_sqrt (div_pos (by norm_num) hk).le
  have hka : k*a^2 = 2 := by rw [ha2]; field_simp
  have hexp : Real.exp (-2) < (1/2:ℝ) := by
    have he := Real.add_one_le_exp (2:ℝ)
    have hp := Real.exp_pos (-2)
    have hm : Real.exp (-2)*Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hpa : μ.real {ω | a ≤ f ω-c} < (1/2:ℝ) := by
    have h := hplus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hma : μ.real {ω | a ≤ c-f ω} < (1/2:ℝ) := by
    have h := hminus a ha
    have he : -k*a^2 = -(2:ℝ) := by nlinarith [hka]
    rw [he] at h
    exact h.trans_lt hexp
  have hmc : |m-c| ≤ a := by
    apply abs_le.mpr
    constructor
    · by_contra h
      have hs : {ω | f ω ≤ m} ⊆ {ω | a ≤ c-f ω} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm1.trans (measureReal_mono hs))) hma
    · by_contra h
      have hs : {ω | m ≤ f ω} ⊆ {ω | a ≤ f ω-c} := by
        intro ω hω
        simp only [mem_ofPred_eq] at *
        linarith
      exact (not_lt_of_ge (hm2.trans (measureReal_mono hs))) hpa
  by_cases hsmall : r ≤ 2*a
  · have hkr : k*r^2/8 ≤ 1 := by
      have hsq : r^2 ≤ 4*a^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq hk.le
      nlinarith [hka]
    have hex : 1 ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    exact measureReal_le_one.trans hex
  · have hhalf : 0 < r/2 := half_pos hr
    have hs : {ω | r ≤ |f ω-m|} ⊆ {ω | r/2 ≤ |f ω-c|} := by
      intro ω hω
      have htri : |f ω-m| ≤ |f ω-c|+|m-c| := by
        simpa only [sub_add_sub_cancel,abs_sub_comm c m] using abs_add_le (f ω-c) (c-m)
      simp only [mem_ofPred_eq] at *
      linarith
    have he : {ω | r/2 ≤ |f ω-c|} =
        {ω | r/2 ≤ f ω-c} ∪ {ω | r/2 ≤ c-f ω} := by
      ext ω
      simp only [mem_ofPred_eq,mem_union,le_abs,neg_sub]
    have ht : μ.real {ω | r/2 ≤ |f ω-c|} ≤ 2*Real.exp (-k*(r/2)^2) := by
      rw [he]
      have hu := measureReal_union_le (μ := μ) {ω | r/2 ≤ f ω-c} {ω | r/2 ≤ c-f ω}
      linarith [hplus (r/2) hhalf,hminus (r/2) hhalf]
    calc
      _ ≤ μ.real {ω | r/2 ≤ |f ω-c|} := measureReal_mono hs
      _ ≤ 2*Real.exp (-k*(r/2)^2) := ht
      _ ≤ Real.exp 1*Real.exp (-k*r^2/8) := by
        apply mul_le_mul
        · simpa only [show (1:ℝ)+1=2 by norm_num] using Real.add_one_le_exp (1:ℝ)
        · apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg hk.le (sq_nonneg r)]
        · exact (Real.exp_pos _).le
        · exact (Real.exp_pos _).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_DerivativeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A derivative comparison obtained from pointwise increments. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

theorem norm_derivative_le_of_increment_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {x L : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h : ∀ t, ‖f t-f x‖ ≤ L*‖g t-g x‖) : ‖f'‖ ≤ L*‖g'‖ := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.norm (hg.tendsto_slope.norm.const_mul L)
  apply Eventually.of_forall
  intro t
  simp only [slope_def_module,norm_smul]
  calc
    ‖(t-x)⁻¹‖*‖f t-f x‖ ≤ ‖(t-x)⁻¹‖*(L*‖g t-g x‖) :=
      mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)
    _ = L*(‖(t-x)⁻¹‖*‖g t-g x‖) := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Frobenius bracket contraction for the special orthogonal algebra. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma matrixFrobeniusPair_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A A = ∑ i, ∑ j, (A i j)^2 := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply,pow_two]
  exact Finset.sum_comm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneFrame
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-plane frame identities in the skew matrix space. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_swap {N : ℕ} (i j : Fin N) :
    planeGenerator j i = -planeGenerator i j := by
  simp only [planeGenerator,neg_sub]

lemma sum_entry_planeGenerator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, A i j • planeGenerator i j) = A-A.transpose := by
  classical
  ext k l
  simp only [Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    planeGenerator,Matrix.single_apply,mul_sub,Finset.sum_sub_distrib]
  simp [ite_and,Matrix.transpose_apply]

lemma matrixFrobeniusPair_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A B = ∑ i, ∑ j, A i j*B i j := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

/-- A linear functional on skew matrices is represented by its plane coordinates. -/
lemma plane_functional_representation {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.transpose = -B) :
    matrixFrobeniusPair (Matrix.of fun i j => ell (planeGenerator i j)) B = 2*ell B := by
  have h := congrArg ell (sum_entry_planeGenerator B)
  simp only [map_sum,map_smul,map_sub,hB,map_neg,smul_eq_mul] at h
  rw [matrixFrobeniusPair_eq_sum]
  calc
    (∑ i, ∑ j, ell (planeGenerator i j)*B i j) =
        ∑ i, ∑ j, B i j*ell (planeGenerator i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    _ = 2*ell B := by linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurve
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixPolynomialOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of polynomial Lie derivatives on genuine matrix curves. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

theorem hasDerivAt_matrixPolynomialEval {N : ℕ}
    (p : MatrixPolynomial N) (M : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) ((A*M t) i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (M s) p)
      (matrixPolynomialEval (M t) (matrixPolynomialDerivation A p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq =>
    convert hp.add hq using 1
    all_goals try with_reducible_and_instances rfl
    all_goals simp only [map_add]
    all_goals rfl
  | mul_X p ij hp =>
    rcases ij with ⟨i,j⟩
    have hx : matrixPolynomialEval (M t)
        (matrixPolynomialDerivation A (X (i,j))) = (A*M t) i j := by
      simp only [matrixPolynomialDerivation_X,map_sum,map_smul,
        matrixPolynomialEval_X,smul_eq_mul,Matrix.mul_apply]
    convert hp.mul (hM i j) using 1
    all_goals try with_reducible_and_instances rfl
    · simp only [map_mul,matrixPolynomialEval_X]
      rfl
    · rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,
        hx,matrixPolynomialEval_X]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarContinuousDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact domination for continuous derivatives along actual Haar rotations. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

lemma continuous_haar_integrable {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable B
    (ae_of_all μ fun U => hB U (Set.mem_univ U))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial averaging kernels on the actual special orthogonal group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarKernelAtom {N : ℕ} (a : Option (Fin N × Fin N)) :
    Continuous (fun V : SpecialOrthogonal N => haarKernelAtom V a) := by
  cases a with
  | none => exact continuous_const
  | some ij =>
    exact (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val)

lemma haarKernelBase_sum {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = ∑ a : Option (Fin N × Fin N),
      haarKernelAtom V a * haarPolynomialValue (haarPolynomialAtom a) U := by
  simp only [Fintype.sum_option,haarKernelAtom,haarPolynomialAtom,
    haarPolynomialValue,map_one,mul_one,matrixPolynomialEval_X,Fintype.sum_prod_type]
  unfold haarKernelBase
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem haarKernelAverage_value {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f V * (haarKernelBase U V)^n ∂μ := by
  have hi (w : Fin n → Option (Fin N × Fin N)) :
      Integrable (fun V => f V * ∏ k, haarKernelAtom V (w k)) μ :=
    continuous_haar_integrable μ _ (hf.mul (continuous_finsetProd _ fun k _ =>
      continuous_haarKernelAtom (w k)))
  simp only [haarKernelAverage,haarPolynomialValue,map_sum,map_smul,
    smul_eq_mul,haarPolynomialWord,map_prod]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun w _ => (hi w).mul_const _)]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    change (∑ w : Fin n → Option (Fin N × Fin N),
      (f V * ∏ k, haarKernelAtom V (w k)) *
        ∏ k, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (haarPolynomialAtom (w k))) =
      f V * haarKernelBase U V ^ n
    rw [haarKernelBase_sum,Fintype.sum_pow]
    simp only [Finset.mul_sum,Finset.prod_mul_distrib,mul_assoc]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaging kernel peaks exactly at coincident orthogonal matrices. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma specialOrthogonal_sum_sq {N : ℕ} (U : SpecialOrthogonal N) :
    (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j)^2) = N := by
  rw [← matrixFrobeniusPair_self]
  unfold matrixFrobeniusPair
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1]
  simp

lemma haarKernelBase_dist {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = 2*N-(frobeniusDistance U V)^2/2 := by
  have hU := specialOrthogonal_sum_sq U
  have hV := specialOrthogonal_sum_sq V
  rw [frobeniusDistance,Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  have hsum : (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j-
      (V : Matrix (Fin N) (Fin N) ℝ) i j)^2) = 2*N-
      2*(∑ i, ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j*
        (V : Matrix (Fin N) (Fin N) ℝ) i j) := by
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [hU,hV]
    ring
  rw [hsum]
  unfold haarKernelBase
  ring

lemma haarKernelBase_nonneg {N : ℕ} (U V : SpecialOrthogonal N) :
    0 ≤ haarKernelBase U V := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      sq_nonneg ((U : Matrix (Fin N) (Fin N) ℝ) i j+
        (V : Matrix (Fin N) (Fin N) ℝ) i j)))
  simp only [add_sq,Finset.sum_add_distrib] at h
  simp_rw [mul_assoc,← Finset.mul_sum] at h
  rw [specialOrthogonal_sum_sq U,specialOrthogonal_sum_sq V] at h
  unfold haarKernelBase
  linarith

lemma haarKernelBase_self {N : ℕ} (U : SpecialOrthogonal N) :
    haarKernelBase U U = 2*N := by
  unfold haarKernelBase
  simp_rw [← pow_two]
  rw [specialOrthogonal_sum_sq]
  ring

lemma haarKernelBase_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    haarKernelBase (W*U) (W*V) = haarKernelBase U V := by
  have he : matrixFrobeniusPair
      ((W : Matrix (Fin N) (Fin N) ℝ)*(U : Matrix (Fin N) (Fin N) ℝ))
      ((W : Matrix (Fin N) (Fin N) ℝ)*(V : Matrix (Fin N) (Fin N) ℝ)) =
      matrixFrobeniusPair (U : Matrix (Fin N) (Fin N) ℝ)
        (V : Matrix (Fin N) (Fin N) ℝ) := by
    unfold matrixFrobeniusPair
    rw [Matrix.transpose_mul,mul_assoc,← mul_assoc (W : Matrix (Fin N) (Fin N) ℝ).transpose,
      (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp W.property).1,one_mul]
  unfold haarKernelBase
  rw [← matrixFrobeniusPair_eq_sum,← matrixFrobeniusPair_eq_sum]
  exact congrArg (fun x : ℝ => N+x) he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized Frobenius geometry for the averaging and tangent estimates. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

lemma frobenius_norm_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖A‖^2 = matrixFrobeniusPair A A := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  have hs : 0 ≤ ∑ i : Fin N, ∑ j : Fin N, (A i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt hs,matrixFrobeniusPair_self]

lemma frobeniusDistance_eq_norm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = ‖(U : Matrix (Fin N) (Fin N) ℝ)-V‖ := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Matrix.sub_apply]
  exact Real.sqrt_eq_rpow _

lemma frobenius_norm_mul_orthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (U : SpecialOrthogonal N) : ‖A*(U : Matrix (Fin N) (Fin N) ℝ)‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq,frobenius_norm_sq]
  unfold matrixFrobeniusPair
  rw [Matrix.transpose_mul,Matrix.trace_mul_cycle]
  rw [mul_assoc A U (U : Matrix (Fin N) (Fin N) ℝ).transpose,
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1,mul_one,Matrix.trace_mul_comm]

lemma frobeniusDistance_mul_left {N : ℕ} (W U V : SpecialOrthogonal N) :
    frobeniusDistance (W*U) (W*V) = frobeniusDistance U V := by
  have h := congrArg (fun x : ℝ => 2*N-x) (haarKernelBase_mul_left W U V)
  rw [haarKernelBase_dist,haarKernelBase_dist] at h
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change (frobeniusDistance (W*U) (W*V))^2 = (frobeniusDistance U V)^2
  linarith

lemma frobeniusDistance_comm {N : ℕ} (U V : SpecialOrthogonal N) :
    frobeniusDistance U V = frobeniusDistance V U := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm,← norm_neg,neg_sub]

lemma frobeniusDistance_mul_right {N : ℕ} (U V W : SpecialOrthogonal N) :
    frobeniusDistance (U*W) (V*W) = frobeniusDistance U V := by
  rw [frobeniusDistance_eq_norm,frobeniusDistance_eq_norm]
  change ‖(U : Matrix (Fin N) (Fin N) ℝ)*W-(V : Matrix (Fin N) (Fin N) ℝ)*W‖ = _
  rw [← sub_mul,frobenius_norm_mul_orthogonal]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frobenius-Lipschitz observables are continuous in the matrix-group topology. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace InvariantIsing

lemma continuous_frobeniusDistance_right {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (fun V => frobeniusDistance V U) := by
  have he (i j : Fin N) : Continuous (fun V : SpecialOrthogonal N =>
      (V : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  unfold frobeniusDistance
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((he i j).sub continuous_const).pow 2

lemma frobeniusDistance_self {N : ℕ} (U : SpecialOrthogonal N) : frobeniusDistance U U = 0 := by
  simp [frobeniusDistance]

theorem continuous_of_frobenius_lipschitz {N : ℕ} (f : SpecialOrthogonal N → ℝ) (L : ℝ)
    (hf : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun V => norm_nonneg _) (fun V => by simpa only [Real.norm_eq_abs] using hf V U)
  have hh := ((continuous_frobeniusDistance_right U).tendsto U).const_mul L
  simpa only [frobeniusDistance_self,mul_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelConvolution
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar convolution by a positive polynomial kernel preserves Lipschitz constants. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarKernelBase {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (haarKernelBase U) := by
  unfold haarKernelBase
  apply continuous_const.add
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp
    ((continuous_apply i).comp continuous_subtype_val))

lemma haarKernelMass_pos {N : ℕ} (hN : 0 < N) (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    0 < haarKernelMass μ n := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : SpecialOrthogonal N))
    ((continuous_haarKernelBase 1).pow n)
    (continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n))
    (fun V => pow_nonneg (haarKernelBase_nonneg 1 V) n)
  change (haarKernelBase 1 1)^n ≠ 0
  rw [haarKernelBase_self]
  exact (pow_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hN)) n).ne'

lemma haarKernelAverage_convolution {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (f : SpecialOrthogonal N → ℝ)
    (hf : Continuous f) (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f (U*V)*(haarKernelBase 1 V)^n ∂μ := by
  rw [haarKernelAverage_value μ f hf]
  have h := integral_mul_left_eq_self (μ := μ)
    (fun V => f V*(haarKernelBase U V)^n) U
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    dsimp only
    rw [show haarKernelBase U (U*V) = haarKernelBase 1 V by
      simpa only [mul_one] using haarKernelBase_mul_left U 1 V]

theorem haarKernelApprox_lipschitz {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ)
    (hL : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) (n : ℕ)
    (U V : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-
      haarPolynomialValue (haarKernelApprox μ f n) V| ≤ L*frobeniusDistance U V := by
  have hZ := haarKernelMass_pos hN μ n
  let k (W : SpecialOrthogonal N) := (haarKernelBase 1 W)^n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi (U : SpecialOrthogonal N) : Integrable (fun W => f (U*W)*k W) μ :=
    continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
  have he (U : SpecialOrthogonal N) : haarPolynomialValue (haarKernelApprox μ f n) U =
      (haarKernelMass μ n)⁻¹*(∫ W, f (U*W)*k W ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change (haarKernelMass μ n)⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U = _
    rw [haarKernelAverage_convolution μ f hf]
  rw [he U,he V,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hZ),← integral_sub (hi U) (hi V)]
  apply (inv_mul_le_iff₀ hZ).mpr
  calc
    |∫ W, (f (U*W)*k W-f (V*W)*k W) ∂μ| ≤
        ∫ W, |f (U*W)*k W-f (V*W)*k W| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ W, (L*frobeniusDistance U V)*k W ∂μ := by
      apply integral_mono
      · exact ((hi U).sub (hi V)).abs
      · exact (continuous_haar_integrable μ _ hk).const_mul _
      · intro W
        dsimp only
        rw [← sub_mul,abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 W) n)]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (haarKernelBase_nonneg 1 W) n)
        exact (hL (U*W) (V*W)).trans_eq (by rw [frobeniusDistance_mul_right])
    _ = haarKernelMass μ n*(L*frobeniusDistance U V) := by
      rw [integral_const_mul,mul_comm]
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelMass
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative concentration of the positive polynomial kernels near the identity. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

lemma haarKernelMass_lower {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    μ.real {V | b < haarKernelBase 1 V} * b^n ≤ haarKernelMass μ n := by
  let S : Set (SpecialOrthogonal N) := {V | b < haarKernelBase 1 V}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (continuous_haarKernelBase 1).measurable
  have hi : Integrable (S.indicator (fun _ => b^n)) μ := (integrable_const _).indicator hS
  have hk := continuous_haar_integrable μ _ ((continuous_haarKernelBase 1).pow n)
  have hle : (∫ V, S.indicator (fun _ => b^n) V ∂μ) ≤ haarKernelMass μ n := by
    apply integral_mono hi hk
    intro V
    by_cases hV : V ∈ S
    · rw [Set.indicator_of_mem hV]
      exact pow_le_pow_left₀ hb hV.le n
    · rw [Set.indicator_of_notMem hV]
      exact pow_nonneg (haarKernelBase_nonneg 1 V) n
  simpa only [integral_indicator_const _ hS,smul_eq_mul] using hle

lemma haarKernel_superlevel_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] {b : ℝ} (hb : b < 2*N) :
    0 < μ.real {V | b < haarKernelBase 1 V} := by
  have hm : 0 < μ {V | b < haarKernelBase 1 V} := IsOpen.measure_pos μ
    (isOpen_lt continuous_const (continuous_haarKernelBase 1))
    ⟨1,by simpa only [mem_ofPred_eq,haarKernelBase_self] using hb⟩
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top μ _)

theorem haarKernelMass_ratio_tendsto_zero {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a : ℝ) (ha : 0 ≤ a) (haN : a < 2*N) :
    Tendsto (fun n : ℕ => a^n/haarKernelMass μ n) atTop (𝓝 0) := by
  let b := (a+2*N)/2
  have hab : a < b := by dsimp [b] <;> linarith
  have hbN : b < 2*N := by dsimp [b] <;> linarith
  have hb : 0 < b := ha.trans_lt hab
  let m := μ.real {V | b < haarKernelBase 1 V}
  have hm : 0 < m := haarKernel_superlevel_pos μ hbN
  have hr : a/b < 1 := (div_lt_one hb).mpr hab
  have hlim : Tendsto (fun n : ℕ => (a/b)^n/m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le) hr).div_const m
  apply squeeze_zero (fun n => div_nonneg (pow_nonneg ha n) (haarKernelMass_pos hN μ n).le) _ hlim
  intro n
  have hl := haarKernelMass_lower μ b hb.le n
  have hZ := haarKernelMass_pos hN μ n
  have hp := pow_pos hb n
  rw [div_pow]
  apply (div_le_div_iff₀ hZ hm).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  calc
    (a^n*m)*b^n = a^n*(m*b^n) := by ring
    _ ≤ a^n*haarKernelMass μ n := mul_le_mul_of_nonneg_left hl (pow_nonneg ha n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelApproximation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixPolynomialOperator_apply _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform approximation by positive polynomial Haar convolution. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem haarKernelApprox_error {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (B ε a : ℝ)
    (hB : 0 ≤ B) (hfB : ∀ V, |f V| ≤ B) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hloc : ∀ U V, a < haarKernelBase 1 V → |f (U*V)-f U| ≤ ε)
    (n : ℕ) (U : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤
      ε+2*B*(a^n/haarKernelMass μ n) := by
  let Z := haarKernelMass μ n
  let k (V : SpecialOrthogonal N) := (haarKernelBase 1 V)^n
  have hZ : 0 < Z := haarKernelMass_pos hN μ n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi : Integrable (fun V => (f (U*V)-f U)*k V) μ :=
    continuous_haar_integrable μ _ (((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).mul hk)
  have he : haarPolynomialValue (haarKernelApprox μ f n) U-f U =
      Z⁻¹*(∫ V, (f (U*V)-f U)*k V ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change Z⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U-f U = _
    rw [haarKernelAverage_convolution μ f hf]
    have he' : (∫ V, (f (U*V)-f U)*k V ∂μ) =
        (∫ V, f (U*V)*k V ∂μ)-f U*Z := by
      simp_rw [sub_mul]
      have hi1 : Integrable (fun V => f (U*V)*k V) μ :=
        continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
      have hi2 : Integrable (fun V => f U*k V) μ :=
        (continuous_haar_integrable μ _ hk).const_mul (f U)
      rw [integral_sub hi1 hi2,integral_const_mul]
      rfl
    rw [he']
    dsimp only [k]
    field_simp
  have hb (V : SpecialOrthogonal N) :
      |(f (U*V)-f U)*k V| ≤ ε*k V+2*B*a^n := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 V) n)]
    by_cases hV : a < haarKernelBase 1 V
    · have hh := mul_le_mul_of_nonneg_right (hloc U V hV)
        (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      have ht : 0 ≤ 2*B*a^n := by positivity
      exact hh.trans (le_add_of_nonneg_right ht)
    · have hbd : |f (U*V)-f U| ≤ 2*B := (abs_sub (f (U*V)) (f U)).trans (by linarith [hfB (U*V),hfB U])
      have hpow : k V ≤ a^n := pow_le_pow_left₀ (haarKernelBase_nonneg 1 V) (le_of_not_gt hV) n
      have hh := mul_le_mul hbd hpow (pow_nonneg (haarKernelBase_nonneg 1 V) n) (by positivity : 0 ≤ 2*B)
      have ht : 0 ≤ ε*k V := mul_nonneg hε (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      exact hh.trans (le_add_of_nonneg_left ht)
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hZ)]
  have hI : |∫ V, (f (U*V)-f U)*k V ∂μ| ≤ ε*Z+2*B*a^n := by
    calc
      _ ≤ ∫ V, |(f (U*V)-f U)*k V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ V, ε*k V+2*B*a^n ∂μ :=
        integral_mono hi.abs (((continuous_haar_integrable μ _ hk).const_mul ε).add (integrable_const _)) hb
      _ = ε*Z+2*B*a^n := by
        rw [integral_add ((continuous_haar_integrable μ _ hk).const_mul ε) (integrable_const _),integral_const_mul]
        simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
        rfl
  calc
    _ ≤ Z⁻¹*(ε*Z+2*B*a^n) := mul_le_mul_of_nonneg_left hI (inv_pos.mpr hZ).le
    _ = ε+2*B*(a^n/Z) := by field_simp

theorem haarKernelApprox_uniform {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U,
      |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤ ε := by
  intro ε hε
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hfB (V : SpecialOrthogonal N) : |f V| ≤ B := by simpa only [Real.norm_eq_abs] using hB V (mem_univ V)
  have hB0 : 0 ≤ B := (abs_nonneg (f 1)).trans (hfB 1)
  let δ := ε/(2*L)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hL)
  have hδeq : L*δ = ε/2 := by dsimp [δ]; field_simp
  let a := max 0 (2*N-δ^2/2)
  have ha : 0 ≤ a := le_max_left _ _
  have haN : a < 2*N := max_lt (by positivity) (by nlinarith [sq_pos_of_pos hδ])
  have hloc (U V : SpecialOrthogonal N) (hV : a < haarKernelBase 1 V) :
      |f (U*V)-f U| ≤ ε/2 := by
    have hda : 2*N-δ^2/2 < haarKernelBase 1 V := (le_max_right _ _).trans_lt hV
    rw [haarKernelBase_dist] at hda
    have hd : frobeniusDistance 1 V < δ := by nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ((1 : Matrix (Fin N) (Fin N) ℝ) i j-(V : Matrix (Fin N) (Fin N) ℝ) i j)^2)]
    have hh := hLip (U*V) (U*1)
    rw [frobeniusDistance_mul_left,mul_one,frobeniusDistance_comm V 1] at hh
    have hh' := mul_lt_mul_of_pos_left hd hL
    rw [hδeq] at hh'
    exact hh.trans hh'.le
  have ht : Tendsto (fun n : ℕ => 2*B*(a^n/haarKernelMass μ n)) atTop (𝓝 0) := by
    simpa using (haarKernelMass_ratio_tendsto_zero hN μ a ha haN).const_mul (2*B)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))] with n hn U
  have hh := haarKernelApprox_error hN μ f hf B (ε/2) a hB0 hfB (by positivity) ha hloc n U
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFunctionalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of squared Lie brackets, with the precise dimension factor. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeFunctionalMatrix_skew {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (planeFunctionalMatrix ell).transpose = -planeFunctionalMatrix ell := by
  ext i j
  change ell (planeGenerator j i) = -ell (planeGenerator i j)
  rw [planeGenerator_swap,map_neg]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialSkewRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponentiating an arbitrary real skew matrix in the physical group. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Frobenius
namespace InvariantIsing

lemma hasDerivAt_specialSkewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) :
      Matrix (Fin N) (Fin N) ℝ)) (A*(U : Matrix (Fin N) (Fin N) ℝ)) 0 := by
  convert (hasDerivAt_exp_smul_const' A (0:ℝ)).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp only [zero_smul,NormedSpace.exp_zero,mul_one]

lemma hasDerivAt_specialSkewRotation_polynomial {N : ℕ} (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => matrixPolynomialEval
      ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation A p)) 0 := by
  have hd := hasDerivAt_specialSkewRotation A hA U
  have hh := hasDerivAt_matrixPolynomialEval p
    (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ))
    A 0 (fun i j => by
      rw [specialSkewRotation_zero,one_mul]
      convert (haarMatrixCoordinate i j).hasFDerivAt.comp_hasDerivAt 0 hd using 1 <;> rfl)
  simpa only [specialSkewRotation_zero,one_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Frobenius-Lipschitz polynomial has dimension-free carré-du-champ control. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

theorem haarPolynomial_direction_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    |matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
      (matrixPolynomialDerivation A p)| ≤ L*‖A‖ := by
  have hf := hasDerivAt_specialSkewRotation_polynomial p A hA U
  have hg := hasDerivAt_specialSkewRotation A hA U
  have hh := norm_derivative_le_of_increment_bound hf hg (fun t => by
    simpa only [specialSkewRotation_zero,one_mul,Real.norm_eq_abs,← frobeniusDistance_eq_norm,
      haarPolynomialValue]
      using hp (specialSkewRotation A hA t*U) U)
  simpa only [Real.norm_eq_abs,frobenius_norm_mul_orthogonal] using hh

theorem haarPolynomial_gamma_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hL : 0 ≤ L)
    (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarPolynomialGamma p p) U ≤ 4*L^2 := by
  let ell := matrixPolynomialDifferential p (U : Matrix (Fin N) (Fin N) ℝ)
  let A := planeFunctionalMatrix ell
  have hA : A.transpose = -A := planeFunctionalMatrix_skew ell
  have hrepr := plane_functional_representation ell A hA
  have hsq : ‖A‖^2 = haarPolynomialValue (haarPolynomialGamma p p) U := by
    rw [frobenius_norm_sq,matrixFrobeniusPair_self]
    simp only [A,planeFunctionalMatrix,haarPolynomialValue,haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  have he : ‖A‖^2 = 2*ell A := by
    rw [frobenius_norm_sq]
    exact hrepr
  have hd : |ell A| ≤ L*‖A‖ := haarPolynomial_direction_le_lipschitz p L hp U A hA
  have hn : ‖A‖ ≤ 2*L := by nlinarith [norm_nonneg A,le_abs_self (ell A)]
  rw [← hsq]
  nlinarith [norm_nonneg A]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments and their derivatives for polynomial observables on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialMoment_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    0 < haarPolynomialMoment μ p t :=
  integral_exp_pos (continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (continuous_haarPolynomialValue p))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarUniformMomentLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing polynomial Haar moments through uniform approximation. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haar_uniform_polynomial_tendsto {N : ℕ} (p : ℕ → MatrixPolynomial N)
    (f : SpecialOrthogonal N → ℝ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε)
    (U : SpecialOrthogonal N) :
    Tendsto (fun n => haarPolynomialValue (p n) U) atTop (𝓝 (f U)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu (ε/2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact (hn U).trans_lt (half_lt_self hε)

theorem haar_uniform_polynomial_integrals {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (p : ℕ → MatrixPolynomial N) (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε) :
    Tendsto (fun n => ∫ U, haarPolynomialValue (p n) U ∂μ) atTop (𝓝 (∫ U, f U ∂μ)) ∧
    ∀ t : ℝ, Tendsto (fun n => haarPolynomialMoment μ (p n) t) atTop
      (𝓝 (∫ U, Real.exp (t*f U) ∂μ)) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U| ≤ B+1 := by
    filter_upwards [hu 1 zero_lt_one] with n hn U
    have hbu : |f U| ≤ B := by simpa only [Real.norm_eq_abs] using hB U (mem_univ U)
    calc
      |haarPolynomialValue (p n) U| ≤ |haarPolynomialValue (p n) U-f U|+|f U| := by
        simpa only [sub_add_cancel] using abs_add_le (haarPolynomialValue (p n) U-f U) (f U)
      _ ≤ B+1 := by linarith [hn U]
  constructor
  · refine tendsto_integral_filter_of_dominated_convergence (fun _ => B+1)
      (Eventually.of_forall fun n => (continuous_haarPolynomialValue (p n)).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      exact ae_of_all μ fun U => by simpa only [Real.norm_eq_abs] using hn U
    · exact ae_of_all μ fun U => haar_uniform_polynomial_tendsto p f hu U
  · intro t
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp (|t| *(B+1)))
      (Eventually.of_forall fun n => (Real.continuous_exp.comp (continuous_const.mul
        (continuous_haarPolynomialValue (p n)))).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      apply ae_of_all
      intro U
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        t*haarPolynomialValue (p n) U ≤ |t*haarPolynomialValue (p n) U| := le_abs_self _
        _ = |t| * |haarPolynomialValue (p n) U| := abs_mul _ _
        _ ≤ |t| *(B+1) := mul_le_mul_of_nonneg_left (hn U) (abs_nonneg _)
    · exact ae_of_all μ fun U => Real.continuous_exp.continuousAt.tendsto.comp
        ((haar_uniform_polynomial_tendsto p f hu U).const_mul t)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments for all continuous Frobenius-Lipschitz observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter
open scoped Topology
namespace InvariantIsing

theorem haar_lipschitz_moment_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {t : ℝ} (ht : 0 < t) :
    (∫ U, Real.exp (t*f U) ∂μ) ≤
      Real.exp ((∫ U, f U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
  have hN0 : 0 < N := by omega
  let p : ℕ → MatrixPolynomial N := haarKernelApprox μ f
  have hu := haarKernelApprox_uniform hN0 μ f hf L hL hLip
  obtain ⟨hmean,hmoment⟩ := haar_uniform_polynomial_integrals μ p f hf hu
  have hG (n : ℕ) (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p n) (p n)) U ≤ 4*L^2 :=
    haarPolynomial_gamma_le_lipschitz (p n) L hL.le
      (haarKernelApprox_lipschitz hN0 μ f hf L hLip n) U
  have hbound (n : ℕ) : haarPolynomialMoment μ (p n) t ≤
      Real.exp ((∫ U, haarPolynomialValue (p n) U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
    have hh := Real.exp_le_exp.mpr
      (haarPolynomialMoment_log_bound hN μ (p n) (4*L^2) (by positivity) (hG n) ht)
    rwa [Real.exp_log (haarPolynomialMoment_pos μ (p n) t)] at hh
  exact le_of_tendsto_of_tendsto (hmoment t)
    (Real.continuous_exp.continuousAt.tendsto.comp ((hmean.mul_const t).add_const _))
    (Eventually.of_forall hbound)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLipschitzTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian tails about the Haar mean for arbitrary Lipschitz observables. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_chernoff {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V)
    (r β : ℝ) (hβ : 0 < β) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp ((4*L^2)/(2*((N:ℝ)-2))*β^2-β*r) := by
  have hf := continuous_of_frobenius_lipschitz f L hLip
  let m := ∫ V, f V ∂μ
  let A := (4*L^2)/(2*((N:ℝ)-2))
  let F (U : SpecialOrthogonal N) := Real.exp (β*(f U-m))
  have hfi : Integrable F μ := continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (hf.sub continuous_const)))
  have hmoment := haar_lipschitz_moment_bound hN μ f hf L hL hLip hβ
  have hI : (∫ U, F U ∂μ) ≤ Real.exp (A*β^2) := by
    have he : (∫ U, F U ∂μ) = Real.exp (-β*m)*(∫ U, Real.exp (β*f U) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by
        change Real.exp (β*(f U-m)) = Real.exp (-β*m)*Real.exp (β*f U)
        rw [← Real.exp_add]
        congr 1
        ring
    rw [he]
    calc
      _ ≤ Real.exp (-β*m)*Real.exp (m*β+A*β^2) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = Real.exp (A*β^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hset : {U | Real.exp (β*r) ≤ F U} = {U | r ≤ f U-m} := by
    ext U
    simp only [mem_ofPred_eq,F,Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ hβ
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun U => (Real.exp_pos _).le)
    hfi (Real.exp (β*r))
  rw [hset] at hm
  have hb : μ.real {U | r ≤ f U-m} ≤ Real.exp (A*β^2)/Real.exp (β*r) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [hm]
  simpa only [Real.exp_sub] using hb

theorem haar_lipschitz_upper_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ f U-(∫ V, f V ∂μ)} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hC : 0 < 4*L^2 := by positivity
  have hb : 0 < ((N:ℝ)-2)*r/(4*L^2) := div_pos (mul_pos hρ hr) hC
  have h := haar_lipschitz_chernoff hN μ f L hL hLip r (((N:ℝ)-2)*r/(4*L^2)) hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarTwoSidedTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both one-sided tails and the centered absolute deviation. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_lower_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ (∫ V, f V ∂μ)-f U} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hh := haar_lipschitz_upper_tail hN μ (fun U => -f U) L hL
    (fun U V => by simpa only [neg_sub_neg,abs_sub_comm] using hLip U V) hr
  simpa only [integral_neg,sub_neg_eq_add,neg_add_eq_sub] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarConcentrationInput
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact Gromov--Milman specialization used by the pressure proof. The proof
uses the actual polynomial heat operator on SO(N), its proved curvature bound,
positive polynomial convolution, and the scalar entropy argument.
-/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

theorem haarConcentration_proved : HaarConcentrationInput := by
  refine ⟨Real.exp 1,1/192,Real.exp_pos _,by norm_num,?_⟩
  intro N hN μ hμ hμinv f hf L hL hLip
  let : IsProbabilityMeasure μ := hμ
  let : μ.IsMulLeftInvariant := hμinv
  obtain ⟨m,hm1,hm2⟩ := measurable_median μ f hf
  refine ⟨m,hm1,hm2,?_⟩
  intro r hr
  let k := ((N:ℝ)-2)/(8*L^2)
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hk : 0 < k := div_pos hρ (by positivity)
  have hplus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ f U-(∫ V, f V ∂μ)} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_upper_tail hN μ f L hL hLip hs
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp only [k]
    ring
  have hminus (s : ℝ) (hs : 0 < s) :
      μ.real {U | s ≤ (∫ V, f V ∂μ)-f U} ≤ Real.exp (-k*s^2) := by
    have hh := haar_lipschitz_lower_tail hN μ f L hL hLip hs
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp only [k]
    ring
  apply (gaussian_median_tail μ f (∫ V, f V ∂μ) m k hk hm1 hm2 hplus hminus hr).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
  have hdim : (N:ℝ) ≤ 3*((N:ℝ)-2) := by
    have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hnum : -3*((N:ℝ)-2)*r^2 ≤ -(N:ℝ)*r^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdim) (sq_nonneg r)]
  calc
    -k*r^2/8 = (-3*((N:ℝ)-2)*r^2)/(192*L^2) := by dsimp only [k] <;> ring
    _ ≤ (-(N:ℝ)*r^2)/(192*L^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = -(1/192)*(N:ℝ)*r^2/L^2 := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_LocalizedAlmostSure
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eventual local exponential tails imply almost-sure convergence whenever
the localizing random bound is eventually finite. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma exponential_tail_extend_initial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℕ → Set Ω)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (N₀ : ℕ)
    (hE : ∀ n, N₀ ≤ n → P.real (E n) ≤ C*Real.exp (-a*(n : ℝ))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, P.real (E n) ≤ D*Real.exp (-a*(n : ℝ)) := by
  let D := C+Real.exp (a*(N₀ : ℝ))
  have hCD : C ≤ D := le_add_of_nonneg_right (Real.exp_pos _).le
  refine ⟨D,by dsimp [D] <;> positivity,fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · exact (hE n hn).trans (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le)
  · have hle : (n : ℝ) ≤ N₀ := by exact_mod_cast (show n ≤ N₀ by omega)
    have he : 1 ≤ Real.exp (a*(N₀ : ℝ))*Real.exp (-a*(n : ℝ)) := by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      nlinarith
    have hED : Real.exp (a*(N₀ : ℝ)) ≤ D := by dsimp [D] <;> linarith
    exact (measureReal_le_one : P.real (E n) ≤ 1).trans
      (he.trans (mul_le_mul_of_nonneg_right hED (Real.exp_pos _).le))

lemma ae_tendsto_zero_of_localized_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : ℕ → Ω → ℝ)
    (htail : ∀ K ε : ℝ, 0 < K → 0 < ε →
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∃ N₀ : ℕ,
        ∀ n, N₀ ≤ n → P.real {ω | ε ≤ |X n ω| ∧ Z n ω ≤ K} ≤ C*Real.exp (-a*(n : ℝ)))
    (hbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ n in atTop, Z n ω ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  let T := fun k n ω => if Z n ω ≤ (k+1 : ℝ) then X n ω else 0
  have hT (k : ℕ) : ∀ᵐ ω ∂P, Tendsto (fun n => T k n ω) atTop (𝓝 0) := by
    apply ae_tendsto_zero_of_exponential_tail
    intro ε hε
    obtain ⟨C,a,hC,ha,N₀,hN₀⟩ := htail (k+1) ε (by positivity) hε
    obtain ⟨D,hD,hDE⟩ := exponential_tail_extend_initial P
      (fun n => {ω | ε ≤ |X n ω| ∧ Z n ω ≤ (k+1 : ℝ)}) hC ha N₀ hN₀
    refine ⟨D,a,hD,ha,fun n => ?_⟩
    have he : {ω | ε ≤ |T k n ω|}={ω | ε ≤ |X n ω| ∧ Z n ω ≤ (k+1 : ℝ)} := by
      ext ω
      by_cases hh : Z n ω ≤ (k+1 : ℝ)
      · simp only [T,hh,ite_true, if_true,mem_ofPred_eq,and_true]
      · simp only [T,hh,ite_false, if_false,abs_zero,mem_ofPred_eq,and_false,not_le_of_gt hε]
    rw [he]
    exact hDE n
  filter_upwards [ae_all_iff.mpr hT,hbound] with ω hω hb
  obtain ⟨K,hK⟩ := hb
  obtain ⟨k,hk⟩ := exists_nat_gt K
  have he : (fun n => T k n ω)=ᶠ[atTop] (fun n => X n ω) := by
    filter_upwards [hK] with n hn
    have hn' : Z n ω ≤ (k+1 : ℝ) := hn.trans (by exact le_trans hk.le (by linarith))
    simp only [T,ite_eq_left hn']
  exact (hω k).congr' he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral excess vanishes under the no-outlier condition. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

lemma spectralExcess_bounds {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) (i : Fin N) :
    a-spectralExcess eig a b ≤ eig i ∧ eig i ≤ b+spectralExcess eig a b := by
  have hh : max (a-eig i) (eig i-b) ≤ spectralExcess eig a b := by
    unfold spectralExcess
    exact Finset.le_max' (insert (0 : ℝ) (Finset.univ.image (fun j => max (a-eig j) (eig j-b))))
      (max (a-eig i) (eig i-b)) (by
        rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hl := (le_max_left (a-eig i) (eig i-b)).trans hh
  have hu := (le_max_right (a-eig i) (eig i-b)).trans hh
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExtremeLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual extreme eigenvalues implies the uniform
no-outlier formulation used by the pressure theorem. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

lemma spectralMinimum_le {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    spectralMinimum eig ≤ eig i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

lemma le_spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    eig i ≤ spectralMaximum eig :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomOrbitLaw
attribute [-instance] _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint conditional-Haar hypothesis for random spectra and fields.
Only the one-dimensional marginal orbit law is prescribed at each dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

lemma measurable_random_specialPressure {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (eig field : Ω → Fin N → ℝ) (heig : Measurable eig) (hfield : Measurable field)
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U) :
    Measurable (fun ω => rotatedPressure (eig ω) (specialRotation (U ω)) (field ω)) := by
  have hE (σ : Spin N) : Measurable (fun ω =>
      rotatedEnergy (eig ω) (specialRotation (U ω)) σ+fieldEnergy (field ω) σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp heig).mul
          (((measurable_specialRotation_eval (spinVector σ) i).comp hU).pow_const 2))).const_mul (1/2 : ℝ)
    · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hfield).mul_const _
  unfold rotatedPressure logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log.const_mul (N : ℝ)⁻¹

lemma measurable_dataPhysicalPressure {N : ℕ} (hN : 0 < N) :
    Measurable (fun z : FieldSpectralData N × Orthogonal N => dataPhysicalPressure z.1 z.2) := by
  have hh := measurable_random_specialPressure
    (fun z : FieldSpectralData N × Orthogonal N => z.1.1)
    (fun z : FieldSpectralData N × Orthogonal N => z.1.2)
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (fun z => cavityOrientationLift hN z.2⁻¹)
    ((measurable_cavityOrientationLift hN).comp measurable_snd.inv)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [dataPhysicalPressure,rotatedPressure,cavityOrientationLift_energy]

lemma measurable_dataPressureMean {N : ℕ} (hN : 0 < N)
    (H : Measure (Orthogonal N)) [SFinite H] :
    Measurable (fun d : FieldSpectralData N => ∫ U, dataPhysicalPressure d U ∂H) :=
  (measurable_dataPhysicalPressure hN).stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_UniformHaarMeanTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform centered Haar tails for bounded Lipschitz observables. The threshold
is independent of the particular observable and of its additive normalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem uniform_bounded_haar_mean_tail (hpub : HaarConcentrationInput) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ K ε : ℝ, 0 < K → 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 3 ≤ N →
      ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
      ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
        (∀ U, |f U| ≤ K) →
        (∀ U V, |f U-f V| ≤ K*frobeniusDistance U V) →
      μ.real {U | ε ≤ |f U-(∫ V, f V ∂μ)|} ≤
        C*Real.exp (-a*(N : ℝ)*(ε/2)^2/K^2) := by
  obtain ⟨C,a,hC,ha,hinput⟩ := hpub
  refine ⟨C,a,hC,ha,?_⟩
  intro K ε hK hε
  let d : ℝ := a*(ε/4)^2/K^2
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hlin : Tendsto (fun n : ℕ => -d*(n : ℝ)) atTop atBot := by
    simpa only [Function.comp_def,neg_mul] using
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hd)
  have hlim : Tendsto (fun n : ℕ => ε/4+2*K*(C*Real.exp (-d*(n : ℝ)))) atTop (𝓝 (ε/4)) := by
    simpa only [mul_zero,add_zero,Function.comp_def] using
      (((Real.tendsto_exp_atBot.comp hlin).const_mul C).const_mul (2*K)).const_add (ε/4)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually
    (Iio_mem_nhds (by linarith : ε/4<ε/2)))
  refine ⟨N₀,?_⟩
  intro N hN hN3 μ hμ hInv f hf hbound hLip
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m,hl,hu,ht⟩ := hinput N hN3 μ hμ hInv f hf K hK hLip
  have hm : |m| ≤ K := abs_median_le_bound μ f m K hbound hl hu
  have hdev U : |f U-m| ≤ 2*K := by
    have hh := (abs_sub (f U) m).trans (add_le_add (hbound U) hm)
    linarith
  have hfi : Integrable f μ := (integrable_const K).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hbound U)
  have hmean := abs_integral_sub_le_deviation_tail μ f hf hfi m (2*K) (ε/4)
    (by positivity) hdev
  have hmean' := hmean.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (ht (ε/4) (by positivity)) (by positivity : 0 ≤ 2*K)))
  have heq : -a*(N : ℝ)*(ε/4)^2/K^2= -d*(N : ℝ) := by dsimp [d] <;> ring
  rw [heq] at hmean'
  have hclose : |(∫ V, f V ∂μ)-m| < ε/2 := hmean'.trans_lt (hN₀ N hN)
  have hs : {U | ε ≤ |f U-(∫ V, f V ∂μ)|} ⊆ {U | ε/2 ≤ |f U-m|} := by
    intro U hU
    have hh := abs_sub_le (f U) m (∫ V, f V ∂μ)
    rw [abs_sub_comm m (∫ V, f V ∂μ)] at hh
    change ε/2 ≤ |f U-m|
    change ε ≤ |f U-(∫ V, f V ∂μ)| at hU
    linarith
  exact (measureReal_mono hs).trans (ht (ε/2) (by positivity))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_UniformPhysicalTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-uniform centered tail for the physical Haar pressure, independent
of the external field. This can be conditioned on random spectral and field data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem uniform_physical_pressure_mean_tail (hpub : HaarConcentrationInput) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ K ε : ℝ, 0 < K → 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 3 ≤ N →
      ∀ μ : Measure (Orthogonal N), IsProbabilityMeasure μ → μ.IsMulRightInvariant →
      ∀ eig c : Fin N → ℝ, (∀ i, |eig i| ≤ K) →
      μ.real {U | ε ≤ |rotatedPressure eig (matrixRotation U⁻¹) c-
        ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ|} ≤
        C*Real.exp (-a*(N : ℝ)*(ε/2)^2/K^2) := by
  obtain ⟨C,a,hC,ha,ht⟩ := uniform_bounded_haar_mean_tail hpub
  refine ⟨C,a,hC,ha,?_⟩
  intro K ε hK hε
  obtain ⟨N₀,hN₀⟩ := ht K ε hK hε
  refine ⟨N₀,?_⟩
  intro N hN hN3 μ hμ hHaar eig c heig
  let : IsProbabilityMeasure μ := hμ
  let : μ.IsMulRightInvariant := hHaar
  have hpos : 0 < N := by omega
  let η := cavityOrientedBaseLaw hpos μ
  let f := fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c-noninteractingPressure c
  have hf : Measurable f := (measurable_rotatedPressure eig c).sub_const _
  have hfb U : |f U| ≤ K :=
    (abs_pressure_sub_noninteracting_le hpos eig c (specialRotation U) K heig).trans (by linarith)
  have hlip U V : |f U-f V| ≤ K*frobeniusDistance U V := by
    dsimp only [f]
    rw [sub_sub_sub_cancel_right]
    exact abs_rotatedPressure_sub_rotation_le hpos eig U V c K hK.le heig
  have hh := hN₀ N hN hN3 η inferInstance (cavityOrientedBaseLaw_leftInvariant hpos μ)
    f hf hfb hlip
  have hmean : (∫ U, f U ∂η)=
      (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ)-noninteractingPressure c := by
    rw [integral_sub (integrable_countPressure hpos η eig c K heig) (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
    rw [cavity_oriented_pressure]
  have hset : MeasurableSet {U | ε ≤ |f U-(∫ V, f V ∂η)|} :=
    measurableSet_le measurable_const (hf.sub_const _).abs
  change (cavityOrientedBaseLaw hpos μ).real _ ≤ _ at hh
  have hT : Measurable (fun V : Orthogonal N => cavityOrientationLift hpos V⁻¹) :=
    (measurable_cavityOrientationLift hpos).comp measurable_inv
  rw [measureReal_def,cavityOrientedBaseLaw,Measure.map_apply hT hset] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext U
  change (ε ≤ |_ - _|) ↔ (ε ≤ |_ - _|)
  rw [hmean]
  simp only [f,rotatedPressure,cavityOrientationLift_energy]
  ring_nf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomOrbitTail
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A localized tail bound under the exact joint conditional orbit hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace InvariantIsing

lemma conditional_orbit_tail_bound {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → FieldSpectralData N) (Y : Ω → ℝ) (hd : Measurable d) (hY : Measurable Y)
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H]
    (hlaw : ConditionalFieldOrbitLaw P d Y H) (K ε B : ℝ)
    (hbound : ∀ data : FieldSpectralData N, (∀ i, |data.1 i| ≤ K) →
      H.real {U | ε ≤ |dataPhysicalPressure data U-(∫ V, dataPhysicalPressure data V ∂H)|} ≤ B) :
    P {ω | (∀ i, |(d ω).1 i| ≤ K) ∧
      ε ≤ |Y ω-(∫ V, dataPhysicalPressure (d ω) V ∂H)|} ≤ ENNReal.ofReal B := by
  let mean := fun data : FieldSpectralData N => ∫ V, dataPhysicalPressure data V ∂H
  have hm : Measurable mean := measurable_dataPressureMean hN H
  let E : Set (FieldSpectralData N × ℝ) := {z | (∀ i, |z.1.1 i| ≤ K) ∧ ε ≤ |z.2-mean z.1|}
  have hK : MeasurableSet {z : FieldSpectralData N × ℝ | ∀ i, |z.1.1 i| ≤ K} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_fst)).abs) measurable_const
  have hE : MeasurableSet E := hK.inter
    (measurableSet_le measurable_const (measurable_snd.sub (hm.comp measurable_fst)).abs)
  have hp : Measurable (fun z : FieldSpectralData N × Orthogonal N =>
      (z.1,dataPhysicalPressure z.1 z.2)) :=
    measurable_fst.prodMk (measurable_dataPhysicalPressure hN)
  have he := congrArg (fun Q : Measure (FieldSpectralData N × ℝ) => Q E) hlaw
  rw [Measure.map_apply (hd.prodMk hY) hE] at he
  erw [Measure.map_apply hp hE,
    Measure.prod_apply (hp hE)] at he
  let : IsProbabilityMeasure (P.map d) :=
    (Measure.isProbabilityMeasure_map_iff hd.aemeasurable).mpr inferInstance
  change P ((fun ω => (d ω,Y ω)) ⁻¹' E) ≤ _
  rw [he]
  calc
    _ ≤ ∫⁻ _data : FieldSpectralData N, ENNReal.ofReal B ∂P.map d := by
      apply lintegral_mono
      intro data
      dsimp only
      by_cases hdata : ∀ i, |data.1 i| ≤ K
      · have hevent : Prod.mk data ⁻¹' ((fun z : FieldSpectralData N × Orthogonal N =>
            (z.1,dataPhysicalPressure z.1 z.2)) ⁻¹' E)=
            {U | ε ≤ |dataPhysicalPressure data U-mean data|} := by
          ext U
          change ((∀ i, |data.1 i| ≤ K) ∧ ε ≤ |dataPhysicalPressure data U-mean data|) ↔ _
          exact and_iff_right hdata
        rw [hevent]
        have hb := ENNReal.ofReal_le_ofReal (hbound data hdata)
        rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top H _)] at hb
      · have hevent : Prod.mk data ⁻¹' ((fun z : FieldSpectralData N × Orthogonal N =>
            (z.1,dataPhysicalPressure z.1 z.2)) ⁻¹' E)=∅ := by
          ext U
          change ((∀ i, |data.1 i| ≤ K) ∧ ε ≤ |dataPhysicalPressure data U-mean data|) ↔ False
          simp only [hdata,false_and]
        rw [hevent,measure_empty]
        exact bot_le
    _ = _ := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSpectralBound
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The extreme eigenvalues control a random spectrum without moment hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma abs_le_spectralRadius {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    |eig i| ≤ spectralRadius eig := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (spectralMinimum eig)).trans (spectralMinimum_le eig i))
  · exact (le_spectralMaximum eig i).trans
      ((le_abs_self _).trans (le_max_right _ _))

lemma spectralRadius_le_iff {n : ℕ} (eig : Fin (n+1) → ℝ) (K : ℝ) :
    spectralRadius eig ≤ K ↔ ∀ i, |eig i| ≤ K := by
  constructor
  · intro h i
    exact (abs_le_spectralRadius eig i).trans h
  · intro h
    apply max_le
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMinimum,← hi] using h i
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMaximum,← hi] using h i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SelectedOrbitAlmostSure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional Haar concentration along a selected sequence of dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

theorem ae_selected_orbit_pressure_sub_mean (hhaar : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → ℕ) (hs : ∀ k, k ≤ s k)
    (d : (k : ℕ) → Ω → FieldSpectralData (s k+1)) (Y : ℕ → Ω → ℝ)
    (hd : ∀ N, Measurable (d N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H (s N+1)))
    (hbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius ((d k ω).1) ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Y k ω-
      ∫ U, dataPhysicalPressure (d k ω) U ∂H (s k+1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_localized_exponential_tail P
    (fun k ω => Y k ω-∫ U, dataPhysicalPressure (d k ω) U ∂H (s k+1))
    (fun k ω => spectralRadius ((d k ω).1)) _ hbound
  intro K ε hK hε
  obtain ⟨C,a,hC,ha,ht⟩ := uniform_physical_pressure_mean_tail hhaar
  obtain ⟨N₀,hN₀⟩ := ht K ε hK hε
  refine ⟨C,a*(ε/2)^2/K^2,hC.le,by positivity,max N₀ 3,?_⟩
  intro n hn
  have hb := conditional_orbit_tail_bound (Nat.succ_pos (s n)) P (d n) (Y n)
    (hd n) (hY n) (H (s n+1)) (hlaw n) K ε
    (C*Real.exp (-a*(s n+1 : ℝ)*(ε/2)^2/K^2)) (fun data hdata => by
      simpa only [dataPhysicalPressure,Nat.cast_add,Nat.cast_one] using
        hN₀ (s n+1) (by have := hs n; omega) (by have := hs n; omega) (H (s n+1)) inferInstance inferInstance
          data.1 data.2 hdata)
  have he : {ω | (∀ i, |(d n ω).1 i| ≤ K) ∧
      ε ≤ |Y n ω-∫ U, dataPhysicalPressure (d n ω) U ∂H (s n+1)|}=
      {ω | ε ≤ |Y n ω-∫ U, dataPhysicalPressure (d n ω) U ∂H (s n+1)| ∧
        spectralRadius ((d n ω).1) ≤ K} := by
    ext ω
    simp only [mem_ofPred_eq,spectralRadius_le_iff,and_comm]
  rw [he] at hb
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  refine hreal.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ a*(ε/2)^2/K^2 := by positivity
  calc
    -a*(s n+1 : ℝ)*(ε/2)^2/K^2= -(a*(ε/2)^2/K^2)*((s n : ℝ)+1) := by ring
    _ ≤ -(a*(ε/2)^2/K^2)*(n : ℝ) := by
      have hsn : (n : ℝ) ≤ s n := by exact_mod_cast hs n
      nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SelectedSpectralExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turning a scalar edge-excess limit into the selected spectral hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma selected_no_outliers_of_excess (N : ℕ → ℕ) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (a b : ℝ) (he : Tendsto (fun k => spectralExcess (eig k) a b) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i, a-ε ≤ eig k i ∧ eig k i ≤ b+ε := by
  intro ε hε
  filter_upwards [he.eventually (Iio_mem_nhds hε)] with k hk i
  have hb := spectralExcess_bounds (eig k) a b i
  constructor <;> linarith

lemma selected_spectralRadius_bounded (s : ℕ → ℕ)
    (eig : (k : ℕ) → Fin (s k+1) → ℝ) (a b : ℝ)
    (he : Tendsto (fun k => spectralExcess (eig k) a b) atTop (𝓝 0)) :
    ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig k) ≤ K := by
  refine ⟨max |a| |b|+1,?_⟩
  filter_upwards [selected_no_outliers_of_excess (fun k => s k+1) eig a b he 1 zero_lt_one]
    with k hk
  apply (spectralRadius_le_iff _ _).mpr
  intro i
  apply abs_le.mpr
  have ha := neg_abs_le a
  have hb := le_abs_self b
  have hma := le_max_left |a| |b|
  have hmb := le_max_right |a| |b|
  constructor <;> linarith [(hk i).1,(hk i).2]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomPressureProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proposition gen:random: convergence in probability from weak empirical
convergence and vanishing edge excess, with no independence across dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_tendsto_in_measure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun k => (hY (k+1)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨u,hu,hwu⟩ := (hweak.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨v,hv,hev⟩ := (hexcess.comp (hns.comp hu).tendsto_atTop).exists_seq_tendsto_ae
  let s := ns ∘ u ∘ v
  have hs : StrictMono s := hns.comp (hu.comp hv)
  have hws : ∀ᵐ ω ∂P, Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos (s k))
      (eig (s k+1) ω)) atTop (𝓝 ν) := by
    filter_upwards [hwu] with ω hω
    exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp
      (hω.comp hv.tendsto_atTop)
  have hbs : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig (s k+1) ω) ≤ K := by
    filter_upwards [hev] with ω hω
    exact selected_spectralRadius_bounded s (fun k => eig (s k+1) ω) a b hω
  have ht := ae_selected_orbit_pressure_sub_mean hhaar P s hs.id_le
    (fun k ω => (eig (s k+1) ω,fun _ => 0)) (fun k => Y (s k+1))
    (fun k => (heig (s k+1)).prodMk measurable_const) (fun k => hY (s k+1)) H
    (fun k => hlaw (s k+1)) hbs
  refine ⟨u ∘ v,hu.comp hv,?_⟩
  filter_upwards [ht,hws,hev] with ω htω hwω heω
  have hm := selected_spectral_pressure_tendsto hhaar hgauss hpub H
    (fun k => s k+1) (fun k => Nat.succ_pos _) ((tendsto_add_atTop_nat 1).comp hs.tendsto_atTop)
    (fun k => eig (s k+1) ω) ν a b hcompact hbound ha hb
    (selected_no_outliers_of_excess (fun k => s k+1) (fun k => eig (s k+1) ω) a b heω) hwω
  have hh := htω.add hm
  simpa only [s,Function.comp_apply,dataPhysicalPressure,sub_add_cancel,zero_add] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform-integrability conclusion of Proposition gen:random. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

lemma pressure_L1_of_probability_and_uniformIntegrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (L : ℝ) (hUI : UniformIntegrable X 1 P)
    (hprob : TendstoInMeasure P X atTop (fun _ => L)) :
    Tendsto (fun n => eLpNorm (fun ω => X n ω-L) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 L) := by
  have hL := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl (by simp)
    hUI.aestronglyMeasurable (memLp_const L) hUI.2.1 hprob
  refine ⟨hL,?_⟩
  have hh := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (fun _ : Ω => L)
    (Filter.Eventually.of_forall fun n => (memLp_one_iff_integrable.mp (hUI.memLp n))) hL
  simpa only [integral_const,probReal_univ,one_smul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomPressureMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete in-probability, L1 and expectation clauses of Proposition gen:random. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0))
    (hUI : UniformIntegrable (fun k => Y (k+1)) 1 P) :
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    Tendsto (fun k => eLpNorm (fun ω => Y (k+1) ω-
      (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, Y (k+1) ω ∂P) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hp := random_pressure_tendsto_in_measure hhaar hgauss hpub P eig Y heig hY H hlaw
    ν a b hcompact hbound ha hb hweak hexcess
  exact ⟨hp,pressure_L1_of_probability_and_uniformIntegrability P _ _ hUI hp⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Unconditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Limiting invariant Ising pressure, magnetic fields, and Gaussian patterns. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
universe u
namespace InvariantIsing

theorem random_pressure_limit_unconditional_oai :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (_heig : ∀ N, Measurable (eig N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (_hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0))
    (_hUI : UniformIntegrable (fun k => Y (k+1)) 1 P),
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    Tendsto (fun k => eLpNorm (fun ω => Y (k+1) ω-
      (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, Y (k+1) ω ∂P) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) :=
  @random_pressure_limit haarConcentration_proved gaussianLipschitzVariance_proved panchenkoTalagrandFieldPair_proved

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.random_pressure_limit_unconditional_oai.{u_1} := @OAI.InvariantIsing.random_pressure_limit_unconditional_oai.{u_1}
