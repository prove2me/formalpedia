-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:59:14.854207+00:00
-- url     : https://prove2.me/submissions/1d0e8e68-3ce4-4336-94d9-52ddf79a66d9

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
import Theorems.Thm_OAI_InvariantIsing_davidsonSzarek_proved
import Theorems.Thm_OAI_InvariantIsing_gaussianLipschitzVariance_proved
import Theorems.Thm_OAI_InvariantIsing_gaussianPattern_ground_limit
import Theorems.Thm_OAI_InvariantIsing_haarPolynomialMoment_log_bound
import Theorems.Thm_OAI_InvariantIsing_marchenkoPastur_proved
import Theorems.Thm_OAI_InvariantIsing_panchenkoTalagrandFieldPair_proved

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFactor
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_CubeOperatorNorm
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not _root_.OAI.InvariantIsing.spinVector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sup-to-norm operator maximum is attained at an Ising vertex. -/
noncomputable section
open Set
open scoped Classical
namespace InvariantIsing

lemma spinSigns_range (N : ℕ) :
    Set.range (fun σ : Spin N => fun i => spinValue (σ i))=
      Set.univ.pi (fun _ : Fin N => ({(-1 : ℝ),1} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨σ,rfl⟩ i _
    cases h : σ i <;> simp [spinValue,h]
  · intro hx
    refine ⟨fun i => decide (x i=1),?_⟩
    funext i
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi
    rcases hi with hi|hi <;> norm_num [spinValue,hi]

lemma mem_spinSigns_convexHull {N : ℕ} (x : Fin N → ℝ) (hx : ‖x‖ ≤ 1) :
    x∈convexHull ℝ (Set.range (fun σ : Spin N => fun i => spinValue (σ i))) := by
  rw [spinSigns_range,convexHull_pi]
  intro i _
  rw [convexHull_pair,segment_eq_Icc (by norm_num : (-1 : ℝ)≤1)]
  exact abs_le.mp ((pi_norm_le_iff_of_nonneg zero_le_one).mp hx i)

lemma cube_operator_norm {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : (Fin N → ℝ) →L[ℝ] E) :
    ‖T‖=Finset.univ.sup' Finset.univ_nonempty
      (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖) := by
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖)
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (Finset.le_sup' (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖)
      (Finset.mem_univ (fun _ => false)))
  have hball (x : Fin N → ℝ) (hx : ‖x‖≤1) : ‖T x‖≤M := by
    have hc := (convexOn_univ_norm (E := E)).comp_linearMap T.toLinearMap
    obtain ⟨y,⟨σ,rfl⟩,hσ⟩ := hc.exists_ge_of_mem_convexHull
      (show Set.range (fun σ : Spin N => fun i => spinValue (σ i)) ⊆
        T.toLinearMap ⁻¹' Set.univ from fun _ _ => Set.mem_univ _)
      (mem_spinSigns_convexHull x hx)
    exact hσ.trans (Finset.le_sup'
      (fun τ : Spin N => ‖T (fun i => spinValue (τ i))‖) (Finset.mem_univ σ))
  apply le_antisymm
  · apply T.opNorm_le_bound' hM
    intro x hx
    have hn : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hb := hball (‖x‖⁻¹ • x) (by simp [norm_smul,hn.ne'])
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hb
    simpa only [mul_comm] using (inv_mul_le_iff₀ hn).mp hb
  · apply Finset.sup'_le
    intro σ _
    have hs : ‖(fun i => spinValue (σ i))‖ ≤ (1 : ℝ) :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp [Real.norm_eq_abs]
    exact (T.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg T) hs)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSquareExtrema
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square extrema of finite nonnegative families. -/
noncomputable section
open scoped Classical
namespace InvariantIsing

lemma finite_sup_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℝ) (hq : 0 ≤ q) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => q*(f i)^2)=
      q*(Finset.univ.sup' Finset.univ_nonempty f)^2 := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hle (i : ι) : f i ≤ f a := by
    rw [← ha]
    exact Finset.le_sup' f (Finset.mem_univ i)
  rw [ha]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (hf i) (hf a) |>.mpr (hle i)) hq
  · exact Finset.le_sup' (fun i => q*(f i)^2) (Finset.mem_univ a)

lemma finite_sup_neg_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℝ) (hq : 0 ≤ q) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => -q*(f i)^2)=
      -q*(Finset.univ.inf' Finset.univ_nonempty f)^2 := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  have hle (i : ι) : f a ≤ f i := by
    rw [← ha]
    exact Finset.inf'_le f (Finset.mem_univ i)
  rw [ha]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact mul_le_mul_of_nonpos_left (sq_le_sq₀ (hf a) (hf i) |>.mpr (hle i)) (neg_nonpos.mpr hq)
  · exact Finset.le_sup' (fun i => -q*(f i)^2) (Finset.mem_univ a)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-pattern Hamiltonian with its diagonal self-interactions.
The array is indexed by spin coordinate first and pattern coordinate second. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma quadraticEnergy_dotProduct {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (σ : Spin N) :
    quadraticEnergy J σ=(1/2 : ℝ)*
      ((fun i => spinValue (σ i)) ⬝ᵥ J *ᵥ (fun i => spinValue (σ i))) := by
  simp only [quadraticEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma gaussianPattern_energy {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    quadraticEnergy (gaussianPatternCoupling c z) σ=c/(2*N)*‖gaussianPatternSum z σ‖^2 := by
  let v := fun i => spinValue (σ i)
  have hn : ‖gaussianPatternSum z σ‖^2=
      ((gaussianPatternArray z)ᵀ *ᵥ v) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ v) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gaussianPatternSum,dotProduct,pow_two]
    rfl
  rw [quadraticEnergy_dotProduct,gaussianPatternCoupling,Matrix.smul_mulVec,dotProduct_smul,
    ← Matrix.mulVec_mulVec,hn]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GroundStateFinite
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual maximum Ising energy and its uniform finite-temperature squeeze. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace InvariantIsing

lemma groundStateEnergy_attained {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) :
    (∀ σ, rotatedEnergy eig U σ ≤ N*groundStateEnergy eig U) ∧
      ∃ σ, rotatedEnergy eig U σ=N*groundStateEnergy eig U := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N : ℝ)*groundStateEnergy eig U=
      Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U) := by
    unfold groundStateEnergy
    field_simp
  rw [he]
  constructor
  · intro σ
    exact Finset.le_sup' _ (Finset.mem_univ σ)
  · obtain ⟨σ,_,hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rotatedEnergy eig U)
    exact ⟨σ,hσ.symm⟩

lemma abs_groundStateEnergy_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |groundStateEnergy eig U| ≤ K/2 := by
  obtain ⟨σ,hσ⟩ := (groundStateEnergy_attained hN eig U).2
  have hh := abs_rotatedEnergy_le eig U K hK σ
  rw [hσ,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise diagonalization of the actual Gaussian-pattern pressure. No
measurable choice of eigenvectors is required for Haar averaging. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma gaussianPatternCoupling_smul {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling c z=c • gaussianPatternCoupling 1 z := by
  simp only [gaussianPatternCoupling,smul_smul,one_div]
  rw [div_eq_mul_inv]

lemma cavityConjugate_diagonal_smul {N : ℕ} (c : ℝ) (U : Orthogonal N) (eig : Fin N → ℝ) :
    c • cavityConjugate U (Matrix.diagonal eig)=
      cavityConjugate U (Matrix.diagonal (fun i => c*eig i)) := by
  have hd : Matrix.diagonal (fun i => c*eig i)=c • Matrix.diagonal eig := by
    ext i j
    by_cases h : i=j <;> simp [h]
  rw [hd]
  simp only [cavityConjugate,smul_mul_assoc,mul_smul_comm]

lemma gaussianPattern_diagonalization {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternCoupling 1 z=
      cavityConjugate V (Matrix.diagonal (gaussianPatternEigenvalues z)) := by
  let hA := gaussianPatternCoupling_isHermitian 1 z
  refine ⟨hA.eigenvectorUnitary,?_⟩
  simpa [cavityConjugate,Unitary.conjStarAlgAut_apply,Function.comp_def,
    gaussianPatternEigenvalues,hA,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSpectralBound
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternGroundFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Gaussian-pattern maximum energies and their finite-temperature squeeze. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace InvariantIsing

lemma measurable_gaussianPatternGroundEnergy (N m : ℕ) (ε : ℝ) :
    Measurable (gaussianPatternGroundEnergy (N := N) (m := m) ε) := by
  have hm (σ : Spin N) : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      ε/(2*N)*‖gaussianPatternSum z σ‖^2) := by
    have hs : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternSum z σ) := by
      unfold gaussianPatternSum gaussianPatternArray
      fun_prop
    exact (hs.measurable.norm.pow_const 2).const_mul _
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun σ _ => hm σ)
  convert hh.const_mul (N : ℝ)⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [gaussianPatternGroundEnergy,Finset.sup'_apply]

lemma gaussianPatternGroundEnergy_orbit {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternGroundEnergy ε z=
      groundStateEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) := by
  obtain ⟨V,hV⟩ := gaussianPattern_diagonalization z
  refine ⟨V,?_⟩
  have he (σ : Spin N) : ε/(2*N)*‖gaussianPatternSum z σ‖^2=
      rotatedEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) σ := by
    rw [← gaussianPattern_energy,gaussianPatternCoupling_smul,hV,cavityConjugate_diagonal_smul]
    exact cavityQuadratic_inverse_rotation _ V σ
  unfold gaussianPatternGroundEnergy groundStateEnergy
  simp only [he]

lemma abs_gaussianPatternGroundEnergy_le {n m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) :
    |gaussianPatternGroundEnergy ε z| ≤
      spectralRadius (fun i => ε*gaussianPatternEigenvalues z i)/2 := by
  obtain ⟨V,hV⟩ := gaussianPatternGroundEnergy_orbit ε z
  rw [hV]
  exact abs_groundStateEnergy_le (Nat.succ_pos n) _ _ _ (abs_le_spectralRadius _)

lemma gaussianPatternGroundEnergy_nonneg {N m : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianPatternGroundEnergy ε z := by
  apply mul_nonneg (by positivity)
  exact (mul_nonneg (div_nonneg hε (by positivity)) (sq_nonneg _)).trans
    (Finset.le_sup' (fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2)
      (Finset.mem_univ (fun _ => false)))

lemma gaussianPatternGroundEnergy_nonpos {N m : ℕ} (ε : ℝ) (hε : ε ≤ 0)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : gaussianPatternGroundEnergy ε z ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sup'_le
  intro σ _
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hε (by positivity)) (sq_nonneg _)

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

lemma uniformIntegrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Z : ℕ → Ω → ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (hZ : UniformIntegrable Z 1 P) (hXZ : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ |Z n ω|) :
    UniformIntegrable X 1 P := by
  have hd n : (fun ω => ‖X n ω‖ₑ) ≤ᵐ[P] (fun ω => ‖Z n ω‖ₑ) :=
    (hXZ n).mono fun ω hω => by
      simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω
  have hu : UnifIntegrable X 1 P := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hZ.2.1 hε
    refine ⟨δ, hδ, fun n s hs hμ => ?_⟩
    refine le_trans (eLpNorm_mono_enorm_ae ?_) (h n s hs hμ)
    filter_upwards [hd n] with ω hω
    by_cases hω' : ω ∈ s
    · simpa [Set.indicator_of_mem hω'] using hω
    · simp [Set.indicator_of_notMem hω']
  obtain ⟨C,hC⟩ := hZ.2.2
  exact ⟨hX, hu, C, fun n => (eLpNorm_mono_enorm_ae (hd n)).trans (hC n)⟩

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomThermalSqueeze
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A soft-maximum squeeze for convergence in probability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma tendstoInMeasure_continuous_comp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ) (L : ℝ)
    (hX : ∀ n, Measurable (X n)) (h : TendstoInMeasure P X atTop (fun _ => L))
    (f : ℝ → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (fun n ω => f (X n ω)) atTop (fun _ => f L) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hf.measurable.comp (hX n)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨u,hu,he⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,he.mono fun ω hω => (hf.tendsto L).comp hω⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternGroundLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subsequent zero-temperature limits for both signs of the Gaussian energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace InvariantIsing

lemma gaussianPattern_ground_uniformIntegrable
    (α : ℝ) (hα : 0 < α) (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ) : UniformIntegrable (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) 1 P := by
  apply uniformIntegrable_of_abs_le P _ _
    (fun k => ((measurable_gaussianPatternGroundEnergy _ _ ε).comp (hZ (k+1))).aestronglyMeasurable)
    (hds.uniform_integrable P Z hlaw ε)
  intro k
  filter_upwards [] with ω
  have hr : 0 ≤ spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) :=
    (abs_nonneg (ε*gaussianPatternEigenvalues (Z (k+1) ω) 0)).trans (abs_le_spectralRadius (fun i => ε*gaussianPatternEigenvalues (Z (k+1) ω) i) 0)
  exact (abs_gaussianPatternGroundEnergy_le ε _).trans ((half_le_self hr).trans (le_abs_self _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Gaussian norm and minimum identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators
namespace InvariantIsing

lemma gaussianPatternOperator_norm {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternOperator z‖=Finset.univ.sup' Finset.univ_nonempty
      (fun σ : Spin N => ‖gaussianPatternSum z σ‖) := cube_operator_norm _

lemma gaussianPattern_max_sqrt {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Real.sqrt (2*gaussianPatternGroundEnergy 1 z)=‖gaussianPatternOperator z‖/N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : 2*gaussianPatternGroundEnergy 1 z=(‖gaussianPatternOperator z‖/N)^2 := by
    rw [gaussianPatternOperator_norm,gaussianPatternGroundEnergy,
      finite_sup_square (fun σ : Spin N => ‖gaussianPatternSum z σ‖) (fun _ => norm_nonneg _)
        (1/(2*N)) (by positivity)]
    field_simp
  rw [he,Real.sqrt_sq (div_nonneg (norm_nonneg _) (Nat.cast_nonneg N))]

lemma gaussianPattern_min_sqrt {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Real.sqrt (-2*gaussianPatternGroundEnergy (-1) z)=
      (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖))/N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let M := Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖)
  have hM : 0 ≤ M := Finset.le_inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖) (fun σ _ => norm_nonneg _)
  have he : -2*gaussianPatternGroundEnergy (-1) z=(M/N)^2 := by
    unfold gaussianPatternGroundEnergy
    have hs := finite_sup_neg_square (fun σ : Spin N => ‖gaussianPatternSum z σ‖)
      (fun _ => norm_nonneg _) (1/(2*N)) (by positivity)
    simp only [neg_div]
    rw [hs]
    dsimp [M]
    field_simp
  rw [he,Real.sqrt_sq (div_nonneg hM (Nat.cast_nonneg N))]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSqrtLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous square-root transport with uniform integrability. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

lemma uniformIntegrable_add_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℕ → Ω → ℝ)
    (hX : UniformIntegrable X 1 P) (hY : UniformIntegrable Y 1 P) :
    UniformIntegrable (fun n ω => X n ω+Y n ω) 1 P := by
  refine ⟨fun n => (hX.1 n).add (hY.1 n), hX.2.1.add hY.2.1 le_rfl hX.1 hY.1, ?_⟩
  obtain ⟨C,hC⟩ := hX.2.2
  obtain ⟨D,hD⟩ := hY.2.2
  refine ⟨C+D,fun n => ?_⟩
  exact (eLpNorm_add_le (hX.1 n) (hY.1 n) le_rfl).trans (add_le_add (hC n) (hD n))

lemma uniformIntegrable_abs_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : UniformIntegrable X 1 P) :
    UniformIntegrable (fun n ω => |X n ω|) 1 P := by
  apply uniformIntegrable_of_abs_le P _ X
    (fun n => (hX.aestronglyMeasurable n).norm) hX
  intro n
  filter_upwards [] with ω
  simp only [Real.norm_eq_abs,abs_abs,le_refl]

lemma random_sqrt_scaled_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (L a : ℝ)
    (ha : |a| ≤ 2) (hX : ∀ n, Measurable (X n)) (hUI : UniformIntegrable X 1 P)
    (hprob : TendstoInMeasure P X atTop (fun _ => L)) :
    TendstoInMeasure P (fun n ω => Real.sqrt (a*X n ω)) atTop (fun _ => Real.sqrt (a*L)) ∧
    Tendsto (fun n => eLpNorm (fun ω => Real.sqrt (a*X n ω)-Real.sqrt (a*L)) 1 P)
      atTop (𝓝 0) := by
  have hs : UniformIntegrable (fun n ω => 1+|X n ω|) 1 P :=
    uniformIntegrable_add_real P _ _ (uniformIntegrable_const le_rfl (by simp) (memLp_const 1))
      (uniformIntegrable_abs_real P X hUI)
  have hsq : UniformIntegrable (fun n ω => Real.sqrt (a*X n ω)) 1 P := by
    apply uniformIntegrable_of_abs_le P _ _
      (fun n => (((hX n).const_mul a).sqrt).aestronglyMeasurable) hs
    intro n
    filter_upwards [] with ω
    rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (by positivity : 0 ≤ 1+|X n ω|)]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hax : a*X n ω ≤ 2*|X n ω| := (le_abs_self (a*X n ω)).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ha (abs_nonneg _))
      nlinarith [sq_nonneg (|X n ω|),sq_abs (X n ω)]
  have hp := tendstoInMeasure_continuous_comp P X L hX hprob
    (fun x => Real.sqrt (a*x)) (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))
  exact ⟨hp,(pressure_L1_of_probability_and_uniformIntegrability P _ _ hsq hp).1⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternCorollary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-pattern maximum-norm and minimum-spin-sum limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace InvariantIsing

theorem gaussianPattern_norm_limits
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    ∃ eplus eminus : ℝ, 0 ≤ eplus ∧ eminus ≤ 0 ∧
      Tendsto (fun β => gaussianPatternLimit α β/β) atTop (𝓝 eplus) ∧
      Tendsto (fun β => gaussianPatternLimit α (-β)/β) atTop (𝓝 eminus) ∧
      (TendstoInMeasure P (fun k ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)) atTop
        (fun _ => Real.sqrt (2*eplus)) ∧
       Tendsto (fun k => eLpNorm (fun ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)-
        Real.sqrt (2*eplus)) 1 P) atTop (𝓝 0)) ∧
      (TendstoInMeasure P (fun k ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1))
        atTop (fun _ => Real.sqrt (-2*eminus)) ∧
       Tendsto (fun k => eLpNorm (fun ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1)-
          Real.sqrt (-2*eminus)) 1 P) atTop (𝓝 0)) := by
  obtain ⟨ep,hpp,hpL1,hpmean,hpt⟩ := gaussianPattern_ground_limit
    hhaar hgauss hpub α hα hmp hds P Z hZ hlaw 1
  obtain ⟨em,hmpb,hmL1,hmmean,hmt⟩ := gaussianPattern_ground_limit
    hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (-1)
  have hp0 : 0 ≤ ep := le_of_tendsto_of_tendsto tendsto_const_nhds hpmean
    (Filter.Eventually.of_forall fun k => integral_nonneg fun ω =>
      gaussianPatternGroundEnergy_nonneg 1 zero_le_one _)
  have hm0 : em ≤ 0 := le_of_tendsto_of_tendsto hmmean tendsto_const_nhds
    (Filter.Eventually.of_forall fun k => integral_nonpos fun ω =>
      gaussianPatternGroundEnergy_nonpos (-1) (by norm_num) _)
  have hp := random_sqrt_scaled_limit P _ ep 2 (by norm_num)
    (fun k => (measurable_gaussianPatternGroundEnergy _ _ 1).comp (hZ (k+1)))
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw 1) hpp
  have hm := random_sqrt_scaled_limit P _ em (-2) (by norm_num)
    (fun k => (measurable_gaussianPatternGroundEnergy _ _ (-1)).comp (hZ (k+1)))
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw (-1)) hmpb
  have heqplus (k : ℕ) (ω : Ω) : Real.sqrt (2*gaussianPatternGroundEnergy 1 (Z (k+1) ω))=
      ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1) := by
    simpa only [Nat.cast_succ] using
      gaussianPattern_max_sqrt (Nat.succ_pos k) (Z (k+1) ω)
  have heqminus (k : ℕ) (ω : Ω) : Real.sqrt (-2*gaussianPatternGroundEnergy (-1) (Z (k+1) ω))=
      (Finset.univ.inf' Finset.univ_nonempty
        (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1) := by
    simpa only [Nat.cast_succ] using
      gaussianPattern_min_sqrt (Nat.succ_pos k) (Z (k+1) ω)
  simp only [Function.comp_apply,heqplus] at hp
  simp only [Function.comp_apply,heqminus] at hm
  refine ⟨ep,em,hp0,hm0,?_,?_,hp,hm⟩
  · simpa only [one_mul] using hpt
  · simpa only [neg_one_mul] using hmt

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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

theorem gaussianPattern_norm_limits_unconditional_oai :
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P),
    ∃ eplus eminus : ℝ, 0 ≤ eplus ∧ eminus ≤ 0 ∧
      Tendsto (fun β => gaussianPatternLimit α β/β) atTop (𝓝 eplus) ∧
      Tendsto (fun β => gaussianPatternLimit α (-β)/β) atTop (𝓝 eminus) ∧
      (TendstoInMeasure P (fun k ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)) atTop
        (fun _ => Real.sqrt (2*eplus)) ∧
       Tendsto (fun k => eLpNorm (fun ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)-
        Real.sqrt (2*eplus)) 1 P) atTop (𝓝 0)) ∧
      (TendstoInMeasure P (fun k ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1))
        atTop (fun _ => Real.sqrt (-2*eminus)) ∧
       Tendsto (fun k => eLpNorm (fun ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1)-
          Real.sqrt (-2*eminus)) 1 P) atTop (𝓝 0)) :=
  fun α hα => @gaussianPattern_norm_limits haarConcentration_proved gaussianLipschitzVariance_proved panchenkoTalagrandFieldPair_proved α hα (marchenkoPastur_proved α hα) (davidsonSzarek_proved α hα)

end InvariantIsing

end

end OAI
end

theorem solution.{u} : type_of% @OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional_oai.{u} := @OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional_oai.{u}
