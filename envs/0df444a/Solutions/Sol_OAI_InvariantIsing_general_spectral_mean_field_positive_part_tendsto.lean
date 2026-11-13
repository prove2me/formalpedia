-- Prove2me | solution 1 for OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:27:18.883875+00:00
-- url     : https://prove2.me/submissions/e1d4dabb-4585-4b0c-85e8-3f44b8f8e9c2

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_compact_spectral_field_pressure_tendsto_of_mem
import Theorems.Thm_OAI_InvariantIsing_spectral_clip_empirical_tendsto
import Theorems.Thm_OAI_InvariantIsing_spectral_clip_mean_field_pressure_close

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_Concentration
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySphereAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSides
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match as many sites of each field label as both finite populations contain. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma fieldLabelInjection_label {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) (s : A → ℕ) (hs : ∀ a, s a ≤ spinGroupSize g a)
    (x : Σ a, Fin (s a)) : g (fieldLabelInjection g s hs x)=x.1 :=
  ((Fintype.equivFin {i : Fin N // g i=x.1}).symm
    (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs x.1) x.2)).property

theorem exists_field_label_matching {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) : ∃ p : Equiv.Perm (Fin N),
      (Finset.univ.filter (fun i => g i=h (p i))).card ≥
        ∑ a, min (spinGroupSize g a) (spinGroupSize h a) := by
  let s := fun a => min (spinGroupSize g a) (spinGroupSize h a)
  let f := fieldLabelInjection g s (fun a => min_le_left _ _)
  let k := fieldLabelInjection h s (fun a => min_le_right _ _)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f k f.injective k.injective
  refine ⟨p,?_⟩
  have hsub : Finset.univ.image f ⊆ Finset.univ.filter (fun i => g i=h (p i)) := by
    intro i hi
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hp]
    exact (fieldLabelInjection_label g s _ x).trans (fieldLabelInjection_label h s _ x).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ f.injective] at hc
  simpa only [Finset.card_univ, Fintype.card_sigma, Fintype.card_fin, s] using hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldMatchingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unmatched field sites are controlled by differences of label counts. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma fieldLabelCount_sum {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) : ∑ a, spinGroupSize g a=N := by
  simpa only [Fintype.card_sigma, Fintype.card_subtype, spinGroupSize, Fintype.card_fin] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv g)

theorem exists_field_permutation_l1_bound {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) (b : A → ℝ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ a, |b a| ≤ B) :
    ∃ p : Equiv.Perm (Fin N),
      (∑ i, |b (g i)-b (h (p i))|) ≤
        2*B*∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a| := by
  obtain ⟨p,hp⟩ := exists_field_label_matching g h
  let S := Finset.univ.filter (fun i => g i=h (p i))
  let T := Finset.univ \ S
  have hsmall : ∑ a, min (spinGroupSize g a) (spinGroupSize h a) ≤ N :=
    (Finset.sum_le_sum (fun a _ => min_le_left _ _)).trans_eq (fieldLabelCount_sum g)
  have hmiss : ((N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) : ℕ) : ℝ) ≤
      ∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a| := by
    rw [Nat.cast_sub hsmall]
    have hn : (N : ℝ)=∑ a, (spinGroupSize g a : ℝ) := by
      exact_mod_cast (fieldLabelCount_sum g).symm
    rw [hn, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : spinGroupSize g a ≤ spinGroupSize h a
    · rw [min_eq_left ha, sub_self]
      exact abs_nonneg _
    · rw [min_eq_right (by omega)]
      exact le_abs_self _
  have hT : T.card ≤ N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simpa only [Finset.card_univ, Fintype.card_fin] using Nat.sub_le_sub_left hp N
  have hsum : (∑ i, |b (g i)-b (h (p i))|) ≤ (T.card : ℝ)*(2*B) := by
    have he : (∑ i, |b (g i)-b (h (p i))|)=∑ i ∈ T, |b (g i)-b (h (p i))| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro i _ hi
      have hg : g i=h (p i) := by
        by_contra hn
        exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hn⟩)
      rw [hg,sub_self,abs_zero]
    rw [he]
    calc
      _ ≤ ∑ _i ∈ T, 2*B := Finset.sum_le_sum fun i _ =>
        (abs_sub _ _).trans (by linarith [hb (g i),hb (h (p i))])
      _ = _ := by simp
  refine ⟨p, hsum.trans ?_⟩
  calc
    (T.card : ℝ)*(2*B) ≤ ((N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) : ℕ) : ℝ)*(2*B) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hT) (by positivity)
    _ ≤ (∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a|)*(2*B) :=
      mul_le_mul_of_nonneg_right hmiss (by positivity)
    _ = _ := mul_comm _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PhysicalFieldPermutation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A deterministic permutation of field sites preserves the physical Haar mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace InvariantIsing

lemma spinVector_fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N)) (σ : Spin N) :
    spinVector (cavitySignedSpinPermutation p (fun _ => false) σ)=
      matrixRotation (fieldSitePermutation p) (spinVector σ) := by
  ext i
  change spinValue (σ (p i))=((p.permMatrix ℝ)*ᵥ (spinVector σ).ofLp) i
  rw [Matrix.permMatrix_mulVec]
  rfl

lemma rotatedPressure_fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N))
    (eig c : Fin N → ℝ) (U : Orthogonal N) :
    rotatedPressure eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) (fun i => c (p i))=
      rotatedPressure eig (matrixRotation U) c := by
  let e := cavitySignedSpinPermutation p (fun _ => false)
  have he (σ : Spin N) :
      rotatedEnergy eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) (e σ)=
        rotatedEnergy eig (matrixRotation U) σ := by
    have hv : matrixRotation (U*(fieldSitePermutation p)⁻¹) (spinVector (e σ))=
        matrixRotation U (spinVector σ) := by
      rw [spinVector_fieldSitePermutation, ← cavity_matrixRotation_mul_apply]
      simp only [inv_mul_cancel_right]
    simp only [rotatedEnergy,hv]
  have hc (σ : Spin N) : fieldEnergy (fun i => c (p i)) (e σ)=fieldEnergy c σ := by
    change (∑ i, c (p i)*spinValue (σ (p i)))=∑ i, c i*spinValue (σ i)
    exact Equiv.sum_comp p (fun i => c i*spinValue (σ i))
  let H := fun σ => Real.exp (rotatedEnergy eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) σ+
    fieldEnergy (fun i => c (p i)) σ)
  have hh : (∑ σ, H σ)=∑ σ, Real.exp (rotatedEnergy eig (matrixRotation U) σ+fieldEnergy c σ) := by
    rw [← Equiv.sum_comp e H]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [H]
    rw [he,hc]
  exact congrArg (fun x => (N : ℝ)⁻¹*Real.log ((Fintype.card (Spin N) : ℝ)⁻¹*x)) hh

lemma physical_meanPressure_field_permutation {N : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (p : Equiv.Perm (Fin N)) (eig c : Fin N → ℝ) :
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) (fun i => c (p i)) ∂μ)=
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ := by
  let : μ.IsMulLeftInvariant := cavity_right_probability_left μ
  rw [← integral_mul_left_eq_self
    (fun V => rotatedPressure eig (matrixRotation V⁻¹) (fun i => c (p i)))
    (fieldSitePermutation p)]
  apply integral_congr_ae
  filter_upwards [] with V
  simp only [mul_inv_rev]
  exact rotatedPressure_fieldSitePermutation p eig c V⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralLabelCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts on arbitrary finite spectral labels and their deterministic relabeling. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

lemma spectralLabelCount_relabel {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {N : ℕ} (g : Fin N → ι) (f : ι → κ) (b : κ) :
    spectralLabelCount (f ∘ g) b =
      ∑ a : {a : ι // f a=b}, spectralLabelCount g a := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter Finset.univ
    (Finset.univ.filter (fun a => f a=b)) g
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => f a=b)) (by simp)
    (fun a => spectralLabelCount g a)]
  simpa only [spectralLabelCount, Finset.mem_filter,Finset.mem_univ,true_and,
    Function.comp_apply] using hh.symm

lemma spectral_label_counts_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → ι) (w : ι → ℝ)
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 w))
    (f : ι → κ) :
    Tendsto (fun k b => (spectralLabelCount (f ∘ g k) b : ℝ)/N k) atTop
      (𝓝 (fun b => ∑ a : {a : ι // f a=b}, w a)) := by
  apply tendsto_pi_nhds.mpr
  intro b
  have hh := tendsto_finsetSum (Finset.univ : Finset {a : ι // f a=b}) (fun a _ =>
    (tendsto_pi_nhds.mp hlim) (a : ι))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  rw [spectralLabelCount_relabel, Nat.cast_sum, Finset.sum_div]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveSpectralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove zero limiting weights without dropping their finite-volume labels. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

lemma positiveSpectralLabel_self {ι : Type*} (w : ι → ℝ)
    (fallback i : {i // 0 < w i}) : positiveSpectralLabel w fallback i=i := by
  simp only [positiveSpectralLabel, dite_eq_left i.property]

lemma positiveSpectralLabel_weight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (fallback b : {i // 0 < w i}) :
    (∑ a : {a // positiveSpectralLabel w fallback a=b}, w a)=w b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => positiveSpectralLabel w fallback a=b))
    (by simp) w]
  apply Finset.sum_eq_single b.val
  · intro a ha hab
    by_cases hp : 0 < w a
    · have hh : positiveSpectralLabel w fallback a=b := (Finset.mem_filter.mp ha).2
      have he : a=b.val := by
        simpa only [positiveSpectralLabel,dite_eq_left hp] using congrArg Subtype.val hh
      exact (hab he).elim
    · exact le_antisymm (le_of_not_gt hp) (hw a)
  · intro hb
    exact (hb (by simp [positiveSpectralLabel_self])).elim

lemma positive_spectral_counts_tendsto {ι : Type*} [Fintype ι]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (fallback : {i // 0 < w i})
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 w)) :
    Tendsto (fun k b =>
      (spectralLabelCount (positiveSpectralLabel w fallback ∘ g k) b : ℝ)/N k)
      atTop (𝓝 (fun b : {i // 0 < w i} => w b)) := by
  apply tendsto_pi_nhds.mpr
  intro b
  have hh := (tendsto_pi_nhds.mp
    (spectral_label_counts_relabel N g w hlim (positiveSpectralLabel w fallback))) b
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg nhds
  calc
    w b = ∑ a : {a // positiveSpectralLabel w fallback a=b}, w a :=
      (positiveSpectralLabel_weight w hw fallback b).symm
    _ = _ := by
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_univ]
      · intro a _
        rfl

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

lemma spectralExcess_nonneg {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) :
    0 ≤ spectralExcess eig a b := Finset.le_max' _ _ (Finset.mem_insert_self _ _)

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

lemma spectralExcess_le {N : ℕ} (eig : Fin N → ℝ) (a b ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i, a-ε ≤ eig i ∧ eig i ≤ b+ε) : spectralExcess eig a b ≤ ε := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hε
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact max_le (by linarith [(h i).1]) (by linarith [(h i).2])

lemma spectralExcess_tendsto (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    Tendsto (fun N => spectralExcess (eig N) a b) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h (ε/2) (by positivity)] with N hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (spectralExcess_nonneg _ _ _)]
  exact (spectralExcess_le _ _ _ _ (by positivity) hN).trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PhysicalPressureMean
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expectations on an arbitrary probability space carrying the physical Haar matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

lemma measurable_physicalPressure {N : ℕ} (hN : 0 < N) (eig c : Fin N → ℝ) :
    Measurable (fun U : Orthogonal N => rotatedPressure eig (matrixRotation U⁻¹) c) := by
  have hm := (measurable_rotatedPressure eig c).comp
    ((measurable_cavityOrientationLift hN).comp measurable_inv)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext U
  simp only [Function.comp_apply,rotatedPressure,cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GroundStateMean
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable physical energies and the expected soft-maximum inequality. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace InvariantIsing

lemma integrable_physicalPressure {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig c : Fin N → ℝ) :
    Integrable (fun ω => rotatedPressure eig (matrixRotation (U ω)⁻¹) c) P := by
  let K := ∑ i, |eig i|
  have he i : |eig i| ≤ K := Finset.single_le_sum (f := fun i => |eig i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  apply (integrable_const (K/2+|noninteractingPressure c|)).mono'
    ((measurable_physicalPressure hN eig c).comp hU).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  have hb := abs_pressure_sub_noninteracting_le hN eig c (matrixRotation (U ω)⁻¹) K he
  have ha := abs_add_le (rotatedPressure eig (matrixRotation (U ω)⁻¹) c-noninteractingPressure c)
    (noninteractingPressure c)
  rw [sub_add_cancel] at ha
  exact ha.trans (add_le_add hb le_rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PhysicalFieldComparison
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field populations with nearby label proportions have nearby Haar-mean pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma abs_rotatedPressure_fields_le {N : ℕ} (eig c d : Fin N → ℝ) (U : Rotation N) :
    |rotatedPressure eig U c-rotatedPressure eig U d| ≤
      (N : ℝ)⁻¹*∑ i, |c i-d i| := by
  have hh := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ)
    (fun σ => rotatedEnergy eig U σ+fieldEnergy d σ)
    (∑ i, |c i-d i|) (fun σ => by
      simpa only [add_sub_add_left_eq_sub] using abs_fieldEnergy_sub_le c d σ)
  have hni : (0 : ℝ)≤(N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  simpa only [rotatedPressure,← mul_sub,abs_mul,abs_of_nonneg hni] using
    mul_le_mul_of_nonneg_left hh hni

lemma physical_mean_field_l1_le {N : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig c d : Fin N → ℝ) :
    |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) c ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) d ∂μ| ≤
      (N : ℝ)⁻¹*∑ i, |c i-d i| := by
  have hc := integrable_physicalPressure hN μ id measurable_id eig c
  have hd := integrable_physicalPressure hN μ id measurable_id eig d
  simp only [id_eq] at hc hd
  change |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) c ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) d ∂μ| ≤ _
  rw [← integral_sub hc hd]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => rotatedPressure eig (matrixRotation U⁻¹) c-rotatedPressure eig (matrixRotation U⁻¹) d)
    (C := (N : ℝ)⁻¹*∑ i, |c i-d i|)
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using abs_rotatedPressure_fields_le eig c d (matrixRotation U⁻¹))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

lemma physical_mean_field_counts_le {N : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (eig : Fin N → ℝ) {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) (b : A → ℝ) {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) (fun i => b (g i)) ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) (fun i => b (h i)) ∂μ| ≤
      2*B*∑ a, |(spinGroupSize g a : ℝ)/N-(spinGroupSize h a : ℝ)/N| := by
  obtain ⟨p,hp⟩ := exists_field_permutation_l1_bound g h b hB hb
  rw [← physical_meanPressure_field_permutation μ p eig (fun i => b (h i))]
  refine (physical_mean_field_l1_le hN μ eig _ _).trans
    ((mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq ?_)
  have hnz : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  simp_rw [← sub_div,abs_div,abs_of_pos hnz]
  rw [← Finset.sum_div]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGeneralSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact spectral law formula with finite external fields and no outliers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem general_spectral_mean_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  have hab : a ≤ b := (hbound ha).2
  have hc := compact_spectral_field_pressure_tendsto_of_mem hhaar hgauss hpub μ
    (fun N i => spectralClip a b (eig N i)) ν a b hcompact hbound ha hb
    (fun N i => spectralClip_mem hab (eig N i))
    (spectral_clip_empirical_tendsto eig ν a b hbound hweak) group γ c hγ hγsum hgroup
  have hη := spectralExcess_tendsto eig a b hno
  have hd : Tendsto (fun N =>
      (∫ V, rotatedPressure (fun i => spectralClip a b (eig N i))
        (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)-
      ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [zero_div] using hη.div_const 2)
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs] using spectral_clip_mean_field_pressure_close (by omega)
      (μ N) (eig N) a b (spectralExcess (eig N) a b) hab
      (spectralExcess_nonneg _ _ _) (spectralExcess_bounds _ _ _) (fun i => c (group N i))
  have hh := hc.sub hd
  simpa only [sub_sub_cancel,sub_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_ZeroFieldPopulations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing field populations can be relabeled into a positive population. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

lemma spectralLabelCount_eq_spinGroupSize {N : ℕ} {A : Type*} [DecidableEq A]
    (g : Fin N → A) (a : A) : spectralLabelCount g a=spinGroupSize g a := by
  unfold spectralLabelCount spinGroupSize
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

lemma positiveFieldProjection_weight {A : Type*} [Fintype A]
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (fallback : {a // 0 < γ a}) (b : A) :
    (∑ a : {a // positiveFieldProjection γ fallback a=b}, γ a)=γ b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => positiveFieldProjection γ fallback a=b))
    (by simp) γ,Finset.sum_filter]
  have hi a : (if positiveFieldProjection γ fallback a=b then γ a else 0)=
      (if a=b then γ a else 0) := by
    by_cases hp : 0 < γ a
    · simp only [positiveFieldProjection,positiveSpectralLabel,dite_eq_left hp]
    · have hz : γ a=0 := le_antisymm (le_of_not_gt hp) (hγ a)
      simp only [hz,ite_self]
  simp_rw [hi]
  simp

lemma positiveFieldProjection_counts {A : Type*} [Fintype A]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → A)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (fallback : {a // 0 < γ a})
    (hg : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 γ)) :
    Tendsto (fun k a => (spectralLabelCount (positiveFieldProjection γ fallback ∘ g k) a : ℝ)/N k)
      atTop (𝓝 γ) := by
  have hh := spectral_label_counts_relabel N g γ hg (positiveFieldProjection γ fallback)
  simpa only [positiveFieldProjection_weight γ hγ fallback] using hh

lemma physical_mean_zero_field_populations {A : Type*} [Fintype A] [DecidableEq A]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (g : (N : ℕ) → Fin N → A) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (fallback : {a // 0 < γ a})
    (hg : Tendsto (fun N a => (spinGroupSize (g N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => (∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹) (fun i => c (g N i)) ∂μ N)-
      ∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹)
        (fun i => c (positiveFieldProjection γ fallback (g N i))) ∂μ N) atTop (𝓝 0) := by
  let h := fun N => positiveFieldProjection γ fallback ∘ g N
  have hh : Tendsto (fun N a => (spinGroupSize (h N) a : ℝ)/N) atTop (𝓝 γ) := by
    have hh := positiveFieldProjection_counts id g γ hγ fallback
      (by simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hg)
    simpa only [spectralLabelCount,spinGroupSize,id_eq,h] using hh
  let B := ∑ a, |c a|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hc a : |c a| ≤ B := Finset.single_le_sum (f := fun a => |c a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have ht := ((tendsto_finsetSum Finset.univ (fun a _ =>
    (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs)).const_mul (2*B))
  simp only [sub_self,abs_zero,Finset.sum_const_zero,mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa only [Real.norm_eq_abs,h,Function.comp_apply] using physical_mean_field_counts_le (by omega) (μ N)
    (eig N) (g N) (h N) c hB hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticZeroPopulationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-field pressure theorem permits labels with zero limiting mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

theorem general_spectral_mean_field_positive_part_tendsto_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1))) atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (fallback : {a // 0 < γ a})
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b)
        (fun i : {a // 0 < γ a} => γ i) (fun i => c i)).toReal) := by
  have hpos : Tendsto (fun N i =>
      (spinGroupSize (positiveSpectralLabel γ fallback ∘ group N) i : ℝ)/N)
      atTop (𝓝 (fun i : {a // 0 < γ a} => γ i)) :=
    by
      have hp := positive_spectral_counts_tendsto id group γ hγ fallback
        (by simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hgroup)
      simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hp
  have hp := general_spectral_mean_field_pressure_tendsto hhaar hgauss hpub μ eig ν a b
    hcompact hbound ha hb hno hweak (fun N => positiveSpectralLabel γ fallback ∘ group N)
    (fun i : {a // 0 < γ a} => γ i) (fun i => c i) (fun i => i.property)
    (positiveSpectralWeights_sum γ hγ hγsum) hpos
  have he := physical_mean_zero_field_populations μ eig group γ c hγ fallback hgroup
  have hh := he.add hp
  simpa only [sub_add_cancel,zero_add,positiveFieldProjection,Function.comp_apply] using hh

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto_oai.{u_1} := @OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto_oai.{u_1}
