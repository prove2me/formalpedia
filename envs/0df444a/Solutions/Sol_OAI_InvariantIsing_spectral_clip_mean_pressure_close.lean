-- Prove2me | solution 1 for OAI.InvariantIsing.spectral_clip_mean_pressure_close
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:18:07.635809+00:00
-- url     : https://prove2.me/submissions/bfbb71fc-5077-450f-b74b-fc9c6e015727

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
import Definitions.Def_OAIQ258004

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCountComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity and scalar shifts for the pointwise and mean pressures.
These are the finite-volume squeeze estimates used in spectral discretization. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma rotatedEnergy_mono {N : ℕ} (eig kap : Fin N → ℝ) (U : Rotation N)
    (h : ∀ i, eig i ≤ kap i) (σ : Spin N) :
    rotatedEnergy eig U σ ≤ rotatedEnergy kap U σ := by
  unfold rotatedEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

lemma rotatedPressure_mono {N : ℕ} (eig kap c : Fin N → ℝ) (U : Rotation N)
    (h : ∀ i, eig i ≤ kap i) :
    rotatedPressure eig U c ≤ rotatedPressure kap U c := by
  have hp := logPartition_le_add
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy kap U σ + fieldEnergy c σ) 0
    (fun σ => by simpa only [add_zero] using add_le_add (rotatedEnergy_mono eig kap U h σ) le_rfl)
  simpa only [rotatedPressure, add_zero] using
    mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg N))

lemma rotatedEnergy_add_scalar {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (a : ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => eig i + a) U σ = rotatedEnergy eig U σ + a * N / 2 := by
  simp only [rotatedEnergy, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    rotated_spin_sq_sum]
  ring

lemma rotatedPressure_add_scalar {N : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (a : ℝ) :
    rotatedPressure (fun i => eig i + a) U c = rotatedPressure eig U c + a / 2 := by
  have he : (fun σ => rotatedEnergy (fun i => eig i + a) U σ + fieldEnergy c σ) =
      (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ + a * N / 2) := by
    funext σ
    rw [rotatedEnergy_add_scalar]
    ring
  rw [rotatedPressure, he, logPartition_add_const]
  unfold rotatedPressure
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma meanPressure_add_scalar {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig c : Fin N → ℝ) (a K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    (∫ U, rotatedPressure (fun i => eig i + a) (specialRotation U) c ∂μ) =
      (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) + a / 2 := by
  simp_rw [rotatedPressure_add_scalar hN]
  rw [integral_add (integrable_countPressure hN μ eig c K heig) (integrable_const _)]
  simp

lemma meanPressure_squeeze {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig lo hi c : Fin N → ℝ) (δ K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hlo : ∀ i, |lo i| ≤ K) (hhi : ∀ i, |hi i| ≤ K)
    (hl : ∀ i, lo i - δ ≤ eig i) (hu : ∀ i, eig i ≤ hi i + δ) :
    (∫ U, rotatedPressure lo (specialRotation U) c ∂μ) - δ / 2 ≤
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ ∧
    (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) ≤
      (∫ U, rotatedPressure hi (specialRotation U) c ∂μ) + δ / 2 := by
  have hli : Integrable (fun U => rotatedPressure (fun i => lo i + -δ) (specialRotation U) c) μ := by
    simp_rw [rotatedPressure_add_scalar hN]
    exact (integrable_countPressure hN μ lo c K hlo).add (integrable_const _)
  have hui : Integrable (fun U => rotatedPressure (fun i => hi i + δ) (specialRotation U) c) μ := by
    simp_rw [rotatedPressure_add_scalar hN]
    exact (integrable_countPressure hN μ hi c K hhi).add (integrable_const _)
  have hei := integrable_countPressure hN μ eig c K heig
  have hlow := integral_mono hli hei (fun U =>
    rotatedPressure_mono _ _ c (specialRotation U) (fun i => by simpa only [sub_eq_add_neg] using hl i))
  have hupp := integral_mono hei hui (fun U => rotatedPressure_mono _ _ c (specialRotation U) hu)
  rw [meanPressure_add_scalar hN μ lo c (-δ) K hlo] at hlow
  rw [meanPressure_add_scalar hN μ hi c δ K hhi] at hupp
  exact ⟨by linarith, hupp⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralSqueeze
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral discretization squeeze for physical orthogonal pressure. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_meanPressure_squeeze {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig lo hi c : Fin N → ℝ) (δ K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hlo : ∀ i, |lo i| ≤ K) (hhi : ∀ i, |hi i| ≤ K)
    (hl : ∀ i, lo i-δ ≤ eig i) (hu : ∀ i, eig i ≤ hi i+δ) :
    (∫ V, rotatedPressure lo (matrixRotation V⁻¹) c ∂μ)-δ/2 ≤
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ ∧
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ) ≤
      (∫ V, rotatedPressure hi (matrixRotation V⁻¹) c ∂μ)+δ/2 := by
  have hh := meanPressure_squeeze hN (cavityOrientedBaseLaw hN μ) eig lo hi c δ K heig hlo hhi hl hu
  simpa only [cavity_oriented_pressure] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralClipping
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping the finite spectra to the limiting support interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma spectralClip_eq {a b x : ℝ} (hx : x∈Icc a b) : spectralClip a b x=x := by
  simp only [spectralClip,min_eq_right hx.2,max_eq_right hx.1]

lemma spectralClip_close {a b x η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hx : a-η ≤ x ∧ x ≤ b+η) : |spectralClip a b x-x| ≤ η := by
  by_cases ha : x < a
  · have he : spectralClip a b x=a := by simp [spectralClip,min_eq_right (ha.le.trans hab),max_eq_left ha.le]
    rw [he,abs_of_nonneg (sub_nonneg.mpr ha.le)]
    linarith [hx.1]
  · by_cases hb : b < x
    · have he : spectralClip a b x=b := by simp [spectralClip,min_eq_left hb.le,max_eq_right hab]
      rw [he,abs_of_nonpos (sub_nonpos.mpr hb.le)]
      linarith [hx.2]
    · rw [spectralClip_eq ⟨le_of_not_gt ha,le_of_not_gt hb⟩,sub_self,abs_zero]
      exact hη

lemma spectral_clip_mean_pressure_close_oai {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig : Fin N → ℝ)
    (a b η : ℝ) (hab : a ≤ b) (hη : 0 ≤ η)
    (heig : ∀ i, a-η ≤ eig i ∧ eig i ≤ b+η) :
    |(∫ V, rotatedPressure (fun i => spectralClip a b (eig i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ)-
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) (fun _ => 0) ∂μ| ≤ η/2 := by
  let K := (∑ i, |eig i|)+|a|+|b|
  have hsum : 0 ≤ ∑ i, |eig i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi i : |eig i| ≤ K := by
    have hh := Finset.single_le_sum (fun i _ => abs_nonneg (eig i)) (Finset.mem_univ i)
    dsimp [K]
    linarith [abs_nonneg a,abs_nonneg b]
  have hc i : |spectralClip a b (eig i)| ≤ K := by
    have hh := spectralClip_mem hab (eig i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hh.1,hh.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hd i := abs_le.mp (spectralClip_close hab hη (heig i))
  have hh := cavity_meanPressure_squeeze hN μ eig
    (fun i => spectralClip a b (eig i)) (fun i => spectralClip a b (eig i))
    (fun _ => 0) η K hi hc hc
    (fun i => by linarith [(hd i).2]) (fun i => by linarith [(hd i).1])
  rw [abs_le]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spectral_clip_mean_pressure_close_oai := @OAI.InvariantIsing.spectral_clip_mean_pressure_close_oai
