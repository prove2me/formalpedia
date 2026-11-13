-- Prove2me | solution 1 for OAI.InvariantIsing.ground_state_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:30:23.893559+00:00
-- url     : https://prove2.me/submissions/a98aa083-9dc0-470a-8c50-22c2dfd7223d

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
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
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_positive_temperature_pressure

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinVector_apply
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

/-- The elementary log-sum bound, with the probability prior's entropy cost. -/
lemma logPartition_bounds {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (M : ℝ) (hM : ∀ x, H x ≤ M) (hx : ∃ x, H x = M) :
    M - Real.log (Fintype.card X) ≤ logPartition H ∧ logPartition H ≤ M := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hlo : Real.exp M ≤ ∑ x, Real.exp (H x) := by
    obtain ⟨x, hx⟩ := hx
    rw [← hx]
    exact Finset.single_le_sum (fun y _ => (Real.exp_pos (H y)).le) (Finset.mem_univ x)
  have hup : (∑ x, Real.exp (H x)) ≤ Fintype.card X * Real.exp M := by
    calc
      _ ≤ ∑ _ : X, Real.exp M :=
        Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (hM x)
      _ = _ := by simp
  rw [logPartition_eq]
  constructor
  · exact sub_le_sub_right (by simpa using Real.log_le_log (Real.exp_pos M) hlo) _
  · have hl := Real.log_le_log (sum_exp_pos H) hup
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero M), Real.log_exp] at hl
    linarith

/-- Uniform cube entropy is `N log 2`. -/
lemma log_card_spin (N : ℕ) : Real.log (Fintype.card (Spin N)) = N * Real.log 2 := by
  simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- Soft maximum estimate used in the zero-temperature corollary, valid at every
finite dimension and every positive inverse temperature. -/
lemma finite_groundState_squeeze {N : ℕ} (hN : 0 < N) (H : Spin N → ℝ)
    (β E : ℝ) (hβ : 0 < β) (hE : ∀ σ, H σ ≤ N * E)
    (hatt : ∃ σ, H σ = N * E) :
    E - Real.log 2 / β ≤ (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ∧
      (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ≤ E := by
  have hscale : ∀ σ, β * H σ ≤ β * (N * E) :=
    fun σ => mul_le_mul_of_nonneg_left (hE σ) hβ.le
  have hatt' : ∃ σ, β * H σ = β * (N * E) := by
    obtain ⟨σ, hσ⟩ := hatt
    exact ⟨σ, by rw [hσ]⟩
  obtain ⟨hlo, hhi⟩ := logPartition_bounds (fun σ => β * H σ) (β * (N * E)) hscale hatt'
  rw [log_card_spin] at hlo
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · have hl := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hn.le)
    apply (le_div_iff₀ hβ).mpr
    calc
      (E - Real.log 2 / β) * β = E * β - Real.log 2 := by field_simp
      _ = (N : ℝ)⁻¹ * (β * (N * E) - N * Real.log 2) := by field_simp
      _ ≤ _ := hl
  · apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hn.le)
    calc
      _ ≤ (N : ℝ)⁻¹ * (β * (N * E)) := hh
      _ = E * β := by field_simp

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

lemma rotatedEnergy_constant {N : ℕ} (a : ℝ) (U : Rotation N) (σ : Spin N) :
    rotatedEnergy (fun _ => a) U σ = a * N / 2 := by
  rw [rotatedEnergy, ← Finset.mul_sum, rotated_spin_sq_sum]
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
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

lemma rotatedEnergy_scale {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (t : ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => t * eig i) U σ = t * rotatedEnergy eig U σ := by
  simp only [rotatedEnergy, mul_assoc, ← Finset.mul_sum]
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralApproximationSqueeze
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final two-scale squeeze used in compact spectral approximation. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma spectral_approximation_squeeze (p : ℕ → ℝ) (lo hi : ℕ → ℕ → ℝ)
    (v δ : ℕ → ℝ) (L : ℝ) (hv : Tendsto v atTop (𝓝 L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hlo : ∀ k, Tendsto (lo k) atTop (𝓝 (v k)))
    (hhi : ∀ k, Tendsto (hi k) atTop (𝓝 (v k)))
    (hbound : ∀ k, ∀ᶠ N in atTop, lo k N-δ k/2 ≤ p N ∧ p N ≤ hi k N+δ k/2) :
    Tendsto p atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk,hdk⟩ := ((Metric.tendsto_nhds.mp hv (ε/3) (by positivity)).and
    (Metric.tendsto_nhds.mp hδ (ε/3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.mp (hlo k) (ε/3) (by positivity),
    Metric.tendsto_nhds.mp (hhi k) (ε/3) (by positivity),hbound k] with N hl hu hp
  rw [Real.dist_eq,abs_lt] at hk hdk hl hu ⊢
  constructor <;> linarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GroundStateFinite
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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

lemma groundStateEnergy_squeeze {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (β : ℝ) (hβ : 0 < β) :
    rotatedPressure (fun i => β*eig i) U (fun _ => 0)/β ≤ groundStateEnergy eig U ∧
      groundStateEnergy eig U ≤
        rotatedPressure (fun i => β*eig i) U (fun _ => 0)/β+Real.log 2/β := by
  have he := groundStateEnergy_attained hN eig U
  have hh := finite_groundState_squeeze hN (rotatedEnergy eig U) β
    (groundStateEnergy eig U) hβ he.1 he.2
  have hp : rotatedPressure (fun i => β*eig i) U (fun _ => 0)=
      (N : ℝ)⁻¹*logPartition (fun σ => β*rotatedEnergy eig U σ) := by
    simp only [rotatedPressure,rotatedEnergy_scale,fieldEnergy,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hp]
  exact ⟨hh.2,by linarith [hh.1]⟩

lemma abs_groundStateEnergy_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |groundStateEnergy eig U| ≤ K/2 := by
  obtain ⟨σ,hσ⟩ := (groundStateEnergy_attained hN eig U).2
  have hh := abs_rotatedEnergy_le eig U K hK σ
  rw [hσ,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

lemma measurable_groundStateEnergy {N : ℕ} (eig : Fin N → ℝ) :
    Measurable (fun V : SpecialOrthogonal N => groundStateEnergy eig (specialRotation V)) := by
  have hE (σ : Spin N) : Measurable (fun V : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation V) σ) :=
    (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul (eig i)).const_mul _
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun σ _ => hE σ)
  convert hh.const_mul (N : ℝ)⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  funext V
  simp only [groundStateEnergy,Finset.sup'_apply]

lemma measurable_physical_groundStateEnergy {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) :
    Measurable (fun V : Orthogonal N => groundStateEnergy eig (matrixRotation V⁻¹)) := by
  have hm := (measurable_groundStateEnergy eig).comp
    ((measurable_cavityOrientationLift hN).comp measurable_inv)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext V
  simp only [Function.comp_apply,groundStateEnergy,cavityOrientationLift_energy]

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

lemma integrable_physicalGroundState {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig : Fin N → ℝ) :
    Integrable (fun ω => groundStateEnergy eig (matrixRotation (U ω)⁻¹)) P := by
  let K := ∑ i, |eig i|
  have he i : |eig i| ≤ K := Finset.single_le_sum (f := fun i => |eig i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (integrable_const (K/2)).mono'
    ((measurable_physical_groundStateEnergy hN eig).comp hU).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using
      abs_groundStateEnergy_le hN eig (matrixRotation (U ω)⁻¹) K he)

lemma mean_groundState_squeeze {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig : Fin N → ℝ)
    (β : ℝ) (hβ : 0 < β) :
    (∫ ω, rotatedPressure (fun i => β*eig i) (matrixRotation (U ω)⁻¹) (fun _ => 0) ∂P)/β ≤
      (∫ ω, groundStateEnergy eig (matrixRotation (U ω)⁻¹) ∂P) ∧
    (∫ ω, groundStateEnergy eig (matrixRotation (U ω)⁻¹) ∂P) ≤
      (∫ ω, rotatedPressure (fun i => β*eig i) (matrixRotation (U ω)⁻¹) (fun _ => 0) ∂P)/β+
        Real.log 2/β := by
  have hp := integrable_physicalPressure hN P U hU (fun i => β*eig i) (fun _ => 0)
  have hg := integrable_physicalGroundState hN P U hU eig
  have hl := integral_mono (hp.div_const β) hg (fun ω =>
    (groundStateEnergy_squeeze hN eig (matrixRotation (U ω)⁻¹) β hβ).1)
  have hu := integral_mono hg ((hp.div_const β).add (integrable_const (Real.log 2/β))) (fun ω =>
    (groundStateEnergy_squeeze hN eig (matrixRotation (U ω)⁻¹) β hβ).2)
  rw [integral_div] at hl
  simp only [Pi.add_apply] at hu
  rw [integral_add (hp.div_const β) (integrable_const _),integral_div,integral_const,
    probReal_univ,one_smul] at hu
  exact ⟨hl,hu⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalLimitSqueeze
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer temperatures determine a unique deterministic zero-temperature limit. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma thermal_squeeze_tendsto (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c L : ℝ)
    (hc : 0 ≤ c) (hv : Tendsto v atTop (𝓝 L))
    (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    Tendsto g atTop (𝓝 L) := by
  have hδ : Tendsto (fun k : ℕ => 2*(c/(k+1))) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*c)
    simp only [mul_zero] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    ring
  apply spectral_approximation_squeeze g p p v (fun k => 2*(c/(k+1))) L hv hδ hp hp
  intro k
  filter_upwards [hb k] with N hN
  have hnonneg : 0 ≤ c/(k+1) := by positivity
  constructor <;> linarith [hN.1,hN.2]

lemma exists_thermal_ground_limit (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    ∃ L : ℝ, Tendsto v atTop (𝓝 L) ∧ Tendsto g atTop (𝓝 L) := by
  have horder (k l : ℕ) : v k ≤ v l+c/(l+1) := by
    apply le_of_tendsto_of_tendsto (hp k) ((hp l).add_const _)
    filter_upwards [hb k,hb l] with N hk hl
    exact hk.1.trans hl.2
  have hδ : Tendsto (fun k : ℕ => c/(k+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hC : CauchySeq v := by
    apply cauchySeq_of_le_tendsto_0 (fun k : ℕ => c/(k+1)) _ hδ
    intro n m k hn hm
    have hn' : (k : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hm' : (k : ℝ)+1 ≤ (m : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hm 1
    have hen : c/((n : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hn'
    have hem : c/((m : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hm'
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [horder n m,horder m n]
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨L,hL,thermal_squeeze_tendsto p g v c L hc hL hp hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GroundStateLimit
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic ground-state limit, almost surely and in expectation,
and the existence of the full real-temperature variational limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem ground_state_limit_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    ∃ M : ℝ,
      Tendsto (fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P)
        atTop (𝓝 M) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹))
        atTop (𝓝 M)) ∧
      Tendsto (thermalVariationalValue ν b) atTop (𝓝 M) := by
  let p := fun (k N : ℕ) => (∫ ω, rotatedPressure (fun i => ((k : ℝ)+1)*eig N i)
    (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/((k : ℝ)+1)
  let v := fun k : ℕ => thermalVariationalValue ν b ((k : ℝ)+1)
  let g := fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P
  have hc : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hp (k : ℕ) : Tendsto (p k) atTop (𝓝 (v k)) :=
    ((positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
      hbound ha hb hno ((k : ℝ)+1) (by positivity) hweak).1).div_const _
  have hmean (k : ℕ) : ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+Real.log 2/(k+1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mean_groundState_squeeze (by omega) P (U N) (hU N) (eig N) _ (by positivity)
  obtain ⟨M,hv,hg⟩ := exists_thermal_ground_limit p g v (Real.log 2) hc hp hmean
  refine ⟨M,hg,?_,?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto
        (fun N => rotatedPressure (fun i => ((k : ℝ)+1)*eig N i)
          (matrixRotation (U N ω)⁻¹) (fun _ => 0)/((k : ℝ)+1)) atTop (𝓝 (v k)) := by
      apply ae_all_iff.mpr
      intro k
      filter_upwards [(positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
        hbound ha hb hno ((k : ℝ)+1) (by positivity) hweak).2] with ω hω
      exact hω.div_const _
    filter_upwards [hall] with ω hω
    apply thermal_squeeze_tendsto _ _ v (Real.log 2) M hc hv hω
    intro k
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact groundStateEnergy_squeeze (by omega) (eig N) (matrixRotation (U N ω)⁻¹) _ (by positivity)
  · have hbounds (β : ℝ) (hβ : 0 < β) :
        thermalVariationalValue ν b β ≤ M ∧ M ≤ thermalVariationalValue ν b β+Real.log 2/β := by
      have ht := ((positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
        hbound ha hb hno β hβ hweak).1).div_const β
      have he : ∀ᶠ N in atTop,
          (∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/β ≤ g N ∧
          g N ≤ (∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/β+
            Real.log 2/β := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact mean_groundState_squeeze (by omega) P (U N) (hU N) (eig N) β hβ
      exact ⟨le_of_tendsto_of_tendsto ht hg (he.mono fun _ h => h.1),
        le_of_tendsto_of_tendsto hg (ht.add_const _) (he.mono fun _ h => h.2)⟩
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ (tendsto_id.const_div_atTop (Real.log 2))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    rw [Real.norm_eq_abs,abs_le]
    simp only [id_eq]
    have hh := hbounds β hβ
    constructor <;> linarith [hh.1,hh.2,div_nonneg hc hβ.le]

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.ground_state_limit_oai.{u_1} := @OAI.InvariantIsing.ground_state_limit_oai.{u_1}
