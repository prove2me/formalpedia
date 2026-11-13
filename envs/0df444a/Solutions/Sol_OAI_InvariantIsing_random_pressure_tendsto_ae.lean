-- Prove2me | solution 1 for OAI.InvariantIsing.random_pressure_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:11.697427+00:00
-- url     : https://prove2.me/submissions/906d4bac-7a95-408a-86d1-7144bb4980f0

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
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
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
import Theorems.Thm_OAI_InvariantIsing_compact_spectral_pressure_tendsto_of_mem
import Theorems.Thm_OAI_InvariantIsing_spectral_clip_empirical_tendsto
import Theorems.Thm_OAI_InvariantIsing_spectral_clip_mean_pressure_close

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureLipschitz
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GeneralSpectralPressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general compact spectral law and no-outlier mean-pressure theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem general_spectral_mean_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hab : a ≤ b := (hbound ha).2
  have hc := compact_spectral_pressure_tendsto_of_mem hhaar hgauss hpub μ
    (fun N i => spectralClip a b (eig N i)) ν a b hcompact hbound ha hb
    (fun N i => spectralClip_mem hab (eig N i))
    (spectral_clip_empirical_tendsto eig ν a b hbound hweak)
  have hη := spectralExcess_tendsto eig a b hno
  have hd : Tendsto (fun N =>
      (∫ V, rotatedPressure (fun i => spectralClip a b (eig N i))
        (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)-
      ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun _ => 0) ∂μ N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [zero_div] using hη.div_const 2)
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs] using spectral_clip_mean_pressure_close (by omega)
      (μ N) (eig N) a b (spectralExcess (eig N) a b) hab
      (spectralExcess_nonneg _ _ _) (spectralExcess_bounds _ _ _)
  have hh := hc.sub hd
  simpa only [sub_sub_cancel,sub_zero] using hh

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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

lemma spectralRadius_eventually_bounded_of_no_outliers
    (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig (k+1)) ≤ K := by
  refine ⟨max |a| |b|+1,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hno 1 zero_lt_one)] with k hk
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomOrbitAlmostSure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure conditional Haar concentration for random spectra and fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

theorem ae_random_orbit_pressure_sub_mean (hhaar : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : (N : ℕ) → Ω → FieldSpectralData N) (Y : ℕ → Ω → ℝ)
    (hd : ∀ N, Measurable (d N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H N))
    (hbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius ((d (k+1) ω).1) ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Y (k+1) ω-
      ∫ U, dataPhysicalPressure (d (k+1) ω) U ∂H (k+1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_localized_exponential_tail P
    (fun k ω => Y (k+1) ω-∫ U, dataPhysicalPressure (d (k+1) ω) U ∂H (k+1))
    (fun k ω => spectralRadius ((d (k+1) ω).1)) _ hbound
  intro K ε hK hε
  obtain ⟨C,a,hC,ha,ht⟩ := uniform_physical_pressure_mean_tail hhaar
  obtain ⟨N₀,hN₀⟩ := ht K ε hK hε
  refine ⟨C,a*(ε/2)^2/K^2,hC.le,by positivity,max N₀ 3,?_⟩
  intro n hn
  have hb := conditional_orbit_tail_bound (Nat.succ_pos n) P (d (n+1)) (Y (n+1))
    (hd (n+1)) (hY (n+1)) (H (n+1)) (hlaw (n+1)) K ε
    (C*Real.exp (-a*(n+1 : ℝ)*(ε/2)^2/K^2)) (fun data hdata => by
      simpa only [dataPhysicalPressure,Nat.cast_add,Nat.cast_one] using
        hN₀ (n+1) (by omega) (by omega) (H (n+1)) inferInstance inferInstance
          data.1 data.2 hdata)
  have he : {ω | (∀ i, |(d (n+1) ω).1 i| ≤ K) ∧
      ε ≤ |Y (n+1) ω-∫ U, dataPhysicalPressure (d (n+1) ω) U ∂H (n+1)|}=
      {ω | ε ≤ |Y (n+1) ω-∫ U, dataPhysicalPressure (d (n+1) ω) U ∂H (n+1)| ∧
        spectralRadius ((d (n+1) ω).1) ≤ K} := by
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
    -a*(n+1 : ℝ)*(ε/2)^2/K^2= -(a*(ε/2)^2/K^2)*((n : ℝ)+1) := by ring
    _ ≤ -(a*(ε/2)^2/K^2)*(n : ℝ) := by nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomPressureAlmostSure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The almost-sure random-spectrum pressure theorem, under the conditional
orbit law in Proposition gen:random. No global integrability is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_tendsto_ae_oai
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
    (hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ eig N ω i ∧ eig N ω i ≤ b+ε)
    (hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω)) atTop (𝓝 ν)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hbounded : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop,
      spectralRadius (eig (k+1) ω) ≤ K := hno.mono fun ω hω =>
    spectralRadius_eventually_bounded_of_no_outliers (fun N => eig N ω) a b hω
  have ht := ae_random_orbit_pressure_sub_mean hhaar P
    (fun N ω => (eig N ω,fun _ => 0)) Y
    (fun N => (heig N).prodMk measurable_const) hY H hlaw hbounded
  filter_upwards [ht,hno,hweak] with ω hω hn hw
  have hm := general_spectral_mean_pressure_tendsto hhaar hgauss hpub H
    (fun N => eig N ω) ν a b hcompact hbound ha hb hn hw
  have hadd := hω.add (hm.comp (tendsto_add_atTop_nat 1))
  simp only [dataPhysicalPressure,Function.comp_apply,sub_add_cancel,zero_add] at hadd
  exact (tendsto_add_atTop_iff_nat 1).mp hadd

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.random_pressure_tendsto_ae_oai.{u_1} := @OAI.InvariantIsing.random_pressure_tendsto_ae_oai.{u_1}
