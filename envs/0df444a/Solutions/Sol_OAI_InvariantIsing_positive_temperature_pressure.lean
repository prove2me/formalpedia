-- Prove2me | solution 1 for OAI.InvariantIsing.positive_temperature_pressure
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:30:31.86968+00:00
-- url     : https://prove2.me/submissions/9a4da082-9f2b-452c-97f3-da46cbb7b359
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_physical_mean_pressure_tendsto
import Theorems.Thm_OAI_InvariantIsing_spectral_clip_empirical_tendsto

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
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
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

/-- Uniformly bounded observables with exponential tails about their medians
have means and medians asymptotically equal. -/
theorem tendsto_mean_sub_median_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (m : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n ω, |f n ω| ≤ B)
    (hl : ∀ n, (1 / 2 : ℝ) ≤ μ.real {ω | f n ω ≤ m n})
    (hu : ∀ n, (1 / 2 : ℝ) ≤ μ.real {ω | m n ≤ f n ω})
    (htail : ∀ r : ℝ, 0 < r → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, μ.real {ω | r ≤ |f n ω - m n|} ≤ C * Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n => (∫ ω, f n ω ∂μ) - m n) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (f n) μ :=
    (integrable_const B).mono' (hf n).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound n ω)
  have hm (n : ℕ) : |m n| ≤ B := abs_median_le_bound μ (f n) (m n) B (hbound n) (hl n) (hu n)
  have hdev (n : ℕ) (ω : Ω) : |f n ω - m n| ≤ 2 * B := by
    have hs := (abs_sub _ _).trans (add_le_add (hbound n ω) (hm n))
    linarith
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, a, hC, ha, ht⟩ := htail (ε / 2) (by positivity)
  have hlim : Tendsto (fun n : ℕ => ε / 2 + 2 * B * (C * Real.exp (-a * (n : ℝ))))
      atTop (𝓝 (ε / 2)) := by
    have hlin : Tendsto (fun n : ℕ => -a * (n : ℝ)) atTop atBot :=
      by simpa only [Function.comp_def, neg_mul] using
        tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have he := (Real.tendsto_exp_atBot.comp hlin).const_mul C
    simpa using (he.const_mul (2 * B)).const_add (ε / 2)
  have hevent : ∀ᶠ n : ℕ in atTop, ε / 2 + 2 * B * (C * Real.exp (-a * (n : ℝ))) < ε :=
    hlim.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro n hn
  have hb := abs_integral_sub_le_deviation_tail μ (f n) (hf n) (hi n) (m n) (2 * B)
    (ε / 2) (by positivity) (hdev n)
  have hb' := hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (ht n) (by positivity : 0 ≤ 2 * B)))
  simpa only [Real.dist_eq, sub_zero] using hb'.trans_lt (hN n hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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

/-- Uniformly bounded spectra give almost-sure concentration about the mean,
for arbitrary deterministic fields and arbitrary dependence across dimensions. -/
theorem ae_pressure_sub_mean_tendsto_zero (hpub : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (n : ℕ) → Ω → SpecialOrthogonal (n + 3))
    (hU : ∀ n, Measurable (U n))
    (hHaar : ∀ n, (P.map (U n)).IsMulLeftInvariant)
    (eig c : (n : ℕ) → Fin (n + 3) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ n i, |eig n i| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      rotatedPressure (eig n) (specialRotation (U n ω)) (c n) -
        ∫ η, rotatedPressure (eig n) (specialRotation (U n η)) (c n) ∂P)
      atTop (𝓝 0) := by
  let F : (n : ℕ) → SpecialOrthogonal (n + 3) → ℝ := fun n V =>
    rotatedPressure (eig n) (specialRotation V) (c n) - noninteractingPressure (c n)
  let f : ℕ → Ω → ℝ := fun n ω => F n (U n ω)
  have hFm (n : ℕ) : Measurable (F n) :=
    (measurable_rotatedPressure (eig n) (c n)).sub_const _
  have hfm (n : ℕ) : Measurable (f n) := (hFm n).comp (hU n)
  have hfb (n : ℕ) (ω : Ω) : |f n ω| ≤ K / 2 :=
    abs_pressure_sub_noninteracting_le (by omega) _ _ _ K (heig n)
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  have hm (n : ℕ) : ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ P.real {ω | f n ω ≤ m} ∧
      (1 / 2 : ℝ) ≤ P.real {ω | m ≤ f n ω} ∧
      ∀ r : ℝ, 0 < r → P.real {ω | r ≤ |f n ω - m|} ≤
        C * Real.exp (-a * (n + 3 : ℝ) * r ^ 2 / K ^ 2) := by
    have hprob : IsProbabilityMeasure (P.map (U n)) :=
      (Measure.isProbabilityMeasure_map_iff (hU n).aemeasurable).mpr inferInstance
    have hLip : ∀ V W, |F n V - F n W| ≤ K * frobeniusDistance V W := by
      intro V W
      dsimp only [F]
      rw [sub_sub_sub_cancel_right]
      exact abs_rotatedPressure_sub_rotation_le (by omega) _ _ _ _ K hK.le (heig n)
    obtain ⟨m, hl, hu, ht⟩ := hp (n + 3) (by omega) (P.map (U n)) hprob
      (hHaar n) (F n) (hFm n) K hK hLip
    refine ⟨m, ?_, ?_, ?_⟩
    · simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le (hFm n) measurable_const)] using hl
    · simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le measurable_const (hFm n))] using hu
    · intro r hr
      simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le measurable_const ((hFm n).sub_const m).abs),
        Nat.cast_add, Nat.cast_ofNat] using ht r hr
  choose m hl hu ht using hm
  have htail : ∀ r : ℝ, 0 < r → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, P.real {ω | r ≤ |f n ω - m n|} ≤ C * Real.exp (-a * (n : ℝ)) := by
    intro r hr
    refine ⟨C, a * r ^ 2 / K ^ 2, hC.le, by positivity, ?_⟩
    intro n
    refine (ht n r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
    have hnonneg : 0 ≤ a * r ^ 2 / K ^ 2 := by positivity
    calc
      -a * ((n : ℝ) + 3) * r ^ 2 / K ^ 2 =
          -(a * r ^ 2 / K ^ 2) * ((n : ℝ) + 3) := by ring
      _ ≤ -(a * r ^ 2 / K ^ 2) * (n : ℝ) :=
        mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hnonneg)
  have hmean := tendsto_mean_sub_median_zero P f hfm m (K / 2) (by positivity)
    hfb hl hu htail
  have hae := ae_tendsto_zero_of_exponential_tail P (fun n ω => f n ω - m n) htail
  have hfi (n : ℕ) : Integrable (f n) P :=
    (integrable_const (K / 2)).mono' (hfm n).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hfb n ω)
  filter_upwards [hae] with ω hω
  have hresult := hω.sub hmean
  have he (n : ℕ) :
      f n ω - m n - ((∫ η, f n η ∂P) - m n) =
        rotatedPressure (eig n) (specialRotation (U n ω)) (c n) -
          ∫ η, rotatedPressure (eig n) (specialRotation (U n η)) (c n) ∂P := by
    have hadd := integral_add (hfi n) (integrable_const (noninteractingPressure (c n)))
    have heq : (fun η => f n η + noninteractingPressure (c n)) =
        (fun η => rotatedPressure (eig n) (specialRotation (U n η)) (c n)) := by
      funext η
      simp [f, F]
    rw [heq] at hadd
    simp only [integral_const, probReal_univ, one_smul] at hadd
    dsimp only [f, F]
    linarith
  simpa only [he, sub_self] using hresult

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PhysicalPressureConcentration
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure pressure concentration for the actual orthogonal matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

theorem ae_physical_pressure_sub_mean_tendsto_zero (hpub : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (n : ℕ) → Ω → Orthogonal (n+3)) (hU : ∀ n, Measurable (U n))
    (hHaar : ∀ n, (P.map (U n)).IsMulRightInvariant)
    (eig c : (n : ℕ) → Fin (n+3) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ n i, |eig n i| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      rotatedPressure (eig n) (matrixRotation (U n ω)⁻¹) (c n)-
        ∫ η, rotatedPressure (eig n) (matrixRotation (U n η)⁻¹) (c n) ∂P)
      atTop (𝓝 0) := by
  let V (n : ℕ) (ω : Ω) := cavityOrientationLift (by omega : 0 < n+3) (U n ω)⁻¹
  have hm n : Measurable (V n) :=
    (measurable_cavityOrientationLift _).comp (hU n).inv
  have hl n : P.map (V n)=cavityOrientedBaseLaw (by omega : 0 < n+3) (P.map (U n)) := by
    change P.map ((fun W => cavityOrientationLift (by omega : 0 < n+3) W⁻¹) ∘ U n)=_
    exact (Measure.map_map ((measurable_cavityOrientationLift _).comp measurable_inv) (hU n)).symm
  have hv n : (P.map (V n)).IsMulLeftInvariant := by
    let : IsProbabilityMeasure (P.map (U n)) :=
      (Measure.isProbabilityMeasure_map_iff (hU n).aemeasurable).mpr inferInstance
    let : (P.map (U n)).IsMulRightInvariant := hHaar n
    rw [hl n]
    exact cavityOrientedBaseLaw_leftInvariant _ _
  have he n ω : rotatedPressure (eig n) (specialRotation (V n ω)) (c n)=
      rotatedPressure (eig n) (matrixRotation (U n ω)⁻¹) (c n) := by
    simp only [V,rotatedPressure,cavityOrientationLift_energy]
  have hh := ae_pressure_sub_mean_tendsto_zero hpub P V hm hv eig c K hK heig
  simpa only [he] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_EmpiricalSpectralLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The empirical spectral probability measure and its finite-set masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace InvariantIsing

lemma empiricalSpectralLaw_map {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map f (empiricalSpectralLaw hN eig : Measure ℝ)=
      (empiricalSpectralLaw hN (fun i => f (eig i)) : Measure ℝ) := by
  change Measure.map f (finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) eig)=
    finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) (fun i => f (eig i))
  unfold finiteSpectralMeasure
  rw [Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul,Measure.map_dirac]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralClipping
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_LimitingPressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Manuscript Theorem 1.1, conditional only on the explicitly cited
published concentration and finite hierarchical field inputs. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem limiting_pressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  refine ⟨physical_mean_pressure_tendsto hhaar hgauss hpub P U hU hHaar eig ν a b
    hcompact hbound ha hb hno hweak,?_⟩
  have hab : a ≤ b := (hbound ha).2
  let clip := fun N (i : Fin N) => spectralClip a b (eig N i)
  have hcmean := physical_mean_pressure_tendsto hhaar hgauss hpub P U hU hHaar clip ν a b
    hcompact hbound ha hb (fun ε hε => Eventually.of_forall (fun N i => by
      have hh := spectralClip_mem hab (eig N i)
      constructor <;> linarith [hh.1,hh.2]))
    (spectral_clip_empirical_tendsto eig ν a b hbound hweak)
  let K := |a|+|b|+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hclip N i : |clip N i| ≤ K := by
    have hh := spectralClip_mem hab (eig N i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hh.1,hh.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hconc := ae_physical_pressure_sub_mean_tendsto_zero hhaar P
    (fun n => U (n+3)) (fun n => hU (n+3)) (fun n => hHaar (n+3))
    (fun n => clip (n+3)) (fun _ _ => 0) K hK (fun n => hclip (n+3))
  have hη := (spectralExcess_tendsto eig a b hno).comp (tendsto_add_atTop_nat 3)
  filter_upwards [hconc] with ω hω
  have hclim := hω.add (hcmean.comp (tendsto_add_atTop_nat 3))
  have hd : Tendsto (fun n => rotatedPressure (eig (n+3)) (matrixRotation (U (n+3) ω)⁻¹) (fun _ => 0)-
      rotatedPressure (clip (n+3)) (matrixRotation (U (n+3) ω)⁻¹) (fun _ => 0))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (by simpa only [zero_div] using hη.div_const 2)
    intro n
    rw [Real.norm_eq_abs,abs_sub_comm]
    exact abs_rotatedPressure_sub_le (by omega) (clip (n+3)) (eig (n+3))
      (matrixRotation (U (n+3) ω)⁻¹) (fun _ => 0) (spectralExcess (eig (n+3)) a b)
      (fun i => spectralClip_close hab (spectralExcess_nonneg _ _ _) (spectralExcess_bounds _ _ _ i))
  apply (tendsto_add_atTop_iff_nat 3).mp
  have hh := hclim.add hd
  convert (config := {transparency := .instances, preTransparency := .instances}) hh using 1
  · funext n
    dsimp only [Function.comp_apply]
    ring
  · simp only [zero_add,add_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ScaledSpectralLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive temperature scaling preserves the precise spectral hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

lemma scaled_spectral_support_bound (ν : ProbabilityMeasure ℝ) (a b β : ℝ)
    (hβ : 0 ≤ β) (hbound : (ν : Measure ℝ).support ⊆ Icc a b) :
    (scaledSpectralLaw ν β : Measure ℝ).support ⊆ Icc (β*a) (β*b) := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  change ∀ᵐ y ∂((ν : Measure ℝ).map (fun x => β*x)), y∈Icc (β*a) (β*b)
  apply (ae_map_iff (measurable_const.mul measurable_id).aemeasurable measurableSet_Icc).mpr
  filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
  exact ⟨mul_le_mul_of_nonneg_left (hbound hx).1 hβ,
    mul_le_mul_of_nonneg_left (hbound hx).2 hβ⟩

lemma scaled_spectral_support_mem (ν : ProbabilityMeasure ℝ) (β x : ℝ)
    (hx : x∈(ν : Measure ℝ).support) :
    β*x∈(scaledSpectralLaw ν β : Measure ℝ).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro S hS hopen
  change ((ν : Measure ℝ).map (fun x => β*x)) S > 0
  have hm : Measurable (fun y : ℝ => β*y) := measurable_const.mul measurable_id
  rw [Measure.map_apply hm hopen.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    ((hopen.preimage (continuous_const.mul continuous_id)).mem_nhds hS)

lemma scaled_spectral_compact (ν : ProbabilityMeasure ℝ) (a b β : ℝ)
    (hβ : 0 ≤ β) (hbound : (ν : Measure ℝ).support ⊆ Icc a b) :
    IsCompact (scaledSpectralLaw ν β : Measure ℝ).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support
    (scaled_spectral_support_bound ν a b β hβ hbound)

lemma scaled_spectral_no_outliers (eig : (N : ℕ) → Fin N → ℝ) (a b β : ℝ)
    (hβ : 0 < β)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i,
      β*a-ε ≤ β*eig N i ∧ β*eig N i ≤ β*b+ε := by
  intro ε hε
  filter_upwards [hno (ε/β) (div_pos hε hβ)] with N hN i
  have hl := mul_le_mul_of_nonneg_left (hN i).1 hβ.le
  have hu := mul_le_mul_of_nonneg_left (hN i).2 hβ.le
  have he : β*(ε/β)=ε := mul_div_cancel₀ ε hβ.ne'
  rw [mul_sub,he] at hl
  rw [mul_add,he] at hu
  exact ⟨hl,hu⟩

lemma scaled_spectral_weak (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (β : ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (fun i => β*eig (k+1) i))
      atTop (𝓝 (scaledSpectralLaw ν β)) := by
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hweak
    (show Continuous (fun x : ℝ => β*x) from continuous_const.mul continuous_id)
  apply hh.congr
  intro k
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map _ _ _ (measurable_const.mul measurable_id)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PositiveTemperaturePressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conditional main theorem at every positive inverse temperature. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem positive_temperature_pressure_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (β : ℝ) (hβ : 0 < β)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) :=
  limiting_pressure hhaar hgauss hpub P U hU hHaar (fun N i => β*eig N i)
    (scaledSpectralLaw ν β) (β*a) (β*b)
    (scaled_spectral_compact ν a b β hβ.le hbound)
    (scaled_spectral_support_bound ν a b β hβ.le hbound)
    (scaled_spectral_support_mem ν β a ha) (scaled_spectral_support_mem ν β b hb)
    (scaled_spectral_no_outliers eig a b β hβ hno) (scaled_spectral_weak eig ν β hweak)

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.positive_temperature_pressure_oai.{u_1} := @OAI.InvariantIsing.positive_temperature_pressure_oai.{u_1}
