-- Prove2me | solution 1 for OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:27:16.540444+00:00
-- url     : https://prove2.me/submissions/de729192-8d14-410e-82da-728d2e668828
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
import Theorems.Thm_OAI_InvariantIsing_entropyFunctional_zero
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finite_type_field_pressure_tendsto

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib d13f23b's `Finset.frontier_biUnion_subset` (CircleDomains, q146). -/
theorem _root_.Finset.frontier_biUnion_subset {X ι : Type*} [TopologicalSpace X] (I : Finset ι)
    (s : ι → Set X) : frontier (⋃ i ∈ I, s i) ⊆ ⋃ i ∈ I, frontier (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    refine (frontier_union_subset _ _).trans ?_
    rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr (ih hx.2)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma spectralFunctional_constant (a : ℝ) (p : OverlapPath) :
    spectralFunctional (fun _ => a) p = a / 2 := by
  simp [spectralFunctional]
  ring

lemma integrable_spectral_composition (R : ℝ → ℝ) (hR : Continuous R)
    (p : OverlapPath) : Integrable (fun r => R (deficit p r)) pathMeasure := by
  change IntegrableOn (fun r => R (deficit p r)) (Set.Ioo (0 : ℝ) 1)
  exact ((hR.comp (continuous_deficit p)).continuousOn.integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- Section 6's uniform comparison of spectral functionals. -/
lemma abs_spectralFunctional_sub_le (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) (p : OverlapPath) :
    |spectralFunctional R p - spectralFunctional Q p| ≤ δ / 2 := by
  have hr : ∀ᵐ r ∂pathMeasure, r ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hi := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun r => R (deficit p r) - Q (deficit p r)) (C := δ) (by
      filter_upwards [hr] with r hr
      simpa only [Real.norm_eq_abs] using hδ _ (deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩))
  have hib : |∫ r, R (deficit p r) - Q (deficit p r) ∂pathMeasure| ≤ δ := by
    simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
      ENNReal.toReal_one, mul_one] using hi
  rw [spectralFunctional, spectralFunctional, ← mul_sub,
    ← integral_sub (integrable_spectral_composition R hR p)
      (integrable_spectral_composition Q hQ p), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * δ := mul_le_mul_of_nonneg_left hib (by norm_num)
    _ = δ / 2 := by ring

end InvariantIsing

end

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The resolvent and the edge-capped inverse for a general spectral law.
The upper edge is an explicit parameter; the hypotheses below say that the
law is supported below it. No inverse is assumed to exist at the edge. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma measurable_resolventKernel (b : ℝ) : Measurable (fun y : ℝ => 1 / (b - y)) :=
  measurable_const.div (measurable_const.sub measurable_id)

lemma resolventKernel_bound {e b y : ℝ} (hb : e < b) (hy : y ≤ e) :
    ‖1 / (b - y)‖ ≤ 1 / (b - e) := by
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith))]
  exact one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith)

lemma integrable_resolventKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    Integrable (fun y => 1 / (b - y)) μ := by
  apply (integrable_const (1 / (b - e))).mono' (measurable_resolventKernel b).aestronglyMeasurable
  filter_upwards [hμ] with y hy
  exact resolventKernel_bound hb hy

lemma measureResolvent_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    measureResolvent μ b ≤ 1 / (b - e) := by
  have hi := integral_mono_ae (integrable_resolventKernel μ hμ hb)
    (integrable_const (1 / (b - e))) (hμ.mono fun y hy =>
      one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith))
  simpa only [measureResolvent, integral_const, probReal_univ, one_smul] using hi

lemma le_measureResolvent (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hb : e < b) :
    1 / (b - l) ≤ measureResolvent μ b := by
  have hex := hμ.exists
  have hbl : l < b := by obtain ⟨y, hy⟩ := hex; linarith [hy.1, hy.2]
  have hi := integral_mono_ae (integrable_const (1 / (b - l)))
    (integrable_resolventKernel μ (hμ.mono fun _ h => h.2) hb)
    (hμ.mono fun y hy => one_div_le_one_div_of_le (by linarith [hy.2]) (by linarith [hy.1]))
  simpa only [measureResolvent, integral_const, probReal_univ, one_smul] using hi

theorem measureResolvent_strictAnti (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b c : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) (hbc : b < c) :
    measureResolvent μ c < measureResolvent μ b := by
  have hi := integrable_resolventKernel μ hμ hb
  have hj := integrable_resolventKernel μ hμ (hb.trans hbc)
  have hlt : ∀ᵐ y ∂μ, 1 / (c - y) < 1 / (b - y) := hμ.mono fun y hy =>
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hle := integral_mono_ae hj hi (hlt.mono fun _ h => h.le)
  apply lt_of_le_of_ne hle
  intro heq
  have hae := (integral_eq_iff_of_ae_le hj hi (hlt.mono fun _ h => h.le)).mp heq
  obtain ⟨y, hy, he⟩ := (hlt.and hae).exists
  exact (ne_of_lt hy) he

theorem continuousAt_measureResolvent (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    ContinuousAt (measureResolvent μ) b := by
  let c := (e + b) / 2
  have hce : e < c := by dsimp only [c] <;> linarith
  have hcb : c < b := by dsimp only [c] <;> linarith
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / (c - e))
  · exact Eventually.of_forall fun z => (measurable_resolventKernel z).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds hcb] with z hz
    have hz' : c < z := hz
    filter_upwards [hμ] with y hy
    exact (resolventKernel_bound (hce.trans hz') hy).trans
      (one_div_le_one_div_of_le (sub_pos.mpr hce) (by linarith))
  · exact integrable_const _
  · filter_upwards [hμ] with y hy
    exact (continuousAt_const.div (continuousAt_id.sub_const y)
      (by change b - y ≠ 0; linarith)).tendsto

theorem exists_measureResolvent_solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e lo x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hlo : e < lo)
    (hx : 0 < x) (hloValue : x ≤ measureResolvent μ lo) :
    ∃ b, e < b ∧ measureResolvent μ b = x := by
  let hi := lo + 1 / x
  have hhi : lo < hi := by dsimp only [hi] <;> linarith [one_div_pos.mpr hx]
  have hhiValue : measureResolvent μ hi ≤ x := by
    apply (measureResolvent_le μ hμ (hlo.trans hhi)).trans
    have hd : 1 / x ≤ hi - e := by dsimp only [hi] <;> linarith
    simpa using one_div_le_one_div_of_le (one_div_pos.mpr hx) hd
  have hc : ContinuousOn (measureResolvent μ) (Icc lo hi) := fun b hb =>
    (continuousAt_measureResolvent μ hμ (hlo.trans_le hb.1)).continuousWithinAt
  obtain ⟨b, hb, hv⟩ := intermediate_value_Icc' hhi.le hc ⟨hhiValue, hloValue⟩
  exact ⟨b, hlo.trans_le hb.1, hv⟩

theorem measureInverse_eq_of_solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b)
    (hsol : measureResolvent μ b = x) : measureInverse μ e x = b := by
  have hex : ∃ b, e < b ∧ measureResolvent μ b = x := ⟨b, hb, hsol⟩
  rw [measureInverse, dite_eq_left hex]
  have hs := hex.choose_spec
  rcases lt_trichotomy hex.choose b with h | h | h
  · have := measureResolvent_strictAnti μ hμ hs.1 h
    linarith [hs.2]
  · exact h
  · have := measureResolvent_strictAnti μ hμ hb h
    linarith [hs.2]

theorem measureInverse_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    e ≤ measureInverse μ e x ∧ measureInverse μ e x ≤ e + 1 / x := by
  by_cases hex : ∃ b, e < b ∧ measureResolvent μ b = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    refine ⟨hs.1.le, ?_⟩
    have hu := measureResolvent_le μ hμ hs.1
    rw [hs.2] at hu
    have hm := (le_div_iff₀ (sub_pos.mpr hs.1)).mp hu
    have hd : hex.choose - e ≤ 1 / x := (le_div_iff₀ hx).mpr (by nlinarith)
    linarith
  · simp only [measureInverse, dite_eq_right hex, le_refl, true_and]
    linarith [one_div_pos.mpr hx]

theorem measureR_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hx : 0 < x) :
    l ≤ measureR μ e x ∧ measureR μ e x ≤ e := by
  have hu := measureInverse_bounds μ (hμ.mono fun _ h => h.2) hx
  rw [measureR, ite_eq_left hx]
  refine ⟨?_, by linarith [hu.2]⟩
  by_cases hex : ∃ b, e < b ∧ measureResolvent μ b = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    have hl := le_measureResolvent μ hμ hs.1
    rw [hs.2] at hl
    obtain ⟨y, hy⟩ := hμ.exists
    have hbl : 0 < hex.choose - l := by linarith [hy.1, hy.2, hs.1]
    have hm := (div_le_iff₀ hbl).mp hl
    have hd : 1 / x ≤ hex.choose - l := (div_le_iff₀ hx).mpr (by nlinarith)
    linarith
  · rw [measureInverse, dite_eq_right hex]
    by_contra hbad
    have hb : e < l + 1 / x := by linarith
    have hl := le_measureResolvent μ hμ hb
    have hv : x ≤ measureResolvent μ (l + 1 / x) := by simpa using hl
    exact hex (exists_measureResolvent_solution μ (hμ.mono fun _ h => h.2) hb hx hv)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_FiniteSpectralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general measure transform agrees with the finite-alphabet transform.
Positive masses ensure that the upper edge is an atom and the inverse is uncapped. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralMeasure (ρ eig : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (f : ℝ → ℝ) :
    (∫ y, f y ∂finiteSpectralMeasure ρ eig) = ∑ a, ρ a * f (eig a) := by
  have hi a : Integrable f (ENNReal.ofReal (ρ a) • Measure.dirac (eig a)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [finiteSpectralMeasure, Measure.sum_fintype,
    integral_finsetSum_measure (fun a _ => hi a)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hρ _), smul_eq_mul]

theorem ae_finiteSpectralMeasure (ρ eig : ι → ℝ) {P : ℝ → Prop} (hP : ∀ a, P (eig a)) :
    ∀ᵐ y ∂finiteSpectralMeasure ρ eig, P y := by
  rw [finiteSpectralMeasure, Measure.ae_sum_iff]
  intro a
  have hd : ∀ᵐ y ∂Measure.dirac (eig a), P y := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hP a
  exact Measure.ae_smul_measure hd _

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

lemma empiricalSpectralLaw_integral {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(empiricalSpectralLaw hN eig : Measure ℝ))=(1 : ℝ)/N*∑ i, f (eig i) := by
  change (∫ x, f x ∂finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig)=_
  rw [integral_finiteSpectralMeasure _ _ (fun _ => by positivity)]
  rw [Finset.mul_sum]

lemma empiricalSpectralLaw_mass {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (empiricalSpectralLaw hN eig : Measure ℝ).real S=
      ((Finset.univ.filter (fun i => eig i∈S)).card : ℝ)/N := by
  classical
  have hh := empiricalSpectralLaw_integral hN eig (S.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator hS,integral_const] at hh
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hh ⊢
  rw [hh]
  simp only [Set.indicator_apply,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_const,nsmul_eq_mul,mul_one]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralLabelCounts
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
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

lemma spectral_label_counts_partition {ι : Type*} [Fintype ι]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν))
    (S : ι → Set ℝ) (hS : ∀ a, MeasurableSet (S a))
    (hboundary : ∀ a, (ν : Measure ℝ) (frontier (S a))=0)
    (g : (k : ℕ) → Fin (N k) → ι)
    (hg : ∀ k a i, g k i=a ↔ eig k i∈S a) :
    Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop
      (𝓝 (fun a => (ν : Measure ℝ).real (S a))) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak (hboundary a)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (S a))).comp hh
  apply hr.congr
  intro k
  change (empiricalSpectralLaw (hN k) (eig k) : Measure ℝ).real (S a)=_
  rw [empiricalSpectralLaw_mass (hN k) (eig k) (S a) (hS a)]
  congr 2
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,hg]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralNullBoundaryCover
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact spectral set has a finite small-ball cover whose boundaries
have zero mass. The centers remain in the spectral set. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical

namespace InvariantIsing

lemma spectral_null_boundary_cover (μ : Measure ℝ) [SFinite μ]
    (K : Set ℝ) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ c r : Fin n → ℝ,
      (∀ i, c i∈K) ∧ (∀ i, δ/2 < r i ∧ r i < δ) ∧
      (∀ i, μ (frontier (ball (c i) (r i)))=0) ∧
      K ⊆ ⋃ i, ball (c i) (r i) := by
  have hex (x : K) : ∃ r ∈ Ioo (δ/2) δ, μ (frontier (ball (x : ℝ) r))=0 := by
    simpa only [thickening_singleton] using
      exists_null_frontier_thickening μ ({(x : ℝ)} : Set ℝ) (by linarith : δ/2 < δ)
  choose r hr hnull using hex
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (lt_trans (half_pos hδ) (hr ⟨x,hx⟩).1)⟩)
  let A := {x : K // x∈t}
  let e := Fintype.equivFin A
  let c : Fin (Fintype.card A) → ℝ := fun i => ((e.symm i).1 : ℝ)
  let r' : Fin (Fintype.card A) → ℝ := fun i => r (e.symm i).1
  refine ⟨Fintype.card A,c,r',fun i => (e.symm i).1.2,fun i => hr (e.symm i).1,
    fun i => hnull (e.symm i).1,?_⟩
  intro x hx
  obtain ⟨y,hy⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
  refine mem_iUnion.mpr ⟨e ⟨y,hyt⟩,?_⟩
  simpa only [c,r',Equiv.symm_apply_apply] using hxy

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralNullBoundaryPartition
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered disjointization preserves the null boundaries required by
the spectral empirical-measure convergence argument. -/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace InvariantIsing

lemma null_frontier_sdiff (μ : Measure ℝ) (A B : Set ℝ)
    (hA : μ (frontier A)=0) (hB : μ (frontier B)=0) : μ (frontier (A\B))=0 := by
  apply measure_mono_null _ (measure_union_null_iff.mpr ⟨hA,hB⟩)
  intro x hx
  have hh := frontier_inter_subset A Bᶜ hx
  rcases hh with ⟨ha,_⟩ | ⟨_,hb⟩
  · exact Or.inl ha
  · exact Or.inr (by simpa only [frontier_compl] using hb)

lemma null_frontier_finsetUnion {ι : Type*} (μ : Measure ℝ) (t : Finset ι)
    (B : ι → Set ℝ) (hB : ∀ i∈t, μ (frontier (B i))=0) :
    μ (frontier (⋃ i∈t, B i))=0 := by
  apply measure_mono_null (t.frontier_biUnion_subset B)
  exact (measure_biUnion_null_iff t.countable_toSet).mpr hB

lemma null_frontier_disjointed {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (hB : ∀ i, μ (frontier (B i))=0) (i : Fin n) :
    μ (frontier (disjointed B i))=0 := by
  rw [disjointed_apply,Finset.sup_eq_iSup]
  exact null_frontier_sdiff μ _ _ (hB i)
    (null_frontier_finsetUnion μ (Finset.Iio i) B (fun j _ => hB j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralBallPartition
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite ball cover yields a measurable partition, including a
zero-mass residual cell outside the covered spectral support. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function

namespace InvariantIsing

lemma spectralBallCell_null_boundary {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (hB : ∀ i, μ (frontier (B i))=0) (i : Option (Fin n)) :
    μ (frontier (spectralBallCell B i))=0 := by
  cases i with
  | none =>
    change μ (frontier (⋃ i, B i)ᶜ)=0
    rw [frontier_compl]
    simpa only [Finset.mem_univ,iUnion_true] using
      null_frontier_finsetUnion μ Finset.univ B (fun i _ => hB i)
  | some i => exact null_frontier_disjointed μ B hB i

lemma spectralBallCell_residual_null {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (K : Set ℝ) (hμ : μ Kᶜ=0) (hcover : K ⊆ ⋃ i, B i) :
    μ (spectralBallCell B none)=0 :=
  measure_mono_null (compl_subset_compl.mpr hcover) hμ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralBallQuantizer
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite quantizer attached to the null-boundary ball cover. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical Function

namespace InvariantIsing

lemma measurable_spectralBallQuantizer {n : ℕ} (c r : Fin n → ℝ) (fallback : ℝ) :
    Measurable (spectralBallQuantizer c r fallback) := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  exact (measurable_of_countable (fun i : Option (Fin n) => i.elim fallback c)).comp
    (measurable_spectralPartitionIndex _ (spectralBallCell_cover _) (spectralBallCell_disjoint _)
      (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

lemma spectralBallQuantizer_close {n : ℕ} (c r : Fin n → ℝ) (fallback δ x : ℝ)
    (hr : ∀ i, r i ≤ δ) (hx : x∈⋃ i, ball (c i) (r i)) :
    dist (spectralBallQuantizer c r fallback x) x ≤ δ := by
  let B := fun i => ball (c i) (r i)
  let j := spectralPartitionIndex (spectralBallCell B) (spectralBallCell_cover B) x
  have hj : x∈spectralBallCell B j := spectralPartitionIndex_mem _ _ x
  cases h : j with
  | none =>
    have hh : x ∉ ⋃ i, B i := by simpa only [h,spectralBallCell, Set.mem_compl_iff] using hj
    exact False.elim (hh hx)
  | some i =>
    have hxi : x∈B i := disjointed_subset B i (by simpa only [h,spectralBallCell] using hj)
    have hd : dist x (c i) < r i := hxi
    have he : spectralBallQuantizer c r fallback x=c i := by
      change j.elim fallback c=c i
      rw [h]
      rfl
    rw [he,dist_comm]
    exact hd.le.trans (hr i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantizationWeak
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly small spectral quantizations converge weakly to the
original law. This uses bounded Lipschitz tests, with explicit error control. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma spectral_quantization_weak (μ : ProbabilityMeasure ℝ)
    (q : ℕ → ℝ → ℝ) (hq : ∀ k, Measurable (q k)) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k, ∀ᵐ x ∂(μ : Measure ℝ), dist (q k x) x ≤ δ k) :
    Tendsto (fun k => μ.map (f := (q k)) (by first | exact (hq k).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hf hfLip
  obtain ⟨C,hC⟩ := hf
  obtain ⟨L,hL⟩ := hfLip
  have hb x : ‖f x‖ ≤ C+|f 0| := by
    have hh := abs_add_le (f x-f 0) (f 0)
    rw [sub_add_cancel] at hh
    exact hh.trans (add_le_add (by simpa only [Real.dist_eq] using hC x 0) le_rfl)
  have hfi : Integrable f (μ : Measure ℝ) :=
    (integrable_const (C+|f 0|)).mono' hL.continuous.measurable.aestronglyMeasurable
      (ae_of_all _ hb)
  have hqi k : Integrable (fun x => f (q k x)) (μ : Measure ℝ) :=
    (integrable_const (C+|f 0|)).mono' (hL.continuous.measurable.comp (hq k)).aestronglyMeasurable
      (ae_of_all _ fun x => hb (q k x))
  have he k : |(∫ x, f x ∂(μ.map (f := (q k)) (by first | exact (hq k).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)| ≤
      (L : ℝ)*δ k := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (hq k).aemeasurable
      hL.continuous.measurable.aestronglyMeasurable,← integral_sub (hqi k) hfi,← Real.norm_eq_abs]
    have hh : ∀ᵐ x ∂(μ : Measure ℝ), ‖f (q k x)-f x‖ ≤ (L : ℝ)*δ k := by
      filter_upwards [hclose k] with x hx
      calc
        _ ≤ (L : ℝ)*dist (q k x) x := by simpa only [dist_eq_norm] using hL.dist_le_mul (q k x) x
        _ ≤ _ := mul_le_mul_of_nonneg_left hx L.coe_nonneg
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hh
  have hz : Tendsto (fun k => (∫ x, f x ∂(μ.map (f := (q k)) (by first | exact (hq k).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ))-
      ∫ x, f x ∂(μ : Measure ℝ)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using he k)
      (by simpa only [mul_zero] using hδ.const_mul (L : ℝ))
  simpa only [sub_add_cancel,zero_add] using hz.add_const (∫ x, f x ∂(μ : Measure ℝ))

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

lemma finiteSpectralMeasure_positive {ι : Type*} [Fintype ι]
    (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    finiteSpectralMeasure (fun i : {i // 0 < w i} => w i) (fun i => lam i)=
      finiteSpectralMeasure w lam := by
  simp only [finiteSpectralMeasure,Measure.sum_fintype]
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    have hp : ¬0 < w i := fun hp => hi ⟨⟨i,hp⟩,rfl⟩
    have hz : w i=0 := le_antisymm (le_of_not_gt hp) (hw i)
    simp only [hz,ENNReal.ofReal_zero,zero_smul]
  · intro i
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite spectral law produced by a measurable partition. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

lemma spectralPartition_pushforward {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (lam : ι → ℝ) :
    μ.map (fun x => lam (spectralPartitionIndex S hcover x))=
      finiteSpectralMeasure (fun i => μ.real (S i)) lam := by
  let : MeasurableSpace ι := ⊤
  have hm := measurable_spectralPartitionIndex S hcover hdis hS
  have hl : Measurable lam := measurable_of_countable lam
  change μ.map (lam ∘ spectralPartitionIndex S hcover)=_
  rw [← Measure.map_map hl hm, Measure.map_eq_sum μ _ hm,
    Measure.map_sum hl.aemeasurable]
  change Measure.sum (fun i => Measure.map lam (μ ((spectralPartitionIndex S hcover) ⁻¹' {i}) •
    Measure.dirac i))=Measure.sum (fun i => ENNReal.ofReal (μ.real (S i)) • Measure.dirac (lam i))
  congr 1
  funext i
  rw [spectralPartitionIndex_preimage S hcover hdis, Measure.map_smul,
    Measure.map_dirac]
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ (S i))]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveSpectralPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-mass cells carry the same spectral law as the original partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators Function

namespace InvariantIsing

lemma ae_spectralPartitionIndex_pos {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) :
    ∀ᵐ x ∂μ, 0 < μ.real (S (spectralPartitionIndex S hcover x)) := by
  have hi (i : ι) : ∀ᵐ x ∂μ, x∈S i → 0 < μ.real (S i) := by
    by_cases hp : 0 < μ.real (S i)
    · exact Filter.Eventually.of_forall (fun _ _ => hp)
    · have hz : μ (S i)=0 := (measureReal_eq_zero_iff).mp
        (le_antisymm (le_of_not_gt hp) measureReal_nonneg)
      filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
      exact fun h => (hx h).elim
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx _ (spectralPartitionIndex_mem S hcover x)

lemma positive_spectral_edge_bounds {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (lam : ι → ℝ) (δ a b : ℝ)
    (ha : a∈μ.support) (hb : b∈μ.support)
    (aMin aMax : {i // 0 < μ.real (S i)})
    (hmin : ∀ i : {i // 0 < μ.real (S i)}, lam aMin ≤ lam i)
    (hmax : ∀ i : {i // 0 < μ.real (S i)}, lam i ≤ lam aMax)
    (hclose : ∀ᵐ x ∂μ, dist (lam (spectralPartitionIndex S hcover x)) x ≤ δ) :
    lam aMin-δ ≤ a ∧ b ≤ lam aMax+δ := by
  have hl : ∀ᵐ x ∂μ, x∈Ici (lam aMin-δ) := by
    filter_upwards [ae_spectralPartitionIndex_pos μ S hcover,hclose] with x hx hc
    have hh := hmin ⟨spectralPartitionIndex S hcover x,hx⟩
    rw [Real.dist_eq,abs_le] at hc
    change lam aMin-δ ≤ x
    linarith
  have hu : ∀ᵐ x ∂μ, x∈Iic (lam aMax+δ) := by
    filter_upwards [ae_spectralPartitionIndex_pos μ S hcover,hclose] with x hx hc
    have hh := hmax ⟨spectralPartitionIndex S hcover x,hx⟩
    rw [Real.dist_eq,abs_le] at hc
    change x ≤ lam aMax+δ
    linarith
  exact ⟨μ.support_subset_of_isClosed isClosed_Ici hl ha,
    μ.support_subset_of_isClosed isClosed_Iic hu hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveSpectralRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-sided spectral rounding remains valid on the zero-mass cells. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical Function

namespace InvariantIsing

lemma positive_spectral_rounding_bounds {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i)
    (lam : ι → ℝ) (a b δ : ℝ)
    (lo hi : {i // 0 < μ.real (S i)})
    (hlo : lam lo-δ ≤ a) (hhi : b ≤ lam hi+δ)
    (hcell : ∀ i, 0 < μ.real (S i) → ∀ x∈S i, dist (lam i) x ≤ δ)
    (x : ℝ) (hx : x∈Icc a b) :
    lam (positiveSpectralLabel (fun i => μ.real (S i)) lo
      (spectralPartitionIndex S hcover x))-δ ≤ x ∧
    x ≤ lam (positiveSpectralLabel (fun i => μ.real (S i)) hi
      (spectralPartitionIndex S hcover x))+δ := by
  let j := spectralPartitionIndex S hcover x
  by_cases hp : 0 < μ.real (S j)
  · have hc := hcell j hp x (spectralPartitionIndex_mem S hcover x)
    rw [Real.dist_eq,abs_le] at hc
    simp only [show spectralPartitionIndex S hcover x=j from rfl,
      positiveSpectralLabel,dite_eq_left hp]
    constructor <;> linarith
  · simp only [show spectralPartitionIndex S hcover x=j from rfl,
      positiveSpectralLabel,dite_eq_right hp]
    exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

lemma positive_spectral_ball_cell_close {n : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c r : Fin n → ℝ)
    (a δ : ℝ) (hr : ∀ i, r i ≤ δ)
    (hzero : μ (spectralBallCell (fun i => ball (c i) (r i)) none)=0)
    (i : Option (Fin n)) (hi : 0 < μ.real (spectralBallCell (fun i => ball (c i) (r i)) i))
    (x : ℝ) (hx : x∈spectralBallCell (fun i => ball (c i) (r i)) i) :
    dist (i.elim a c) x ≤ δ := by
  cases i with
  | none =>
    have hz : μ.real (spectralBallCell (fun i => ball (c i) (r i)) none)=0 :=
      (measureReal_eq_zero_iff).mpr hzero
    exact (not_lt_of_ge hz.le hi).elim
  | some i =>
    have hh : x∈ball (c i) (r i) := disjointed_subset (fun i => ball (c i) (r i)) i hx
    simpa only [Option.elim_some,dist_comm] using (show dist x (c i) ≤ δ from hh.le.trans (hr i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactSpectralPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive-mass spectral partitions for the compact-support approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

theorem exists_compact_spectral_partition (ν : ProbabilityMeasure ℝ) (a b δ : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (hδ : 0 < δ) :
    Nonempty (CompactSpectralPartition ν a b δ) := by
  obtain ⟨n,c,r,hc,hr,hn,hb⟩ := spectral_null_boundary_cover (ν : Measure ℝ)
    (ν : Measure ℝ).support hcompact δ hδ
  let S := spectralBallCell (fun i => ball (c i) (r i))
  let w := spectralBallWeight ν c r
  have hsum : ∑ i, w i=1 := spectralPartitionWeights_sum (ν : Measure ℝ) S
    (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
  obtain ⟨i,hi⟩ := exists_pos_spectral_weight (fun _ => measureReal_nonneg) hsum
  let P := {i // 0 < w i}
  have he : (Finset.univ : Finset P).Nonempty := ⟨⟨i,hi⟩,Finset.mem_univ _⟩
  obtain ⟨lo,_,hlo⟩ := Finset.exists_min_image Finset.univ
    (fun i : P => spectralBallValue c a i) he
  obtain ⟨up,_,hup⟩ := Finset.exists_max_image Finset.univ
    (fun i : P => spectralBallValue c a i) he
  exact ⟨⟨n,c,r,(fun i => hbound (hc i)),(fun i => (hr i).2.le),hn,hb,lo,up,
    (fun i => hlo i (Finset.mem_univ i)),(fun i => hup i (Finset.mem_univ i))⟩⟩

namespace CompactSpectralPartition

variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

lemma value_mem (hab : a ≤ b) (i : Option (Fin D.size)) : D.value i∈Icc a b := by
  cases i with
  | none => exact ⟨le_rfl,hab⟩
  | some i => exact D.center_mem i

lemma residual_zero : (ν : Measure ℝ) (D.cells none)=0 :=
  spectralBallCell_residual_null (ν : Measure ℝ) _ (ν : Measure ℝ).support
    (ν : Measure ℝ).measure_compl_support D.covers

lemma law_eq_map : (D.law : Measure ℝ)=
    (ν : Measure ℝ).map (spectralBallQuantizer D.center D.radius a) := by
  change finiteSpectralMeasure (fun i : D.Positive => D.weight i) (fun i => D.value i)=_
  rw [finiteSpectralMeasure_positive D.weight D.value (fun _ => measureReal_nonneg)]
  exact (spectralPartition_pushforward (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
    (spectralBallCell_disjoint _) (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    D.value).symm

lemma quantizer_close : ∀ᵐ x ∂(ν : Measure ℝ),
    dist (spectralBallQuantizer D.center D.radius a x) x ≤ δ := by
  filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
  exact spectralBallQuantizer_close D.center D.radius a δ x D.radius_le (D.covers hx)

lemma endpoint_bounds (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    D.value D.lower-δ ≤ a ∧ b ≤ D.edge+δ :=
  positive_spectral_edge_bounds (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
    D.value δ a b ha hb D.lower D.upper D.lower_le D.le_upper D.quantizer_close

lemma law_support (hab : a ≤ b) : ∀ᵐ x ∂(D.law : Measure ℝ), x∈Icc a D.edge := by
  exact ae_finiteSpectralMeasure _ _ (fun i : D.Positive =>
    ⟨(D.value_mem hab i).1,D.le_upper i⟩)

end CompactSpectralPartition
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureInverseContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Order tests and continuity for the inverse across the capped branch. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

theorem measureInverse_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) (hb : e < b) :
    measureInverse μ e x ≤ b ↔ measureResolvent μ b ≤ x := by
  by_cases hex : ∃ r, e < r ∧ measureResolvent μ r = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    constructor
    · intro hrb
      rcases hrb.eq_or_lt with h | h
      · rw [← h, hs.2]
      · have ht := measureResolvent_strictAnti μ hμ hs.1 h
        rw [hs.2] at ht
        exact ht.le
    · intro hR
      by_contra hnot
      have ht := measureResolvent_strictAnti μ hμ hb (lt_of_not_ge hnot)
      rw [hs.2] at ht
      exact (not_lt_of_ge hR) ht
  · rw [measureInverse, dite_eq_right hex]
    constructor
    · intro _
      by_contra hnot
      exact hex (exists_measureResolvent_solution μ hμ hb hx (lt_of_not_ge hnot).le)
    · intro _
      exact hb.le

theorem measureInverse_lt_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) (hb : e < b) :
    measureInverse μ e x < b ↔ measureResolvent μ b < x := by
  by_cases hex : ∃ r, e < r ∧ measureResolvent μ r = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    constructor
    · intro hrb
      have ht := measureResolvent_strictAnti μ hμ hs.1 hrb
      rwa [hs.2] at ht
    · intro hR
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with h | h
      · rw [h, hs.2] at hR
        exact lt_irrefl _ hR
      · have ht := measureResolvent_strictAnti μ hμ hb h
        rw [hs.2] at ht
        exact (not_lt_of_ge ht.le) hR
  · rw [measureInverse, dite_eq_right hex]
    have hv : measureResolvent μ b < x := by
      by_contra hnot
      exact hex (exists_measureResolvent_solution μ hμ hb hx (le_of_not_gt hnot))
    exact ⟨fun _ => hv, fun _ => hb⟩

theorem continuousAt_measureInverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    ContinuousAt (measureInverse μ e) x := by
  have hbound := (measureInverse_bounds μ hμ hx).1
  have hxp : ∀ᶠ y in 𝓝 x, 0 < y := Ioi_mem_nhds hx
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases hle : l < e
    · filter_upwards [hxp] with y hy
      exact hle.trans_le (measureInverse_bounds μ hμ hy).1
    · let c := (l + measureInverse μ e x) / 2
      have hec : e < c := by dsimp only [c] <;> linarith [le_of_not_gt hle]
      have hlc : l < c := by dsimp only [c] <;> linarith
      have hci : c < measureInverse μ e x := by dsimp only [c] <;> linarith
      have hR : x < measureResolvent μ c := by
        by_contra hnot
        exact (not_le_of_gt hci)
          ((measureInverse_le_iff μ hμ hx hec).mpr (le_of_not_gt hnot))
      filter_upwards [hxp, Iio_mem_nhds hR] with y hy hRy
      have hnot : ¬ measureInverse μ e y ≤ c := by
        intro hle
        exact (not_le_of_gt hRy) ((measureInverse_le_iff μ hμ hy hec).mp hle)
      exact hlc.trans (lt_of_not_ge hnot)
  · intro u hu
    have heu : e < u := hbound.trans_lt hu
    have hR := (measureInverse_lt_iff μ hμ hx heu).mp hu
    filter_upwards [hxp, Ioi_mem_nhds hR] with y hy hRy
    exact (measureInverse_lt_iff μ hμ hy heu).mpr hRy

theorem continuousAt_measureR_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    ContinuousAt (measureR μ e) x := by
  have hc : ContinuousAt (fun y => measureInverse μ e y - 1 / y) x :=
    (continuousAt_measureInverse μ hμ hx).sub
    (continuousAt_const.div continuousAt_id hx.ne')
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [measureR, ite_eq_left (show 0 < y from hy)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureRBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-support estimates for the general spectral transform. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma integrable_spectralCoordinate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) : Integrable (fun y => y) μ := by
  apply (integrable_const (|l| + |e|)).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hμ] with y hy
  rw [Real.norm_eq_abs, abs_le]
  simp only [id_eq]
  constructor
  · linarith [neg_abs_le l, abs_nonneg e, hy.1]
  · linarith [le_abs_self e, abs_nonneg l, hy.2]

theorem measureR_bounds_all (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (x : ℝ) :
    l ≤ measureR μ e x ∧ measureR μ e x ≤ e := by
  by_cases hx : 0 < x
  · exact measureR_bounds μ hμ hx
  · rw [measureR, ite_eq_right hx]
    constructor
    · simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (integrable_const l) (integrable_spectralCoordinate μ hμ)
          (hμ.mono fun _ h => h.1)
    · simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (integrable_spectralCoordinate μ hμ) (integrable_const e)
          (hμ.mono fun _ h => h.2)

theorem measureInverse_uncapped_small (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e x : ℝ} (hK : 0 < K) (he : e ≤ K)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    e < measureInverse μ e x ∧ measureResolvent μ (measureInverse μ e x) = x := by
  have htest : e < 1 / x - K := by
    have h := (le_div_iff₀ hx).mpr hsmall
    nlinarith
  have hl := le_measureResolvent μ hμ htest
  have hvalue : x ≤ measureResolvent μ (1 / x - K) := by
    simpa only [sub_neg_eq_add, sub_add_cancel, one_div_one_div] using hl
  have hex := exists_measureResolvent_solution μ (hμ.mono fun _ h => h.2) htest hx hvalue
  obtain ⟨b, hb, hsol⟩ := hex
  rw [measureInverse_eq_of_solution μ (hμ.mono fun _ h => h.2) hb hsol]
  exact ⟨hb, hsol⟩

theorem measureR_sub_mean_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hx : 0 < x)
    (hs : e < measureInverse μ e x ∧ measureResolvent μ (measureInverse μ e x) = x) :
    measureR μ e x - ∫ y, y ∂μ =
      ∫ y, (measureR μ e x - y) ^ 2 / (measureInverse μ e x - y) ∂μ := by
  let b := measureInverse μ e x
  have hi := integrable_spectralCoordinate μ hμ
  have hk : Integrable (fun y => 1 / (b - y)) μ :=
    integrable_resolventKernel μ (hμ.mono fun _ h => h.2) hs.1
  have ha : ∀ᵐ y ∂μ, (measureR μ e x - y) ^ 2 / (b - y) =
      (b - y) - 2 / x + (1 / x ^ 2) * (1 / (b - y)) := by
    filter_upwards [hμ] with y hy
    have hby : b - y ≠ 0 := by dsimp only [b] <;> linarith [hs.1, hy.2]
    simp only [measureR, ite_eq_left hx]
    change (b - 1 / x - y) ^ 2 / (b - y) = _
    field_simp [hx.ne', hby]
    ring
  have hibase : Integrable (fun y => b - y) μ := (integrable_const b).sub hi
  have hib : Integrable (fun y => b - y - 2 / x) μ :=
    hibase.sub (integrable_const (2 / x))
  have hir : Integrable (fun y => (1 / x ^ 2) * (1 / (b - y))) μ := hk.const_mul _
  have hsplit : (∫ y, b - y - 2 / x ∂μ) = b - (∫ y, y ∂μ) - 2 / x := by
    calc
      _ = (∫ y, b - y ∂μ) - (∫ _, 2 / x ∂μ) :=
        integral_sub hibase (integrable_const (2 / x))
      _ = _ := by
        rw [show (∫ y, b - y ∂μ) = (∫ _, b ∂μ) - (∫ y, y ∂μ) from
          integral_sub (integrable_const b) hi]
        simp
  rw [integral_congr_ae ha, integral_add hib hir, hsplit, integral_const_mul]
  change measureR μ e x - (∫ y, y ∂μ) =
    b - (∫ y, y ∂μ) - 2 / x + (1 / x ^ 2) * measureResolvent μ b
  rw [hs.2]
  simp only [measureR, ite_eq_left hx]
  change b - 1 / x - (∫ y, y ∂μ) = _
  field_simp
  ring

theorem measureR_sub_mean_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e x : ℝ} (hK : 0 < K) (he : e ≤ K)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    0 ≤ measureR μ e x - ∫ y, y ∂μ ∧
      measureR μ e x - ∫ y, y ∂μ ≤ 8 * K ^ 2 * x := by
  let b := measureInverse μ e x
  let r := measureR μ e x
  have hs := measureInverse_uncapped_small μ hK he hμ hx hsmall
  have hr := measureR_bounds μ hμ hx
  have hbr : x * b = x * r + 1 := by
    dsimp only [b, r]
    simp only [measureR, ite_eq_left hx]
    field_simp
    ring
  have hb : ∀ᵐ y ∂μ, 0 ≤ (r - y) ^ 2 / (b - y) ∧
      (r - y) ^ 2 / (b - y) ≤ 8 * K ^ 2 * x := by
    filter_upwards [hμ] with y hy
    have hden : 0 < b - y := by dsimp only [b] <;> linarith [hs.1, hy.2]
    have hlo : -2 * K ≤ r - y := by dsimp only [r] <;> linarith [hr.1, hy.2]
    have hhi : r - y ≤ 2 * K := by dsimp only [r] <;> linarith [hr.2, hy.1]
    have hsq : (r - y) ^ 2 ≤ 4 * K ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
    have hinv : 1 / (b - y) ≤ 2 * x := by
      apply (div_le_iff₀ hden).mpr
      have := mul_le_mul_of_nonneg_left hlo hx.le
      nlinarith
    refine ⟨div_nonneg (sq_nonneg _) hden.le, ?_⟩
    calc
      (r - y) ^ 2 / (b - y) = (r - y) ^ 2 * (1 / (b - y)) := by ring
      _ ≤ (4 * K ^ 2) * (2 * x) := mul_le_mul hsq hinv (one_div_pos.mpr hden).le (by positivity)
      _ = 8 * K ^ 2 * x := by ring
  have hm : Measurable (fun y : ℝ => (r - y) ^ 2 / (b - y)) :=
    ((measurable_const.sub measurable_id).pow_const 2).div (measurable_const.sub measurable_id)
  have hi : Integrable (fun y => (r - y) ^ 2 / (b - y)) μ := by
    apply (integrable_const (8 * K ^ 2 * x)).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
  rw [measureR_sub_mean_identity μ hμ hx hs]
  constructor
  · exact integral_nonneg_of_ae (hb.mono fun _ h => h.1)
  · have hu := integral_mono_ae hi (integrable_const (8 * K ^ 2 * x)) (hb.mono fun _ h => h.2)
    simpa only [integral_const, probReal_univ, one_smul] using hu

theorem continuousAt_measureR_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    ContinuousAt (measureR μ e) 0 := by
  have herr : ∀ᶠ x : ℝ in 𝓝 0,
      ‖measureR μ e x - ∫ y, y ∂μ‖ ≤ 8 * K ^ 2 * |x| := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * K) by positivity)] with x hxsmall
    by_cases hx : 0 < x
    · have hsmall : 4 * K * x ≤ 1 := by
        have := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hxsmall
        nlinarith
      have hb := measureR_sub_mean_bound μ hK he hμ hx hsmall
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_pos hx] using hb.2
    · simp only [measureR, ite_eq_right hx, sub_self, norm_zero]
      positivity
  have ht : Tendsto (fun x : ℝ => 8 * K ^ 2 * |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (8 * K ^ 2)
  have hl := (tendsto_sub_nhds_zero_iff).mp (squeeze_zero_norm' herr ht)
  simpa only [ContinuousAt, measureR, lt_self_iff_false, ite_false, if_false] using hl

theorem continuous_measureR (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    Continuous (measureR μ e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ∫ y, y ∂μ) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [measureR, ite_eq_right (not_lt.mpr (show y < 0 from hy).le)]
  · subst x
    exact continuousAt_measureR_zero μ hK he hμ
  · exact continuousAt_measureR_pos μ (hμ.mono fun _ h => h.2) hx

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureWeakResolvent
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent continuity under weak convergence and convergence of upper
edges. Bounded continuous test functions avoid the pole outside the supports. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BoundedContinuousFunction

namespace InvariantIsing

theorem measureResolvent_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hsupport : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hsupport0 : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    {b : ℝ} (hb : e < b) :
    Tendsto (fun k => measureResolvent (μs k : Measure ℝ) b) atTop
      (𝓝 (measureResolvent (μ : Measure ℝ) b)) := by
  let c := (e + b) / 2
  let d := b - c
  have hec : e < c := by dsimp only [c] <;> linarith
  have hcb : c < b := by dsimp only [c] <;> linarith
  have hd : 0 < d := sub_pos.mpr hcb
  let f : ℝ → ℝ := fun y => 1 / max d (b - y)
  have hf : Continuous f := continuous_const.div
    (continuous_const.max (continuous_const.sub continuous_id))
    (fun y => ne_of_gt (hd.trans_le (le_max_left _ _)))
  have hfb y : |f y| ≤ 1 / d := by
    dsimp only [f]
    rw [abs_of_pos (one_div_pos.mpr (hd.trans_le (le_max_left _ _)))]
    exact one_div_le_one_div_of_le hd (le_max_left _ _)
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 / d) (by
    intro y z
    rw [Real.dist_eq]
    calc
      |f y - f z| ≤ |f y| + |f z| := abs_sub _ _
      _ ≤ 1 / d + 1 / d := add_le_add (hfb y) (hfb z)
      _ = 2 / d := by ring)
  have heq (ν : Measure ℝ) (hν : ∀ᵐ y ∂ν, y ≤ c) :
      (∫ y, F y ∂ν) = measureResolvent ν b := by
    apply integral_congr_ae
    filter_upwards [hν] with y hy
    change 1 / max d (b - y) = 1 / (b - y)
    rw [max_eq_right (by dsimp only [d] <;> linarith)]
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) F
  rw [heq (μ : Measure ℝ) (hsupport0.mono fun y hy => hy.trans hec.le)] at ht
  apply ht.congr'
  filter_upwards [hedge.eventually (Iio_mem_nhds hec)] with k hk
  exact heq (μs k : Measure ℝ) ((hsupport k).mono fun y hy => hy.trans hk.le)

theorem measureInverse_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hsupport : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hsupport0 : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => measureInverse (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureInverse (μ : Measure ℝ) e x)) := by
  have hbound := (measureInverse_bounds (μ : Measure ℝ) hsupport0 hx).1
  have hxp : ∀ᶠ k in atTop, 0 < xs k := hxs.eventually (Ioi_mem_nhds hx)
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases hle : l < e
    · filter_upwards [hxp, hedge.eventually (Ioi_mem_nhds hle)] with k hk hek
      exact hek.trans_le (measureInverse_bounds (μs k : Measure ℝ) (hsupport k) hk).1
    · let c := (l + measureInverse (μ : Measure ℝ) e x) / 2
      have hec : e < c := by dsimp only [c] <;> linarith [le_of_not_gt hle]
      have hlc : l < c := by dsimp only [c] <;> linarith
      have hci : c < measureInverse (μ : Measure ℝ) e x := by dsimp only [c] <;> linarith
      have hR : x < measureResolvent (μ : Measure ℝ) c := by
        by_contra hnot
        exact (not_le_of_gt hci)
          ((measureInverse_le_iff (μ : Measure ℝ) hsupport0 hx hec).mpr (le_of_not_gt hnot))
      have hRc := measureResolvent_tendsto_weak μs μ es e hweak hedge hsupport hsupport0 hec
      filter_upwards [hxp, hedge.eventually (Iio_mem_nhds hec), hxs.eventually_lt hRc hR]
        with k hk hek hRk
      apply hlc.trans
      apply lt_of_not_ge
      intro hnot
      exact (not_le_of_gt hRk)
        ((measureInverse_le_iff (μs k : Measure ℝ) (hsupport k) hk hek).mp hnot)
  · intro u hu
    have heu : e < u := hbound.trans_lt hu
    have hR := (measureInverse_lt_iff (μ : Measure ℝ) hsupport0 hx heu).mp hu
    have hRu := measureResolvent_tendsto_weak μs μ es e hweak hedge hsupport hsupport0 heu
    filter_upwards [hxp, hedge.eventually (Iio_mem_nhds heu), hRu.eventually_lt hxs hR]
      with k hk hek hRk
    exact (measureInverse_lt_iff (μs k : Measure ℝ) (hsupport k) hk hek).mpr hRk

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureSpectralContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral-transform continuity for compactly supported laws, including
the zero argument and the upper-edge branch. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BoundedContinuousFunction

namespace InvariantIsing

theorem spectralMean_tendsto_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) {K : ℝ} (hK : 0 ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) K)
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) K) :
    Tendsto (fun k => ∫ y, y ∂(μs k : Measure ℝ)) atTop
      (𝓝 (∫ y, y ∂(μ : Measure ℝ))) := by
  let f : ℝ → ℝ := fun y => max (-K) (min K y)
  have hf : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hb y : |f y| ≤ K := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * K) (by
    intro y z
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans ((add_le_add (hb y) (hb z)).trans_eq (by ring)))
  have heq (ν : Measure ℝ) (hν : ∀ᵐ y ∂ν, y ∈ Icc (-K) K) :
      (∫ y, F y ∂ν) = ∫ y, y ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with y hy
    change max (-K) (min K y) = y
    rw [min_eq_right hy.2, max_eq_right hy.1]
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) F
  rw [heq (μ : Measure ℝ) hμ] at ht
  exact ht.congr' (Eventually.of_forall fun k => heq (μs k : Measure ℝ) (hs k))

theorem measureR_tendsto_weak_pos
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ≤ es k)
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ≤ e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e x)) := by
  have hi := measureInverse_tendsto_weak μs μ es e hweak hedge hs hμ xs hxs hx
  have hrecip : Tendsto (fun k => 1 / xs k) atTop (𝓝 (1 / x)) :=
    tendsto_const_nhds.div hxs hx.ne'
  have ht : Tendsto
      (fun k => measureInverse (μs k : Measure ℝ) (es k) (xs k) - 1 / xs k)
      atTop (𝓝 (measureR (μ : Measure ℝ) e x)) := by
    simpa only [measureR, ite_eq_left hx] using hi.sub hrecip
  apply ht.congr'
  filter_upwards [hxs.eventually (Ioi_mem_nhds hx)] with k hk
  simp only [measureR, ite_eq_left (show 0 < xs k from hk)]

theorem measureR_tendsto_weak_zero
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (xs : ℕ → ℝ) (hxs : Tendsto xs atTop (𝓝 0)) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e 0)) := by
  have hm := spectralMean_tendsto_weak μs μ hweak hK.le
    (fun k => (hs k).mono fun y hy => ⟨hy.1, hy.2.trans (hes k)⟩)
    (hμ.mono fun y hy => ⟨hy.1, hy.2.trans he⟩)
  have herr : ∀ᶠ k in atTop,
      ‖measureR (μs k : Measure ℝ) (es k) (xs k) - ∫ y, y ∂(μs k : Measure ℝ)‖ ≤
        8 * K ^ 2 * |xs k| := by
    filter_upwards [hxs.eventually (Iio_mem_nhds
      (show (0 : ℝ) < 1 / (4 * K) by positivity))] with k hk
    by_cases hxk : 0 < xs k
    · have hsmall : 4 * K * xs k ≤ 1 := by
        have := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hk
        nlinarith
      have hb := measureR_sub_mean_bound (μs k : Measure ℝ) hK (hes k) (hs k) hxk hsmall
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, abs_of_pos hxk] using hb.2
    · simp only [measureR, ite_eq_right hxk, sub_self, norm_zero]
      positivity
  have hb : Tendsto (fun k => 8 * K ^ 2 * |xs k|) atTop (𝓝 0) := by
    simpa using hxs.abs.const_mul (8 * K ^ 2)
  have ht := (squeeze_zero_norm' herr hb).add hm
  simpa only [sub_add_cancel, zero_add, measureR, lt_self_iff_false, ite_false, if_false] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureVariationalContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform transform convergence and continuity of the variational value
for the compact spectral laws in manuscript Lemma `gen:R-continuity`. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

theorem measureR_tendsto_weak_nonneg
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 ≤ x) :
    Tendsto (fun k => measureR (μs k : Measure ℝ) (es k) (xs k)) atTop
      (𝓝 (measureR (μ : Measure ℝ) e x)) := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    exact measureR_tendsto_weak_zero μs μ es e hweak hK he hes hs hμ xs hxs
  · exact measureR_tendsto_weak_pos μs μ es e hweak hedge
      (fun k => (hs k).mono fun _ h => h.2) (hμ.mono fun _ h => h.2) xs hxs hx

theorem measureR_uniform_weak
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) 1,
      |measureR (μs k : Measure ℝ) (es k) x - measureR (μ : Measure ℝ) e x| < ε := by
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ x ∈ Icc (0 : ℝ) 1,
      ε ≤ |measureR (μs k : Measure ℝ) (es k) x - measureR (μ : Measure ℝ) e x| := by
    simpa only [Filter.not_eventually, not_forall, _root_.not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose xs hxs herr using hφbad
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxs
  have hR := measureR_tendsto_weak_nonneg (fun k => μs (φ (ψ k))) μ
    (fun k => es (φ (ψ k))) e (hweak.comp (hφ.comp hψ).tendsto_atTop)
    (hedge.comp (hφ.comp hψ).tendsto_atTop) hK he (fun k => hes (φ (ψ k)))
    (fun k => hs (φ (ψ k))) hμ (fun k => xs (ψ k)) hlim hx.1
  have hfixed := (continuous_measureR (μ : Measure ℝ) hK he hμ).continuousAt.tendsto.comp hlim
  have hzero : Tendsto (fun k =>
      |measureR (μs (φ (ψ k)) : Measure ℝ) (es (φ (ψ k))) (xs (ψ k)) -
        measureR (μ : Measure ℝ) e (xs (ψ k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hR.sub hfixed).abs
  obtain ⟨k, hk⟩ := (hzero.eventually (Iio_mem_nhds hε)).exists
  exact (not_le_of_gt hk) (herr (ψ k))

theorem measureVariational_ne_top_bot (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K e : ℝ} (hK : 0 < K) (he : e ≤ K) (hμ : ∀ᵐ y ∂μ, y ∈ Icc (-K) e) :
    variationalFunctional (measureR μ e) ≠ ⊤ ∧ variationalFunctional (measureR μ e) ≠ ⊥ := by
  have hR := continuous_measureR μ hK he hμ
  have hb x : |measureR μ e x - 0| ≤ K := by
    have h := measureR_bounds_all μ hμ x
    rw [sub_zero, abs_le]
    exact ⟨h.1, h.2.trans he⟩
  have hspec p : |spectralFunctional (measureR μ e) p| ≤ K / 2 := by
    simpa only [spectralFunctional_constant, zero_div, sub_zero] using
      abs_spectralFunctional_sub_le (measureR μ e) (fun _ => 0) hR continuous_const
        K (fun x _ => hb x) p
  have hupper : variationalFunctional (measureR μ e) ≤ (K / 2 : ℝ) := by
    let p := constantPath 0 (by constructor <;> norm_num)
    have hi := iInf_le (fun p : OverlapPath => entropyFunctional p +
      (spectralFunctional (measureR μ e) p : EReal)) p
    simp only [p, entropyFunctional_zero, zero_add] at hi
    exact hi.trans (by exact_mod_cast (abs_le.mp (hspec p)).2)
  have hlower : ((-(K / 2) : ℝ) : EReal) ≤ variationalFunctional (measureR μ e) := by
    apply le_iInf
    intro p
    have hl : ((-(K / 2) : ℝ) : EReal) ≤ (spectralFunctional (measureR μ e) p : EReal) := by
      exact_mod_cast (abs_le.mp (hspec p)).1
    have hnonneg := add_le_add (entropyFunctional_nonneg p)
      (le_rfl : (spectralFunctional (measureR μ e) p : EReal) ≤ _)
    exact hl.trans (by simpa only [zero_add] using hnonneg)
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlower⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactPartitionContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite positive-mass partition values converge to the compact spectral value. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

lemma compact_partition_laws_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => (D k).law) atTop (𝓝 ν) := by
  have hh := spectral_quantization_weak ν
    (fun k => spectralBallQuantizer (D k).center (D k).radius a)
    (fun k => measurable_spectralBallQuantizer _ _ _) δ hδ (fun k => (D k).quantizer_close)
  apply hh.congr
  intro k
  apply Subtype.ext
  exact (D k).law_eq_map.symm

lemma compact_partition_edges_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hab : a ≤ b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => (D k).edge) atTop (𝓝 b) := by
  have hlo k : b-δ k ≤ (D k).edge := by linarith [(D k).endpoint_bounds ha hb]
  have hhi k : (D k).edge ≤ b := ((D k).value_mem hab (D k).upper).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using tendsto_const_nhds.sub hδ)
    tendsto_const_nhds hlo hhi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactPartitionPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite positive spectral partitions bracket physical mean pressure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function

namespace InvariantIsing.CompactSpectralPartition

variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

lemma rounding_bounds (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (x : ℝ) (hx : x∈Icc a b) : D.lowerValue x-δ ≤ x ∧ x ≤ D.upperValue x+δ := by
  have he := D.endpoint_bounds ha hb
  exact positive_spectral_rounding_bounds (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
    D.value a b δ D.lower D.upper he.1 he.2
    (positive_spectral_ball_cell_close (ν : Measure ℝ) D.center D.radius a δ
      D.radius_le D.residual_zero) x hx

lemma rounded_mem (hab : a ≤ b) (x : ℝ) :
    D.lowerValue x∈Icc a b ∧ D.upperValue x∈Icc a b :=
  ⟨D.value_mem hab _,D.value_mem hab _⟩

end InvariantIsing.CompactSpectralPartition

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpectralContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform spectral-transform errors pass through both magnetic
optimizations, and imply continuity in positive spectral populations. -/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

lemma magneticVariationalFunctional_le_add {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) :
    magneticVariationalFunctional R γ mag ≤ magneticVariationalFunctional Q γ mag + ((δ / 2 : ℝ) : EReal) := by
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mp
  apply le_iInf
  intro p
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mpr
  have hspec : (spectralFunctional R p : EReal) ≤
      (spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe
    have hb := (abs_le.mp (abs_spectralFunctional_sub_le R Q hR hQ δ hδ p)).2
    linarith
  calc
    magneticVariationalFunctional R γ mag ≤ magneticEntropyFunctional γ mag p + (spectralFunctional R p : EReal) :=
      iInf_le _ p
    _ ≤ magneticEntropyFunctional γ mag p +
        ((spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal)) :=
      add_le_add le_rfl hspec
    _ = _ := by rw [add_assoc]


lemma finiteMagneticFunctional_spectral_le_add {A : Type*} [Fintype A]
    (γ b : A → ℝ) (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Icc (0 : ℝ) 1, |R x-Q x| ≤ δ) :
    finiteMagneticFunctional R γ b ≤ finiteMagneticFunctional Q γ b+((δ/2 : ℝ) : EReal) := by
  apply iSup_le
  intro mag
  have hh := magneticVariationalFunctional_le_add γ (fun a => (mag.val a : ℝ)) R Q hR hQ δ hδ
  have hi := le_iSup (fun t : RationalMagnetization A =>
    ((∑ a, γ a*b a*(t.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional Q γ (fun a => (t.val a : ℝ))) mag
  calc
    _ ≤ ((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
        (magneticVariationalFunctional Q γ (fun a => (mag.val a : ℝ))+((δ/2 : ℝ) : EReal)) :=
      add_le_add le_rfl hh
    _ = (((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
        magneticVariationalFunctional Q γ (fun a => (mag.val a : ℝ)))+((δ/2 : ℝ) : EReal) :=
      (add_assoc _ _ _).symm
    _ ≤ _ := add_le_add hi le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpectralPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null-boundary spectral rounding for the finite external-field formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical BigOperators Function
namespace InvariantIsing

theorem spectral_partition_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (hbd : ∀ i, (ν : Measure ℝ) (frontier (S i))=0)
    (lam : ι → ℝ) (fallback aMax : {i // 0 < (ν : Measure ℝ).real (S i)})
    (hMax : ∀ a : {i // 0 < (ν : Measure ℝ).real (S i)}, lam a ≤ lam aMax)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure
      (fun i => lam (positiveSpectralLabel (fun a => (ν : Measure ℝ).real (S a)) fallback
        (spectralPartitionIndex S hcover (eig N i))))
      (matrixRotation V⁻¹) (fun i => b (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR
        (finiteSpectralMeasure (fun i : {i // 0 < (ν : Measure ℝ).real (S i)} =>
          (ν : Measure ℝ).real (S i)) (fun i => lam i)) (lam aMax)) γ b).toReal) := by
  let w := fun a => (ν : Measure ℝ).real (S a)
  let g := fun N (i : Fin N) => spectralPartitionIndex S hcover (eig N i)
  have hc := spectral_label_counts_partition (fun k => k+1) Nat.succ_pos
    (fun k => eig (k+1)) ν hweak S hS hbd (fun k => g (k+1))
    (fun k a i => spectralPartitionIndex_eq_iff S hcover hdis (eig (k+1) i) a)
  have hp := positive_spectral_counts_tendsto (fun k => k+1) (fun k => g (k+1))
    w (fun _ => measureReal_nonneg) fallback hc
  have hfull : Tendsto (fun N a =>
      (spectralLabelCount (positiveSpectralLabel w fallback ∘ g N) a : ℝ)/N)
      atTop (𝓝 (fun a : {i // 0 < w i} => w a)) :=
    (tendsto_add_atTop_iff_nat 1).mp hp
  exact finite_type_field_pressure_tendsto hhaar hgauss hpub μ (fun a : {i // 0 < w i} => lam a)
    (fun N => positiveSpectralLabel w fallback ∘ g N) (fun a : {i // 0 < w i} => w a)
    (fun a => a.property) (positiveSpectralWeights_sum w (fun _ => measureReal_nonneg)
      (spectralPartitionWeights_sum (ν : Measure ℝ) S hcover hdis hS)) hfull aMax hMax group γ b hγ hγsum hgroup

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCompactPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive spectral partition bounds for the finite-field pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function
namespace InvariantIsing.CompactSpectralPartition
variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

lemma field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => D.lowerValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (D.law : Measure ℝ) D.edge) γ c).toReal) ∧
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => D.upperValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (D.law : Measure ℝ) D.edge) γ c).toReal) := by
  have hh (fallback : D.Positive) := spectral_partition_field_pressure_tendsto hhaar hgauss hpub μ eig ν hweak
    D.cells (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    (spectralBallCell_null_boundary (ν : Measure ℝ) _ D.null_boundary)
    D.value fallback D.upper D.le_upper group γ c hγ hγsum hgroup
  exact ⟨hh D.lower,hh D.upper⟩

lemma mean_field_pressure_bounds {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig : Fin N → ℝ)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hab : a ≤ b) (heig : ∀ i, eig i∈Icc a b) (c : Fin N → ℝ) :
    (∫ V, rotatedPressure (fun i => D.lowerValue (eig i))
      (matrixRotation V⁻¹) c ∂μ)-δ/2 ≤
        ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ ∧
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ) ≤
      (∫ V, rotatedPressure (fun i => D.upperValue (eig i))
        (matrixRotation V⁻¹) c ∂μ)+δ/2 := by
  let K := max |a| |b|
  have hbound (x : ℝ) (hx : x∈Icc a b) : |x| ≤ K := by
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le a
      have hk : |a| ≤ K := le_max_left _ _
      linarith [hx.1]
    · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))
  exact cavity_meanPressure_squeeze hN μ eig (fun i => D.lowerValue (eig i))
    (fun i => D.upperValue (eig i)) c δ K
    (fun i => hbound _ (heig i))
    (fun i => hbound _ (D.rounded_mem hab (eig i)).1)
    (fun i => hbound _ (D.rounded_mem hab (eig i)).2)
    (fun i => (D.rounding_bounds ha hb _ (heig i)).1)
    (fun i => (D.rounding_bounds ha hb _ (heig i)).2)

end InvariantIsing.CompactSpectralPartition

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_MeasureMagneticContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact spectral weak convergence preserves the finite-field magnetic value. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace InvariantIsing

theorem measureMagnetic_tendsto_weak {A : Type*} [Fintype A]
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (es : ℕ → ℝ) (e : ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hedge : Tendsto es atTop (𝓝 e))
    {K : ℝ} (hK : 0 < K) (he : e ≤ K) (hes : ∀ k, es k ≤ K)
    (hs : ∀ k, ∀ᵐ y ∂(μs k : Measure ℝ), y ∈ Icc (-K) (es k))
    (hμ : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Icc (-K) e)
    (γ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (measureR (μs k : Measure ℝ) (es k)) γ b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (measureR (μ : Measure ℝ) e) γ b).toReal) := by
  have hf0 := measureVariational_ne_top_bot (μ : Measure ℝ) hK he hμ
  have hf := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hf0.1 hf0.2
  have hR := continuous_measureR (μ : Measure ℝ) hK he hμ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [measureR_uniform_weak μs μ es e hweak hedge hK he hes hs hμ ε hε] with k hk
  have hfk0 := measureVariational_ne_top_bot (μs k : Measure ℝ) hK (hes k) (hs k)
  have hfk := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hfk0.1 hfk0.2
  have hRk := continuous_measureR (μs k : Measure ℝ) hK (hes k) (hs k)
  have hl := finiteMagneticFunctional_spectral_le_add γ b _ _ hRk hR ε (fun x hx => (hk x hx).le)
  have hr := finiteMagneticFunctional_spectral_le_add γ b _ _ hR hRk ε
    (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2, ← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hl hr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPartitionContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Magnetic variational convergence for finite positive spectral partitions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma compact_partition_magnetic_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hab : a ≤ b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b) (hδ : Tendsto δ atTop (𝓝 0))
    {A : Type*} [Fintype A] (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (measureR ((D k).law : Measure ℝ) (D k).edge) γ c).toReal)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  let K := |a|+|b|+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have haK : -K ≤ a := by dsimp [K] <;> linarith [neg_abs_le a,abs_nonneg b]
  have hbK : b ≤ K := by dsimp [K] <;> linarith [le_abs_self b,abs_nonneg a]
  exact measureMagnetic_tendsto_weak (fun k => (D k).law) ν
    (fun k => (D k).edge) b (compact_partition_laws_tendsto ν a b δ D hδ)
    (compact_partition_edges_tendsto ν a b δ D hab ha hb hδ) hK hbK
    (fun k => (((D k).value_mem hab (D k).upper).2).trans hbK)
    (fun k => ((D k).law_support hab).mono (fun _ hx => ⟨haK.trans hx.1,hx.2⟩))
    (by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact ⟨haK.trans (hbound hx).1,(hbound hx).2⟩) γ c hγ hγsum

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCompactSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite external-field formula for an arbitrary compact spectral law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem compact_spectral_field_pressure_tendsto_of_mem_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (heig : ∀ N i, eig N i∈Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ c : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (eig N) (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  let δ := fun k : ℕ => (1 : ℝ)/(k+1)
  let D (k : ℕ) : CompactSpectralPartition ν a b (δ k) := Classical.choice
    (exists_compact_spectral_partition ν a b (δ k) hcompact hbound (by dsimp [δ] <;> positivity))
  have hab : a ≤ b := (hbound ha).2
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hL := compact_partition_magnetic_tendsto ν a b δ D hab ha hb hbound hδ γ c
    (fun a => (hγ a).le) hγsum
  apply spectral_approximation_squeeze _
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).lowerValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
    (fun k N => ∫ V, rotatedPressure (fun i => (D k).upperValue (eig N i))
      (matrixRotation V⁻¹) (fun i => c (group N i)) ∂μ N)
    (fun k => (finiteMagneticFunctional (measureR ((D k).law : Measure ℝ) (D k).edge) γ c).toReal)
    δ _ hL hδ
    (fun k => ((D k).field_pressure_tendsto hhaar hgauss hpub μ eig hweak group γ c hγ hγsum hgroup).1)
    (fun k => ((D k).field_pressure_tendsto hhaar hgauss hpub μ eig hweak group γ c hγ hγsum hgroup).2)
  intro k
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (D k).mean_field_pressure_bounds (by omega) (μ N) (eig N) ha hb hab (heig N) (fun i => c (group N i))

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem_oai.{u_1} := @OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem_oai.{u_1}
