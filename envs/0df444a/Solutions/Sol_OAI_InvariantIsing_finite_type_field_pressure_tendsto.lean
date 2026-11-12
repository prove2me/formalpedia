-- Prove2me | solution 1 for OAI.InvariantIsing.finite_type_field_pressure_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:29:59.607195+00:00
-- url     : https://prove2.me/submissions/08441b44-59d2-446c-87de-359b91d9327f
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
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_transport_le
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finite_physical_field_pressure_upper
import Theorems.Thm_OAI_InvariantIsing_magnetic_affine_field_subsequence_lower

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
-- module Solutions.OAIQ258_II.IsingPerceptron_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section FiniteGibbs
variable {S : Type*} [Fintype S]

lemma finiteGibbs_nonneg {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    0 ≤ finiteGibbs w H x :=
  div_nonneg (mul_nonneg (hw.1 x) (Real.exp_pos _).le) (finitePartition_pos hw H).le

lemma finiteGibbs_sum {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    ∑ x, finiteGibbs w H x = 1 := by
  simp only [finiteGibbs, ← Finset.sum_div]
  exact div_self (finitePartition_pos hw H).ne'

lemma finiteGibbs_average_bound {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ x, |A x| ≤ K) :
    |∑ x, finiteGibbs w H x * A x| ≤ K := by
  calc
    _ ≤ ∑ x, |finiteGibbs w H x * A x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, finiteGibbs w H x * |A x| := by
      congr 1; ext x; rw [abs_mul, abs_of_nonneg (finiteGibbs_nonneg hw H x)]
    _ ≤ ∑ x, finiteGibbs w H x * K := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hA x) (finiteGibbs_nonneg hw H x))
    _ = K := by rw [← Finset.sum_mul, finiteGibbs_sum hw H, one_mul]

lemma hasDerivAt_finitePartition {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (w : S → ℝ) :
    HasDerivAt (fun s => finitePartition w (H s))
      (∑ x, w x * Real.exp (H t x) * dH x) t := by
  simpa only [finitePartition, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hH x).exp.const_mul (w x)))

lemma hasDerivAt_finiteGibbs {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (x : S) :
    HasDerivAt (fun s => finiteGibbs w (H s) x)
      (finiteGibbs w (H t) x *
        (dH x - ∑ y, finiteGibbs w (H t) y * dH y)) t := by
  have hd := ((hH x).exp.const_mul (w x)).div
    (hasDerivAt_finitePartition hH w) (finitePartition_pos hw (H t)).ne'
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [finiteGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(finitePartition_pos hw (H t)).ne']

lemma hasDerivAt_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) :
    HasDerivAt (fun s => Real.log (finitePartition w (H s)))
      (∑ x, finiteGibbs w (H t) x * dH x) t := by
  convert (hasDerivAt_finitePartition hH w).log (finitePartition_pos hw (H t)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteGibbs, div_mul_eq_mul_div, Finset.sum_div]

end FiniteGibbs

section Thermal
variable {S : Type*} [Fintype S]

lemma hasDerivAt_finiteGibbs_mean {w : S → ℝ} (hw : GibbsReference w)
    (B Y : S → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ x, finiteGibbs w (fun y => B y+s*Y y) x * Y x)
      (∑ x, finiteGibbs w (fun y => B y+t*Y y) x *
        (Y x-∑ z, finiteGibbs w (fun y => B y+t*Y y) z*Y z)^2) t := by
  have hd x := (hasDerivAt_finiteGibbs hw
    (fun y => (hasDerivAt_const t (B y)).add ((hasDerivAt_id t).mul_const (Y y))) x).mul_const (Y x)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hd x)
  convert hsum using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  let p := finiteGibbs w (fun y => B y+t*Y y)
  let m := ∑ z, p z*Y z
  have hp : ∑ x, p x = 1 := finiteGibbs_sum hw _
  change (∑ x, p x * (Y x-m)^2) = ∑ x, (p x * ((0+1*Y x)-∑ y, p y*(0+1*Y y)))*Y x
  simp only [zero_add, one_mul]
  change (∑ x, p x * (Y x-m)^2) = ∑ x, p x*(Y x-m)*Y x
  have he x : p x * (Y x-m)^2 = p x*(Y x-m)*Y x - m*(p x*Y x)+m^2*p x := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]
  change (∑ x, p x*(Y x-m)*Y x) - m*m + m^2*1 = _
  ring

lemma convexOn_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    (B Y : S → ℝ) :
    ConvexOn ℝ Set.univ (fun s => Real.log (finitePartition w (fun y => B y+s*Y y))) := by
  have h1 t := hasDerivAt_log_finitePartition hw
    (fun y => (hasDerivAt_const t (B y)).add ((hasDerivAt_id t).mul_const (Y y)))
  simp only [zero_add, one_mul] at h1
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (continuous_iff_continuousAt.mpr (fun t => (h1 t).continuousAt)).continuousOn
    (fun t _ => (h1 t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_finiteGibbs_mean hw B Y t).hasDerivWithinAt)
  intro t _
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (finiteGibbs_nonneg hw _ x) (sq_nonneg _))

end Thermal

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Ward
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume Gibbs rotation identity

Differentiation of a normalized Gibbs average produces the observable
variation and its covariance with the Hamiltonian variation. Haar invariance
then gives their exact integral identity. The spin prior may have zero weights.
No limiting Ward equations or pressure bounds are assumed here.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

lemma abs_gibbsAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ σ, |A σ| ≤ K) :
    |gibbsAverage w H A| ≤ K := finiteGibbs_average_bound hw H A hA

lemma measurable_gibbsAverage {Ω : Type*} [MeasurableSpace Ω]
    (w : S → ℝ) (H A : Ω → S → ℝ)
    (hH : ∀ σ, Measurable (fun ω => H ω σ))
    (hA : ∀ σ, Measurable (fun ω => A ω σ)) :
    Measurable (fun ω => gibbsAverage w (H ω) (A ω)) := by
  unfold gibbsAverage finiteGibbs finitePartition
  exact Finset.measurable_sum _ fun σ _ =>
    ((measurable_const.mul (hH σ).exp).div
      (Finset.measurable_sum _ fun τ _ => measurable_const.mul (hH τ).exp)).mul (hA σ)

/-- Derivative of a finite Gibbs expectation: the variation of the observable
plus its Gibbs covariance with the variation of the Hamiltonian. -/
lemma hasDerivAt_gibbsAverage {w : S → ℝ} (hw : GibbsReference w)
    {H A : ℝ → S → ℝ} {dH dA : S → ℝ} {t : ℝ}
    (hH : ∀ σ, HasDerivAt (fun s => H s σ) (dH σ) t)
    (hA : ∀ σ, HasDerivAt (fun s => A s σ) (dA σ) t) :
    HasDerivAt (fun s => gibbsAverage w (H s) (A s))
      (gibbsAverage w (H t) dA +
        gibbsAverage w (H t) (fun σ => A t σ * dH σ) -
        gibbsAverage w (H t) (A t) * gibbsAverage w (H t) dH) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (hasDerivAt_finiteGibbs hw hH σ).mul (hA σ))
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [gibbsAverage]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring

lemma abs_gibbsVariation_le {w : S → ℝ} (hw : GibbsReference w)
    (H A dH dA : S → ℝ) {K L M : ℝ}
    (hK : 0 ≤ K)
    (hA : ∀ σ, |A σ| ≤ K) (hH : ∀ σ, |dH σ| ≤ L)
    (hdA : ∀ σ, |dA σ| ≤ M) :
    |gibbsAverage w H dA + gibbsAverage w H (fun σ => A σ * dH σ) -
      gibbsAverage w H A * gibbsAverage w H dH| ≤ M + 2 * K * L := by
  have ha := abs_gibbsAverage_le hw H A hA
  have hh := abs_gibbsAverage_le hw H dH hH
  have hda := abs_gibbsAverage_le hw H dA hdA
  have hprod := abs_gibbsAverage_le hw H (fun σ => A σ * dH σ) (fun σ => by
    rw [abs_mul]
    exact mul_le_mul (hA σ) (hH σ) (abs_nonneg _) hK)
  calc
    _ ≤ |gibbsAverage w H dA| + |gibbsAverage w H (fun σ => A σ * dH σ)| +
        |gibbsAverage w H A * gibbsAverage w H dH| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + K * L + K * L := by
      rw [abs_mul]
      exact add_le_add (add_le_add hda hprod) (mul_le_mul ha hh (abs_nonneg _) hK)
    _ = M + 2 * K * L := by ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coordinate-plane rotations for the finite Haar Ward calculation. -/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

lemma planeGenerator_mulVec {N : ℕ} (i j k : Fin N) (v : Fin N → ℝ) :
    (planeGenerator i j *ᵥ v) k =
      (if k = i then v j else 0) - (if k = j then v i else 0) := by
  simp [planeGenerator, Matrix.sub_mulVec, Matrix.single_mulVec, Function.update_apply, eq_comm]

/-- The coordinate derivative along a genuine Haar-preserving plane rotation. -/
lemma hasDerivAt_planeRotation_coordinate {N : ℕ} (i j k : Fin N)
    (U : Orthogonal N) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (fun s => matrixRotation (planeRotation i j s * U) v k)
      ((if k = i then matrixRotation (planeRotation i j t * U) v j else 0) -
        (if k = j then matrixRotation (planeRotation i j t * U) v i else 0)) t := by
  let A := planeGenerator i j
  let ev := matrixVectorCoordinate k v.ofLp
  have he := (hasDerivAt_exp_smul_const' A t).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ)
  have hd := ev.hasFDerivAt.comp_hasDerivAt t he
  refine hd.congr_deriv (Eq.symm ?_)
  · change _ = ((A * NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ
        v.ofLp) k
    rw [mul_assoc, ← Matrix.mulVec_mulVec]
    exact (planeGenerator_mulVec i j k
      ((NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v.ofLp)).symm

lemma hasDerivAt_planeRotation_energy {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (eig : Fin N → ℝ) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => rotatedEnergy eig (matrixRotation (planeRotation i j s * U)) σ)
      ((eig i - eig j) * matrixRotation (planeRotation i j t * U) (spinVector σ) i *
        matrixRotation (planeRotation i j t * U) (spinVector σ) j) t := by
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_planeRotation_coordinate i j k U (spinVector σ) t).pow 2).const_mul
      (eig k))).const_mul (1 / 2 : ℝ)
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [Nat.cast_ofNat, mul_sub, mul_ite, mul_zero, sub_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinateWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coordinate Haar Ward identity for the Ising Hamiltonian

This proves the finite-dimensional identity for the unperturbed model with an
arbitrary deterministic spin prior and magnetic field.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_spinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun U : Orthogonal N => spinCoordinate U σ i) := by
  simp only [spinCoordinate, matrixRotation_apply, spinVector_apply]
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun U : Orthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact he.mul_const _

lemma measurable_orbitHamiltonian {N : ℕ} (eig c : Fin N → ℝ) (σ : Spin N) :
    Measurable (fun U : Orthogonal N => orbitHamiltonian eig c U σ) := by
  exact ((Finset.measurable_sum _ fun i _ =>
    ((measurable_spinCoordinate σ i).pow_const 2).const_mul (eig i)).const_mul
      (1 / 2 : ℝ)).add_const _

lemma spinCoordinate_sq_le {N : ℕ} (U : Orthogonal N) (σ : Spin N) (i : Fin N) :
    spinCoordinate U σ i ^ 2 ≤ N := by
  rw [← rotated_spin_sq_sum (matrixRotation U) σ]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma abs_coordinateProduct_le {N : ℕ} (i j : Fin N) (U : Orthogonal N) (σ : Spin N) :
    |coordinateProduct i j U σ| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  have hs : |coordinateProduct i j U σ| ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [sq_abs, coordinateProduct, mul_pow]
    simpa only [pow_two] using mul_le_mul hi hj (sq_nonneg _) (Nat.cast_nonneg _)
  exact (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp hs

lemma abs_coordinateSquareDifference_le {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (σ : Spin N) :
    |spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (spinCoordinate U σ j)],
    by nlinarith [sq_nonneg (spinCoordinate U σ i)]⟩

lemma hasDerivAt_plane_coordinateProduct {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (U : Orthogonal N) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => coordinateProduct i j (planeRotation i j s * U) σ)
      (spinCoordinate (planeRotation i j t * U) σ j ^ 2 -
        spinCoordinate (planeRotation i j t * U) σ i ^ 2) t := by
  have hd := (hasDerivAt_planeRotation_coordinate i j i U (spinVector σ) t).mul
    (hasDerivAt_planeRotation_coordinate i j j U (spinVector σ) t)
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [spinCoordinate, ite_true, if_true, hij, Ne.symm hij, ite_false, if_false, sub_zero, zero_sub]
    ring

lemma gibbsAverage_const_mul {S : Type*} [Fintype S] (w H A : S → ℝ) (a : ℝ) :
    gibbsAverage w H (fun σ => a * A σ) = a * gibbsAverage w H A := by
  simp only [gibbsAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite spectral resolvents

The finite-alphabet arguments in Sections 3 and 5 of the manuscript use
the unique solution of `∑ a, ρ a / (b - eig a) = x` above all eigenvalues.
The solution is unique and satisfies deterministic bounds.
The weights may vanish; their sum being one is the only normalization.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The transform of a point mass is the constant equal to its atom. -/
theorem finiteResolvent_constant {ρ : ι → ℝ} (hρsum : ∑ a, ρ a = 1)
    (b c : ℝ) :
    finiteResolvent ρ (fun _ => c) b = 1 / (b - c) := by
  unfold finiteResolvent
  rw [← Finset.sum_div, hρsum]

theorem constant_spectrum_solution {ρ : ι → ℝ}
    (hρsum : ∑ a, ρ a = 1) {x c : ℝ} (hx : 0 < x) :
    finiteResolvent ρ (fun _ => c) (c + 1 / x) = x := by
  rw [finiteResolvent_constant hρsum]
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and positive scaling of the finite spectral transform. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteInverse_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) (c : ℝ) :
    finiteInverse ρ (fun _ => c) hρ hρsum x = c + 1 / x := by
  have hs := finiteInverse_spec ρ (fun _ => c) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs.1
    (fun _ => by linarith [one_div_pos.mpr hx]) hs.2
  exact constant_spectrum_solution hρsum hx

theorem finiteR_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x c : ℝ) :
    finiteR ρ (fun _ => c) hρ hρsum x = c := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx, finiteInverse_constant ρ hρ hρsum hx c]
    ring
  · simp only [finiteR, ite_eq_right hx]
    rw [← Finset.sum_mul, hρsum, one_mul]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialPlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine coordinate-plane rotations and infinitesimal Haar invariance on
`SO(N)`, the rotation group used by the actual enriched model. -/

noncomputable section

open MeasureTheory Filter IsingPerceptron
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

lemma measurable_specialToOrthogonal {N : ℕ} :
    Measurable (specialToOrthogonal : SpecialOrthogonal N → Orthogonal N) :=
  measurable_subtype_coe.subtype_mk

/-- A dominated infinitesimal left rotation has Haar mean zero. -/
lemma integral_special_rotation_derivative_eq_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [μ.IsMulLeftInvariant] (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    (f : SpecialOrthogonal N → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (f' : ℝ → SpecialOrthogonal N → ℝ) (hf' : AEStronglyMeasurable (f' 0) μ)
    (B : SpecialOrthogonal N → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ B U)
    (hderiv : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t) :
    ∫ U, f' 0 U ∂μ = 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun U => f (R t * U)) μ := by
    apply Filter.Eventually.of_forall
    intro t
    have hmul : Measurable (fun U : SpecialOrthogonal N => R t * U) := by
      apply Measurable.subtype_mk
      change Measurable (fun U : SpecialOrthogonal N =>
        (R t : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ))
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      simp only [Matrix.mul_apply]
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          ((measurable_pi_apply k).comp measurable_subtype_coe))
    exact (hf.comp hmul).aestronglyMeasurable
  have hi : Integrable (fun U => f (R 0 * U)) μ := by simpa only [hR, one_mul] using hfi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hf'
    hbound hB hderiv
  have he : (fun t => ∫ U, f (R t * U) ∂μ) = fun _ : ℝ => ∫ U, f U ∂μ := by
    funext t
    exact integral_mul_left_eq_self f (R t)
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (∫ U, f U ∂μ))


variable {S : Type*} [Fintype S]

/-- Exact finite-volume Haar Ward identity. All regularity assumptions concern
finite-dimensional derivatives; none assumes a limiting overlap identity. -/
theorem integral_special_gibbs_rotation_identity {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H A : SpecialOrthogonal N → S → ℝ)
    (hHm : ∀ σ, Measurable (fun U => H U σ))
    (hAm : ∀ σ, Measurable (fun U => A U σ))
    (dH dA : ℝ → SpecialOrthogonal N → S → ℝ)
    (hdHm : ∀ σ, Measurable (fun U => dH 0 U σ))
    (hdAm : ∀ σ, Measurable (fun U => dA 0 U σ))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) (dH t U σ) t)
    (hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t)
    (K L M : ℝ) (hK : 0 ≤ K)
    (hAb : ∀ U σ, |A U σ| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dH t U σ| ≤ L)
    (hdAb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dA t U σ| ≤ M) :
    (∫ U, gibbsAverage w (H U) (dA 0 U) +
      gibbsAverage w (H U) (fun σ => A U σ * dH 0 U σ) -
      gibbsAverage w (H U) (A U) * gibbsAverage w (H U) (dH 0 U) ∂μ) = 0 := by
  let f : SpecialOrthogonal N → ℝ := fun U => gibbsAverage w (H U) (A U)
  let f' : ℝ → SpecialOrthogonal N → ℝ := fun t U =>
    gibbsAverage w (H (R t * U)) (dA t U) +
      gibbsAverage w (H (R t * U)) (fun σ => A (R t * U) σ * dH t U σ) -
      gibbsAverage w (H (R t * U)) (A (R t * U)) *
        gibbsAverage w (H (R t * U)) (dH t U)
  have hm : Measurable f := measurable_gibbsAverage w H A hHm hAm
  have hi : Integrable f μ := (integrable_const K).mono' hm.aestronglyMeasurable
    (ae_of_all μ fun U => by
      simpa only [Real.norm_eq_abs] using
        (abs_gibbsAverage_le hw (H U) (A U) (hAb U)))
  have hm' : Measurable (f' 0) := by
    simp only [f', hR, one_mul]
    exact ((measurable_gibbsAverage w H (dA 0) hHm hdAm).add
      (measurable_gibbsAverage w H (fun U σ => A U σ * dH 0 U σ) hHm
        (fun σ => (hAm σ).mul (hdHm σ)))).sub
      ((measurable_gibbsAverage w H A hHm hAm).mul
        (measurable_gibbsAverage w H (dH 0) hHm hdHm))
  have hb : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ M + 2 * K * L := by
    exact ae_of_all _ fun U t ht => by
      simpa only [f', Real.norm_eq_abs] using
        abs_gibbsVariation_le hw (H (R t * U)) (A (R t * U)) (dH t U) (dA t U)
          hK (hAb _) (hdHb U t ht) (hdAb U t ht)
  have hd : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t :=
    ae_of_all _ fun U t ht => hasDerivAt_gibbsAverage hw (hHd U t ht) (hAd U t ht)
  have he := integral_special_rotation_derivative_eq_zero μ R hR f hm hi f'
    hm'.aestronglyMeasurable (fun _ => M + 2 * K * L) (integrable_const _) hb hd
  simpa only [f', hR, one_mul] using he


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GibbsSecant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Gibbs averages bound a finite log-partition difference. These
are the convex secant inequalities used to change spectral multiplicities. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma log_finitePartition_sub_ge_gibbsAverage
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    gibbsAverage w H (fun s => K s - H s) ≤
      Real.log (finitePartition w K) - Real.log (finitePartition w H) := by
  let Y := fun s => K s - H s
  have hd := hasDerivAt_log_finitePartition hw (t := (0 : ℝ))
    (fun s => (hasDerivAt_const 0 (H s)).add ((hasDerivAt_id 0).mul_const (Y s)))
  have hc := convexOn_log_finitePartition hw H Y
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (by norm_num) hd
  simpa only [slope_def_field, sub_zero, div_one, zero_add, zero_mul, one_mul,
    add_sub_cancel, Y, gibbsAverage, Pi.add_apply, id_eq, add_zero] using hs

lemma log_finitePartition_sub_le_gibbsAverage
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    Real.log (finitePartition w K) - Real.log (finitePartition w H) ≤
      gibbsAverage w K (fun s => K s - H s) := by
  have h := log_finitePartition_sub_ge_gibbsAverage hw K H
  have he : gibbsAverage w K (fun s => H s - K s) =
      -gibbsAverage w K (fun s => K s - H s) := by
    simp only [gibbsAverage, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he] at h
  linarith

lemma log_finitePartition_secant_bounds
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    gibbsAverage w H (fun s => K s - H s) ≤
      Real.log (finitePartition w K) - Real.log (finitePartition w H) ∧
    Real.log (finitePartition w K) - Real.log (finitePartition w H) ≤
      gibbsAverage w K (fun s => K s - H s) :=
  ⟨log_finitePartition_sub_ge_gibbsAverage hw H K,
    log_finitePartition_sub_le_gibbsAverage hw H K⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralProjectionMass
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar-averaged squared projections are constant within each eigenspace.
This follows from the finite coordinate Ward identity and holds for any
fixed nonzero nonnegative spin prior, including deterministic fields. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma integrable_gibbsCoordinateSquare {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ) (i : Fin N) :
    Integrable (fun U => gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2)) μ := by
  apply (integrable_const (N : ℝ)).mono'
    (measurable_gibbsAverage w _ _ (fun σ => (measurable_orbitHamiltonian eig c σ).comp measurable_specialToOrthogonal)
      (fun σ => ((measurable_spinCoordinate σ i).pow_const 2).comp measurable_specialToOrthogonal)).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs]
  exact abs_gibbsAverage_le hw _ _ (fun σ => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact spinCoordinate_sq_le (specialToOrthogonal U) σ i)

lemma meanCoordinateSquare_nonneg {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) {w : Spin N → ℝ} (hw : GibbsReference w)
    (eig c : Fin N → ℝ) (i : Fin N) :
    0 ≤ meanCoordinateSquare μ w eig c i := by
  apply integral_nonneg
  intro U
  exact Finset.sum_nonneg fun σ _ =>
    mul_nonneg (finiteGibbs_nonneg hw _ σ) (sq_nonneg _)

lemma sum_meanCoordinateSquare {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ) :
    ∑ i, meanCoordinateSquare μ w eig c i = N := by
  unfold meanCoordinateSquare
  rw [← integral_finsetSum _ (fun i _ => integrable_gibbsCoordinateSquare μ hw eig c i)]
  have he (U : SpecialOrthogonal N) :
      (∑ i, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2)) = N := by
    simp only [gibbsAverage]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hnorm (σ : Spin N) : ∑ i, spinCoordinate (specialToOrthogonal U) σ i ^ 2 = N :=
      rotated_spin_sq_sum (specialRotation U) σ
    simp_rw [hnorm]
    rw [← Finset.sum_mul, finiteGibbs_sum hw, one_mul]
  simp only [he, integral_const, probReal_univ, one_smul]

lemma meanCoordinateSquare_eq_of_eigenvalue_eq {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (i j : Fin N) (hij : eig i = eig j) :
    meanCoordinateSquare μ w eig c i = meanCoordinateSquare μ w eig c j := by
  by_cases heq : i = j
  · rw [heq]
  let R := specialPlaneRotation i j
  let H := fun U : SpecialOrthogonal N => orbitHamiltonian eig c (specialToOrthogonal U)
  let A := fun U : SpecialOrthogonal N => coordinateProduct i j (specialToOrthogonal U)
  let dA := fun t U σ => spinCoordinate (specialToOrthogonal (R t * U)) σ j ^ 2 -
    spinCoordinate (specialToOrthogonal (R t * U)) σ i ^ 2
  have hR : R 0 = 1 := specialPlaneRotation_zero i j
  have hHm (σ : Spin N) : Measurable (fun U => H U σ) :=
    (measurable_orbitHamiltonian eig c σ).comp measurable_specialToOrthogonal
  have hAm (σ : Spin N) : Measurable (fun U => A U σ) :=
    ((measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)).comp
      measurable_specialToOrthogonal
  have hdAm (σ : Spin N) : Measurable (fun U => dA 0 U σ) := by
    simp only [dA, hR, one_mul]
    exact (((measurable_spinCoordinate σ j).pow_const 2).sub
      ((measurable_spinCoordinate σ i).pow_const 2)).comp measurable_specialToOrthogonal
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) 0 t := by
    intro U t _ σ
    simpa only [H, R, map_mul, specialToOrthogonal_planeRotation, orbitHamiltonian,
      hij, sub_self, zero_mul] using
      (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig σ t).add_const
        (fieldEnergy c σ)
  have hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t := by
    intro U t _ σ
    simpa only [A, R, dA, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_plane_coordinateProduct i j heq (specialToOrthogonal U) σ t
  have h := integral_special_gibbs_rotation_identity μ R hR hw H A hHm hAm
    (fun _ _ _ => 0) dA (fun _ => measurable_const) hdAm hHd hAd
    (N : ℝ) 0 (N : ℝ) (Nat.cast_nonneg _)
    (fun U σ => abs_coordinateProduct_le i j (specialToOrthogonal U) σ)
    (fun _ _ _ _ => by simp)
    (fun U t _ σ => abs_coordinateSquareDifference_le i j (specialToOrthogonal (R t * U)) σ)
  simp only [dA, hR, one_mul, H, mul_zero, gibbsAverage, Finset.sum_const_zero,
    add_zero, sub_zero] at h
  change (∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
    (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2 -
      spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ) = 0 at h
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2 - spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U)) (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2) -
        gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U)) (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, mul_sub, Finset.sum_sub_distrib]
  simp_rw [he] at h
  rw [integral_sub (integrable_gibbsCoordinateSquare μ hw eig c j)
    (integrable_gibbsCoordinateSquare μ hw eig c i)] at h
  exact (sub_eq_zero.mp h).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGroupMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The changed coordinates in an eigenspace carry precisely their fraction
of its Haar-averaged squared spin norm. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma sum_changed_group_mass_le {ι A : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] (label : ι → A) (changed : Finset ι)
    (mass : A → ℝ) (hmass : ∀ a, 0 ≤ mass a) (r : ℝ)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    ∑ i ∈ changed, mass (label i) ≤ r * ∑ i, mass (label i) := by
  have hchanged := Finset.sum_fiberwise' changed label mass
  have hall := Finset.sum_fiberwise' Finset.univ label mass
  rw [← hchanged, ← hall, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right (hcount a) (hmass a)

lemma abs_weighted_spectral_change_le {ι A : Type*} [Fintype ι] [Fintype A]
    [DecidableEq ι] [DecidableEq A] (label : ι → A) (changed : Finset ι)
    (mass : A → ℝ) (hmass : ∀ a, 0 ≤ mass a) (delta : ι → ℝ)
    (hzero : ∀ i, i ∉ changed → delta i = 0)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |delta i| ≤ L)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    |∑ i, delta i * mass (label i)| ≤ L * r * ∑ i, mass (label i) := by
  have he : (∑ i, delta i * mass (label i)) =
      ∑ i ∈ changed, delta i * mass (label i) := by
    symm
    exact Finset.sum_subset (Finset.subset_univ changed) (fun i _ hi => by rw [hzero i hi, zero_mul])
  rw [he]
  calc
    _ ≤ ∑ i ∈ changed, |delta i * mass (label i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ changed, L * mass (label i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hmass _)]
      exact mul_le_mul_of_nonneg_right (hdelta i) (hmass _)
    _ = L * ∑ i ∈ changed, mass (label i) := (Finset.mul_sum _ _ _).symm
    _ ≤ L * (r * ∑ i, mass (label i)) :=
      mul_le_mul_of_nonneg_left (sum_changed_group_mass_le label changed mass hmass r hcount) hL
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCountEndpoint
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint derivative bounds for changing spectral multiplicities. The
fraction estimate uses the actual Haar Gibbs projection masses. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma integrable_gibbsSpectralDirection {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ) :
    Integrable (fun U => gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2)) μ := by
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      ∑ i, delta i * gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_gibbsCoordinateSquare μ hw eig c i).const_mul _

lemma integral_gibbsSpectralDirection {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ) :
    (∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ) =
      ∑ i, delta i * meanCoordinateSquare μ w eig c i := by
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      ∑ i, delta i * gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_gibbsCoordinateSquare μ hw eig c i).const_mul _)]
  simp only [integral_const_mul, meanCoordinateSquare]

lemma abs_integral_gibbsSpectralDirection_le {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ)
    (label : Fin N → Fin m) (hlabel : Function.Surjective label)
    (lam : Fin m → ℝ) (hspectral : ∀ i, eig i = lam (label i))
    (changed : Finset (Fin N)) (hzero : ∀ i, i ∉ changed → delta i = 0)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |delta i| ≤ L)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    |∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ| ≤ L * r * N := by
  let rep : Fin m → Fin N := fun a => (hlabel a).choose
  have hrep a : label (rep a) = a := (hlabel a).choose_spec
  let mass : Fin m → ℝ := fun a => meanCoordinateSquare μ w eig c (rep a)
  have hm a : 0 ≤ mass a := meanCoordinateSquare_nonneg μ hw eig c (rep a)
  have he i : meanCoordinateSquare μ w eig c i = mass (label i) := by
    apply meanCoordinateSquare_eq_of_eigenvalue_eq μ hw eig c
    rw [hspectral i, hspectral (rep (label i)), hrep]
  rw [integral_gibbsSpectralDirection μ hw]
  simp_rw [he]
  have hs : (∑ i, mass (label i)) = N := by
    simp_rw [← he]
    exact sum_meanCoordinateSquare μ hw eig c
  simpa only [hs] using abs_weighted_spectral_change_le label changed mass hm delta
    hzero L r hL hdelta hcount

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCountComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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

lemma rotatedPressure_spectral_secant {N : ℕ} (eig kap c : Fin N → ℝ)
    (U : SpecialOrthogonal N) :
    (N : ℝ)⁻¹ * (1 / 2) * gibbsAverage (fun _ => 1) (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ≤
      rotatedPressure kap (specialRotation U) c - rotatedPressure eig (specialRotation U) c ∧
    rotatedPressure kap (specialRotation U) c - rotatedPressure eig (specialRotation U) c ≤
      (N : ℝ)⁻¹ * (1 / 2) * gibbsAverage (fun _ => 1) (orbitHamiltonian kap c (specialToOrthogonal U))
        (fun σ => ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
  have h := log_finitePartition_secant_bounds GibbsReference_one
    (orbitHamiltonian eig c (specialToOrthogonal U)) (orbitHamiltonian kap c (specialToOrthogonal U))
  have hd (σ : Spin N) : orbitHamiltonian kap c (specialToOrthogonal U) σ - orbitHamiltonian eig c (specialToOrthogonal U) σ =
      (1 / 2 : ℝ) * ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2 := by
    simp only [orbitHamiltonian, add_sub_add_right_eq_sub, rotatedEnergy,
      sub_mul, Finset.sum_sub_distrib, spinCoordinate]
    ring
  have he : Real.log (finitePartition (fun _ : Spin N => 1) (orbitHamiltonian kap c (specialToOrthogonal U))) -
      Real.log (finitePartition (fun _ : Spin N => 1) (orbitHamiltonian eig c (specialToOrthogonal U))) =
      logPartition (orbitHamiltonian kap c (specialToOrthogonal U)) - logPartition (orbitHamiltonian eig c (specialToOrthogonal U)) := by
    simp only [logPartition_eq, finitePartition, one_mul]
    ring
  simp_rw [hd] at h
  rw [gibbsAverage_const_mul, gibbsAverage_const_mul, he] at h
  constructor
  · convert mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr (Nat.cast_nonneg N)) using 1 <;>
      first | rfl | simp only [rotatedPressure, mul_sub, mul_assoc]
    all_goals rfl
  · convert mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr (Nat.cast_nonneg N)) using 1 <;>
      first | rfl | simp only [rotatedPressure, mul_sub, mul_assoc]
    all_goals rfl

/-- Changing a fraction at most `r` of every endpoint eigenspace changes the
mean pressure by at most `L*r/2`, where every eigenvalue displacement is at most `L`. -/
theorem meanPressure_change_counts_le {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig kap c : Fin N → ℝ) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hkap : ∀ i, |kap i| ≤ K)
    (label label' : Fin N → Fin m)
    (hl : Function.Surjective label) (hl' : Function.Surjective label')
    (lam : Fin m → ℝ) (he : ∀ i, eig i = lam (label i))
    (hk : ∀ i, kap i = lam (label' i))
    (changed : Finset (Fin N)) (hzero : ∀ i, i ∉ changed → kap i = eig i)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |kap i - eig i| ≤ L)
    (hc : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ))
    (hc' : ∀ a, ((changed.filter fun i => label' i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label' i = a).card : ℝ)) :
    |(∫ U, rotatedPressure kap (specialRotation U) c ∂μ) -
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ| ≤ L * r / 2 := by
  let delta := fun i => kap i - eig i
  have hz : ∀ i, i ∉ changed → delta i = 0 := by
    intro i hi
    simp only [delta, hzero i hi, sub_self]
  have hAe := integrable_gibbsSpectralDirection μ GibbsReference_one eig c delta
  have hAk := integrable_gibbsSpectralDirection μ GibbsReference_one kap c delta
  have hPe := integrable_countPressure hN μ eig c K heig
  have hPk := integrable_countPressure hN μ kap c K hkap
  have hlo := integral_mono (hAe.const_mul ((N : ℝ)⁻¹ * (1 / 2))) (hPk.sub hPe)
    (fun U => (rotatedPressure_spectral_secant eig kap c U).1)
  have hup := integral_mono (hPk.sub hPe) (hAk.const_mul ((N : ℝ)⁻¹ * (1 / 2)))
    (fun U => (rotatedPressure_spectral_secant eig kap c U).2)
  have hsub : (∫ U, rotatedPressure kap (specialRotation U) c -
      rotatedPressure eig (specialRotation U) c ∂μ) =
      (∫ U, rotatedPressure kap (specialRotation U) c ∂μ) -
        ∫ U, rotatedPressure eig (specialRotation U) c ∂μ := integral_sub hPk hPe
  simp only [Pi.sub_apply] at hlo hup
  rw [integral_const_mul, hsub] at hlo
  rw [integral_const_mul, hsub] at hup
  have hbe := abs_integral_gibbsSpectralDirection_le μ GibbsReference_one eig c delta
    label hl lam he changed hz L r hL hdelta hc
  have hbk := abs_integral_gibbsSpectralDirection_le μ GibbsReference_one kap c delta
    label' hl' lam hk changed hz L r hL hdelta hc'
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn0 : 0 ≤ (N : ℝ)⁻¹ * (1 / 2) := by positivity
  have hbL := mul_le_mul_of_nonneg_left (abs_le.mp hbe).1 hn0
  have hbU := mul_le_mul_of_nonneg_left (abs_le.mp hbk).2 hn0
  have hs : (N : ℝ)⁻¹ * (1 / 2) * (L * r * N) = L * r / 2 := by field_simp
  have hs' : (N : ℝ)⁻¹ * (1 / 2) * -(L * r * N) = -(L * r / 2) := by
    rw [mul_neg, hs]
  rw [hs'] at hbL
  rw [hs] at hbU
  exact abs_le.mpr ⟨hbL.trans hlo, hup.trans hbU⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPermutation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral reorderings can be realized inside SO(N). A single row sign
corrects a permutation determinant without changing any squared projection. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma spectralPermutation_coordinate_sq {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (specialRotation (spectralPermutation hN p * U) x i) ^ 2 =
      (specialRotation U x (p i)) ^ 2 := by
  have he : specialRotation (spectralPermutation hN p * U) x i =
      (if i = (⟨0, hN⟩ : Fin N) then (p.permMatrix ℝ).det else 1) *
        specialRotation U x (p i) := by
    change (((permutationSignDiagonal hN p * p.permMatrix ℝ) *
      (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x.ofLp) i = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
    simp only [permutationSignDiagonal, Matrix.mulVec_diagonal,
      Function.comp_apply, specialRotation_apply]
    rfl
  rw [he, mul_pow]
  split_ifs
  · rw [permutationMatrix_det_sq, one_mul]
  · rw [one_pow, one_mul]

lemma rotatedEnergy_spectralPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (eig : Fin N → ℝ) (U : SpecialOrthogonal N) (σ : Spin N) :
    rotatedEnergy (fun i => eig (p i)) (specialRotation (spectralPermutation hN p * U)) σ =
      rotatedEnergy eig (specialRotation U) σ := by
  simp only [rotatedEnergy, spectralPermutation_coordinate_sq]
  rw [Equiv.sum_comp p (fun i => eig i * (specialRotation U (spinVector σ) i) ^ 2)]

lemma meanPressure_spectralPermutation {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulLeftInvariant]
    (p : Equiv.Perm (Fin N)) (eig c : Fin N → ℝ) :
    (∫ U, rotatedPressure (fun i => eig (p i)) (specialRotation U) c ∂μ) =
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ := by
  have he (U : SpecialOrthogonal N) :
      rotatedPressure (fun i => eig (p i)) (specialRotation (spectralPermutation hN p * U)) c =
        rotatedPressure eig (specialRotation U) c := by
    simp only [rotatedPressure, rotatedEnergy_spectralPermutation]
  rw [← integral_mul_left_eq_self
    (fun U => rotatedPressure (fun i => eig (p i)) (specialRotation U) c)
    (spectralPermutation hN p)]
  simp only [he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical spectral labels form the actual finite partition with
exact prescribed block dimensions. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavity_group_dimension_card {N m : ℕ} (dims : Fin m → ℕ)
    (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N) (a : Fin m) :
    (cavitySpectralGroup (fun i => (E.symm i).1) a).card=dims a := by
  have he := Fintype.card_congr (cavityGroupSetEquiv dims E a)
  simpa only [Fintype.card_fin, Fintype.card_coe] using he.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrderedGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical ordered finite spectral groups are literal contiguous windows.
This fixes the full/base spectral ordering in the rational cavity sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityOrderedGroup_congr {N m : ℕ} {dims dims' : Fin m → ℕ}
    (hsum : ∑ a, dims a=N) (hsum' : ∑ a, dims' a=N) (heq : dims=dims') :
    cavityOrderedGroup dims hsum=cavityOrderedGroup dims' hsum' := by
  cases heq
  rfl

lemma cavityOrderedGroup_card {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) :
    (cavitySpectralGroup (cavityOrderedGroup dims hsum) a).card=dims a :=
  cavity_group_dimension_card dims (cavityOrderedEquiv dims hsum) a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational count progression has exactly the prescribed normalized
masses at every size, and its ordered block endpoints have exact limits. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityRationalDimension_tendsto (n q : ℕ) (hn : 0<n) :
    Tendsto (fun r : ℕ => (r+q)*n) atTop atTop := by
  apply tendsto_atTop_mono (fun r => ?_) tendsto_id
  change r≤(r+q)*n
  exact (Nat.le_add_right r q).trans (Nat.le_mul_of_pos_right _ hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed integer offsets in the block counts cover every residue class
of physical dimensions without changing the limiting rational masses. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavity_affine_ratio_tendsto (s c n d q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    Tendsto (fun r : ℕ => (((r+q)*s+c : ℕ) : ℝ)/((r+q)*n+d : ℕ)) atTop
      (𝓝 ((s : ℝ)/n)) := by
  have ha : Tendsto (fun r : ℕ => (r+q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.mul_one, Nat.cast_add] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (cavityRationalDimension_tendsto 1 q (by omega))
  have hi := tendsto_inv_atTop_zero.comp ha
  have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (s : ℝ)) atTop (𝓝 (s : ℝ))).add (hi.const_mul (c : ℝ))).div
    (tendsto_const_nhds.add (hi.const_mul (d : ℝ)))
    (by exact_mod_cast hn.ne' : (n : ℝ)+(d : ℝ)*0≠0))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr
  intro r
  have hr : (r+q : ℝ)≠0 := by exact_mod_cast (show r+q≠0 by omega)
  have hd : (r+q : ℝ)*(n : ℝ)+d≠0 := by positivity
  dsimp only [Pi.div_apply, Function.comp_def]
  push_cast
  field_simp

lemma cavityAffineCount_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityAffineCount s c q r a : ℝ)/cavityAffineSize n q c r)
      atTop (𝓝 ((s a : ℝ)/n)) :=
  cavity_affine_ratio_tendsto (s a) (c a) n (∑ a, c a) q hn hq

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityAffineLabel_eq_ordered {m n : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (hn : 0 < n) (N v : ℕ)
    (hN : N=v*n+∑ a, c a) (hc : ∑ a, (v*s a+c a)=N) :
    cavityAffineLabel hm s c hsum N=cavityOrderedGroup (fun a => v*s a+c a) hc := by
  have hsub : N-∑ a, c a=v*n := by omega
  have hd : n∣(N-∑ a, c a) := hsub ▸ dvd_mul_left n v
  have hle : (∑ a, c a) ≤ N := by omega
  have hv : (N-∑ a, c a)/n=v :=
    Nat.eq_of_mul_eq_mul_right hn ((Nat.div_mul_cancel hd).trans hsub)
  have hh : (∑ a, c a) ≤ N ∧ n∣(N-∑ a, c a) := ⟨hle,hd⟩
  simp only [cavityAffineLabel, dite_eq_left hh]
  apply cavityOrderedGroup_congr
  funext a
  rw [hv]

lemma cavityAffineLabel_progression {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (q r : ℕ) :
    cavityAffineLabel hm s c hsum (cavityAffineSize n q c r)=
      cavityOrderedGroup (cavityAffineCount s c q r) (cavityAffineCount_sum s c hsum q r) :=
  cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+q) rfl _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidueFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical rational multiplicities at every physical dimension. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityResidueOffset_sum {m : ℕ} (hm : 0 < m) (t : ℕ) :
    ∑ a, cavityResidueOffset hm t a=t := by
  classical
  simp [cavityResidueOffset]

lemma cavityResidueSize {m : ℕ} (hm : 0 < m) (n q t r : ℕ) :
    cavityAffineSize n q (cavityResidueOffset hm t) r=(r+q)*n+t := by
  simp only [cavityAffineSize, cavityResidueOffset_sum]

lemma cavityResidueSize_mod {m n : ℕ} (hm : 0 < m) (q t r : ℕ) (ht : t < n) :
    cavityAffineSize n q (cavityResidueOffset hm t) r%n=t := by
  rw [cavityResidueSize]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma cavityResidueLabel_progression {m n : ℕ} (hm : 0 < m)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) (q t r : ℕ) (ht : t < n) :
    cavityResidueLabel hm s hsum (cavityAffineSize n q (cavityResidueOffset hm t) r)=
      cavityAffineLabel hm s (cavityResidueOffset hm t) hsum
        (cavityAffineSize n q (cavityResidueOffset hm t) r) := by
  unfold cavityResidueLabel
  rw [cavityResidueSize_mod hm q t r ht]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidueConvergence
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many arithmetic progressions exhaust all sufficiently large sizes. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_residue_tendsto {n : ℕ} (hn : 0 < n) (q : ℕ) (f : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : Fin n, Tendsto (fun r : ℕ => f ((r+q)*n+t)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ r in atTop, ∀ t : Fin n, dist (f ((r+q)*n+t)) L < ε :=
    Filter.eventually_all.mpr (fun t => Metric.tendsto_nhds.mp (h t) ε hε)
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨(R+q)*n,fun N hN => ?_⟩
  have hdiv : R+q ≤ N/n := (Nat.le_div_iff_mul_le hn).mpr hN
  let t : Fin n := ⟨N%n,Nat.mod_lt _ hn⟩
  have hr : R ≤ N/n-q := by omega
  have hEq : (N/n-q+q)*n+t=N := by
    dsimp only [t]
    rw [Nat.sub_add_cancel (by omega)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod N n
  simpa only [hEq] using hR (N/n-q) hr t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-dimension canonical rational labels have the prescribed
positive limiting proportions. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavity_canonical_mass_tendsto {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) :
    Tendsto (fun N a => ((cavitySpectralGroup (cavityResidueLabel hm s hsum N) a).card : ℝ)/N)
      atTop (𝓝 (fun a => (s a : ℝ)/n)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply cavity_residue_tendsto hn 1
  intro t
  have hh := cavityAffineCount_ratio s (cavityResidueOffset hm t) hn (q := 1) zero_lt_one a
  apply hh.congr
  intro r
  rw [← cavityResidueSize hm n 1 (t : ℕ) r]
  rw [cavityResidueLabel_progression hm s hsum 1 (t : ℕ) r t.isLt,
    cavityAffineLabel_progression hm s (cavityResidueOffset hm t) hsum hn,
    cavityOrderedGroup_card]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCountAlignment
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Align two finite spectral labelings so each common eigenspace retains
as many axes as possible. A maximizing permutation has no unmatched pair
that can be improved by a transposition. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma exists_spectral_label_alignment {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) :
    ∃ p : Equiv.Perm ι, ∀ v : A,
      (∀ i, a i = v → b (p i) = v) ∨ (∀ i, b (p i) = v → a i = v) := by
  classical
  let matchSet := fun p : Equiv.Perm ι => Finset.univ.filter fun i => a i = b (p i)
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : Equiv.Perm ι => (matchSet p).card) Finset.univ_nonempty
  refine ⟨p, fun v => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨⟨i, hi, hbi⟩, j, hj, haj⟩ := h
  have hij : i ≠ j := by
    intro he
    subst j
    exact hbi hj
  let q : Equiv.Perm ι := (Equiv.swap i j).trans p
  have hqi : q i = p j := by simp [q]
  have hqk k (hki : k ≠ i) (hkj : k ≠ j) : q k = p k := by
    simp only [q, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hsub : matchSet p ⊆ matchSet q := by
    intro k hk
    have hk' : a k = b (p k) := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro he
      subst k
      exact hbi (hk'.symm.trans hi)
    have hkj : k ≠ j := by
      intro he
      subst k
      exact haj (hk'.trans hj)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ k, by rw [hqk k hki hkj]; exact hk'⟩
  have hin : i ∈ matchSet q := Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, by rw [hqi]; exact hi.trans hj.symm⟩
  have hout : i ∉ matchSet p := by
    intro hi'
    exact hbi ((Finset.mem_filter.mp hi').2.symm.trans hi)
  have hstrict : (matchSet p).card < (matchSet q).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, by intro he; rw [← he] at hin; exact hout hin⟩)
  exact (not_lt_of_ge (hp q (Finset.mem_univ q))) hstrict

lemma spectral_alignment_common_count {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) (p : Equiv.Perm ι) (v : A)
    (hp : (∀ i, a i = v → b (p i) = v) ∨ (∀ i, b (p i) = v → a i = v)) :
    ((Finset.univ.filter fun i => a i = v ∧ b (p i) = v).card) =
      min ((Finset.univ.filter fun i => a i = v).card)
        ((Finset.univ.filter fun i => b (p i) = v).card) := by
  let left := Finset.univ.filter fun i => a i = v
  let right := Finset.univ.filter fun i => b (p i) = v
  let both := Finset.univ.filter fun i => a i = v ∧ b (p i) = v
  change both.card = min left.card right.card
  rcases hp with hp | hp
  · have hsub : left ⊆ right := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp i (Finset.mem_filter.mp hi).2⟩
    have he : both = left := by
      ext i
      simp only [both, left, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => hi.1, fun hi => ⟨hi, hp i hi⟩⟩
    rw [he, min_eq_left (Finset.card_le_card hsub)]
  · have hsub : right ⊆ left := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp i (Finset.mem_filter.mp hi).2⟩
    have he : both = right := by
      ext i
      simp only [both, right, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => hi.2, fun hi => ⟨hp i hi, hi⟩⟩
    rw [he, min_eq_right (Finset.card_le_card hsub)]

lemma spectral_label_count_comp {ι A : Type*} [Fintype ι]
    [DecidableEq A] (b : ι → A) (p : Equiv.Perm ι) (v : A) :
    (Finset.univ.filter fun i => b (p i) = v).card =
      (Finset.univ.filter fun i => b i = v).card := by
  classical
  have h := Equiv.sum_comp p (fun i => if b i = v then (1 : ℕ) else 0)
  simpa using h

lemma aligned_changed_count_le {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) (v : A)
    (hp : (∀ i, a i = v → b i = v) ∨ (∀ i, b i = v → a i = v)) :
    ((Finset.univ.filter fun i => a i = v ∧ a i ≠ b i).card : ℝ) ≤
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b i = v).card : ℝ)| := by
  let left := Finset.univ.filter fun i => a i = v
  let both := Finset.univ.filter fun i => a i = v ∧ b i = v
  let diff := Finset.univ.filter fun i => a i = v ∧ a i ≠ b i
  have heq : both.card + diff.card = left.card := by
    have h := Finset.card_filter_add_card_filter_not (s := left) (fun i => b i = v)
    have hpos : left.filter (fun i => b i = v) = both := by
      ext i
      simp only [left, both, Finset.mem_filter, Finset.mem_univ, true_and]
    have hneg : left.filter (fun i => ¬ b i = v) = diff := by
      ext i
      simp only [left, diff, Finset.mem_filter, Finset.mem_univ, true_and]
      aesop
    rw [hpos, hneg] at h
    exact h
  have hboth := spectral_alignment_common_count a b (Equiv.refl ι) v hp
  change both.card = min left.card (Finset.univ.filter fun i => b i = v).card at hboth
  rw [hboth] at heq
  rcases le_total left.card (Finset.univ.filter fun i => b i = v).card with hl | hr
  · rw [min_eq_left hl] at heq
    have hd : diff.card = 0 := by omega
    change (diff.card : ℝ) ≤ _
    rw [hd, Nat.cast_zero]
    exact abs_nonneg _
  · rw [min_eq_right hr] at heq
    have hc : ((Finset.univ.filter fun i => b i = v).card : ℝ) + diff.card = left.card := by
      exact_mod_cast heq
    change (diff.card : ℝ) ≤ |(left.card : ℝ) - _|
    exact (le_abs_self _).trans' (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralMultiplicity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral multiplicity comparison, with an arbitrary deterministic
magnetic field. The relative count error is supplied as a scalar bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

/-- Manuscript Lemma gen:counts. Taking `r` to be the maximum relative
multiplicity error gives its displayed bound. -/
theorem meanPressure_multiplicity_comparison {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a b : Fin N → Fin m) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (lam : Fin m → ℝ) (c : Fin N → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdiam : ∀ v w, |lam v - lam w| ≤ L)
    (herr : ∀ v,
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b i = v).card : ℝ)| ≤
      r * min ((Finset.univ.filter fun i => a i = v).card : ℝ)
        ((Finset.univ.filter fun i => b i = v).card : ℝ)) :
    |(∫ U, rotatedPressure (fun i => lam (b i)) (specialRotation U) c ∂μ) -
      ∫ U, rotatedPressure (fun i => lam (a i)) (specialRotation U) c ∂μ| ≤ L * r / 2 := by
  classical
  obtain ⟨p, hp⟩ := exists_spectral_label_alignment a b
  let b' := fun i => b (p i)
  let changed := Finset.univ.filter fun i => a i ≠ b' i
  have herr' v :
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b' i = v).card : ℝ)| ≤
      r * min ((Finset.univ.filter fun i => a i = v).card : ℝ)
        ((Finset.univ.filter fun i => b' i = v).card : ℝ) := by
    simpa only [b', spectral_label_count_comp] using herr v
  have hc v : ((changed.filter fun i => a i = v).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => a i = v).card : ℝ) := by
    have hd := aligned_changed_count_le a b' v (hp v)
    have he : changed.filter (fun i => a i = v) =
        Finset.univ.filter (fun i => a i = v ∧ a i ≠ b' i) := by
      ext i
      simp only [changed, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    rw [he]
    exact hd.trans ((herr' v).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hr))
  have hc' v : ((changed.filter fun i => b' i = v).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => b' i = v).card : ℝ) := by
    have hp' : (∀ i, b' i = v → a i = v) ∨ (∀ i, a i = v → b' i = v) := (hp v).symm
    have hd := aligned_changed_count_le b' a v hp'
    have he : changed.filter (fun i => b' i = v) =
        Finset.univ.filter (fun i => b' i = v ∧ b' i ≠ a i) := by
      ext i
      simp only [changed, Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
      exact and_comm
    rw [he]
    rw [abs_sub_comm] at hd
    exact hd.trans ((herr' v).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hr))
  have hcomp := meanPressure_change_counts_le hN μ
    (fun i => lam (a i)) (fun i => lam (b' i)) c K
    (fun i => hK (a i)) (fun i => hK (b' i)) a b' ha (hb.comp p.surjective)
    lam (fun _ => rfl) (fun _ => rfl) changed
    (fun i hi => by
      have hlabel : a i = b' i := by simpa only [changed, Finset.mem_filter,
        Finset.mem_univ, true_and, not_not] using hi
      rw [hlabel])
    L r hL (fun i => hdiam (b' i) (a i)) hc hc'
  have he := meanPressure_spectralPermutation hN μ p (fun i => lam (b i)) c
  simpa only [b', he] using hcomp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_MultiplicityContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic removal of finite-alphabet multiplicity restrictions. The
comparison only uses the limiting positive group proportions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma eventually_relative_count_bound {A : Type*} [Fintype A]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (a b : ℕ → A → ℕ)
    (rho tau : A → ℝ) (hrho : ∀ v, 0 < rho v) (htau : ∀ v, 0 < tau v)
    (ha : Tendsto (fun k v => (a k v : ℝ) / N k) atTop (𝓝 rho))
    (hb : Tendsto (fun k v => (b k v : ℝ) / N k) atTop (𝓝 tau))
    (R : ℝ) (hR : ∀ v, |rho v - tau v| / min (rho v) (tau v) < R) :
    ∀ᶠ k in atTop, ∀ v,
      |(a k v : ℝ) - b k v| ≤ R * min (a k v : ℝ) (b k v : ℝ) := by
  apply Filter.eventually_all.mpr
  intro v
  have hα := (tendsto_pi_nhds.mp ha) v
  have hβ := (tendsto_pi_nhds.mp hb) v
  have hden := hα.min hβ
  have hpos : 0 < min (rho v) (tau v) := lt_min (hrho v) (htau v)
  have hratio := (hα.sub hβ).abs.div hden (ne_of_gt hpos)
  filter_upwards [hratio.eventually (Iio_mem_nhds (hR v)),
    hden.eventually (Ioi_mem_nhds hpos)] with k hk hdk
  have hfrac : |(a k v : ℝ) / N k - (b k v : ℝ) / N k| ≤
      R * min ((a k v : ℝ) / N k) ((b k v : ℝ) / N k) :=
    ((div_lt_iff₀ (show 0 < min ((a k v : ℝ) / N k) ((b k v : ℝ) / N k) from hdk)).mp hk).le
  have hn : 0 < (N k : ℝ) := by exact_mod_cast hN k
  rw [← sub_div, abs_div, abs_of_pos hn, min_div_div_right hn.le,
    ← mul_div_assoc] at hfrac
  exact (div_le_div_iff_of_pos_right hn).mp hfrac

lemma eventually_surjective_label {N : ℕ → ℕ} {m : ℕ}
    (hN : ∀ k, 0 < N k) (a : (k : ℕ) → Fin (N k) → Fin m)
    (rho : Fin m → ℝ) (hrho : ∀ v, 0 < rho v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k)
      atTop (𝓝 rho)) :
    ∀ᶠ k in atTop, Function.Surjective (a k) := by
  have hall : ∀ v, ∀ᶠ k in atTop,
      0 < ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k :=
    fun v => ((tendsto_pi_nhds.mp ha) v).eventually (Ioi_mem_nhds (hrho v))
  filter_upwards [Filter.eventually_all.mpr hall] with k hk
  intro v
  have hn : 0 < (N k : ℝ) := by exact_mod_cast hN k
  have hp : (0 : ℝ) < (Finset.univ.filter fun i => a k i = v).card :=
    (div_pos_iff_of_pos_right hn).mp (hk v)
  have hcard : 0 < (Finset.univ.filter fun i => a k i = v).card := by exact_mod_cast hp
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- Two spectra with the same finite alphabet and the same positive limiting
proportions have asymptotically equal Haar mean pressures. -/
theorem meanPressure_same_proportions_tendsto {m : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] (hμ : ∀ k, (μ k).IsMulLeftInvariant)
    (a b : (k : ℕ) → Fin (N k) → Fin m)
    (rho : Fin m → ℝ) (hrho : ∀ v, 0 < rho v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k)
      atTop (𝓝 rho))
    (hb : Tendsto (fun k v => ((Finset.univ.filter fun i => b k i = v).card : ℝ) / N k)
      atTop (𝓝 rho))
    (lam : Fin m → ℝ) (c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L : ℝ) (hL : 0 ≤ L) (hdiam : ∀ v w, |lam v - lam w| ≤ L) :
    Tendsto (fun k =>
      (∫ U, rotatedPressure (fun i => lam (b k i)) (specialRotation U) (c k) ∂μ k) -
        ∫ U, rotatedPressure (fun i => lam (a k i)) (specialRotation U) (c k) ∂μ k)
      atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := ε / (L + 1)
  have hR : 0 < R := div_pos hε (by linarith)
  have hc := eventually_relative_count_bound N hN
    (fun k v => (Finset.univ.filter fun i => a k i = v).card)
    (fun k v => (Finset.univ.filter fun i => b k i = v).card)
    rho rho hrho hrho ha hb R (fun v => by simpa only [sub_self, abs_zero, zero_div] using hR)
  filter_upwards [hc, eventually_surjective_label hN a rho hrho ha,
    eventually_surjective_label hN b rho hrho hb] with k hk hka hkb
  let := hμ k
  have hp := meanPressure_multiplicity_comparison (hN k) (μ k)
    (a k) (b k) hka hkb lam (c k) K hK L R hL hR.le hdiam hk
  have he : R * (L + 1) = ε := div_mul_cancel₀ ε (by linarith : L + 1 ≠ 0)
  have hsmall : L * R / 2 < ε := by nlinarith
  simpa only [Real.dist_eq, sub_zero] using hp.trans_lt hsmall

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultiplicityTransport
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity comparison for the physical orthogonal Haar law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_meanPressure_multiplicity_comparison {N m : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (a b : Fin N → Fin m) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (lam : Fin m → ℝ) (c : Fin N → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdiam : ∀ v w, |lam v-lam w| ≤ L)
    (herr : ∀ v, |((Finset.univ.filter fun i => a i=v).card : ℝ)-
      ((Finset.univ.filter fun i => b i=v).card : ℝ)| ≤
      r*min ((Finset.univ.filter fun i => a i=v).card : ℝ)
        ((Finset.univ.filter fun i => b i=v).card : ℝ)) :
    |(∫ V, rotatedPressure (fun i => lam (b i)) (matrixRotation V⁻¹) c ∂μ)-
      ∫ V, rotatedPressure (fun i => lam (a i)) (matrixRotation V⁻¹) c ∂μ| ≤ L*r/2 := by
  let ν := cavityOrientedBaseLaw hN μ
  let : ν.IsMulLeftInvariant := cavityOrientedBaseLaw_leftInvariant hN μ
  have hh := meanPressure_multiplicity_comparison hN ν a b ha hb lam c K hK L r hL hr hdiam herr
  rw [cavity_oriented_pressure, cavity_oriented_pressure] at hh
  exact hh

lemma cavity_meanPressure_same_proportions_tendsto {m : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (a b : (k : ℕ) → Fin (N k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ v, 0 < ρ v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i=v).card : ℝ)/N k)
      atTop (𝓝 ρ))
    (hb : Tendsto (fun k v => ((Finset.univ.filter fun i => b k i=v).card : ℝ)/N k)
      atTop (𝓝 ρ))
    (lam : Fin m → ℝ) (c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L : ℝ) (hL : 0 ≤ L) (hdiam : ∀ v w, |lam v-lam w| ≤ L) :
    Tendsto (fun k => (∫ V, rotatedPressure (fun i => lam (b k i))
      (matrixRotation V⁻¹) (c k) ∂μ k)-
      ∫ V, rotatedPressure (fun i => lam (a k i)) (matrixRotation V⁻¹) (c k) ∂μ k)
      atTop (𝓝 0) := by
  have hh := meanPressure_same_proportions_tendsto N hN
    (fun k => cavityOrientedBaseLaw (hN k) (μ k))
    (fun k => cavityOrientedBaseLaw_leftInvariant (hN k) (μ k))
    a b ρ hρ ha hb lam c K hK L hL hdiam
  simpa only [cavity_oriented_pressure] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrefixAffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityPrefixAffineLabel_progression {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (q r : ℕ) :
    cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n q c r)=
      cavityOrderedGroup (cavityAffineCount s c q r) (cavityPrefixAffineCount_sum s c hsum q r) :=
  cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+q) (Nat.add_comm _ _) _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveGroupProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeating a finite field block multiplies each group size by the
number of repetitions and preserves its attainable magnetizations. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma consecutiveSiteGroup_size {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (a : A) :
    spinGroupSize (consecutiveSiteGroup K group) a=K*spinGroupSize group a := by
  simp only [spinGroupSize, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin K × Fin n ≃ Fin (K*n))]
  simp only [consecutiveSiteGroup, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  change (∑ _ : Fin K, (∑ i : Fin n, if group i=a then 1 else 0)) = _
  simp

lemma consecutiveSiteGroup_attainable {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) :
    ∀ a, K*k a ≤ spinGroupSize (consecutiveSiteGroup K group) a := by
  intro a
  rw [consecutiveSiteGroup_size]
  exact Nat.mul_le_mul_left K (hk a)

lemma consecutiveSiteGroup_proportion {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a) :
    ∀ a, (spinGroupSize (consecutiveSiteGroup K group) a : ℝ)=(K*n : ℕ)*γ a := by
  intro a
  rw [consecutiveSiteGroup_size, Nat.cast_mul, hcount, Nat.cast_mul]
  ring

lemma consecutiveSiteGroup_magnetization {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (mag : A → ℝ)
    (hk : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2)) :
    ∀ a, (K*k a : ℕ)= (spinGroupSize (consecutiveSiteGroup K group) a : ℝ)*((1+mag a)/2) := by
  intro a
  rw [consecutiveSiteGroup_size, Nat.cast_mul, hk, Nat.cast_mul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_FiniteSpectralContinuity
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity under changes of the positive masses of a fixed finite spectral
alphabet. The inverse is compared using its defining resolvent equation. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteResolvent_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) (b : ℝ) :
    Tendsto (fun k => finiteResolvent (ρs k) eig b) atTop (𝓝 (finiteResolvent ρ eig b)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ =>
    ((tendsto_pi_nhds.mp hρs) a).div_const (b - eig a))

theorem finiteInverse_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteInverse ρ eig hpos hsum x)) := by
  have hs := finiteInverse_spec ρ eig hpos hsum hx
  have hxp : ∀ᶠ k in atTop, 0 < xs k := hxs.eventually (Ioi_mem_nhds hx)
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases he : ∀ a, eig a < l
    · have hR : x < finiteResolvent ρ eig l := by
        rw [← hs.2]
        exact finiteResolvent_strictAnti (fun a => (hpos a).le) hsum he hl
      have ht := hxs.eventually_lt (finiteResolvent_tendsto_weights ρs ρ eig hρs l) hR
      filter_upwards [hxp, ht] with k hk hlt
      have hsk := finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with h | h
      · rw [← h, hsk.2] at hlt
        exact (lt_irrefl _ hlt)
      · have hc := finiteResolvent_strictAnti (fun a => (hspos k a).le)
          (hssum k) hsk.1 h
        rw [hsk.2] at hc
        exact (not_lt_of_ge hc.le hlt)
    · push Not at he
      obtain ⟨a, ha⟩ := he
      filter_upwards [hxp] with k hk
      exact ha.trans_lt ((finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk).1 a)
  · intro u hu
    have he : ∀ a, eig a < u := fun a => (hs.1 a).trans hu
    have hR : finiteResolvent ρ eig u < x := by
      rw [← hs.2]
      exact finiteResolvent_strictAnti (fun a => (hpos a).le) hsum hs.1 hu
    have ht := (finiteResolvent_tendsto_weights ρs ρ eig hρs u).eventually_lt hxs hR
    filter_upwards [hxp, ht] with k hk hlt
    have hsk := finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk
    by_contra hnot
    rcases (le_of_not_gt hnot).eq_or_lt with h | h
    · rw [h, hsk.2] at hlt
      exact (lt_irrefl _ hlt)
    · have hc := finiteResolvent_strictAnti (fun a => (hspos k a).le) (hssum k) he h
      rw [hsk.2] at hc
      exact (not_lt_of_ge hc.le hlt)

theorem finiteR_tendsto_weights_pos (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
  have hb := finiteInverse_tendsto_weights ρs ρ eig hspos hssum hpos hsum hρs xs hxs hx
  have hi : Tendsto (fun k => 1 / xs k) atTop (𝓝 (1 / x)) :=
    tendsto_const_nhds.div hxs hx.ne'
  have he : (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k)) =ᶠ[atTop]
      (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k) - 1 / xs k) := by
    filter_upwards [hxs.eventually (Ioi_mem_nhds hx)] with k hk
    simp only [finiteR, ite_eq_left hk]
  have hl : Tendsto
      (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k) - 1 / xs k)
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
    simpa only [finiteR, ite_eq_left hx] using hb.sub hi
  exact hl.congr' he.symm

theorem finiteR_tendsto_weights_zero (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) (hxs : Tendsto xs atTop (𝓝 0)) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum 0)) := by
  let K := 1 + ∑ a, |eig a|
  have hK : 0 < K := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun a _ => abs_nonneg (eig a))
    dsimp only [K]
    linarith
  have heig a : |eig a| ≤ K := by
    have := Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
    dsimp only [K]
    linarith
  have hsmall : ∀ᶠ k in atTop, xs k < 1 / (4 * K) :=
    hxs.eventually (Iio_mem_nhds (by positivity))
  have herr : ∀ᶠ k in atTop,
      ‖finiteR (ρs k) eig (hspos k) (hssum k) (xs k) - ∑ a, ρs k a * eig a‖ ≤
        8 * K ^ 2 * |xs k| := by
    filter_upwards [hsmall] with k hk
    rw [Real.norm_eq_abs]
    by_cases hxk : 0 < xs k
    · rw [abs_of_nonneg (sub_nonneg.mpr (mean_le_finiteR (ρs k) eig
        (hspos k) (hssum k) hxk)), abs_of_pos hxk]
      apply finiteR_sub_mean_le (ρs k) eig (hspos k) (hssum k) hK.le heig hxk
      have := (lt_div_iff₀ (show 0 < 4 * K by positivity)).mp hk
      nlinarith
    · simp only [finiteR, ite_eq_right hxk, sub_self, abs_zero]
      positivity
  have hb : Tendsto (fun k => 8 * K ^ 2 * |xs k|) atTop (𝓝 0) := by
    simpa using hxs.abs.const_mul (8 * K ^ 2)
  have hz := squeeze_zero_norm' herr hb
  have hm : Tendsto (fun k => ∑ a, ρs k a * eig a) atTop (𝓝 (∑ a, ρ a * eig a)) :=
    tendsto_finsetSum Finset.univ (fun a _ => ((tendsto_pi_nhds.mp hρs) a).mul_const _)
  simpa only [sub_add_cancel, zero_add, finiteR, lt_self_iff_false, ite_false, if_false] using hz.add hm

theorem finiteR_tendsto_weights_nonneg (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 ≤ x) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    exact finiteR_tendsto_weights_zero ρs ρ eig hspos hssum hpos hsum hρs xs hxs
  · exact finiteR_tendsto_weights_pos ρs ρ eig hspos hssum hpos hsum hρs xs hxs hx

/-- Uniformity on the whole interval includes the transform's value at zero. -/
theorem finiteR_uniform_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) 1,
      |finiteR (ρs k) eig (hspos k) (hssum k) x - finiteR ρ eig hpos hsum x| < ε := by
  classical
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ x ∈ Icc (0 : ℝ) 1,
      ε ≤ |finiteR (ρs k) eig (hspos k) (hssum k) x - finiteR ρ eig hpos hsum x| := by
    simpa only [Filter.not_eventually, not_forall, _root_.not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose xs hxs herror using hφbad
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxs
  have hweights := hρs.comp (hφ.comp hψ).tendsto_atTop
  have hR := finiteR_tendsto_weights_nonneg
    (fun k => ρs (φ (ψ k))) ρ eig (fun k => hspos (φ (ψ k)))
    (fun k => hssum (φ (ψ k))) hpos hsum hweights (fun k => xs (ψ k)) hlim hx.1
  have hfixed := (continuous_finiteR ρ eig hpos hsum).continuousAt.tendsto.comp hlim
  have hdiff := (hR.sub hfixed).abs
  have hzero : Tendsto (fun k =>
      |finiteR (ρs (φ (ψ k))) eig (hspos (φ (ψ k))) (hssum (φ (ψ k))) (xs (ψ k)) -
        finiteR ρ eig hpos hsum (xs (ψ k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using hdiff
  have hsmall : ∀ᶠ k in atTop,
      |finiteR (ρs (φ (ψ k))) eig (hspos (φ (ψ k))) (hssum (φ (ψ k))) (xs (ψ k)) -
        finiteR ρ eig hpos hsum (xs (ψ k))| < ε := by
    exact hzero.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (herror (ψ k))

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

theorem measureResolvent_finiteSpectralMeasure (ρ eig : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (b : ℝ) : measureResolvent (finiteSpectralMeasure ρ eig) b = finiteResolvent ρ eig b := by
  rw [measureResolvent, integral_finiteSpectralMeasure ρ eig hρ]
  simp only [finiteResolvent, mul_one_div]

theorem measureR_finiteSpectralMeasure (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (aMax : ι) (hMax : ∀ a, eig a ≤ eig aMax) (x : ℝ) :
    measureR (finiteSpectralMeasure ρ eig) (eig aMax) x = finiteR ρ eig hρ hsum x := by
  let := finiteSpectralMeasure_probability ρ eig (fun a => (hρ a).le) hsum
  by_cases hx : 0 < x
  · have hs := finiteInverse_spec ρ eig hρ hsum hx
    have hsol : measureResolvent (finiteSpectralMeasure ρ eig) (finiteInverse ρ eig hρ hsum x) = x := by
      rw [measureResolvent_finiteSpectralMeasure ρ eig (fun a => (hρ a).le)]
      exact hs.2
    have hi := measureInverse_eq_of_solution (finiteSpectralMeasure ρ eig)
      (ae_finiteSpectralMeasure ρ eig hMax) (hs.1 aMax) hsol
    simp only [measureR, finiteR, ite_eq_left hx, hi]
  · simp only [measureR, finiteR, ite_eq_right hx,
      integral_finiteSpectralMeasure ρ eig (fun a => (hρ a).le)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_PositiveRationalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rational approximations to a finite probability vector,
with explicit integer multiplicities. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma positiveApproxCount_pos (x : ℝ) (k : ℕ) : 0 < positiveApproxCount x k := by
  unfold positiveApproxCount
  omega

lemma positiveApproxCount_ratio (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => (positiveApproxCount x k : ℝ)/(k+1)) atTop (𝓝 x) := by
  have herror k : 0 ≤ (positiveApproxCount x k : ℝ)/(k+1)-x ∧
      (positiveApproxCount x k : ℝ)/(k+1)-x ≤ 1/(k+1) := by
    have hk : 0 < (k+1 : ℝ) := by positivity
    have hlow := Nat.lt_floor_add_one ((k+1 : ℝ)*x)
    have hupp := Nat.floor_le (mul_nonneg hk.le hx)
    have heq : (positiveApproxCount x k : ℝ)/(k+1)-x=
        (((⌊(k+1 : ℝ)*x⌋₊ : ℕ) : ℝ)+1-x*(k+1))/(k+1) := by
      simp only [positiveApproxCount,Nat.cast_add,Nat.cast_one]
      field_simp
    rw [heq]
    constructor
    · apply div_nonneg _ hk.le
      nlinarith
    · apply div_le_div_of_nonneg_right _ hk.le
      nlinarith
  have he := squeeze_zero (fun k => (herror k).1) (fun k => (herror k).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_add_cancel,zero_add] using he.add_const x

lemma positiveApproxDenominator_pos {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) :
    0 < positiveApproxDenominator ρ k := by
  have hle := Finset.single_le_sum (f := fun a => positiveApproxCount (ρ a) k)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0,hm⟩ : Fin m))
  exact (positiveApproxCount_pos (ρ ⟨0,hm⟩) k).trans_le hle

lemma positiveApproxWeights_tendsto {m : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a=1) :
    Tendsto (fun k a => (positiveApproxCount (ρ a) k : ℝ)/positiveApproxDenominator ρ k)
      atTop (𝓝 ρ) := by
  have hden : Tendsto (fun k => (positiveApproxDenominator ρ k : ℝ)/(k+1)) atTop (𝓝 (1:ℝ)) := by
    have hh := tendsto_finsetSum Finset.univ (fun a _ => positiveApproxCount_ratio (ρ a) (hρ a))
    simpa only [positiveApproxDenominator,Nat.cast_sum,Finset.sum_div,hsum] using hh
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := (positiveApproxCount_ratio (ρ a) (hρ a)).div hden one_ne_zero
  simp only [div_one] at hh
  apply hh.congr
  intro k
  exact div_div_div_cancel_right₀ (by positivity : (k+1 : ℝ)≠0) _ _

lemma positiveApproxWeights_pos {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) (a : Fin m) :
    0 < positiveApproxWeights ρ k a :=
  div_pos (by exact_mod_cast positiveApproxCount_pos (ρ a) k)
    (by exact_mod_cast positiveApproxDenominator_pos hm ρ k)

lemma positiveApproxWeights_sum {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) :
    ∑ a, positiveApproxWeights ρ k a=1 := by
  simp only [positiveApproxWeights,← Finset.sum_div,← Nat.cast_sum]
  exact div_self (Nat.cast_ne_zero.mpr (positiveApproxDenominator_pos hm ρ k).ne')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteTypePressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-alphabet pressure theorem for a finite type of spectral cells. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators

namespace InvariantIsing

lemma finiteSpectralMeasure_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (w lam : ι → ℝ) :
    finiteSpectralMeasure (w ∘ e) (lam ∘ e)=finiteSpectralMeasure w lam := by
  unfold finiteSpectralMeasure
  exact Measure.sum_comp_equiv e (fun i => ENNReal.ofReal (w i) • Measure.dirac (lam i))

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetFieldPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact field contributions in repeated blocks following a zero-field prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma offset_field_fraction_tendsto {n : ℕ} (hn : 0 < n) (r q : ℕ) (hq : 0 < q) (F : ℝ) :
    Tendsto (fun j : ℕ => ((q+j : ℕ) : ℝ)*(n : ℝ)*F/(r+(q+j)*n)) atTop (𝓝 F) := by
  have hh := (cavity_affine_ratio_tendsto n 0 n r q hn hq).mul_const F
  have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Nat.add_zero, Nat.cast_mul, Nat.cast_add, div_self hnz, one_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  simp only [Nat.cast_add]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetFieldPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-field prefix has vanishing population; repeated field blocks
retain the original label proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma offsetSiteGroup_none {n K r : ℕ} {A : Type*} [DecidableEq A] (g : Fin n → A) :
    spinGroupSize (offsetSiteGroup r K g) none=r := by
  simp only [spinGroupSize, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp [offsetSiteGroup]

lemma offsetSiteGroup_some {n K r : ℕ} {A : Type*} [DecidableEq A] (g : Fin n → A) (a : A) :
    spinGroupSize (offsetSiteGroup r K g) (some a)=K*spinGroupSize g a := by
  rw [← consecutiveSiteGroup_size (K := K) g a]
  simp only [spinGroupSize, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp [offsetSiteGroup]

lemma offsetSiteGroup_field {n r K : ℕ} {A : Type*} (g : Fin n → A) (b : A → ℝ) :
    (fun i => Option.elim (offsetSiteGroup r K g i) 0 b)=
      offsetBlockField r K (fun i => b (g i)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [offsetSiteGroup,offsetBlockField,consecutiveSiteGroup,consecutiveBlockField]

lemma offsetSiteGroup_population_tendsto {n : ℕ} (hn : 0<n) (r q : ℕ) (hq : 0<q)
    {A : Type*} [Fintype A] [DecidableEq A] (g : Fin n → A) (γ : A → ℝ)
    (hg : ∀ a, (spinGroupSize g a : ℝ)=n*γ a) :
    Tendsto (fun j a => (spinGroupSize (offsetSiteGroup r (q+j) g) a : ℝ)/(r+(q+j)*n))
      atTop (𝓝 (fun a => Option.elim a 0 γ)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  cases a with
  | none =>
      have hh := cavity_affine_ratio_tendsto 0 r n r q hn hq
      simpa only [offsetSiteGroup_none,Nat.mul_zero,Nat.zero_add,Nat.cast_zero,zero_div,
        Nat.cast_add,Nat.cast_mul,Nat.add_comm,add_comm,add_zero,Option.elim_none] using hh
  | some a =>
      have hh := offset_field_fraction_tendsto hn r q hq (γ a)
      simpa only [offsetSiteGroup_some,Nat.cast_mul,hg,mul_assoc,Option.elim_some] using hh

lemma someSiteGroup_population_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (g : (j : ℕ) → Fin (N j) → A) (γ : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ)) :
    Tendsto (fun j a => (spinGroupSize (fun i => some (g j i)) a : ℝ)/N j)
      atTop (𝓝 (fun a => Option.elim a 0 γ)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  cases a with
  | none =>
      simpa only [spinGroupSize,Option.some_ne_none,Finset.filter_false,Finset.card_empty,
        Nat.cast_zero,zero_div,Option.elim_none] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | some a =>
      simpa only [spinGroupSize,Option.some.injEq,Option.elim_some] using (tendsto_pi_nhds.mp hg) a

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PhysicalFieldPopulationLimit
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of physical mean pressure under matching limiting finite
spectral and field populations. Zero limiting field weights are allowed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem physical_mean_field_populations_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0<N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant] (eig : (j : ℕ) → Fin (N j) → ℝ)
    (g h : (j : ℕ) → Fin (N j) → A) (γ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 γ))
    {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    Tendsto (fun j => (∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (g j i)) ∂μ j)-
      ∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (h j i)) ∂μ j)
      atTop (𝓝 0) := by
  have he a : Tendsto (fun j => |(spinGroupSize (g j) a : ℝ)/N j-
      (spinGroupSize (h j) a : ℝ)/N j|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using
      (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs
  have hs := (tendsto_finsetSum Finset.univ (fun a _ => he a)).const_mul (2*B)
  simp only [Finset.sum_const_zero,mul_zero] at hs
  apply squeeze_zero_norm (fun j => ?_) hs
  simpa only [Real.norm_eq_abs] using physical_mean_field_counts_le (hN j) (μ j)
    (eig j) (g j) (h j) b hB hb

theorem physical_mean_joint_populations_tendsto {m : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0<N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant]
    (e f : (j : ℕ) → Fin (N j) → Fin m) (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a)
    (he : Tendsto (fun j a => (spinGroupSize (e j) a : ℝ)/N j) atTop (𝓝 ρ))
    (hf : Tendsto (fun j a => (spinGroupSize (f j) a : ℝ)/N j) atTop (𝓝 ρ))
    (lam : Fin m → ℝ) {K : ℝ} (hK : 0≤K) (hlam : ∀ a, |lam a|≤K)
    (g h : (j : ℕ) → Fin (N j) → A) (γ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 γ))
    {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    Tendsto (fun j => (∫ U, rotatedPressure (fun i => lam (f j i)) (matrixRotation U⁻¹)
      (fun i => b (h j i)) ∂μ j)-
      ∫ U, rotatedPressure (fun i => lam (e j i)) (matrixRotation U⁻¹)
      (fun i => b (g j i)) ∂μ j) atTop (𝓝 0) := by
  have hs := cavity_meanPressure_same_proportions_tendsto N hN μ e f ρ hρ he hf lam
    (fun j i => b (h j i)) K hlam (2*K) (by positivity)
    (fun a b => (abs_sub _ _).trans (by linarith [hlam a,hlam b]))
  have ht := physical_mean_field_populations_tendsto N hN μ (fun j i => lam (e j i))
    h g γ b hh hg hB hb
  have hz := hs.add ht
  simp only [add_zero] at hz
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_AffineTemplateComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An affine block template and any physical model with the same limiting
finite populations have asymptotically identical mean pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem affine_template_pressure_comparison {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (q : ℕ) (hq : 0<q) (spec c : Fin m → ℕ) (hspec : ∑ a, spec a=n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hcount : ∀ a, (spec a : ℝ)=n*ρ a)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    (group : Fin n → A) (hgroup : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {K B : ℝ} (hK : 0≤K) (hlam : ∀ a, |lam a|≤K) (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    let N := fun j => (∑ a, c a)+(q+j)*n
    Tendsto (fun j => (∫ U, rotatedPressure (fun i => lam (e (N j) i)) (matrixRotation U⁻¹)
      (fun i => b (g (N j) i)) ∂μ (N j))-
      ∫ U, rotatedPressure (fun i => lam (cavityAffineLabel hm spec c hspec (N j) i))
        (matrixRotation U⁻¹) (offsetBlockField (∑ a, c a) (q+j) (fun i => b (group i))) ∂μ (N j))
      atTop (𝓝 0) := by
  intro N
  have hN j : 0<N j := Nat.add_pos_right _ (Nat.mul_pos (by omega) hn)
  have hNl : Tendsto N atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_add_left _ _)
    (by simpa only [Nat.add_comm] using cavityRationalDimension_tendsto n q hn)
  let f := fun j => cavityAffineLabel hm spec c hspec (N j)
  have hfcard j a : spinGroupSize (f j) a=cavityAffineCount spec c q j a := by
    dsimp only [f,N]
    rw [show (∑ a, c a)+(q+j)*n=cavityPrefixAffineSize n q c j by
      simp only [cavityPrefixAffineSize,Nat.add_comm]]
    rw [cavityPrefixAffineLabel_progression hm spec c hspec hn]
    exact cavityOrderedGroup_card _ _ a
  have hf : Tendsto (fun j a => (spinGroupSize (f j) a : ℝ)/N j) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro a
    have hratio : (spec a : ℝ)/n=ρ a := by
      rw [hcount, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    simpa only [hfcard,N,cavityAffineSize,Nat.add_comm,hratio] using
      cavityAffineCount_ratio spec c hn hq a
  let gamma : Option A → ℝ := fun a => Option.elim a 0 γ
  let field : Option A → ℝ := fun a => Option.elim a 0 b
  have hfield a : |field a|≤B := by
    cases a with
    | none => simpa only [field,Option.elim_none,abs_zero] using hB
    | some a => exact hb a
  have hpop := offsetSiteGroup_population_tendsto hn (∑ a, c a) q hq group γ hgroup
  have htarget := someSiteGroup_population_tendsto N (fun j => g (N j)) γ (hg.comp hNl)
  have hh := physical_mean_joint_populations_tendsto N hN (fun j => μ (N j))
    f (fun j => e (N j)) ρ hρ hf (he.comp hNl) lam hK hlam
    (fun j => offsetSiteGroup (∑ a, c a) (q+j) group)
    (fun j i => some (g (N j) i)) gamma field
    (by simpa only [N,gamma,Nat.cast_add,Nat.cast_mul] using hpop) htarget hB hfield
  have hfield_eq j : (fun i => field (offsetSiteGroup (∑ a, c a) (q+j) group i))=
      offsetBlockField (∑ a, c a) (q+j) (fun i => b (group i)) :=
    offsetSiteGroup_field group b
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  congr 1
  exact congrArg (fun z => ∫ U, rotatedPressure (fun i => lam (f j i))
    (matrixRotation U⁻¹) z ∂μ (N j)) (hfield_eq j).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite field populations admit exact block templates and canonical
all-dimensional labels with the corresponding limiting proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinGroupSize_equiv {A B : Type*} [DecidableEq A] [DecidableEq B]
    {N : ℕ} (E : A ≃ B) (g : Fin N → B) (a : A) :
    spinGroupSize (fun i => E.symm (g i)) a=spinGroupSize g (E a) := by
  simp only [spinGroupSize,Equiv.symm_apply_eq]

lemma countedFieldGroup_size {A : Type*} [Fintype A] [DecidableEq A]
    {N : ℕ} (s : A → ℕ) (hs : ∑ a, s a=N) (a : A) :
    spinGroupSize (countedFieldGroup s hs) a=s a := by
  rw [countedFieldGroup,spinGroupSize_equiv]
  exact (cavityOrderedGroup_card _ _ _).trans (by simp)

lemma canonicalFieldLabel_population {A : Type*} [Fintype A] [DecidableEq A]
    (a0 : A) (s : A → ℕ) (hs : 0 < ∑ a, s a) :
    Tendsto (fun N a => (spinGroupSize (canonicalFieldLabel a0 s N) a : ℝ)/N)
      atTop (𝓝 (fun a => (s a : ℝ)/(∑ a, s a))) := by
  let E := Fintype.equivFin A
  have hh := cavity_canonical_mass_tendsto (Fintype.card_pos_iff.mpr ⟨a0⟩) hs
    (fun j => s (E.symm j)) (Equiv.sum_comp E.symm s)
  apply tendsto_pi_nhds.mpr
  intro a
  have ha := (tendsto_pi_nhds.mp hh) (E a)
  dsimp only [canonicalFieldLabel]
  simp only [spinGroupSize_equiv]
  simpa only [E,Equiv.symm_apply_apply,spinGroupSize,cavitySpectralGroup] using ha

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interior limit gives a common strict magnetization bound for all
sufficiently large members of a finite family. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma exists_uniform_magnetization_radius {A : Type*} [Fintype A]
    (s : ℕ → A → ℝ) (t : A → ℝ) (hs : Tendsto s atTop (𝓝 t))
    (ht : ∀ a, |t a|<1) :
    ∃ r : ℝ, r<1 ∧ (∀ a, |t a| ≤ r) ∧ ∀ᶠ k in atTop, ∀ a, |s k a| ≤ r := by
  classical
  by_cases hA : Nonempty A
  · have : Nonempty A := hA
    have hne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    let M := Finset.univ.sup' hne (fun a => |t a|)
    have hM : M<1 := (Finset.sup'_lt_iff hne).mpr (fun a _ => ht a)
    obtain ⟨r, hMr, hr⟩ := exists_between hM
    have htr a : |t a| < r := (Finset.le_sup' (fun a => |t a|) (Finset.mem_univ a)).trans_lt hMr
    refine ⟨r, hr, fun a => (htr a).le, ?_⟩
    rw [Filter.eventually_all]
    intro a
    exact ((((tendsto_pi_nhds.mp hs) a).abs).eventually (Iio_mem_nhds (htr a))).mono
      (fun _ h => h.le)
  · have : IsEmpty A := not_nonempty_iff.mp hA
    exact ⟨0, by norm_num, fun a => isEmptyElim a, Filter.Eventually.of_forall (fun _ a => isEmptyElim a)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FinitePopulationCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coupling retains a common fraction of every population and sends
the remaining mass independently to the required residual population. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma retainedPopulationCoupling_nonneg {A : Type*} [DecidableEq A]
    (γ δ : A → ℝ) {ε : ℝ} (hε : ε ≤ 1) (hγ : ∀ a, 0 ≤ γ a)
    (hδ : ∀ a, (1-ε)*γ a ≤ δ a) (a j : A) :
    0 ≤ retainedPopulationCoupling γ δ ε a j := by
  apply add_nonneg
  · split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hε) (hγ a)
    · rfl
  · exact mul_nonneg (hγ a) (sub_nonneg.mpr (hδ j))

lemma retainedPopulationCoupling_row {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ : A → ℝ) (hγ : ∑ a, γ a=1) (hδ : ∑ a, δ a=1) (ε : ℝ) (a : A) :
    ∑ j, retainedPopulationCoupling γ δ ε a j=γ a := by
  simp only [retainedPopulationCoupling,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,hγ,hδ]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  ring

lemma retainedPopulationCoupling_col {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ : A → ℝ) (hγ : ∑ a, γ a=1) (ε : ℝ) (j : A) :
    ∑ a, retainedPopulationCoupling γ δ ε a j=δ j := by
  simp only [retainedPopulationCoupling,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hγ]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  ring

lemma retainedPopulationCoupling_cost {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hδsum : ∑ a, δ a=1) {ε D : ℝ}
    (hδ : ∀ a, (1-ε)*γ a ≤ δ a) (hb : ∀ a, |b a| ≤ D) :
    (∑ a, ∑ j, retainedPopulationCoupling γ δ ε a j* |b a-b j|) ≤ 2*D*ε := by
  have he a j : retainedPopulationCoupling γ δ ε a j* |b a-b j|=
      (γ a*(δ j-(1-ε)*γ j))* |b a-b j| := by
    unfold retainedPopulationCoupling
    split_ifs with h
    · subst j; simp
    · simp
  simp_rw [he]
  calc
    _ ≤ ∑ a, ∑ j, (γ a*(δ j-(1-ε)*γ j))*(2*D) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hb a,hb j]))
        (mul_nonneg (hγ a) (sub_nonneg.mpr (hδ j)))
    _ = 2*D*ε := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_sub_distrib,
        ← Finset.mul_sum,hγsum,hδsum]
      rw [← Finset.sum_mul,hγsum]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PhysicalFieldPopulationComparison
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different limiting field populations give a quantitative comparison
of the physical mean pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem physical_mean_field_population_comparison {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant] (eig : (j : ℕ) → Fin (N j) → ℝ)
    (g h : (j : ℕ) → Fin (N j) → A) (γ δ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 δ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D) :
    ∀ ε > 0, ∀ᶠ j in atTop,
      |(∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (g j i)) ∂μ j)-
        ∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (h j i)) ∂μ j| ≤
      2*D*(∑ a, |γ a-δ a|)+ε := by
  have he a := (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs
  have hs := (tendsto_finsetSum Finset.univ (fun a _ => he a)).const_mul (2*D)
  intro ε hε
  have hsmall := hs.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hsmall] with j hj
  exact (physical_mean_field_counts_le (hN j) (μ j) (eig j) (g j) (h j) b hD hb).trans hj.le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PositiveFieldApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rational approximations to arbitrary finite field populations. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma fieldApproxDenominator_pos {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) :
    0 < fieldApproxDenominator γ k :=
  (positiveApproxCount_pos (γ a0) k).trans_le
    (Finset.single_le_sum (f := fun a => positiveApproxCount (γ a) k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))

lemma fieldApproxWeights_pos {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) (a : A) :
    0 < fieldApproxWeights γ k a :=
  div_pos (Nat.cast_pos.mpr (positiveApproxCount_pos _ _))
    (Nat.cast_pos.mpr (fieldApproxDenominator_pos a0 γ k))

lemma fieldApproxWeights_sum {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) :
    ∑ a, fieldApproxWeights γ k a=1 := by
  simp only [fieldApproxWeights,← Finset.sum_div,← Nat.cast_sum]
  exact div_self (Nat.cast_ne_zero.mpr (fieldApproxDenominator_pos a0 γ k).ne')

lemma fieldApproxWeights_tendsto {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hsum : ∑ a, γ a=1) :
    Tendsto (fieldApproxWeights γ) atTop (𝓝 γ) := by
  have hden : Tendsto (fun k => (fieldApproxDenominator γ k : ℝ)/(k+1)) atTop (𝓝 (1:ℝ)) := by
    have hh := tendsto_finsetSum Finset.univ (fun a _ => positiveApproxCount_ratio (γ a) (hγ a))
    simpa only [fieldApproxDenominator,Nat.cast_sum,Finset.sum_div,hsum] using hh
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := (positiveApproxCount_ratio (γ a) (hγ a)).div hden one_ne_zero
  simp only [div_one] at hh
  apply hh.congr
  intro k
  exact div_div_div_cancel_right₀ (by positivity : (k+1 : ℝ)≠0) _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAffineTemplateLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single rational spectral/field template supplies the growing
attainable blocks in the physical magnetic pressure lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_affine_template_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (c : ℕ → Fin m → ℕ)
    (R : (r : ℕ) → Finset (Spin (∑ a, c r a))) (hR : ∀ r, (R r).Nonempty)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (b : A → ℝ) (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ r, ∀ ε > 0, ∀ᶠ j in atTop,
      let B := (r+1)*n
      let q := m*B-B+B+3
      let M := (∑ a, c r a)+(q+j)*B
      let g := cavityAffineLabel (by omega : 0 < m) (fun a => (r+1)*spec a) (c r)
        (by rw [← Finset.mul_sum, hspec]) M
      L+(∑ a, γ a*b a*mag a)-ε ≤ ∫ V, rotatedPressure (fun i => lam (g i)) (matrixRotation V⁻¹)
        (offsetBlockField (∑ a, c r a) (q+j) (fun i => b (consecutiveSiteGroup (r+1) group i))) ∂μ M := by
  let N := fun r => (r+1)*n
  have hN r : 0 < N r := Nat.mul_pos (Nat.succ_pos r) hn
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    exact (Nat.le_succ r).trans (Nat.le_mul_of_pos_right (r+1) hn)
  let sp := fun r a => (r+1)*spec a
  have hsp' r a : 0 < sp r a := Nat.mul_pos (Nat.succ_pos r) (hsp a)
  have hspec' r : ∑ a, sp r a=N r := by
    dsimp only [sp, N]
    rw [← Finset.mul_sum, hspec]
  have hρsp r a : (sp r a : ℝ)=(N r : ℝ)*ρ a := by
    dsimp only [sp, N]
    rw [Nat.cast_mul, hρspec, Nat.cast_mul]
    ring
  have hh := magnetic_affine_field_subsequence_lower hhaar hgauss hpub hm ρ lam hρ hsum hK hlam
    amax hmax μ N hN hNlim sp hsp' hspec' hρsp c R hR
    (fun r => consecutiveSiteGroup (r+1) group) (fun r a => (r+1)*k a)
    (fun _ => consecutiveSiteGroup_attainable group k hk) γ mag hγ hγsum
    (fun _ => consecutiveSiteGroup_proportion group γ hcount) hs hmag
    (fun _ => consecutiveSiteGroup_magnetization group k mag hc) b L hL
  exact hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticResidueSelection
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting a bad residue for each candidate block is enough to test the
full-sequence pressure lower bound. -/
noncomputable section
open Filter
namespace InvariantIsing

lemma cavity_residue_eventually_lower {n : ℕ} (hn : 0 < n) (q : ℕ)
    (P : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : Fin n, ∀ ε > 0, ∀ᶠ j in atTop, L-ε ≤ P (t+(q+j)*n)) :
    ∀ ε > 0, ∀ᶠ N in atTop, L-ε ≤ P N := by
  intro ε hε
  have he : ∀ᶠ j in atTop, ∀ t : Fin n, L-ε ≤ P (t+(q+j)*n) :=
    Filter.eventually_all.mpr (fun t => h t ε hε)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨(q+J)*n, fun N hN => ?_⟩
  have hdiv : q+J ≤ N/n := (Nat.le_div_iff_mul_le hn).mpr hN
  let t : Fin n := ⟨N%n,Nat.mod_lt _ hn⟩
  have hj : J ≤ N/n-q := by omega
  have heq : (t : ℕ)+(q+(N/n-q))*n=N := by
    have hq : q+(N/n-q)=N/n := by omega
    rw [hq]
    simpa only [t, Nat.mul_comm] using Nat.mod_add_div N n
  simpa only [heq] using hJ (N/n-q) hj t

theorem magnetic_full_lower_of_residue_selection
    (n q : ℕ → ℕ) (hn : ∀ r, 0 < n r) (P : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : (r : ℕ) → Fin (n r), ∃ r,
      ∀ ε > 0, ∀ᶠ j in atTop, L-ε ≤ P (t r+(q r+j)*n r)) :
    ∀ ε > 0, ∀ᶠ N in atTop, L-ε ≤ P N := by
  have hex : ∃ r, ∀ t : Fin (n r), ∀ ε > 0,
      ∀ᶠ j in atTop, L-ε ≤ P (t+(q r+j)*n r) := by
    by_contra hnone
    have hbad : ∀ r, ∃ t : Fin (n r), ¬(∀ ε > 0,
        ∀ᶠ j in atTop, L-ε ≤ P (t+(q r+j)*n r)) := by
      intro r
      by_contra hnr
      push Not at hnr
      exact hnone ⟨r,hnr⟩
    choose t ht using hbad
    obtain ⟨r,hr⟩ := h t
    exact ht r hr
  obtain ⟨r,hr⟩ := hex
  exact cavity_residue_eventually_lower (hn r) (q r) P L hr

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTemplateFullLower
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational spectral and magnetic template gives a lower bound along
all physical dimensions, by selecting an arbitrary bad residue for each
candidate block size. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_template_full_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∀ ε > 0, ∀ᶠ M in atTop, L+(∑ a, γ a*b a*mag a)-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  let B := fun r => (r+1)*n
  let q := fun r => m*B r-B r+B r+3
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  apply magnetic_full_lower_of_residue_selection B q
    (fun r => Nat.mul_pos (Nat.succ_pos r) hn) P (L+∑ a, γ a*b a*mag a)
  intro t
  let c := fun r => cavityResidueOffset (by omega : 0 < m) (t r)
  let R := fun r => (Finset.univ : Finset (Spin (∑ a, c r a)))
  have hR r : (R r).Nonempty := Finset.univ_nonempty
  obtain ⟨r,hr⟩ := magnetic_affine_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec c R hR
    group k hk γ mag hγ hγsum hcount hs hmag hc b L hL
  refine ⟨r,fun ε hε => ?_⟩
  have hspec' : ∑ a, (r+1)*spec a=B r := by rw [← Finset.mul_sum,hspec]
  have hρspec' a : ((r+1)*spec a : ℕ)=(B r : ℝ)*ρ a := by
    dsimp only [B]
    rw [Nat.cast_mul,Nat.cast_mul,hρspec]
    ring
  have hcomp := affine_template_pressure_comparison (by omega : 0 < m)
    (Nat.mul_pos (Nat.succ_pos r) hn) (q r) (by dsimp only [q]; omega)
    (fun a => (r+1)*spec a) (c r) hspec' ρ lam hρ hρspec' μ e he
    g γ b hg (consecutiveSiteGroup (r+1) group)
    (consecutiveSiteGroup_proportion group γ hcount) hK hlam hD hb
  have hevent := (tendsto_order.mp hcomp).1 (-ε/2) (by linarith)
  filter_upwards [hr (ε/2) (by linarith),hevent] with j hj hd
  dsimp only at hj hd
  have hsumc : ∑ a, c r a=(t r : ℕ) := cavityResidueOffset_sum _ _
  rw [hsumc] at hj hd
  change L+(∑ a, γ a*b a*mag a)-ε ≤ P ((t r : ℕ)+(q r+j)*B r)
  dsimp only [P]
  dsimp only [B,q] at *
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RationalMagnetizationCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common denominator makes any finite rational interior magnetization
attainable after repeating the original group block. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma rational_magnetization_counts {A : Type*} [Fintype A] [DecidableEq A]
    (size : A → ℕ) (mag : RationalMagnetization A) :
    ∃ d : ℕ, 0 < d ∧ ∃ k : A → ℕ, (∀ a, k a ≤ d*size a) ∧
      ∀ a, (k a : ℝ)=(d*size a : ℕ)*((1+(mag.val a : ℝ))/2) := by
  let p := fun a => (1+mag.val a)/2
  have hp a : 0 ≤ p a := by
    have hh := (abs_lt.mp (mag.property a)).1
    have hh' : 0 ≤ (1+(mag.val a : ℝ))/2 := by linarith
    exact_mod_cast hh'
  have hp1 a : (p a : ℝ) ≤ 1 := by
    have hh := (abs_lt.mp (mag.property a)).2
    dsimp only [p]
    push_cast
    linarith
  let d := ∏ a, (p a).den
  have hd : 0 < d := Finset.prod_pos (fun a _ => (p a).den_pos)
  have hdiv a : (p a).den ∣ d := Finset.dvd_prod_of_mem (fun a => (p a).den) (Finset.mem_univ a)
  let k := fun a => (d/(p a).den)*(p a).num.toNat*size a
  have he a : (k a : ℝ)=(d*size a : ℕ)*(p a : ℝ) := by
    have hnum : ((p a).num.toNat : ℝ)=(p a : ℝ)*(p a).den := by
      have hnat : ((p a).num.toNat : ℤ)=(p a).num :=
        Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hp a))
      have hreal : ((p a).num.toNat : ℝ)=((p a).num : ℝ) := by exact_mod_cast hnat
      rw [hreal,Rat.cast_def]
      exact (div_mul_cancel₀ ((p a).num : ℝ)
        (Nat.cast_ne_zero.mpr (p a).den_pos.ne')).symm
    have hprod : ((d/(p a).den : ℕ) : ℝ)*(p a).den=d := by
      exact_mod_cast Nat.div_mul_cancel (hdiv a)
    dsimp only [k]
    rw [Nat.cast_mul,Nat.cast_mul,hnum,Nat.cast_mul]
    calc
      _ = (((d/(p a).den : ℕ) : ℝ)*(p a).den)*size a*(p a : ℝ) := by ring
      _ = _ := by rw [hprod]
  refine ⟨d,hd,k,?_,?_⟩
  · intro a
    have hh : (k a : ℝ) ≤ (d*size a : ℕ) := by
      rw [he]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hp1 a)
    exact_mod_cast hh
  · intro a
    simpa only [p,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat] using he a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRationalTemplateLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every rational interior profile is admissible after a finite common
denominator repetition of a spectral and field template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_rational_template_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (mag : RationalMagnetization A)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ
      (fun a => (mag.val a : ℝ))).toReal) :
    ∀ ε > 0, ∀ᶠ M in atTop, L+(∑ a, γ a*b a*(mag.val a : ℝ))-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  obtain ⟨d,hd,k,hk,hkc⟩ := rational_magnetization_counts (spinGroupSize group) mag
  obtain ⟨s,hs,hmags,_⟩ := exists_uniform_magnetization_radius
    (fun _ : ℕ => fun a => (mag.val a : ℝ)) (fun a => (mag.val a : ℝ))
    tendsto_const_nhds mag.property
  have hcount' := consecutiveSiteGroup_proportion (K := d) group γ hcount
  have hspec' : ∑ a, d*spec a=d*n := by rw [← Finset.mul_sum,hspec]
  have hρspec' a : (d*spec a : ℕ)=(d*n : ℕ)*ρ a := by
    rw [Nat.cast_mul,Nat.cast_mul,hρspec]
    ring
  exact magnetic_template_full_pressure_lower hhaar hgauss hpub hm (Nat.mul_pos hd hn)
    ρ lam hρ hsum hK hlam amax hmax μ (fun a => d*spec a)
    (fun a => Nat.mul_pos hd (hsp a)) hspec' hρspec' e he
    (consecutiveSiteGroup d group) k
    (by simpa only [consecutiveSiteGroup_size] using hk) γ (fun a => (mag.val a : ℝ))
    hγ hγsum hcount' hs hmags
    (by simpa only [consecutiveSiteGroup_size,Nat.cast_mul] using hkc)
    g b hg hD hb L hL

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteTemplateLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full rational magnetization supremum is a lower bound for physical
pressure whenever the spectral and field populations have a finite template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_template_magnetic_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  intro ε hε
  let R := finiteR ρ lam hρ hsum
  let F := (finiteMagneticFunctional R γ b).toReal
  have hr := finiteVariational_ne_top_bot ρ lam hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hr.1 hr.2
  have hlt : ((F-ε/3 : ℝ) : EReal)<finiteMagneticFunctional R γ b := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    apply EReal.coe_lt_coe
    change F-ε/3<F
    linarith
  obtain ⟨mag,hmag⟩ := lt_iSup_iff.mp hlt
  have hmfin := finiteMagneticVariational_ne_top_bot ρ lam hρ hsum γ
    (fun a => (mag.val a : ℝ)) hγ hγsum (fun a => (mag.property a).le)
  change ((F-ε/3 : ℝ) : EReal)<
    ((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional R γ (fun a => (mag.val a : ℝ)) at hmag
  rw [← EReal.coe_toReal hmfin.1 hmfin.2,← EReal.coe_add] at hmag
  have hmag' := EReal.coe_lt_coe_iff.mp hmag
  let V := (magneticVariationalFunctional R γ (fun a => (mag.val a : ℝ))).toReal
  have hevent := magnetic_rational_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec e he group γ hγ hγsum
    hcount mag g b hg hD hb (V-ε/3) (by dsimp only [V,R] <;> linarith) (ε/3) (by positivity)
  filter_upwards [hevent] with M hM
  change F-ε ≤ _
  change V-ε/3+(∑ a, γ a*b a*(mag.val a : ℝ))-ε/3 ≤ _ at hM
  change F-ε/3<(∑ a, γ a*b a*(mag.val a : ℝ))+V at hmag'
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCountTemplateLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral and field rational populations with different denominators
have a common physical block template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_count_template_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (w : A → ℕ) (hd : 0 < ∑ a, w a)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (w a : ℝ)=(∑ a, w a : ℕ)*γ a)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  let d := ∑ a, w a
  have htot : ∑ a, n*w a=n*d := by rw [← Finset.mul_sum]
  let group := countedFieldGroup (fun a => n*w a) htot
  have hgroup a : (spinGroupSize group a : ℝ)=(n*d : ℕ)*γ a := by
    rw [countedFieldGroup_size,Nat.cast_mul,hcount,Nat.cast_mul]
    ring
  have hspec' : ∑ a, d*spec a=n*d := by rw [← Finset.mul_sum,hspec,Nat.mul_comm]
  have hρspec' a : (d*spec a : ℕ)=(n*d : ℕ)*ρ a := by
    rw [Nat.cast_mul,hρspec,Nat.cast_mul]
    ring
  exact finite_template_magnetic_pressure_lower hhaar hgauss hpub hm (Nat.mul_pos hn hd)
    ρ lam hρ hsum hK hlam amax hmax μ (fun a => d*spec a)
    (fun a => Nat.mul_pos hd (hsp a)) hspec' hρspec' e he group γ hγ hγsum hgroup
    g b hg hD hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPopulationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity in positive field populations, with the same finite field
alphabet and a bound independent of all optimizing parameters. -/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

theorem finiteMagneticFunctional_population_le {A ι : Type*}
    [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ δ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ a, 0 < δ a)
    (hγsum : ∑ a, γ a=1) (hδsum : ∑ a, δ a=1)
    {ε D : ℝ} (hε : ε ≤ 1) (hdom : ∀ a, (1-ε)*γ a ≤ δ a) (hb : ∀ a, |b a| ≤ D) :
    (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ b).toReal+2*D*ε := by
  have hh := finiteMagneticFunctional_transport_le ρ eig hρ hsum
    (retainedPopulationCoupling γ δ ε) γ b δ b
    (retainedPopulationCoupling_nonneg γ δ hε hγ hdom) hγ hδ hγsum hδsum
    (retainedPopulationCoupling_row γ δ hγsum hδsum ε)
    (retainedPopulationCoupling_col γ δ hγsum ε)
  exact hh.trans (add_le_add le_rfl (retainedPopulationCoupling_cost γ δ b hγ hγsum hδsum hdom hb))

theorem finiteMagneticFunctional_tendsto_populations {A ι : Type*}
    [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γs : ℕ → A → ℝ) (γ b : A → ℝ)
    (hγs : ∀ k a, 0 < γs k a) (hγssum : ∀ k, ∑ a, γs k a=1)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hlim : Tendsto γs atTop (𝓝 γ)) :
    Tendsto (fun k => (finiteMagneticFunctional (finiteR ρ eig hρ hsum) (γs k) b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal) := by
  classical
  let D := ∑ a, |b a|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤D := Finset.single_le_sum (f := fun a => |b a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := min (1/2 : ℝ) (ε/(4*(D+1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hleft : ∀ᶠ k in atTop, ∀ a, (1-t)*γ a ≤ γs k a := by
    apply Filter.eventually_all.mpr
    intro a
    exact (((tendsto_pi_nhds.mp hlim) a).eventually
      (Ioi_mem_nhds (by nlinarith [hγ a]))).mono (fun _ h => h.le)
  have hright : ∀ᶠ k in atTop, ∀ a, (1-t)*γs k a ≤ γ a := by
    apply Filter.eventually_all.mpr
    intro a
    exact ((((tendsto_pi_nhds.mp hlim) a).const_mul (1-t)).eventually
      (Iio_mem_nhds (by nlinarith [hγ a]))).mono (fun _ h => h.le)
  have hsmall : 2*D*t<ε := by
    have hh : t*(4*(D+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  filter_upwards [hleft,hright] with k hl hr
  have h1 := finiteMagneticFunctional_population_le ρ eig hρ hsum γ (γs k) b
    (fun a => (hγ a).le) (hγs k) hγsum (hγssum k) ht1 hl hb
  have h2 := finiteMagneticFunctional_population_le ρ eig hρ hsum (γs k) γ b
    (fun a => (hγs k a).le) hγ (hγssum k) hγsum ht1 hr hb
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldPopulationLower
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary positive real field populations are reached from rational
field blocks by quantitative pressure and variational comparisons. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_rational_spectrum_field_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (γ : A → ℝ) (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  have hA : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hγsum
  let a0 : A := Classical.choice hA
  let τ := fieldApproxWeights γ
  have hτ := fieldApproxWeights_tendsto γ (fun a => (hγ a).le) hγsum
  have hτpos j a : 0 < τ j a := fieldApproxWeights_pos a0 γ j a
  have hτsum j : ∑ a, τ j a=1 := fieldApproxWeights_sum a0 γ j
  let R := finiteR ρ lam hρ hsum
  let F := (finiteMagneticFunctional R γ b).toReal
  let Fq := fun j => (finiteMagneticFunctional R (τ j) b).toReal
  have hF : Tendsto Fq atTop (𝓝 F) := finiteMagneticFunctional_tendsto_populations
    ρ lam hρ hsum τ γ b hτpos hτsum hγ hγsum hτ
  have hErr : Tendsto (fun j => 2*D*(∑ a, |γ a-τ j a|)) atTop (𝓝 0) := by
    have hh := (tendsto_finsetSum Finset.univ (fun a _ =>
      ((tendsto_const_nhds (x := γ a)).sub ((tendsto_pi_nhds.mp hτ) a)).abs)).const_mul (2*D)
    simpa only [sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hh
  intro ε hε
  obtain ⟨j,hjErr,hjF⟩ := ((hErr.eventually (Iio_mem_nhds (show 0<ε/4 by positivity))).and
    (Metric.tendsto_nhds.mp hF (ε/4) (by positivity))).exists
  let w := fun a => positiveApproxCount (γ a) j
  have hd : 0 < ∑ a, w a := fieldApproxDenominator_pos a0 γ j
  have hw a : (w a : ℝ)=(∑ a, w a : ℕ)*τ j a := by
    dsimp only [τ,fieldApproxWeights,w,fieldApproxDenominator]
    exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd.ne')).symm
  let cg := canonicalFieldLabel a0 w
  have hc : Tendsto (fun M a => (spinGroupSize (cg M) a : ℝ)/M) atTop (𝓝 (τ j)) :=
    canonicalFieldLabel_population a0 w hd
  have hlo := finite_count_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec e he w hd
    (τ j) (fun a => (hτpos j a).le) (hτsum j) hw cg b hc hD hb (ε/4) (by positivity)
  have hcomp := physical_mean_field_population_comparison (fun k => k+1) (fun _ => by omega)
    (fun k => μ (k+1)) (fun k i => lam (e (k+1) i)) (fun k => g (k+1))
    (fun k => cg (k+1)) γ (τ j) b (hg.comp (tendsto_add_atTop_nat 1))
    (hc.comp (tendsto_add_atTop_nat 1)) hD hb (ε/4) (by positivity)
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  have hev : ∀ᶠ k in atTop, F-ε≤P (k+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hlo,hcomp] with k hk hck
    have hh := (abs_le.mp hck).1
    rw [Real.dist_eq] at hjF
    have hFq := (abs_lt.mp hjF).1
    change Fq j-ε/4≤_ at hk
    change -_ ≤ P (k+1)-_ at hh
    linarith
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hev
  apply eventually_atTop.mpr
  refine ⟨J+1,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+1 := ⟨M-1,(Nat.sub_add_cancel (by omega)).symm⟩
  exact hJ k (by omega)

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

theorem finiteMagneticFunctional_tendsto_weights {A ι : Type*} [Fintype A] [Fintype ι]
    (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a=1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (γ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (finiteR (ρs k) eig (hspos k) (hssum k)) γ b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (finiteR ρ eig hpos hsum) γ b).toReal) := by
  have hr := finiteVariational_ne_top_bot ρ eig hpos hsum
  have hf := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hr.1 hr.2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finiteR_uniform_weights ρs ρ eig hspos hssum hpos hsum hρs ε hε] with k hk
  have hrk := finiteVariational_ne_top_bot (ρs k) eig (hspos k) (hssum k)
  have hfk := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hrk.1 hrk.2
  have hleft := finiteMagneticFunctional_spectral_le_add γ b
    (finiteR (ρs k) eig (hspos k) (hssum k)) (finiteR ρ eig hpos hsum)
    (continuous_finiteR (ρs k) eig (hspos k) (hssum k)) (continuous_finiteR ρ eig hpos hsum)
    ε (fun x hx => (hk x hx).le)
  have hright := finiteMagneticFunctional_spectral_le_add γ b
    (finiteR ρ eig hpos hsum) (finiteR (ρs k) eig (hspos k) (hssum k))
    (continuous_finiteR ρ eig hpos hsum) (continuous_finiteR (ρs k) eig (hspos k) (hssum k))
    ε (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2,← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add,EReal.coe_le_coe_iff] at hleft hright
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpectralPopulationLower
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational approximation of the spectral populations gives the physical
finite-field lower bound for arbitrary positive real populations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_physical_field_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (γ : A → ℝ) (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  have hm0 : 0 < m := by omega
  let τ := positiveApproxWeights ρ
  have hτpos j a : 0 < τ j a := positiveApproxWeights_pos hm0 ρ j a
  have hτsum j : ∑ a, τ j a=1 := positiveApproxWeights_sum hm0 ρ j
  have hτ : Tendsto τ atTop (𝓝 ρ) := positiveApproxWeights_tendsto ρ (fun a => (hρ a).le) hsum
  let F := (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal
  let Fq := fun j => (finiteMagneticFunctional (finiteR (τ j) lam (hτpos j) (hτsum j)) γ b).toReal
  have hF : Tendsto Fq atTop (𝓝 F) := finiteMagneticFunctional_tendsto_weights
    τ ρ lam hτpos hτsum hρ hsum hτ γ b (fun a => (hγ a).le) hγsum
  intro ε hε
  let r := ε/(4*(2*K+1))
  have hr : 0 < r := div_pos hε (by positivity)
  have hrel : ∀ᶠ j in atTop, ∀ a, |ρ a-τ j a|/min (ρ a) (τ j a) < r := by
    apply Filter.eventually_all.mpr
    intro a
    have ht := (tendsto_pi_nhds.mp hτ) a
    have hc : Tendsto (fun _ : ℕ => ρ a) atTop (𝓝 (ρ a)) := tendsto_const_nhds
    have hh := ((hc.sub ht).abs).div (hc.min ht) (by simpa only [min_self] using (hρ a).ne')
    change Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop
      (𝓝 (|ρ a-ρ a|/min (ρ a) (ρ a))) at hh
    have hz : Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop (𝓝 0) := by
      simpa only [sub_self,abs_zero,zero_div] using hh
    exact hz.eventually (Iio_mem_nhds hr)
  obtain ⟨j,hj,hjF⟩ := (hrel.and (Metric.tendsto_nhds.mp hF (ε/4) (by positivity))).exists
  let s := fun a => positiveApproxCount (ρ a) j
  let n := positiveApproxDenominator ρ j
  have hn : 0 < n := positiveApproxDenominator_pos hm0 ρ j
  have hs a : 0 < s a := positiveApproxCount_pos (ρ a) j
  have hsn : ∑ a, s a=n := rfl
  have hcount a : (s a : ℝ)=(n : ℝ)*τ j a := by
    exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')).symm
  let A := fun M => cavityResidueLabel hm0 s hsn M
  have hA : Tendsto (fun M a => (spinGroupSize (A M) a : ℝ)/M) atTop (𝓝 (τ j)) :=
    cavity_canonical_mass_tendsto hm0 hn s hsn
  have hlo := finite_rational_spectrum_field_pressure_lower hhaar hgauss hpub hm hn
    (τ j) lam (hτpos j) (hτsum j) hK hlam amax hmax μ s hs hsn hcount A hA γ hγ hγsum
    g b hg hD hb (ε/4) (by positivity)
  have he' := he.comp (tendsto_add_atTop_nat 1)
  have hA' := hA.comp (tendsto_add_atTop_nat 1)
  have hcounts := eventually_relative_count_bound (fun k => k+1) (fun _ => by omega)
    (fun k a => spinGroupSize (e (k+1)) a) (fun k a => spinGroupSize (A (k+1)) a)
    ρ (τ j) hρ (hτpos j) he' hA' r hj
  have hesurj := eventually_surjective_label (fun _ => by omega) (fun k => e (k+1)) ρ hρ he'
  have hAsurj := eventually_surjective_label (fun _ => by omega) (fun k => A (k+1)) (τ j) (hτpos j) hA'
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  have hsmall : 2*K*r/2<ε/4 := by
    have hh : r*(4*(2*K+1))=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hev : ∀ᶠ k in atTop, F-ε≤P (k+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hlo,hcounts,hesurj,hAsurj] with k hl hk hes hAs
    have hcomp := cavity_meanPressure_multiplicity_comparison (by omega : 0 < k+1) (μ (k+1))
      (e (k+1)) (A (k+1)) hes hAs lam (fun i => b (g (k+1) i)) K hlam
      (2*K) r (by positivity) hr.le
      (fun a b => (abs_sub _ _).trans (by linarith [hlam a,hlam b])) hk
    have hh := (abs_le.mp hcomp).2
    rw [Real.dist_eq] at hjF
    have hFq := (abs_lt.mp hjF).1
    change Fq j-ε/4≤_ at hl
    change _-P (k+1)≤_ at hh
    linarith
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hev
  apply eventually_atTop.mpr
  refine ⟨J+1,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+1 := ⟨M-1,(Nat.sub_add_cancel (by omega)).symm⟩
  exact hJ k (by omega)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFinitePopulationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite-alphabet external-field pressure formula with arbitrary
positive real spectral and field populations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_positive_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m) (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    Tendsto (fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
      (fun i => b (g M i)) ∂μ M) atTop
      (𝓝 (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal) := by
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hlam a : |lam a|≤K := Finset.single_le_sum (f := fun a => |lam a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  obtain ⟨amax,_,hmax⟩ := Finset.exists_max_image Finset.univ lam
    ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  let D := ∑ a, |b a|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤D := Finset.single_le_sum (f := fun a => |b a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hlo := finite_physical_field_pressure_lower hhaar hgauss hpub hm ρ lam hρ hsum
    hK hlam amax (fun a => hmax a (Finset.mem_univ _)) μ e he γ hγ hγsum g b hg hD hb
  have hup := finite_physical_field_pressure_upper hhaar hgauss ρ lam hρ hsum μ e he
    g γ b hγ hγsum hg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlo (ε/2) (half_pos hε),hup (ε/2) (half_pos hε)] with M hl hu
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-alphabet external-field formula also includes a one-point
spectral law, represented by two equal eigenvalue labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_alphabet_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    Tendsto (fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
      (fun i => b (g M i)) ∂μ M) atTop
      (𝓝 (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal) := by
  by_cases hm : 2 ≤ m
  · exact finite_positive_field_pressure_tendsto hhaar hgauss hpub hm ρ lam hρ hsum μ e he
      g γ b hγ hγsum hg
  have hm0 : 0 < m := by
    by_contra hn
    have hz : m=0 := by omega
    subst m
    simp at hsum
  have hm1 : m=1 := by omega
  subst m
  have hlam : lam=fun _ => lam 0 := funext fun a => congrArg lam (Subsingleton.elim a 0)
  have hR : finiteR ρ lam hρ hsum=fun _ => lam 0 := by
    funext x
    rw [hlam]
    exact finiteR_constant ρ hρ hsum x (lam 0)
  let ρ' : Fin 2 → ℝ := fun _ => 1/2
  have hρ' a : 0 < ρ' a := by norm_num [ρ']
  have hsum' : ∑ a, ρ' a=1 := by first | (simp [ρ',Fin.sum_univ_two]; all_goals first | (norm_num [ρ',Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [ρ',Fin.sum_univ_two]; done) | norm_num [ρ',Fin.sum_univ_two]
  let s : Fin 2 → ℕ := fun _ => 1
  have hs : ∑ a, s a=2 := by first | (simp [s,Fin.sum_univ_two]; all_goals first | (norm_num [s,Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [s,Fin.sum_univ_two]; done) | norm_num [s,Fin.sum_univ_two]
  let e' := fun M => cavityResidueLabel (by omega : 0 < 2) s hs M
  have he' : Tendsto (fun M a => (spinGroupSize (e' M) a : ℝ)/M) atTop (𝓝 ρ') := by
    simpa only [s,ρ',Nat.cast_one,Nat.cast_ofNat,e',spinGroupSize,cavitySpectralGroup] using
      cavity_canonical_mass_tendsto (by omega : 0 < 2) (by omega : 0 < 2) s hs
  have hR' : finiteR ρ' (fun _ => lam 0) hρ' hsum'=fun _ => lam 0 := by
    funext x
    exact finiteR_constant ρ' hρ' hsum' x (lam 0)
  have hh := finite_positive_field_pressure_tendsto hhaar hgauss hpub (by omega : 2 ≤ 2)
    ρ' (fun _ => lam 0) hρ' hsum' μ e' he' g γ b hγ hγsum hg
  rw [hR'] at hh
  rw [hR]
  have heig M : (fun i => lam (e M i))=(fun _ : Fin M => lam 0) :=
    funext fun i => congrArg lam (Subsingleton.elim (e M i) 0)
  apply hh.congr
  intro M
  rw [heig M]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The external-field formula with a general finite type of spectral labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators
namespace InvariantIsing

theorem finite_type_field_pressure_tendsto_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : ι → ℝ)
    (g : (N : ℕ) → Fin N → ι)
    (w : ι → ℝ) (hw : ∀ a, 0 < w a) (hsum : ∑ a, w a=1)
    (hlim : Tendsto (fun N a => (spectralLabelCount (g N) a : ℝ)/N) atTop (𝓝 w))
    (aMax : ι) (hMax : ∀ a, lam a ≤ lam aMax)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => lam (g N i))
      (matrixRotation V⁻¹) (fun i => b (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (finiteSpectralMeasure w lam) (lam aMax)) γ b).toReal) := by
  let e := Fintype.equivFin ι
  let wf := w ∘ e.symm
  let lf := lam ∘ e.symm
  have hwp : ∀ a, 0 < wf a := fun a => hw (e.symm a)
  have hws : ∑ a, wf a=1 := (e.symm.sum_comp w).trans hsum
  have hl : Tendsto (fun N a =>
      ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/N) atTop (𝓝 wf) := by
    apply tendsto_pi_nhds.mpr
    intro a
    change Tendsto (fun N => ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/N)
      atTop (𝓝 (w (e.symm a)))
    convert (tendsto_pi_nhds.mp hlim) (e.symm a) using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    congr 2
    apply congrArg Finset.card
    ext i
    simp only [cavitySpectralGroup,Finset.mem_filter,Finset.mem_univ,
      true_and,← e.eq_symm_apply]
  have hh := finite_alphabet_field_pressure_tendsto hhaar hgauss hpub wf lf hwp hws μ
    (fun N i => e (g N i)) hl group γ b hγ hγsum hgroup
  have hR : measureR (finiteSpectralMeasure w lam) (lam aMax)=finiteR wf lf hwp hws := by
    funext x
    rw [← finiteSpectralMeasure_equiv e.symm w lam]
    have he := measureR_finiteSpectralMeasure wf lf hwp hws (e aMax)
      (fun a => by simpa only [lf,Function.comp_apply,e.symm_apply_apply] using hMax (e.symm a)) x
    simpa only [lf,Function.comp_apply,e.symm_apply_apply] using he
  rw [hR]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  simp only [lf,Function.comp_apply,e.symm_apply_apply]

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.finite_type_field_pressure_tendsto_oai.{u_1, u_2} := @OAI.InvariantIsing.finite_type_field_pressure_tendsto_oai.{u_1, u_2}
