-- Prove2me | solution 1 for OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:14.575206+00:00
-- url     : https://prove2.me/submissions/5cc2ffec-dd8f-4b61-a171-1651415cd593

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_tensor_pressure_mean
import Theorems.Thm_OAI_InvariantIsing_cavity_window_minimum_variational_lower
import Theorems.Thm_OAI_InvariantIsing_finiteSpectrum_meanPressure_variational_upper
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_tensor_envelope_pressure_lower
import Theorems.Thm_OAI_InvariantIsing_tensor_zero_field_minimizing_sequence
import Theorems.Thm_OAI_InvariantIsing_variationalFunctional_constant

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.spinValue_not
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

lemma rotatedPressure_constant {N : ℕ} (hN : 0 < N) (a : ℝ) (U : Rotation N) :
    rotatedPressure (fun _ => a) U (fun _ => 0) = a / 2 := by
  have he : (fun σ => rotatedEnergy (fun _ : Fin N => a) U σ +
      fieldEnergy (fun _ => 0) σ) = (fun _ : Spin N => 0 + a * N / 2) := by
    funext σ
    simp [rotatedEnergy_constant, fieldEnergy]
  rw [rotatedPressure, he, logPartition_add_const, logPartition_zero, zero_add]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameTransitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
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

/-- A common uniform spectral error passes through the path infimum without
exchanging the field supremum and the path infimum. -/
lemma variationalFunctional_le_add (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) :
    variationalFunctional R ≤ variationalFunctional Q + ((δ / 2 : ℝ) : EReal) := by
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
    variationalFunctional R ≤ entropyFunctional p + (spectralFunctional R p : EReal) :=
      iInf_le _ p
    _ ≤ entropyFunctional p +
        ((spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal)) :=
      add_le_add le_rfl hspec
    _ = _ := by rw [add_assoc]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the limiting cavity columns by a fixed orthonormal special
frame. This is the reference frame for the continuous complement rule. -/

noncomputable section
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_frame_completion {d n : ℕ}
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ B : Matrix (Fin (d + n)) (Fin d) ℝ,
      B.transpose * B = 1 ∧ E.transpose * B = 0 := by
  let e := EuclideanSpace.basisFun (Fin (d + n)) ℝ
  have hr : Orthonormal ℝ (fun j : Fin n => e (Fin.natAdd d j)) :=
    e.orthonormal.comp _ (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive
    (fun j : Fin n => e (Fin.natAdd d j))
    (fun j : Fin n => WithLp.toLp 2 (fun i => E i j)) hr (cavity_orthonormal_of_gram E hE)
  let B : Matrix (Fin (d + n)) (Fin d) ℝ := fun i j => U (e (Fin.castAdd n j)) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    change (∑ k, U (e (Fin.castAdd n i)) k * U (e (Fin.castAdd n j)) k) =
      if i = j then 1 else 0
    have hh := U.inner_map_map (e (Fin.castAdd n i)) (e (Fin.castAdd n j))
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n i) (Fin.castAdd n j)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fin.castAdd_inj, mul_comm] using hh.trans he
  · ext i j
    change (∑ k, E k i * U (e (Fin.castAdd n j)) k) = 0
    have hh := U.inner_map_map (e (Fin.castAdd n j)) (e (Fin.natAdd d i))
    rw [hU i] at hh
    have hne : Fin.castAdd n j ≠ Fin.natAdd d i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have he := orthonormal_iff_ite.mp e.orthonormal (Fin.castAdd n j) (Fin.natAdd d i)
    rw [ite_eq_right hne] at he
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply] using hh.trans he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialPlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma cavitySpectralGroup_pairwiseDisjoint {N m : ℕ} (g : Fin N → Fin m) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (cavitySpectralGroup g) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' : g i=a := (Finset.mem_filter.mp hi).2
  have hj' : g i=b := (Finset.mem_filter.mp hj).2
  exact hab (hi'.symm.trans hj')

lemma cavitySpectralGroup_cover {N m : ℕ} (g : Fin N → Fin m) :
    Finset.univ.biUnion (cavitySpectralGroup g)=Finset.univ := by
  classical
  ext i
  simp [cavitySpectralGroup]

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

lemma cavityOrderedEquiv_val {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (x : (a : Fin m) × Fin (dims a)) :
    (cavityOrderedEquiv dims hsum x).val=cavityOrderedStart dims x.1+x.2.val := by
  simp only [cavityOrderedEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, cavityOrderedStart]

lemma cavityOrderedGroup_window {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) (i : Fin N) :
    cavityOrderedGroup dims hsum i=a ↔
      cavityOrderedStart dims a ≤ i.val ∧ i.val < cavityOrderedStart dims a+dims a := by
  constructor
  · intro ha
    let x := (cavityOrderedEquiv dims hsum).symm i
    have hx : (cavityOrderedEquiv dims hsum x).val=i.val :=
      congrArg Fin.val ((cavityOrderedEquiv dims hsum).apply_symm_apply i)
    rw [cavityOrderedEquiv_val] at hx
    have hxval := x.2.isLt
    have hxa : x.1=a := ha
    simp only [hxa] at hx hxval
    omega
  · rintro ⟨hl,hw⟩
    let j : Fin (dims a) := ⟨i.val-cavityOrderedStart dims a, by omega⟩
    have he : cavityOrderedEquiv dims hsum ⟨a,j⟩=i := by
      apply Fin.ext
      rw [cavityOrderedEquiv_val]
      change cavityOrderedStart dims a+(i.val-cavityOrderedStart dims a)=i.val
      omega
    rw [← he]
    exact congrArg Sigma.fst ((cavityOrderedEquiv dims hsum).symm_apply_apply ⟨a,j⟩)

lemma cavityOrderedGroup_card {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) :
    (cavitySpectralGroup (cavityOrderedGroup dims hsum) a).card=dims a :=
  cavity_group_dimension_card dims (cavityOrderedEquiv dims hsum) a

lemma cavityOrderedStart_add_le {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) (hd : 0 < dims a) : cavityOrderedStart dims a+dims a ≤ N := by
  let j : Fin (dims a) := ⟨dims a-1, by omega⟩
  have hi := (cavityOrderedEquiv dims hsum ⟨a,j⟩).isLt
  rw [cavityOrderedEquiv_val] at hi
  change cavityOrderedStart dims a+(dims a-1)<N at hi
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrderedBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special axes can be identified with the same ordered
spectral basis used for the scalar pressure sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseGroupEquiv_trans {N M m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (f : Fin N ≃ Fin M) :
    cavityBaseGroupEquiv k (e.trans f) g=(cavityBaseGroupEquiv k e g).trans f := rfl

lemma cavityOrderedBase_group {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) :
    cavityBaseGroupEquiv k (cavityOrderedBase k g hsum) g=
      cavityOrderedEquiv (cavityBaseGroupDimension k g) hsum := by
  unfold cavityOrderedBase
  rw [cavityBaseGroupEquiv_trans]
  simp only [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

lemma cavityOrderedBase_label {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) (i : Fin N) :
    Sum.elim (fun w => w.1) g ((cavityOrderedBase k g hsum).symm i)=
      cavityOrderedGroup (cavityBaseGroupDimension k g) hsum i := by
  rw [← cavityBaseGroupEquiv_label, cavityOrderedBase_group]
  rfl

lemma cavity_special_labels_exists {m n d : ℕ} (s : Fin m → ℕ)
    (hdim : ∑ a, (n-s a)=d) :
    ∃ g : Fin d → Fin m, ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a := by
  refine ⟨cavityOrderedGroup (fun a => n-s a) hdim,?_⟩
  intro a
  exact cavityOrderedGroup_card (fun a => n-s a) hdim a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational spectral law gives an exact arithmetic progression of
positive multiplicities and the finite exceptional-axis multiplicities. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityRationalCount_positive {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    {q : ℕ} (hq : 0<q) (r : ℕ) (a : Fin m) : 0 < cavityRationalCount s q r a :=
  Nat.mul_pos (by omega) (hs a)

lemma cavityRationalCount_tendsto {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (q : ℕ) (a : Fin m) : Filter.Tendsto (fun r => cavityRationalCount s q r a)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun r => ?_) Filter.tendsto_id
  change r ≤ (r+q)*s a
  exact (Nat.le_add_right r q).trans (Nat.le_mul_of_pos_right _ (hs a))

lemma cavityRationalSpecial_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n) :
    ∑ a, (n-s a)=m*n-n := by
  rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => cavityRationalCount_le_total s hs a)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hs]

lemma cavityRationalRetained_ge {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (r : ℕ) (a : Fin m) : d ≤ cavityRationalCount s (d+n+3) (r+1) a-n := by
  have hp := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  unfold cavityRationalCount
  omega

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact contiguous full-system windows for a rational spectral law. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityRationalMass_difference {m n : ℕ} (s : Fin m → ℕ) (a : Fin m) :
    (cavityOrderedStart s a+s a : ℝ)/n-(cavityOrderedStart s a : ℝ)/n=(s a : ℝ)/n := by
  ring

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

lemma cavityAffineSize_tendsto {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (hn : 0 < n) :
    Tendsto (cavityAffineSize n q c) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) (cavityRationalDimension_tendsto n q hn)

lemma cavityAffineCount_tendsto {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityAffineCount s c q r a) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) (cavityRationalCount_tendsto s hs q a)

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

lemma cavityAffineStart {m : ℕ} (s c : Fin m → ℕ) (q r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityAffineCount s c q r) a=
      (r+q)*cavityOrderedStart s a+cavityOrderedStart c a := by
  simp only [cavityOrderedStart, cavityAffineCount, cavityRationalCount,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma cavityAffineStart_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityOrderedStart (cavityAffineCount s c q r) a : ℝ)/
      cavityAffineSize n q c r) atTop (𝓝 ((cavityOrderedStart s a : ℝ)/n)) := by
  simpa only [cavityAffineStart, cavityAffineSize] using
    cavity_affine_ratio_tendsto (cavityOrderedStart s a) (cavityOrderedStart c a)
      n (∑ a, c a) q hn hq

lemma cavityAffineEnd_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => ((cavityOrderedStart (cavityAffineCount s c q r) a+
      cavityAffineCount s c q r a : ℕ) : ℝ)/cavityAffineSize n q c r)
      atTop (𝓝 (((cavityOrderedStart s a+s a : ℕ) : ℝ)/n)) := by
  simpa only [Nat.cast_add, add_div] using
    (cavityAffineStart_ratio s c hn hq a).add (cavityAffineCount_ratio s c hn hq a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special axes for counts with a fixed residue offset. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityAffineRetained_ge {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (r : ℕ) (a : Fin m) : d ≤ cavityAffineRetained n d s c r a :=
  (cavityRationalRetained_ge s hs r a).trans (Nat.le_add_right _ _)

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

lemma cavityAffineFullGroup_eq {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (d r : ℕ) :
    cavityAffineFullGroup s c hsum d r=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r+n) := by
  symm
  apply cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+1+(d+n+3)) _
  dsimp only [cavityAffineSize]
  ring

lemma cavityAffineBase_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityAffineSize n (d+n+3) c r)) :
    Sum.elim (fun w => w.1) g ((cavityAffineBaseEquiv s c hs hsum g hg r).symm i)=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r) i := by
  rw [cavityAffineLabel_progression hm s c hsum hn]
  change Sum.elim _ g ((cavityOrderedBase _ g _).symm i)=_
  rw [cavityOrderedBase_label]
  have hcount : cavityBaseGroupDimension (cavityAffineRetained n d s c r) g=
      cavityAffineCount s c (d+n+3) r := by
    funext a
    exact cavityAffineBase_dimension s c hs hsum g hg r a
  simp only [hcount]

lemma cavityAffineBase_canonical_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityAffineSize n (d+n+3) c r)) :
    ((cavityBaseGroupEquiv (cavityAffineRetained n d s c r)
      (cavityAffineBaseEquiv s c hs hsum g hg r) g).symm i).1=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r) i :=
  (cavityBaseGroupEquiv_label _ _ _ i).trans (cavityAffineBase_label hm s c hs hsum hn g hg r i)

lemma cavityAffineBase_partition {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) :
    cavityBaseGroup (cavityAffineRetained n d s c r) (cavityAffineBaseEquiv s c hs hsum g hg r) g=
      cavitySpectralGroup (cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r)) := by
  funext a
  apply Finset.ext
  intro i
  simp only [cavityBaseGroup, cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
    cavityAffineBase_label hm s c hs hsum hn g hg r i]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint limits and uniform positive proportions for affine block counts. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityAffineStart_alternative {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    (∀ r, cavityOrderedStart (cavityAffineCount s c q r) a=0) ∨
      Tendsto (fun r => cavityOrderedStart (cavityAffineCount s c q r) a) atTop atTop := by
  by_cases ha : a.val=0
  · left
    intro r
    have hz : IsEmpty (Fin a) := ⟨fun i => by have hi := i.isLt; omega⟩
    simp only [cavityOrderedStart]
    exact Finset.sum_eq_zero (fun i _ => isEmptyElim i)
  · right
    have hp : 0 < cavityOrderedStart s a := by
      let i : Fin a := ⟨0,by omega⟩
      have hh := Finset.single_le_sum (f := fun i : Fin a => s (Fin.castLE a.isLt.le i))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact (hs (Fin.castLE a.isLt.le i)).trans_le hh
    apply tendsto_atTop_mono _ (cavityRationalDimension_tendsto (cavityOrderedStart s a) q hp)
    intro r
    rw [cavityAffineStart]
    exact Nat.le_add_right _ _

lemma cavityAffineEnd_tendsto {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityOrderedStart (cavityAffineCount s c q r) a+
      cavityAffineCount s c q r a) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) (cavityAffineCount_tendsto s c hs q a)

lemma cavityAffineFullStart_ratio {m n q : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityOrderedStart (cavityAffineCount s c q (r+1)) a : ℝ)/
      (cavityAffineSize n q c r+n)) atTop (𝓝 ((cavityOrderedStart s a : ℝ)/n)) := by
  have h := (cavityAffineStart_ratio s c hn hq a).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, cavityAffineSize_succ, Nat.cast_add] using h

lemma cavityAffineFullEnd_ratio {m n q : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => ((cavityOrderedStart (cavityAffineCount s c q (r+1)) a+
      cavityAffineCount s c q (r+1) a : ℕ) : ℝ)/(cavityAffineSize n q c r+n)) atTop
      (𝓝 (((cavityOrderedStart s a+s a : ℕ) : ℝ)/n)) := by
  have h := (cavityAffineEnd_ratio s c hn hq a).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, cavityAffineSize_succ, Nat.cast_add] using h

lemma cavityAffineFullWindow_size {m n q : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hq : n ≤ q) (r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityAffineCount s c q (r+1)) a+n ≤
      cavityOrderedStart (cavityAffineCount s c q (r+1)) a+cavityAffineCount s c q (r+1) a := by
  apply Nat.add_le_add_left
  have hh := Nat.le_mul_of_pos_right (r+1+q) (hs a)
  dsimp only [cavityAffineCount,cavityRationalCount]
  omega

lemma cavityAffineMass_lower {m n q : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hn : 0 < n) (hq : 0 < q) (r : ℕ) (a : Fin m) :
    (1 : ℝ)/(n+∑ a, c a : ℕ) ≤
      (cavityAffineCount s c q r a : ℝ)/cavityAffineSize n q c r := by
  have hr : 0 < r+q := by omega
  have hdim : r+q ≤ cavityAffineCount s c q r a :=
    (Nat.le_mul_of_pos_right _ (hs a)).trans (Nat.le_add_right _ _)
  have hc : (∑ a, c a) ≤ (r+q)*(∑ a, c a) := Nat.le_mul_of_pos_left _ hr
  have hineq : cavityAffineSize n q c r ≤ cavityAffineCount s c q r a*(n+∑ a, c a) := by
    calc
      _ ≤ (r+q)*n+(r+q)*(∑ a, c a) := Nat.add_le_add_left hc _
      _ = (r+q)*(n+∑ a, c a) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hdim
  have hsize : 0 < cavityAffineSize n q c r := by
    dsimp only [cavityAffineSize]
    positivity
  apply (div_le_div_iff₀ (by exact_mod_cast (show 0 < n+∑ a, c a by omega))
    (by exact_mod_cast hsize)).mpr
  simpa only [one_mul, Nat.cast_mul] using (show (cavityAffineSize n q c r : ℝ) ≤
    ((cavityAffineCount s c q r a*(n+∑ a, c a) : ℕ) : ℝ) by exact_mod_cast hineq)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLimitingComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed limiting complement required by the physical cavity bound
exists for every positive finite spectral law. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem cavity_limiting_complement_exists {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0≤ρ a) (hsum : ∑ a, ρ a=1) :
    ∃ B : Matrix (Fin (d+n)) (Fin d) ℝ,
      B.transpose*B=1 ∧ (cavityReindexedStack e (fun a => ρ a • 1)).transpose*B=0 := by
  let E := cavityReindexedStack e (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hE : E.transpose*E=1 := by
    ext i j
    have he := Equiv.sum_comp e.symm (fun k =>
      cavityLimitingStack (n := n) ρ k i*cavityLimitingStack (n := n) ρ k j)
    have hg := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
      (cavityLimitingStack_gram (n := n) ρ hρ hsum)
    simpa only [E, Matrix.mul_apply, Matrix.transpose_apply, cavityReindexedStack,
      cavitySpectralStack_scalar_eq ρ hρ] using he.trans hg
  exact cavity_frame_completion E hE

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational spectral proportions provide all finite auxiliary axes and
the fixed orthogonal complement in the cavity construction. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem cavity_rational_auxiliary_geometry {m n : ℕ} (hm : 2  ≤  m) (hn : 0 < n)
    (s : Fin m → ℕ) (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) :
    let d := m*n-n
    0 < d ∧ ∃ es : Fin (m*n) ≃ Fin (d+n),
      ∃ a₀ : Fin d → Fin m, ∃ B₀ : Matrix (Fin (d+n)) (Fin d) ℝ,
        (∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-s a) ∧
        B₀.transpose*B₀=1 ∧
        (cavityReindexedStack es (fun a => ((s a : ℝ)/n) • 1)).transpose*B₀=0 := by
  intro d
  have hmn : n+n ≤ m*n := by
    have hh := Nat.mul_le_mul_right n hm
    simpa only [two_mul] using hh
  have hdn : d+n=m*n := Nat.sub_add_cancel (by omega)
  have hd : 0 < d := by dsimp only [d]; omega
  let es : Fin (m*n) ≃ Fin (d+n) := finCongr hdn.symm
  obtain ⟨a₀,ha₀⟩ := cavity_special_labels_exists s (cavityRationalSpecial_sum s hsum)
  obtain ⟨B₀,hB₀,hperp⟩ := cavity_limiting_complement_exists es (fun a => (s a : ℝ)/n)
    (fun a => (cavityRationalMass_positive s hs hn a).le) (cavityRationalMass_sum s hsum hn)
  exact ⟨hd,es,a₀,B₀,ha₀,hB₀,hperp⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-volume perturbation minimizers provide exactly the natural-index
amplitudes used in the physical cavity model. The unused coordinates are one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityBaseAmplitude_fin {N : ℕ} (u : Fin N → ℝ) (j : Fin N) :
    cavityBaseAmplitude u j = u j := by
  simp only [cavityBaseAmplitude, dite_eq_left j.isLt]

lemma cavityBaseAmplitude_restrict {N : ℕ} (u : Fin N → ℝ) :
    (fun j : Fin N => cavityBaseAmplitude u j) = u :=
  funext (cavityBaseAmplitude_fin u)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineMinimumLower
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-residue rational finite-spectrum cavity increment bound with all finite
window, axis and limiting-complement geometry constructed explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_minimum_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ j, lam j ≤ lam a) (R : Rotation n)
    (u : (r : ℕ) → Fin (cavityAffineSize n (m*n-n+n+3) c r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r j, v r j ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ j, v' j ∈ Set.Icc (1 : ℝ) 2) →
      let N := cavityAffineSize n (m*n-n+n+3) c r
      let g := cavityAffineLabel (by omega : 0 < m) s c hsum N
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityAffineSize_ge_three n (m*n-n) c r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) (u r) (v r) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by
        have := cavityAffineSize_ge_three n (m*n-n) c r hn; omega) (μ N))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 depth b
        (fun _ => 0) u' v') :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
    let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g (N r+n) i)) (cavitySpectralGroup (g (N r+n))) (v r) 1)
        (cavitySpectralGroup (g (N r+n))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N r+n)).prod θ) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g (N r) i)) (cavitySpectralGroup (g (N r))) (v r) 1)
        (cavitySpectralGroup (g (N r))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N r)).prod θ
    ∀ ε > 0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal-
        (n : ℝ)⁻¹*Δ r < ε := by
  intro N g θ Δ
  let d := m*n-n
  let q := d+n+3
  let ρ := fun j => (s j : ℝ)/n
  have hm0 : 0 < m := by omega
  have hρ j : 0 < ρ j := cavityRationalMass_positive s hs hn j
  have hρsum : ∑ j, ρ j=1 := cavityRationalMass_sum s hsum hn
  obtain ⟨hd,es,a₀,B₀,hcounts,hB₀,hperp⟩ := cavity_rational_auxiliary_geometry hm hn s hs hsum
  let k := cavityAffineRetained n d s c
  let e := cavityAffineBaseEquiv s c hs hsum a₀ hcounts
  let gf := cavityAffineFullGroup s c hsum d
  let l := fun r j => cavityOrderedStart (cavityAffineCount s c q (r+1)) j
  let w := fun r j => l r j+cavityAffineCount s c q (r+1) j
  have hN r : 3 ≤ N r := cavityAffineSize_ge_three n d c r hn
  have hNl : Tendsto N atTop atTop := cavityAffineSize_tendsto n q c hn
  have hk r j : d ≤ k r j := cavityAffineRetained_ge s c hs r j
  have hdim r j : cavityBaseGroupDimension (k r) a₀ j=cavityAffineCount s c q r j :=
    cavityAffineBase_dimension s c hs hsum a₀ hcounts r j
  have hgroups r j : 0 < cavityBaseGroupDimension (k r) a₀ j := by
    rw [hdim]
    exact (cavityRationalCount_positive s hs (by omega) r j).trans_le (Nat.le_add_right _ _)
  have hdims j : Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ j) atTop atTop := by
    simpa only [hdim] using cavityAffineCount_tendsto s c hs q j
  have hmasslim : Tendsto (fun r j => (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hdim] using cavityAffineCount_ratio s c hn (q := q) (by omega) j
  have hc : 0 < (1:ℝ)/(n+∑ a, c a : ℕ) := by
    apply div_pos zero_lt_one
    exact_mod_cast (show 0 < n+∑ a, c a by omega)
  have hfrac r j : (1:ℝ)/(n+∑ a, c a : ℕ) ≤
      (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r := by
    rw [hdim]
    exact cavityAffineMass_lower s c hs hn (by omega) r j
  have hwindow r j i : gf r i=j ↔ l r j ≤ i.val ∧ i.val < w r j :=
    cavityOrderedGroup_window _ _ j i
  have hln r j : l r j+n ≤ w r j :=
    cavityAffineFullWindow_size s c hs (by omega) r j
  have hw r j : w r j ≤ N r+n :=
    cavityOrderedStart_add_le (cavityAffineCount s c q (r+1))
      (cavityAffineFull_sum s c hsum q r) j ((cavityRationalCount_positive s hs (by omega) (r+1) j).trans_le (Nat.le_add_right _ _))
  have hl j : Tendsto (fun r => (l r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j : ℝ)/n)) :=
    cavityAffineFullStart_ratio s c hn (by omega) j
  have hwlim j : Tendsto (fun r => (w r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j+s j : ℝ)/n)) := by
    simpa only [w, l, N, Nat.cast_add] using cavityAffineFullEnd_ratio s c hn (by omega : 0 < q) j
  have HH := cavity_window_minimum_variational_lower hhaar hgauss hpub N depth b hb hN hNl
    gf k (cavityAffineRetainedEquiv s c hs hsum d) e es B₀ a₀ hk
    (fun r j => μ (cavityBaseGroupDimension (k r) a₀ j)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) lam v hv u hu (by
      intro r u' v' hu' hv'
      have hh := hmin r u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityAffineLabel hm0 s c hsum (N r) i :=
        cavityAffineBase_canonical_label hm0 s c hs hsum hn a₀ hcounts r i
      simp_rw [heq]
      exact hh)
    hd hn hB₀
    ρ hρ hρsum (fun j => (cavityOrderedStart s j : ℝ)/n)
    (fun j => (cavityOrderedStart s j+s j : ℝ)/n)
    (funext fun j => (cavityRationalMass_difference s j).symm)
    (fun j => (cavityAffineEnd_tendsto s c hs q j).comp (tendsto_add_atTop_nat 1)) (fun j => (cavityAffineStart_alternative s c hs q j).elim
      (fun h => Or.inl (fun r => h (r+1)))
      (fun h => Or.inr (h.comp (tendsto_add_atTop_nat 1))))
    hl hwlim hperp hgroups hdims hc hfrac hmasslim a ha s
    (cavityRationalCount_le_total s hsum) hcounts (fun _ => by dsimp only [ρ]; field_simp) R
  intro ε hε
  filter_upwards [HH ε hε] with r hr
  have hf : gf r=g (N r+n) := cavityAffineFullGroup_eq hm0 s c hsum hn d r
  have hb' (i : Fin (N r)) : Sum.elim (fun w => w.1) a₀ ((e r).symm i)=g (N r) i :=
    cavityAffineBase_label hm0 s c hs hsum hn a₀ hcounts r i
  have hp : cavityBaseGroup (k r) (e r) a₀=cavitySpectralGroup (g (N r)) :=
    cavityAffineBase_partition hm0 s c hs hsum hn a₀ hcounts r
  have heig : (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i))) =
      (fun i => lam (g (N r) i)) := funext fun i => congrArg lam (hb' i)
  rw [hf,hp] at hr
  rw [heig] at hr
  exact hr

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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

lemma cavityOrientedFamily_pos (μ : (N : ℕ) → Measure (Orthogonal N))
    {N : ℕ} (hN : 0 < N) :
    cavityOrientedFamily μ N=cavityOrientedBaseLaw hN (μ N) := by
  simp only [cavityOrientedFamily, dite_eq_left hN]

instance cavityOrientedFamily_probability (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] (N : ℕ) :
    IsProbabilityMeasure (cavityOrientedFamily μ N) := by
  by_cases hN : 0 < N
  · rw [cavityOrientedFamily_pos μ hN]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · simp only [cavityOrientedFamily, dite_eq_right hN]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cavityOrientedFamily_leftInvariant (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] [∀ N, (μ N).IsMulRightInvariant] (N : ℕ) :
    (cavityOrientedFamily μ N).IsMulLeftInvariant := by
  by_cases hN : 0 < N
  · rw [cavityOrientedFamily_pos μ hN]
    exact cavityOrientedBaseLaw_leftInvariant hN (μ N)
  · have hzero : N=0 := by omega
    subst N
    constructor
    intro g
    have hg : g=1 := by
      apply Subtype.ext
      ext i
      exact Fin.elim0 i
    rw [hg]
    simp

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffinePressureLower
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-residue rational finite-spectrum pressure lower bound. All minimizers,
subsequence limits and cavity geometry are constructed in the proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ j, lam j ≤ lam a) (R : Rotation n) :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
    ∀ ε > 0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (g (N r) i)) (matrixRotation V⁻¹)
        (fun _ => 0) ∂μ (N r) := by
  intro N g
  let ν := cavityOrientedFamily μ
  let eig := fun M i => lam (g M i)
  let I := fun M => cavitySpectralGroup (g M)
  let L := (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
    (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal
  have hν M : (ν M).IsMulLeftInvariant := cavityOrientedFamily_leftInvariant μ M
  have hN r : 3 ≤ N r := cavityAffineSize_ge_three n (m*n-n) c r hn
  have hpos r : 0 < N r := by have := hN r; omega
  obtain ⟨u,v,hu,hv,hmin⟩ := tensor_zero_field_minimizing_sequence hhaar hgauss
    m depth b hb ν hν eig (fun _ _ => 0) I
  have hinc := cavity_affine_minimum_lower hhaar hgauss hpub hm hn s c hs hsum
    depth b hb μ lam a ha R (fun r => u (N r)) (fun r => v (N r))
    (fun r => hu (N r)) (fun r => hv (N r)) (by
      intro r u' v' hu' hv'
      simpa only [ν,cavityOrientedFamily_pos μ (hpos r)] using
        hmin (N r) (hN r) u' v' hu' hv')
  let N₀ := (m*n-n+n+3)*n+∑ a, c a
  have hN₀ : 3 ≤ N₀ := by simpa only [N, cavityAffineSize, zero_add] using hN 0
  have hindex r : N₀+n*r=N r := by
    dsimp only [N₀,N,cavityAffineSize]
    ring
  have hh := tensor_envelope_pressure_lower hhaar hgauss m depth N₀ n hN₀ hn
    b hb ν hν eig (fun _ _ => 0) I u v hu hv hmin L (by
      intro ε hε
      filter_upwards [hinc ε hε] with r hr
      dsimp only
      rw [hindex]
      have hf := cavity_tensor_pressure_mean (by have := hpos r; omega : 0 < N r+n)
        (μ (N r+n)) (eig (N r+n)) (I (N r+n)) (cavityBaseAmplitude (u (N r)))
        (v (N r)) 1 b hb
      have hb' := cavity_tensor_pressure_mean (hpos r) (μ (N r)) (eig (N r)) (I (N r))
        (cavityBaseAmplitude (u (N r))) (v (N r)) 1 b hb
      rw [cavityBaseAmplitude_restrict] at hb'
      rw [← cavityOrientedFamily_pos μ (by have := hpos r; omega)] at hf
      rw [← cavityOrientedFamily_pos μ (hpos r)] at hb'
      change L-(n : ℝ)⁻¹*((∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (eig (N r+n)) (I (N r+n)) (v (N r)) 1)
        (I (N r+n)) (cavityBaseAmplitude (u (N r))) z.1
          ∂(μ (N r+n)).prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) -
        ∫ z, cavityRotationLogMean z.2
          (diagonalPerturbedEigenvalues (eig (N r)) (I (N r)) (v (N r)) 1)
          (I (N r)) (cavityBaseAmplitude (u (N r))) z.1
            ∂(μ (N r)).prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) < ε at hr
      rw [hf,hb'] at hr
      simp only [Nat.cast_add] at hr
      change L-ε ≤ _
      rw [div_eq_mul_inv]
      linarith)
  intro ε hε
  filter_upwards [hh ε hε] with r hr
  rw [hindex] at hr
  dsimp only [ν] at hr
  rw [cavityOrientedFamily_pos μ (hpos r), cavity_oriented_pressure] at hr
  exact hr

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffinePressureLimit
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact limiting pressure for rational finite spectra along each
fixed residue progression. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ) :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
    Tendsto (fun r => ∫ V, rotatedPressure (fun i => lam (g (N r) i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N r)) atTop
      (𝓝 (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal) := by
  intro N g
  have hm0 : 0 < m := by omega
  let q := m*n-n+n+3
  let ρ := fun a => (s a : ℝ)/n
  let eig := fun r i => lam (g (N r) i)
  let I := fun r => cavitySpectralGroup (g (N r))
  let L := (variationalFunctional (finiteR ρ lam
    (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ lam
    ⟨⟨0,hm0⟩,Finset.mem_univ _⟩
  have hb : CascadeExponents 0 (fun _ => 0) := by
    constructor <;> intro i hi <;> omega
  have hlo := cavity_affine_pressure_lower hhaar hgauss hpub hm hn s c hs hsum
    0 (fun _ => 0) hb μ lam a (fun j => ha j (Finset.mem_univ j))
    (LinearIsometryEquiv.refl ℝ _)
  have hpos r : 0 < N r := by
    change 0 < cavityAffineSize n (m*n-n+n+3) c r
    have := cavityAffineSize_ge_three n (m*n-n) c r hn
    omega
  let ν := fun r => cavityOrientedBaseLaw (hpos r) (μ (N r))
  have hcard r a : (I r a).card=cavityAffineCount s c q r a := by
    change (cavitySpectralGroup (cavityAffineLabel hm0 s c hsum (cavityAffineSize n q c r)) a).card=_
    rw [cavityAffineLabel_progression hm0 s c hsum hn]
    exact cavityOrderedGroup_card _ _ a
  have hmass : Tendsto (fun r a => ((I r a).card : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [hcard] using cavityAffineCount_ratio s c hn (q := q) (by omega) a
  let K := 1+∑ a, |lam a|
  have hK : 0 < K := by
    have h := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => abs_nonneg (lam a))
    dsimp only [K]
    linarith
  have hbound r i : |eig r i| ≤ K := by
    have h := Finset.single_le_sum (f := fun a => |lam a|)
      (fun a _ => abs_nonneg (lam a)) (Finset.mem_univ (g (N r) i))
    dsimp only [eig,K]
    linarith
  have hup := finiteSpectrum_meanPressure_variational_upper hhaar hgauss N
    (fun r => cavityAffineSize_ge_three n (m*n-n) c r hn)
    (cavityAffineSize_tendsto n q c hn) m ν
    (fun r => cavityOrientedBaseLaw_leftInvariant (hpos r) (μ (N r))) eig K hK hbound I
    (fun r => cavitySpectralGroup_pairwiseDisjoint _) (fun r => cavitySpectralGroup_cover _)
    lam (by intro r a i hi; change lam (g (N r) i)=lam a; rw [(Finset.mem_filter.mp hi).2])
    ρ (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn) hmass
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlo (ε/2) (half_pos hε),hup (ε/2) (half_pos hε)] with r hl hu
  rw [cavity_oriented_pressure] at hu
  change dist _ L < ε
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrientedFamily_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultiplicityTransport
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalAllSizes
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational finite-spectrum pressure convergence on the full sequence
of physical dimensions, with every residue class accounted for. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_rational_all_sizes_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ) :
    Tendsto (fun N => ∫ V, rotatedPressure
      (fun i => lam (cavityResidueLabel (by omega : 0 < m) s hsum N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N) atTop
      (𝓝 (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal) := by
  let P := fun N => ∫ V, rotatedPressure
    (fun i => lam (cavityResidueLabel (by omega : 0 < m) s hsum N i))
    (matrixRotation V⁻¹) (fun _ => 0) ∂μ N
  let q := m*n-n+n+3
  apply cavity_residue_tendsto hn q P
  intro t
  have hh := cavity_affine_pressure_tendsto hhaar hgauss hpub hm hn s
    (cavityResidueOffset (by omega : 0 < m) t) hs hsum μ lam
  apply hh.congr
  intro r
  dsimp only [P]
  rw [← cavityResidueSize (by omega : 0 < m) n q (t : ℕ) r]
  rw [cavityResidueLabel_progression (by omega : 0 < m) s hsum q (t : ℕ) r t.isLt]

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

theorem finiteVariational_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) :
    Tendsto (fun k => (variationalFunctional (finiteR (ρs k) eig (hspos k) (hssum k))).toReal)
      atTop (𝓝 (variationalFunctional (finiteR ρ eig hpos hsum)).toReal) := by
  have hf := finiteVariational_ne_top_bot ρ eig hpos hsum
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finiteR_uniform_weights ρs ρ eig hspos hssum hpos hsum hρs ε hε] with k hk
  have hfk := finiteVariational_ne_top_bot (ρs k) eig (hspos k) (hssum k)
  have hleft := variationalFunctional_le_add (finiteR (ρs k) eig (hspos k) (hssum k))
    (finiteR ρ eig hpos hsum) (continuous_finiteR (ρs k) eig (hspos k) (hssum k))
    (continuous_finiteR ρ eig hpos hsum) ε (fun x hx => (hk x hx).le)
  have hright := variationalFunctional_le_add (finiteR ρ eig hpos hsum)
    (finiteR (ρs k) eig (hspos k) (hssum k)) (continuous_finiteR ρ eig hpos hsum)
    (continuous_finiteR (ρs k) eig (hspos k) (hssum k)) ε
    (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2, ← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hleft hright
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedDimensions
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-alphabet mean limit along arbitrary diverging dimensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_selected_dimensions_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun k a => ((cavitySpectralGroup (g k) a).card : ℝ)/D k) atTop (𝓝 ρ)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal) := by
  have hm0 : 0 < m := by omega
  let τ := positiveApproxWeights ρ
  have hτpos j a : 0 < τ j a := positiveApproxWeights_pos hm0 ρ j a
  have hτsum j : ∑ a, τ j a=1 := positiveApproxWeights_sum hm0 ρ j
  have hτ : Tendsto τ atTop (𝓝 ρ) := positiveApproxWeights_tendsto ρ (fun a => (hρ a).le) hρsum
  let F := fun j => (variationalFunctional (finiteR (τ j) lam (hτpos j) (hτsum j))).toReal
  let L := (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal
  have hF : Tendsto F atTop (𝓝 L) :=
    finiteVariational_tendsto_weights τ ρ lam hτpos hτsum hρ hρsum hτ
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound a : |lam a| ≤ K :=
    Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hdiam a b : |lam a-lam b| ≤ 2*K :=
    (abs_sub _ _).trans (by linarith [hbound a,hbound b])
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := ε/(3*(2*K+1))
  have hR : 0 < R := by dsimp only [R] <;> positivity
  have hrel : ∀ᶠ j in atTop, ∀ a, |ρ a-τ j a|/min (ρ a) (τ j a) < R := by
    apply Filter.eventually_all.mpr
    intro a
    have ht := (tendsto_pi_nhds.mp hτ) a
    have hconst : Tendsto (fun _ : ℕ => ρ a) atTop (𝓝 (ρ a)) := tendsto_const_nhds
    have hh := ((hconst.sub ht).abs).div
      (hconst.min ht) (by simpa only [min_self] using (hρ a).ne')
    change Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop
      (𝓝 (|ρ a-ρ a|/min (ρ a) (ρ a))) at hh
    have hz : Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero, zero_div] using hh
    exact hz.eventually (Iio_mem_nhds hR)
  obtain ⟨j,hj,hFj⟩ := (hrel.and (Metric.tendsto_nhds.mp hF (ε/3) (by positivity))).exists
  let s := fun a => positiveApproxCount (ρ a) j
  let n := positiveApproxDenominator ρ j
  have hn : 0 < n := positiveApproxDenominator_pos hm0 ρ j
  have hs a : 0 < s a := positiveApproxCount_pos (ρ a) j
  have hsum : ∑ a, s a=n := rfl
  let A := fun N => cavityResidueLabel hm0 s hsum N
  have hAlim : Tendsto (fun k a => ((cavitySpectralGroup (A (D k)) a).card : ℝ)/(D k : ℝ))
      atTop (𝓝 (τ j)) :=
    (cavity_canonical_mass_tendsto hm0 hn s hsum).comp hDlim
  have hglim := hρlim
  have hcounts := eventually_relative_count_bound D hD
    (fun k a => (cavitySpectralGroup (g k) a).card)
    (fun k a => (cavitySpectralGroup (A (D k)) a).card) ρ (τ j) hρ (hτpos j) hglim hAlim R hj
  have hgSurj := eventually_surjective_label hD g ρ hρ hglim
  have hASurj := eventually_surjective_label hD (fun k => A (D k)) (τ j) (hτpos j) hAlim
  have hP := (cavity_rational_all_sizes_tendsto hhaar hgauss hpub hm hn s hs hsum μ lam).comp
    hDlim
  have hPsmall := Metric.tendsto_nhds.mp hP (ε/3) (by positivity)
  filter_upwards [hcounts,hgSurj,hASurj,hPsmall] with k hk hgk hAk hPk
  have hc := cavity_meanPressure_multiplicity_comparison (hD k) (μ (D k))
    (g k) (A (D k)) hgk hAk lam (fun _ => 0) K hbound (2*K) R (by positivity) hR.le hdiam hk
  let P := ∫ V, rotatedPressure (fun i => lam (g k i)) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)
  let Q := ∫ V, rotatedPressure (fun i => lam (A (D k) i)) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)
  have hPQ : |P-Q| ≤ 2*K*R/2 := by simpa only [abs_sub_comm] using hc
  have hQL : |Q-F j| < ε/3 := by
    rw [Real.dist_eq] at hPk
    change |Q-F j| < ε/3 at hPk
    exact hPk
  have hFL : |F j-L| < ε/3 := by simpa only [Real.dist_eq] using hFj
  have hsmall : 2*K*R/2 < ε/3 := by
    have hmul : R*(3*(2*K+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  change dist P L < ε
  rw [Real.dist_eq]
  have ht := abs_sub_le P Q L
  have ht' := abs_sub_le Q (F j) L
  linarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SelectedAlphabetPressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-alphabet pressure theorem along diverging dimensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem selected_finite_alphabet_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {m : ℕ}
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun k a => ((cavitySpectralGroup (g k) a).card : ℝ)/D k) atTop (𝓝 ρ)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal) := by
  by_cases hm : 2 ≤ m
  · exact cavity_selected_dimensions_pressure_tendsto hhaar hgauss hpub hm μ lam D hD hDlim g ρ hρ hρsum hρlim
  have hm0 : 0 < m := by
    obtain ⟨a,_⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
    exact Nat.pos_of_ne_zero (by intro hz; subst m; exact Fin.elim0 a)
  have hm1 : m=1 := by omega
  subst m
  have hlam : lam=fun _ => lam 0 := funext fun a => congrArg lam (Subsingleton.elim a 0)
  have hR : finiteR ρ lam hρ hρsum=fun _ => lam 0 := by
    funext x
    rw [hlam]
    exact finiteR_constant ρ hρ hρsum x (lam 0)
  rw [hR, variationalFunctional_constant, EReal.toReal_coe]
  have he : ∀ᶠ k in atTop, (∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k))=lam 0/2 := by
    apply Filter.Eventually.of_forall
    intro k
    have hpos : 0 < D k := hD k
    have heig : (fun i => lam (g k i))=fun _ => lam 0 :=
      funext fun i => congrArg lam (Subsingleton.elim (g k i) 0)
    rw [heig]
    simp only [rotatedPressure_constant hpos,integral_const,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul]
  exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SelectedTypePressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spectral cell types along diverging dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators
namespace InvariantIsing

theorem selected_finite_type_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : ι → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → ι)
    (w : ι → ℝ) (hw : ∀ a, 0 < w a) (hsum : ∑ a, w a=1)
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/D k) atTop (𝓝 w))
    (aMax : ι) (hMax : ∀ a, lam a ≤ lam aMax) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (finiteSpectralMeasure w lam) (lam aMax))).toReal) := by
  let e := Fintype.equivFin ι
  let wf := w ∘ e.symm
  let lf := lam ∘ e.symm
  have hwp : ∀ a, 0 < wf a := fun a => hw (e.symm a)
  have hws : ∑ a, wf a=1 := (e.symm.sum_comp w).trans hsum
  have hl : Tendsto (fun N a =>
      ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/D N) atTop (𝓝 wf) := by
    apply tendsto_pi_nhds.mpr
    intro a
    change Tendsto (fun N => ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/D N)
      atTop (𝓝 (w (e.symm a)))
    convert (tendsto_pi_nhds.mp hlim) (e.symm a) using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    congr 2
    apply congrArg Finset.card
    ext i
    simp only [cavitySpectralGroup,Finset.mem_filter,Finset.mem_univ,
      true_and,← e.eq_symm_apply]
  have hh := selected_finite_alphabet_pressure_tendsto hhaar hgauss hpub μ lf D hD hDlim
    (fun N i => e (g N i)) wf hwp hws hl
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

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SelectedPartitionPressure
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral rounding for a sequence of selected dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function
namespace InvariantIsing

theorem selected_partition_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (eig : (k : ℕ) → Fin (D k) → ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν))
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (hbd : ∀ i, (ν : Measure ℝ) (frontier (S i))=0)
    (lam : ι → ℝ) (fallback aMax : {i // 0 < (ν : Measure ℝ).real (S i)})
    (hMax : ∀ a : {i // 0 < (ν : Measure ℝ).real (S i)}, lam a ≤ lam aMax) :
    Tendsto (fun k => ∫ V, rotatedPressure
      (fun i => lam (positiveSpectralLabel (fun a => (ν : Measure ℝ).real (S a)) fallback
        (spectralPartitionIndex S hcover (eig k i))))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR
        (finiteSpectralMeasure (fun i : {i // 0 < (ν : Measure ℝ).real (S i)} =>
          (ν : Measure ℝ).real (S i)) (fun i => lam i)) (lam aMax))).toReal) := by
  let w := fun a => (ν : Measure ℝ).real (S a)
  let g := fun k (i : Fin (D k)) => spectralPartitionIndex S hcover (eig k i)
  have hc := spectral_label_counts_partition D hD eig ν hweak S hS hbd g
    (fun k a i => spectralPartitionIndex_eq_iff S hcover hdis (eig k i) a)
  have hp := positive_spectral_counts_tendsto D g w (fun _ => measureReal_nonneg) fallback hc
  exact selected_finite_type_pressure_tendsto hhaar hgauss hpub μ
    (fun a : {i // 0 < w i} => lam a) D hD hDlim
    (fun k => positiveSpectralLabel w fallback ∘ g k) (fun a : {i // 0 < w i} => w a)
    (fun a => a.property) (positiveSpectralWeights_sum w (fun _ => measureReal_nonneg)
      (spectralPartitionWeights_sum (ν : Measure ℝ) S hcover hdis hS)) hp aMax hMax

namespace CompactSpectralPartition

lemma selected_pressure_tendsto_oai {ν : ProbabilityMeasure ℝ} {a b δ : ℝ}
    (P : CompactSpectralPartition ν a b δ)
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (eig : (k : ℕ) → Fin (D k) → ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.lowerValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) ∧
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.upperValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) := by
  have hh (fallback : P.Positive) := selected_partition_pressure_tendsto hhaar hgauss hpub μ
    D hD hDlim eig ν hweak P.cells (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    (spectralBallCell_null_boundary (ν : Measure ℝ) _ P.null_boundary)
    P.value fallback P.upper P.le_upper
  exact ⟨hh P.lower,hh P.upper⟩

end CompactSpectralPartition
end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto_oai := @OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto_oai
