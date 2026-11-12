-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:27.024052+00:00
-- url     : https://prove2.me/submissions/6e0d3ac0-ac50-43bc-8483-2174349cbf21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_canonical_group_block_tendsto
import Theorems.Thm_OAI_InvariantIsing_cavity_spectral_haar_test_tendsto
import Theorems.Thm_OAI_InvariantIsing_cavity_strict_recalculated_gaussian_error
import Theorems.Thm_OAI_InvariantIsing_continuous_cavityCanonicalLabel
import Theorems.Thm_OAI_InvariantIsing_continuous_cavitySynchronizedBlock
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_spin

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
open MeasureTheory in
theorem _root_.MeasureTheory.ProbabilityMeasure.mapAE_eq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (ν : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (h : AEMeasurable f (ν : Measure Ω)) : ν.mapAE f = ν.map h := by
  classical
  unfold ProbabilityMeasure.mapAE
  exact dif_pos h

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak continuity of the finite Gaussian marks in their covariance,
including singular limiting covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a : Type*} [Fintype a] [DecidableEq a]

lemma cavity_sqrt_tendsto (S : ℕ → Matrix a a ℝ)
    (S₀ : Matrix a a ℝ) (hS : ∀ n, (S n).PosSemidef)
    (hS₀ : S₀.PosSemidef) (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => CFC.sqrt (S n)) atTop (𝓝 (CFC.sqrt S₀)) := by
  have hw : Tendsto S atTop (𝓝[{A : Matrix a a ℝ | 0 ≤ A}] S₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hS n).nonneg)⟩
  have hc := (CFC.continuousOn_sqrt (A := Matrix a a ℝ)).continuousWithinAt
    hS₀.nonneg
  exact hc.tendsto.comp hw

lemma cavity_matrix_action_continuous (x : EuclideanSpace ℝ a) :
    Continuous (fun A : Matrix a a ℝ => A.toEuclideanLin x) := by
  change Continuous (fun A : Matrix a a ℝ =>
    WithLp.toLp 2 (fun i => ∑ j, A i j * x j))
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianJointTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint weak continuity of Gaussian marks and their finite overlap
labels, including singular covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a] [MetricSpace L]

lemma cavity_gaussian_joint_test_tendsto
    (l : ℕ → L) (l₀ : L) (hl : Tendsto l atTop (𝓝 l₀))
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, F (l n, z) ∂multivariateGaussian 0 (S n)) atTop
      (𝓝 (∫ z, F (l₀, z) ∂multivariateGaussian 0 S₀)) := by
  have hrep (x : L) (A : Matrix a a ℝ) :
      (∫ z, F (x, z) ∂multivariateGaussian 0 A) =
        ∫ z : EuclideanSpace ℝ a, F (x, (CFC.sqrt A).toEuclideanLin z) ∂stdGaussian _ := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp only [zero_add]
    rfl
  simp_rw [hrep]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp (continuous_const.prodMk
      (CFC.sqrt (S n)).toEuclideanLin.continuous_of_finiteDimensional)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun z => F.norm_coe_le_norm _)
  · exact ae_of_all _ fun z => F.continuous.tendsto _ |>.comp
      (hl.prodMk_nhds ((cavity_matrix_action_continuous z).tendsto _ |>.comp
        (cavity_sqrt_tendsto S S₀ hS hS₀ hlim)))

lemma cavity_gaussian_joint_test_extension (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    ∃ G : L × Matrix a a ℝ →ᵇ ℝ, ∀ l S, S.PosSemidef →
      G (l, S) = ∫ z, F (l, z) ∂multivariateGaussian 0 S := by
  let s : Set (L × Matrix a a ℝ) := {p | p.2.PosSemidef}
  have hs : IsClosed s := Matrix.posSemidef_is_closed.preimage continuous_snd
  let g : s → ℝ := fun p => ∫ z, F (p.1.1, z) ∂multivariateGaussian 0 p.1.2
  have hg : Continuous g := by
    apply continuous_iff_seqContinuous.mpr
    intro p p₀ hp
    exact cavity_gaussian_joint_test_tendsto (fun n => (p n).1.1) p₀.1.1
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hp)
      (fun n => (p n).1.2) p₀.1.2 (fun n => (p n).2) p₀.2
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hp) F
  have hgb (p : s) : ‖g p‖ ≤ ‖F‖ := by
    have hb := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ a) p.1.2)
      (f := fun z => F (p.1.1, z)) (C := ‖F‖)
      (ae_of_all _ fun z => F.norm_coe_le_norm _)
    simpa only [probReal_univ, mul_one] using hb
  let b : s →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg ‖F‖ hgb
  obtain ⟨G, _, hG⟩ := b.exists_norm_eq_domRestrict_eq_of_closed hs
  refine ⟨G, fun l S hS => ?_⟩
  exact congrArg (fun f : s →ᵇ ℝ => f ⟨(l, S), hS⟩) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianMarkedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint law of an overlap label and its Gaussian cavity marks.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a]
  [MetricSpace L] [MeasurableSpace L] [BorelSpace L]

omit [BorelSpace L] in
lemma cavityGaussianMarkedLaw_integral [SecondCountableTopology L]
    (Q : ProbabilityMeasure (L × Matrix a a ℝ))
    (f : L × EuclideanSpace ℝ a → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂(cavityGaussianMarkedLaw Q : Measure (L × EuclideanSpace ℝ a))) =
      ∫ p, ∫ y, f (p.1, y) ∂multivariateGaussian 0 p.2
        ∂(Q : Measure (L × Matrix a a ℝ)) := by
  have hi : Integrable (fun p => f (cavityGaussianMarkedMap p))
      ((Q : Measure (L × Matrix a a ℝ)).compProd cavityGaussianKernel) :=
    Integrable.of_bound (hf.comp measurable_cavityGaussianMarkedMap).aestronglyMeasurable
      C (ae_of_all _ fun p => hb _)
  change (∫ x, f x ∂((Q : Measure (L × Matrix a a ℝ)).compProd cavityGaussianKernel).map
    cavityGaussianMarkedMap) = _
  rw [integral_map measurable_cavityGaussianMarkedMap.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd hi]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

/-- Equation (4.10): uniform deficit error is bounded by the L¹ path error. -/
lemma abs_deficit_sub_path_le (p q : OverlapPath) (r : ℝ) :
    |deficit p r - deficit q r| ≤ ∫ s, |p s - q s| ∂pathMeasure := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (q.integrable_complement_max r)]
  calc
    _ ≤ ∫ s, |(1 - max (p s) r) - (1 - max (q s) r)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, |p s - q s| ∂pathMeasure := by
      apply integral_mono
        ((p.integrable_complement_max r).sub (q.integrable_complement_max r)).abs
        (p.integrable.sub q.integrable).abs
      intro s
      have he : (1 - max (p s) r) - (1 - max (q s) r) =
          -(max (p s) r - max (q s) r) := by ring
      change |(1 - max (p s) r) - (1 - max (q s) r)| ≤ |p s - q s|
      rw [he, abs_neg]
      exact abs_max_sub_max_le_abs (p s) (q s) r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalLabels
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical spectral labels as continuous monotone functions of the
total overlap, with the diagonal bound built into their range. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityCanonicalCoordinate_monotone {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Monotone (cavityCanonicalCoordinate ρ eig hρ hρsum p a) := by
  intro s t hst
  have hc : (Set.projIcc 0 1 zero_le_one s : ℝ) ≤ (Set.projIcc 0 1 zero_le_one t : ℝ) :=
    max_le_max le_rfl (min_le_min le_rfl hst)
  exact intervalIntegral.integral_mono_interval le_rfl (Set.projIcc 0 1 zero_le_one s).property.1 hc
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a (Set.projIcc 0 1 zero_le_one t).property)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cylinderCross_prefix (a b : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    cylinderCross a b = ∑ i : Fin n, a i*b i := by
  rw [cylinderCross,a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*b i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => a i*b i) n).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

end IsingPerceptron

namespace IsingPerceptron

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false, if_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true, if_true,ih]

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true, if_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true, if_true] <;> ring
  · simp only [h,ite_false, if_false,zero_mul]

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
namespace IsingPerceptron

lemma cylinderCross_comm (a b : ℕ →₀ ℝ) : cylinderCross a b = cylinderCross b a := by
  classical
  let n := a.support.sup id + b.support.sup id + 1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinderCross_prefix b a hb]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma cylinderCross_fin_covariance {m : ℕ} (A : Fin m → ℕ →₀ ℝ) (x : Fin m → ℝ) :
    (∑ i, x i • A i).sum (fun _ v => v^2) =
      x ⬝ᵥ (fun i j => cylinderCross (A i) (A j)) *ᵥ x := by
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinderCross_comm (A j) (A i)]
  ring

lemma cylinderCross_matrix_posSemidef {m : ℕ} (A : Fin m → ℕ →₀ ℝ) :
    Matrix.PosSemidef (fun i j => cylinderCross (A i) (A j)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change cylinderCross (A j) (A i) = cylinderCross (A i) (A j)
    exact cylinderCross_comm _ _
  · intro x
    simp only [star_trivial]
    rw [← cylinderCross_fin_covariance]
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariancePositive
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual block covariance for all spectral groups
and all fresh axes. No invertibility is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

lemma continuous_cavityGroupReplicaCovariance {m r : ℕ} (q : ℕ) :
    Continuous (cavityGroupReplicaCovariance (m := m) (r := r) q) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simpa only [cavityGroupReplicaCovariance, ite_eq_left h] using
      (show Continuous (fun Q : Fin m → Matrix (Fin r) (Fin r) ℝ => Q i.1 i.2.1 j.2.1) from by fun_prop)
  · simp only [cavityGroupReplicaCovariance, ite_eq_right h]
    exact continuous_const

lemma cavityGroupReplicaCovariance_posSemidef {m r q : ℕ}
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ) (hQ : ∀ a, (Q a).PosSemidef) :
    (cavityGroupReplicaCovariance q Q).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro ⟨a, i, t⟩ ⟨b, j, s⟩
    by_cases hab : a = b
    · subst b
      by_cases hts : t = s
      · subst s
        simpa only [cavityGroupReplicaCovariance, and_self, ite_true, if_true, star_trivial] using
          (hQ a).isHermitian.apply i j
      · simp [cavityGroupReplicaCovariance, hts, Ne.symm hts]
    · simp [cavityGroupReplicaCovariance, hab, Ne.symm hab]
  · intro v
    have hm (a : Fin m) (i : Fin r) (t : Fin q) :
        (cavityGroupReplicaCovariance q Q *ᵥ v) (a, i, t) =
          ∑ j, Q a i j * v (a, j, t) := by
      simp [Matrix.mulVec, dotProduct, cavityGroupReplicaCovariance,
        Fintype.sum_prod_type, ite_and, ite_mul]
    have he : star v ⬝ᵥ (cavityGroupReplicaCovariance q Q *ᵥ v) =
        ∑ a : Fin m, ∑ t : Fin q,
          star (fun i : Fin r => v (a, i, t)) ⬝ᵥ (Q a *ᵥ fun i => v (a, i, t)) := by
      simp only [dotProduct, Pi.star_apply, star_trivial, Fintype.sum_prod_type]
      simp_rw [hm]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    rw [he]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun t _ =>
      (hQ a).dotProduct_mulVec_nonneg (fun i => v (a, i, t))

lemma continuous_cavitySpectralBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ) :
    Continuous (cavitySpectralBlockCovariance (r := r) q ρ) := by
  apply (continuous_cavityGroupReplicaCovariance q).comp
  fun_prop

lemma cavitySpectralBlockCovariance_posSemidef {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (x : SpectralArray (m + 1)) (hx : SpectralGram x) :
    (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x)).PosSemidef := by
  apply cavityGroupReplicaCovariance_posSemidef
  intro a
  have hh := (hx a.castSucc r).smul (inv_nonneg.mpr (hρ a))
  have he : (fun i j : Fin r => (spectralBlockView (m + 1) r x i j a.castSucc : ℝ) / ρ a) =
      (ρ a)⁻¹ • (fun i j : Fin r => spectralCoordinateArray a.castSucc x i j) := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
      spectralBlockView, spectralCoordinateArray]
  rw [he]
  exact hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCascadeCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of finite cascade covariance paths with a prescribed
diagonal and an independent terminal residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma cavity_cascade_patch_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (h0 : 0 ≤ a 0) {D : ℝ} (hD : a n ≤ D) (σ : ℕ → LabeledLeaf n) :
    GramDiagonal D (diagonalPatch D (cascadeScalarArray n a σ)) := by
  constructor
  · intro r
    let A : Fin r → ℕ →₀ ℝ := fun i =>
      treeFieldCoefficients n (σ i) (fun j => pathAmplitude a j) (fun _ : Unit => 1)
    have hA (i j : Fin r) : cylinderCross (A i) (A j) = cascadeScalarArray n a σ i j := by
      rw [treeField_path_cross n (σ i) (σ j) ha h0]
      simp only [Fintype.sum_unique, mul_one, cascadeScalarArray]
    have hM : (fun i j : Fin r => diagonalPatch D (cascadeScalarArray n a σ) i j) =
        (show Matrix (Fin r) (Fin r) ℝ from fun i j => cylinderCross (A i) (A j)) +
          Matrix.diagonal (fun _ => D - a n) := by
      funext i j
      change (if (i : ℕ) = (j : ℕ) then D else cascadeScalarArray n a σ i j) =
        cylinderCross (A i) (A j) + (if i = j then D - a n else 0)
      simp only [hA, Fin.val_inj]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, if_true, cascadeScalarArray, labeledCommonDepth_self]
        ring
      · simp only [ite_eq_right hij, add_zero]
    rw [hM]
    exact (cylinderCross_matrix_posSemidef A).add
      (Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr hD))
  · intro i
    simp only [diagonalPatch, ite_true, if_true]

lemma cavity_cascade_transformed_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (f : ℝ → ℝ) (hf : Monotone f) (hf0 : 0 ≤ f (a 0)) {D : ℝ} (hfD : f (a n) ≤ D)
    (σ : ℕ → LabeledLeaf n) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r =>
      if i = j then D else f (cascadeScalarArray n a σ i j)) := by
  have h := (cavity_cascade_patch_gram n (hf.comp ha) hf0 hfD σ).1 r
  simpa only [diagonalPatch, cascadeScalarArray, Function.comp_apply, Fin.val_inj] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCascadeCovarianceLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The grouped Gaussian covariance on rounded cascades is positive
semidefinite from monotone synchronized coordinates and diagonal excess. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

theorem cavity_cascade_synchronized_covariance_posSemidef {m r q : ℕ}
    (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1)
    (d : SpectralEntry (m + 1)) (f : Fin (m + 1) → ℝ → Icc (-1 : ℝ) 1)
    (hf : ∀ j, Continuous (f j))
    (hmono : ∀ j : Fin m, Monotone (fun t => (f j.castSucc t : ℝ)))
    (h0 : ∀ j : Fin m, 0 ≤ (f j.castSucc (a 0) : ℝ))
    (hD : ∀ j : Fin m, (f j.castSucc (a n) : ℝ) ≤ (d j.castSucc : ℝ))
    (ρ : Fin m → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray),
      (cavitySpectralBlockCovariance q ρ
        (cavitySynchronizedBlock d f (arrayBlock spinArray r x))).PosSemidef := by
  let C := fun x : JointArray => cavitySpectralBlockCovariance q ρ
    (cavitySynchronizedBlock d f (arrayBlock spinArray r x))
  have hC : Continuous C := (continuous_cavitySpectralBlockCovariance q ρ).comp
    ((continuous_cavitySynchronizedBlock d f hf).comp (by unfold arrayBlock spinArray; fun_prop))
  have hMap : Measurable (fun σ : ℕ → LabeledLeaf n =>
      compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) :=
    continuous_compactScalarArray.measurable.comp
      ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))
  change ∀ᵐ x ∂(cascadeReplicaLaw n b).map (fun σ =>
    compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))), (C x).PosSemidef
  apply (ae_map_iff hMap.aemeasurable (Matrix.posSemidef_is_closed.preimage hC).measurableSet).mpr
  apply ae_of_all
  intro σ
  change (cavitySpectralBlockCovariance q ρ (cavitySynchronizedBlock d f
    (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ)))))).PosSemidef
  apply cavityGroupReplicaCovariance_posSemidef
  intro j
  have h := (cavity_cascade_transformed_gram n ha (fun t => (f j.castSucc t : ℝ))
    (hmono j) (h0 j) (hD j) σ r).smul (inv_nonneg.mpr (hρ j))
  have he : (fun i k : Fin r =>
      (cavitySynchronizedBlock d f
        (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ)))))
        i k j.castSucc / ρ j) =
      (ρ j)⁻¹ • (fun i k : Fin r =>
        if i = k then (d j.castSucc : ℝ) else (f j.castSucc (cascadeScalarArray n a σ i k) : ℝ)) := by
    funext i k
    simp only [cavitySynchronizedBlock, arrayBlock, cascadeCompact_spin n ha ha0 ha1 σ,
      Pi.smul_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst k
      simp only [ite_true, if_true]
      ring
    · simp only [ite_eq_right hik, diagonalPatch, Fin.val_inj]
      ring
  rw [he]
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupBlockGaussian
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian marking of the physical spectral-group block. The variance
is the projected overlap divided by the group proportion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

lemma continuous_cavityGroupBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ) :
    Continuous (cavityGroupBlockCovariance (r := r) q ρ) := by
  apply (continuous_cavityGroupReplicaCovariance q).comp
  fun_prop

lemma cavityGroupBlockCovariance_posSemidef {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (x : SpectralArray (m + 1)) (hx : SpectralGram x) :
    (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x)).PosSemidef :=
  cavitySpectralBlockCovariance_posSemidef ρ hρ x hx

lemma cavity_cascade_group_covariance_posSemidef {m r q : ℕ}
    (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1)
    (d : SpectralEntry m) (f : Fin m → ℝ → Icc (-1 : ℝ) 1)
    (hf : ∀ j, Continuous (f j)) (hmono : ∀ j, Monotone (fun t => (f j t : ℝ)))
    (h0 : ∀ j, 0 ≤ (f j (a 0) : ℝ)) (hD : ∀ j, (f j (a n) : ℝ) ≤ (d j : ℝ))
    (ρ : Fin m → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray),
      (cavityGroupBlockCovariance q ρ (cavitySynchronizedBlock d f (arrayBlock spinArray r x))).PosSemidef := by
  let z : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  let d' : SpectralEntry (m + 1) := Fin.lastCases z d
  let f' : Fin (m + 1) → ℝ → Icc (-1 : ℝ) 1 := Fin.lastCases (fun _ => z) f
  have hf' : ∀ j, Continuous (f' j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f', Fin.lastCases_last] using
        (continuous_const : Continuous (fun _ : ℝ => z))
    · simpa only [f', Fin.lastCases_castSucc] using hf i
  have he := cavity_cascade_synchronized_covariance_posSemidef (r := r) (q := q)
    n b a ha ha0 ha1 d' f' hf'
    (by simpa only [f', Fin.lastCases_castSucc] using hmono)
    (by simpa only [f', Fin.lastCases_castSucc] using h0)
    (by simpa only [f', d', Fin.lastCases_castSucc] using hD) ρ hρ
  simpa only [cavitySpectralBlockCovariance, cavityGroupBlockCovariance,
    cavitySynchronizedBlock, f', d', Fin.lastCases_castSucc] using he

theorem cavity_canonical_marked_group_block_tendsto {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ a, 0 ≤ d a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = d a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0)
    (r q : ℕ) (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q hP hn
    let B := fun x : JointArray => cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
      (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x)
    Tendsto (fun n => ∫ x, ∫ z, F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B x))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 (∫ x, ∫ z, F (cavitySpectralGroupBlock m r x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x))
        ∂(Q : Measure (SpectralArray (m + 1))))) := by
  intro p B
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance q ρ x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance q ρ)⟩
  have ht := cavity_canonical_group_block_tendsto Q hgg hG d hd0 hd hE hP hn
    ρ eig hρ hρsum hoff hdiag r H
  change Tendsto (fun n => ∫ x, H (B x)
    ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
    atTop (𝓝 (∫ x, H (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1))))) at ht
  have hS n : ∀ᵐ x ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray),
      (cavityGroupBlockCovariance q ρ (B x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) (uniformCellAverage p n)
      (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
      (cavityCanonicalDiagonal ρ eig hρ hρsum p) (cavityCanonicalLabel ρ eig hρ hρsum p)
      (continuous_cavityCanonicalLabel ρ eig hρ hρsum p)
      (cavityCanonicalCoordinate_monotone ρ eig hρ hρsum p)
      (fun a => cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p a _)
      (fun a => cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p a _)
      ρ (fun a => (hρ a).le)
  have heS n : (∫ x, H (B x)
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray)) =
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray) :=
    integral_congr_ae ((hS n).mono fun x hx => hExt _ _ hx)
  have heQ : (∫ x, H (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ x, ∫ z, F (cavitySpectralGroupBlock m r x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x))
        ∂(Q : Measure (SpectralArray (m + 1))) :=
    integral_congr_ae (hG.mono fun x hx => hExt _ _
      (cavityGroupBlockCovariance_posSemidef ρ (fun a => (hρ a).le) x hx))
  simpa only [heS, heQ] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySoftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous cutoffs for finite-replica passage. Their removal costs
only the discarded mass, including the zero-normalizer convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavityRadialCutoff_eq_one {B x : ℝ} (hx : x ≤ B) : cavityRadialCutoff B x = 1 := by
  unfold cavityRadialCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cavityRadialCutoff_eq_zero {B x : ℝ} (hx : B + 1 ≤ x) : cavityRadialCutoff B x = 0 := by
  unfold cavityRadialCutoff
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalContinuity
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recalculating the canonical covariance after an L1 path
approximation changes every covariance endpoint uniformly. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityCanonicalCoordinate_uniform_of_L1 {m : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (a : Fin m) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a t -
        cavityCanonicalCoordinate ρ eig hρ hρsum p a t| < ε := by
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (continuousOn_projectedResolventDerivative ρ eig hρ hρsum a (c := 1))
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  filter_upwards [hL.eventually (Iio_mem_nhds hδ)] with n hn
  have hden (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |spectralPathDensity ρ eig hρ hρsum (q n) a r -
        spectralPathDensity ρ eig hρ hρsum p a r| < ε / 2 := by
    apply hmod (deficit (q n) r) (deficit_mem_unit (q n) hr)
      (deficit p r) (deficit_mem_unit p hr)
    exact (abs_deficit_sub_path_le (q n) p r).trans_lt hn
  intro t
  let c := Set.projIcc 0 1 zero_le_one t
  have hiq := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum (q n) a c.property
  have hip := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a c.property
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (c : ℝ)) (C := ε / 2)
    (f := fun r => spectralPathDensity ρ eig hρ hρsum (q n) a r -
      spectralPathDensity ρ eig hρ hρsum p a r) (fun r hr => by
        rw [uIoc_of_le c.property.1] at hr
        exact (hden r ⟨hr.1.le, hr.2.trans c.property.2⟩).le)
  change |(∫ r in 0..(c : ℝ), spectralPathDensity ρ eig hρ hρsum (q n) a r) -
    ∫ r in 0..(c : ℝ), spectralPathDensity ρ eig hρ hρsum p a r| < ε
  rw [← intervalIntegral.integral_sub hiq hip]
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg c.property.1] at hb
  have hc : ε / 2 * (c : ℝ) ≤ ε / 2 := by nlinarith [c.property.2]
  exact (hb.trans hc).trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRecalculatedLabels
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recalculating the covariance from a nearby path is uniform in every
finite overlap block. Thus it is harmless before taking cascade limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_recalculated_label_test_uniform {m r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (F : SpectralBlock m r →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : Fin r → Fin r → ℝ,
      |F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
          (cavityCanonicalLabel ρ eig hρ hρsum (q n)) x) -
        F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
          (cavityCanonicalLabel ρ eig hρ hρsum p) x)| < ε := by
  intro ε hε
  have hu := (isCompact_univ : IsCompact (univ : Set (SpectralBlock m r))).uniformContinuousOn_of_continuous
    F.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have he : ∀ᶠ n in atTop, ∀ a : Fin m, ∀ t : ℝ,
      |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a t -
        cavityCanonicalCoordinate ρ eig hρ hρsum p a t| < δ :=
    eventually_all.mpr (fun a => cavityCanonicalCoordinate_uniform_of_L1 ρ eig hρ hρsum p q hL a δ hδ)
  filter_upwards [he] with n hn
  intro x
  apply hmod _ (mem_univ _) _ (mem_univ _)
  apply (dist_pi_lt_iff hδ).mpr
  intro i
  apply (dist_pi_lt_iff hδ).mpr
  intro j
  apply (dist_pi_lt_iff hδ).mpr
  intro a
  by_cases hij : i = j
  · simp only [cavitySynchronizedBlock, ite_eq_left hij]
    change |spectralGroupDiagonal ρ eig hρ hρsum (q n) a -
      spectralGroupDiagonal ρ eig hρ hρsum p a| < δ
    simpa only [cavityCanonicalCoordinate, spectralGroupDiagonal,
      Set.projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)] using hn a 1
  · simp only [cavitySynchronizedBlock, ite_eq_right hij]
    change |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a (x i j) -
      cavityCanonicalCoordinate ρ eig hρ hρsum p a (x i j)| < δ
    exact hn a (x i j)

theorem cavity_recalculated_label_integral_error {m r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (P : ℕ → ProbabilityMeasure JointArray) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n => ∫ x,
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
        (cavityCanonicalLabel ρ eig hρ hρsum (q n)) (arrayBlock spinArray r x)) -
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
        (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x))
      ∂(P n : Measure JointArray)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_recalculated_label_test_uniform ρ eig hρ hρsum p q hL F
    (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := (P n : Measure JointArray))
    (f := fun x =>
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
        (cavityCanonicalLabel ρ eig hρ hρsum (q n)) (arrayBlock spinArray r x)) -
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
        (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x)))
    (C := ε / 2) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hn _).le)
  simp only [probReal_univ, mul_one] at hb
  exact hb.trans_lt (half_lt_self hε)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRecalculatedGaussian
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-cascade Gaussian covariance can be recalculated with the
approximating path before taking its replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_recalculated_gaussian_cascade_error {m r k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (q n) x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B (q n) x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  let P n := cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n)
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k ρ x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k ρ)⟩
  have hpos (n : ℕ) (p' : OverlapPath) : ∀ᵐ x ∂(P n : Measure JointArray),
      (cavityGroupBlockCovariance k ρ (B p' x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) (uniformCellAverage p n)
      (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
      (cavityCanonicalDiagonal ρ eig hρ hρsum p') (cavityCanonicalLabel ρ eig hρ hρsum p')
      (continuous_cavityCanonicalLabel ρ eig hρ hρsum p')
      (cavityCanonicalCoordinate_monotone ρ eig hρ hρsum p')
      (fun a => cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p' a _)
      (fun a => cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p' a _)
      ρ (fun a => (hρ a).le)
  have hi (n : ℕ) (p' : OverlapPath) : Integrable (fun x => H (B p' x)) (P n : Measure JointArray) := by
    let J : JointArray →ᵇ ℝ := H.compContinuous
      ⟨B p', (continuous_cavitySynchronizedBlock _ _
        (continuous_cavityCanonicalLabel ρ eig hρ hρsum p')).comp (by
          unfold arrayBlock spinArray
          fun_prop)⟩
    exact J.integrable _
  have he (n : ℕ) (p' : OverlapPath) :
      (∫ x, H (B p' x) ∂(P n : Measure JointArray)) =
        ∫ x, ∫ z, F (B p' x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p' x))
          ∂(P n : Measure JointArray) :=
    integral_congr_ae ((hpos n p').mono (fun x hx => hExt _ _ hx))
  have ht := cavity_recalculated_label_integral_error ρ eig hρ hρsum p q hL P H
  change Tendsto (fun n => ∫ x, H (B (q n) x) - H (B p x) ∂(P n : Measure JointArray))
    atTop (𝓝 0) at ht
  have hid n : (∫ x, H (B (q n) x) - H (B p x) ∂(P n : Measure JointArray)) =
      (∫ x, ∫ z, F (B (q n) x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B (q n) x))
        ∂(P n : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p x))
        ∂(P n : Measure JointArray) := by
    rw [integral_sub (hi n (q n)) (hi n p), he, he]
  simpa only [hid] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCascadeMatch
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh Haar field and the recalculated finite cascade have matching
bounded spectral-group replica tests. The common limit is identified by GG
and the Ward equations, rather than assumed as an auxiliary cascade law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavityGroupBlockOfBlock {m r : ℕ} :
    Continuous (cavityGroupBlockOfBlock (m := m) (r := r)) := by
  unfold cavityGroupBlockOfBlock
  fun_prop

theorem cavity_haar_recalculated_cascade_match {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (pseq : ℕ → OverlapPath)
    (hLp : Tendsto (fun k => ∫ s, |pseq k s - spectralSpinQuantilePath Q₀ hP hn s| ∂pathMeasure)
      atTop (𝓝 0))
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun k =>
      (∫ x, ∫ U, F (cavitySpectralGroupBlock m r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) -
      ∫ x, ∫ z, F (B (pseq k) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B (pseq k) x))
        ∂(cascadeCompactLaw k (uniformExponent k) (uniformCellAverage p k) : Measure JointArray))
      atTop (𝓝 0) := by
  intro p B
  let F' : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun z => (cavityGroupBlockOfBlock z.1, z.2),
      (continuous_cavityGroupBlockOfBlock.comp continuous_fst).prodMk continuous_snd⟩
  have hh := cavity_spectral_haar_test_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim F'
  have hc := cavity_canonical_marked_group_block_tendsto Q₀ hgg hG d hd0 hd hE hP hn
    ρ eig hρ hρsum hoff hdiag r q F
  have he := cavity_recalculated_gaussian_cascade_error ρ eig hρ hρsum p pseq hLp F
  have hdiff := hh.sub hc
  have hout := hdiff.sub he
  simpa only [F', BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    cavityGroupBlockOfBlock_view, cavityGroupBlockCovariance, cavitySpectralBlockCovariance,
    cavitySpectralGroupBlock, spectralBlockView,
    sub_self, sub_sub_sub_cancel_right, p, B] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockMarkedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian marks attached to a sampled spectral block. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

variable {m r q : ℕ} {E : Type*} [MeasurableSpace E]

lemma cavityBlockMarkedLaw_integral (Q : ProbabilityMeasure E) (ρ : Fin m → ℝ)
    (b : E → SpectralBlock m r) (hb : Measurable b)
    (f : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ p, f p ∂(cavityBlockMarkedLaw (q := q) Q ρ b : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))) =
      ∫ x, ∫ y, f (b x,y) ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (b x))
        ∂(Q : Measure E) := by
  let Z := SpectralBlock m r × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ
  let g : Z → ℝ := fun p => ∫ y, f (p.1,y) ∂multivariateGaussian 0 p.2
  have hfm : Measurable (fun p : Z × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) =>
      f (p.1.1,p.2)) := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have hg : Measurable g :=
    hfm.stronglyMeasurable.integral_kernel_prod_right' (κ := cavityGaussianKernel) |>.measurable
  have hmap : Measurable (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))) :=
    hb.prodMk ((continuous_cavityGroupBlockCovariance q ρ).measurable.comp hb)
  unfold cavityBlockMarkedLaw
  rw [ProbabilityMeasure.mapAE_eq Q hmap.aemeasurable]
  rw [cavityGaussianMarkedLaw_integral _ f hf hbound]
  change (∫ p, g p ∂((Q : Measure E).map
    (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))))) = _
  rw [integral_map hmap.aemeasurable hg.aestronglyMeasurable]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWeakApproximation
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable tests can be passed through a weak limit when
continuous error envelopes have vanishing integral in the limiting law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_continuous_approximation_error {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (f : E → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (F G : E →ᵇ ℝ)
    (herror : ∀ x, |f x-F x| ≤ G x) :
    |(∫ x, f x ∂(μ : Measure E)) - ∫ x, F x ∂(μ : Measure E)| ≤
      ∫ x, G x ∂(μ : Measure E) := by
  have hfi : Integrable f (μ : Measure E) := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hF : Integrable (fun x => F x) (μ : Measure E) := F.integrable (μ := (μ : Measure E))
  have hG : Integrable (fun x => G x) (μ : Measure E) := G.integrable (μ := (μ : Measure E))
  rw [← integral_sub hfi hF]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hfi.sub hF).abs hG herror)

theorem cavity_weak_integral_of_continuous_approximation {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (f : E → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (F G : ℕ → E →ᵇ ℝ) (herror : ∀ j x, |f x-F j x| ≤ G j x)
    (hG : Tendsto (fun j => ∫ x, G j x ∂(ν : Measure E)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := (hG.eventually (gt_mem_nhds (show (0 : ℝ) < ε/8 by positivity))).exists
  have hFj := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (F j)
  have hGj := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (G j)
  have hFclose := hFj.eventually (Metric.ball_mem_nhds
    (∫ x, F j x ∂(ν : Measure E)) (show 0 < ε/4 by positivity))
  have hGclose := hGj.eventually (Metric.ball_mem_nhds
    (∫ x, G j x ∂(ν : Measure E)) (show 0 < ε/4 by positivity))
  filter_upwards [hFclose,hGclose] with n hnF hnG
  rw [Real.dist_eq] at hnF hnG ⊢
  have heμ := cavity_continuous_approximation_error (μ n) f hf hb (F j) (G j) (herror j)
  have heν := cavity_continuous_approximation_error ν f hf hb (F j) (G j) (herror j)
  have htri := abs_sub_le
    (∫ x, f x ∂(μ n : Measure E)) (∫ x, F j x ∂(μ n : Measure E))
    (∫ x, f x ∂(ν : Measure E))
  have htri' := abs_sub_le
    (∫ x, F j x ∂(μ n : Measure E)) (∫ x, F j x ∂(ν : Measure E))
    (∫ x, f x ∂(ν : Measure E))
  rw [abs_sub_comm (∫ x, F j x ∂(ν : Measure E))] at htri'
  linarith [(abs_le.mp (le_of_lt hnG)).2]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundaryCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous upper and lower approximations to a hard radial cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavityBoundaryUpper_one {r B x : ℝ} (hr : 0 ≤ r) (hx : x ≤ B) :
    cavityBoundaryUpper r B x = 1 :=
  cavityRadialCutoff_eq_one (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hx))

lemma cavityBoundaryLower_zero {r B x : ℝ} (hr : 0 ≤ r) (hx : B ≤ x) :
    cavityBoundaryLower r B x = 0 :=
  cavityRadialCutoff_eq_zero (by
    have := mul_nonneg hr (sub_nonneg.mpr hx)
    linarith)

lemma cavityBoundaryGap_mem {r B x : ℝ} (hr : 0 ≤ r) :
    cavityBoundaryGap r B x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ≤ B
  · rw [cavityBoundaryGap, cavityBoundaryUpper_one hr hx]
    have hh := cavityRadialCutoff_mem 0 (r*(x-B)+1)
    change 0 ≤ 1-cavityRadialCutoff 0 (r*(x-B)+1) ∧
      1-cavityRadialCutoff 0 (r*(x-B)+1) ≤ 1
    constructor <;> linarith [hh.1,hh.2]
  · rw [cavityBoundaryGap, cavityBoundaryLower_zero hr (le_of_not_ge hx), sub_zero]
    exact cavityRadialCutoff_mem 0 (r*(x-B))

lemma cavityBoundaryUpper_error {r B x a : ℝ} (hr : 0 ≤ r) :
    |(if x ≤ B then a else 0)-a*cavityBoundaryUpper r B x| ≤
      |a| *cavityBoundaryGap r B x := by
  by_cases hx : x ≤ B
  · rw [ite_eq_left hx, cavityBoundaryUpper_one hr hx, mul_one, sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg _) (cavityBoundaryGap_mem hr).1
  · rw [ite_eq_right hx, zero_sub, abs_neg, abs_mul, cavityBoundaryGap,
      cavityBoundaryLower_zero hr (le_of_not_ge hx), sub_zero]
    change |a| * |cavityRadialCutoff 0 (r*(x-B))| ≤ |a| * cavityRadialCutoff 0 (r*(x-B))
    rw [abs_of_nonneg (cavityRadialCutoff_mem 0 (r*(x-B))).1]

lemma cavityBoundaryGap_tendsto {B x : ℝ} (hx : x ≠ B) :
    Tendsto (fun n : ℕ => cavityBoundaryGap ((n : ℝ)+1) B x) atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, cavityBoundaryGap ((n : ℝ)+1) B x = 0 := by
    rcases lt_or_gt_of_ne hx with hx | hx
    · have hg : 0 < B-x := sub_pos.mpr hx
      have hn : ∀ᶠ n : ℕ in atTop, 1/(B-x) < (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [hn] with n hn
      have hp : 1 < (n : ℝ)*(B-x) := (div_lt_iff₀ hg).mp hn
      have hu := cavityBoundaryUpper_one (by positivity : 0 ≤ (n : ℝ)+1) hx.le
      have hl : cavityBoundaryLower ((n : ℝ)+1) B x = 1 :=
        cavityRadialCutoff_eq_one (by nlinarith)
      rw [cavityBoundaryGap,hu,hl,sub_self]
    · have hg : 0 < x-B := sub_pos.mpr hx
      have hn : ∀ᶠ n : ℕ in atTop, 1/(x-B) < (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [hn] with n hn
      have hp : 1 < (n : ℝ)*(x-B) := (div_lt_iff₀ hg).mp hn
      have hu : cavityBoundaryUpper ((n : ℝ)+1) B x = 0 :=
        cavityRadialCutoff_eq_zero (by nlinarith)
      have hl := cavityBoundaryLower_zero (by positivity : 0 ≤ (n : ℝ)+1) hx.le
      rw [cavityBoundaryGap,hu,hl,sub_self]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteExponentLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A depth-n cascade only uses its first n exponents. This identifies
the uniform approximation convention with the field-chain convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_labeled_exponent_congr (n : ℕ) (b c : ℕ → ℝ)
    (hbc : ∀ i, i < n → b i = c i) :
    labeledCascadeLaw n b = labeledCascadeLaw n c := by
  induction n generalizing b c with
  | zero => rfl
  | succ n ih =>
    have h0 := hbc 0 (Nat.zero_lt_succ n)
    have ht := ih (fun i => b (i + 1)) (fun i => c (i + 1))
      (fun i hi => hbc (i + 1) (by omega))
    apply Subtype.ext
    change (labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun i => b (i + 1)) : Measure (LabeledTree n))))) =
      (labeledPoissonLaw (intensityComponents (powerIntensity (c 0)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun i => c (i + 1)) : Measure (LabeledTree n)))))
    rw [h0, ht]

lemma cavity_cascade_exponent_congr (n : ℕ) (b c a : ℕ → ℝ)
    (hbc : ∀ i, i < n → b i = c i) :
    cascadeCompactLaw n b a = cascadeCompactLaw n c a := by
  simp only [cascadeCompactLaw, cascadeReplicaLaw, cavity_labeled_exponent_congr n b c hbc]
  rfl

lemma cavity_uniform_chain_exponent (n i : ℕ) (hi : i < n) :
    uniformExponent n i = chainExponent (uniformCut n) i := by
  rw [chainExponent_apply _ hi]
  simp only [uniformExponent, uniformCut, Nat.cast_add, Nat.cast_one]

lemma cavity_uniform_chain_law (n : ℕ) (a : ℕ → ℝ) :
    cascadeCompactLaw n (uniformExponent n) a =
      cascadeCompactLaw n (chainExponent (uniformCut n)) a :=
  cavity_cascade_exponent_congr n _ _ a (cavity_uniform_chain_exponent n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarMarkedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint probability laws for the physical fresh Haar marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {m r q : ℕ} {N : Fin m → ℕ} {X L : Type*}
  [MeasurableSpace X] [MetricSpace L] [MeasurableSpace L]
  [BorelSpace L] [SecondCountableTopology L]

omit [MetricSpace L] [BorelSpace L] [SecondCountableTopology L] in
lemma cavityHaarMarkedLaw_integral (P : Measure X) [IsProbabilityMeasure P]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (f : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂(cavityHaarMarkedLaw P μ l hl v hv A₀ : Measure _)) =
      ∫ x, ∫ U, f (l x, cavityGroupMatrixProjection (v x) (cavityGroupHaarFrames A₀ U))
        ∂Measure.pi μ ∂P := by
  have hi : Integrable (fun p => f (cavityHaarMarkedMap l v A₀ p))
      (P.prod (Measure.pi μ)) :=
    Integrable.of_bound ((hf.comp (measurable_cavityHaarMarkedMap l hl v hv A₀)).aestronglyMeasurable)
      C (ae_of_all _ fun p => hb _)
  change (∫ x, f x ∂(P.prod (Measure.pi μ)).map (cavityHaarMarkedMap l v A₀)) = _
  rw [integral_map
    (measurable_cavityHaarMarkedMap l hl v hv A₀).aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximum selected-coordinate norm gives exactly the simultaneous
spatial restriction of every replica. A common divergent sequence of
radii avoids the boundaries of all the limiting replica laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavityReplicaRadius {m r q d : ℕ} {L : Type*} [TopologicalSpace L]
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    Continuous (cavityReplicaRadius (L := L) J) :=
  (J.continuous.comp continuous_snd).norm

lemma cavityReplicaRadius_le_iff {m r q d : ℕ} {L : Type*}
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (p : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    {B : ℝ} (hB : 0 ≤ B) :
    cavityReplicaRadius J p ≤ B ↔ ∀ i, 1 + ‖J p.2 i‖^2 ≤ 1+B^2 := by
  rw [cavityReplicaRadius, pi_norm_le_iff_of_nonneg hB]
  apply forall_congr'
  intro i
  constructor
  · intro h
    have hn := sq_le_sq₀ (norm_nonneg (J p.2 i)) hB |>.mpr h
    linarith
  · intro h
    exact (sq_le_sq₀ (norm_nonneg (J p.2 i)) hB).mp (by linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hard spatial restrictions of the actual capped spin replica test.
Their only discontinuity lies on the maximum-radius boundary. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavityRestrictedSpinReplicaValue_eq {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityRestrictedSpinReplicaValue K L C T B J π F =
      {z | cavityReplicaRadius J z ≤ B}.indicator
        (cavityCappedSpinReplicaValue K L C T J π F) := by
  classical
  funext z
  by_cases hz : cavityReplicaRadius J z ≤ B
  · rw [Set.indicator_of_mem (show z ∈ {z | cavityReplicaRadius J z ≤ B} from hz)]
    unfold cavityRestrictedSpinReplicaValue cavityCappedSpinReplicaValue
    have hi := (cavityReplicaRadius_le_iff J z hB).mp hz
    simp only [hi, ite_true, if_true]
  · rw [Set.indicator_of_notMem (show z ∉ {z | cavityReplicaRadius J z ≤ B} from hz)]
    have hnot : ¬ ∀ i, 1+‖J z.2 i‖^2 ≤ 1+B^2 :=
      fun hi => hz ((cavityReplicaRadius_le_iff J z hB).mpr hi)
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    have hp (ε : Fin r → Spin k) :
        (∏ j, if 1+‖J z.2 j‖^2 ≤ 1+B^2 then
          Real.exp (min (cavityLogFactor K L C (J z.2 j) (ε j)) T) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    simp only [cavityRestrictedSpinReplicaValue,hp,zero_mul,integral_zero]

lemma measurable_cavityRestrictedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityRestrictedSpinReplicaValue K L C T B J π F) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  exact (cavityCappedSpinReplicaTest K L C T J π F).continuous.measurable.indicator
    (measurableSet_le (continuous_cavityReplicaRadius J).measurable measurable_const)

lemma cavityRestrictedSpinReplicaValue_bound {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    ‖cavityRestrictedSpinReplicaValue K L C T B J π F z‖ ≤ (Real.exp T)^r * ‖F‖ := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  by_cases hz : cavityReplicaRadius J z ≤ B
  · rw [Set.indicator_of_mem (show z ∈ {z | cavityReplicaRadius J z ≤ B} from hz)]
    exact cavityCappedSpinReplicaValue_bound K L C T J π F z
  · rw [Set.indicator_of_notMem (show z ∉ {z | cavityReplicaRadius J z ≤ B} from hz),norm_zero]
    positivity

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWeakRadialCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence of a bounded continuous replica test restricted by
a continuous radius, at any radius with zero limiting boundary mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_weak_radial_cutoff_integral {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν)) (R : E → ℝ) (hR : Continuous R)
    (F : E →ᵇ ℝ) (B : ℝ)
    (hnull : (ν : Measure E) {x | R x=B}=0) :
    Tendsto (fun n => ∫ x, {x | R x ≤ B}.indicator (fun x => F x) x ∂(μ n : Measure E))
      atTop (𝓝 (∫ x, {x | R x ≤ B}.indicator (fun x => F x) x ∂(ν : Measure E))) := by
  let U (j : ℕ) := cavityBoundaryProfile R hR ((j : ℝ)+1) B 0
  let L (j : ℕ) := cavityBoundaryProfile R hR ((j : ℝ)+1) B 1
  let A (j : ℕ) : E →ᵇ ℝ := F*U j
  let G (j : ℕ) : E →ᵇ ℝ := BoundedContinuousFunction.const E ‖F‖*(U j-L j)
  have hg j x : G j x = ‖F‖*cavityBoundaryGap ((j : ℝ)+1) B (R x) := by
    simp only [G,U,L,cavityBoundaryProfile,BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup,cavityBoundaryGap,
      cavityBoundaryUpper,cavityBoundaryLower,add_zero]
  have hfm : Measurable ({x | R x ≤ B}.indicator (fun x => F x)) :=
    F.continuous.measurable.indicator (measurableSet_le hR.measurable measurable_const)
  have hfb x : |{x | R x ≤ B}.indicator (fun x => F x) x| ≤ ‖F‖ := by
    by_cases hx : R x ≤ B
    · rw [Set.indicator_of_mem (show x ∈ {y | R y ≤ B} from hx)]
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm x
    · rw [Set.indicator_of_notMem (show x ∉ {y | R y ≤ B} from hx),abs_zero]
      exact norm_nonneg F
  apply cavity_weak_integral_of_continuous_approximation μ ν hμ _ hfm hfb A G
  · intro j x
    rw [hg]
    have he := cavityBoundaryUpper_error (r := (j : ℝ)+1) (B := B) (x := R x)
      (a := F x) (by positivity)
    have hb := mul_le_mul_of_nonneg_right (F.norm_coe_le_norm x)
      (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).1
    apply (show |{x | R x ≤ B}.indicator (fun x => F x) x - A j x| ≤
      |F x| *cavityBoundaryGap ((j : ℝ)+1) B (R x) from ?_).trans hb
    simpa only [A,U,cavityBoundaryProfile,BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup,add_zero,
      Set.indicator_apply,Set.mem_ofPred_eq,cavityBoundaryUpper] using he
  · have hneq : ∀ᵐ x ∂(ν : Measure E), R x ≠ B := compl_mem_ae_iff.mpr hnull
    have hlim : ∀ᵐ x ∂(ν : Measure E), Tendsto (fun j => G j x) atTop (𝓝 0) := by
      filter_upwards [hneq] with x hx
      simp_rw [hg]
      simpa only [mul_zero] using tendsto_const_nhds.mul (cavityBoundaryGap_tendsto hx)
    have hb j x : ‖G j x‖ ≤ ‖F‖ := by
      rw [hg,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg F),
        abs_of_nonneg (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).1]
      exact mul_le_of_le_one_right (norm_nonneg F)
        (cavityBoundaryGap_mem (r := (j : ℝ)+1) (B := B) (x := R x) (by positivity)).2
    have ht := tendsto_integral_of_dominated_convergence (fun _ : E => ‖F‖)
      (fun j => (G j).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun j => ae_of_all _ (hb j)) hlim
    simpa only [integral_zero] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedSpinLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of hard-restricted spin replica numerators follows from
the joint marked laws at the common continuity radii. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_restricted_spin_replica_tendsto {m r q d k : ℕ}
    (Q : ℕ → ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (Q₀ : ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (hQ : Tendsto Q atTop (𝓝 Q₀))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (hnull : (Q₀ : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius J z = B} = 0) :
    Tendsto (fun n => ∫ z, cavityRestrictedSpinReplicaValue K L C T B J π F z
        ∂(Q n : Measure _)) atTop
      (𝓝 (∫ z, cavityRestrictedSpinReplicaValue K L C T B J π F z
        ∂(Q₀ : Measure _))) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  exact cavity_weak_radial_cutoff_integral Q Q₀ hQ (cavityReplicaRadius J)
    (continuous_cavityReplicaRadius J) (cavityCappedSpinReplicaTest K L C T J π F) B hnull

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralMarkedLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical spectral replica law with its fresh Haar coordinates
converges as a probability law, before any radius restriction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_haar_marked_law_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
 :
    Tendsto (fun k => cavityHaarMarkedLaw (P k) (μ k)
      (fun x => cavitySpectralGroupBlock m r (a k x))
      ((continuous_cavitySpectralGroupBlock m r).measurable.comp (ha k))
      (v k) (hvM k) (A₀ k)) atTop
      (𝓝 (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x),
    cavityBlockMarkedLaw_integral _ _ _ (continuous_cavitySpectralGroupBlock m r).measurable
      _ F.continuous.measurable (fun x => F.norm_coe_le_norm x)]
  let F' : SpectralBlock (m+1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun z => (cavityGroupBlockOfBlock z.1,z.2),
      (continuous_cavityGroupBlockOfBlock.comp continuous_fst).prodMk continuous_snd⟩
  have ht := cavity_spectral_haar_test_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ hρ hρs hρ0 hcov Q Q₀ hQ hlim F'
  simpa only [F',BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    cavityGroupBlockOfBlock_view,cavityGroupBlockCovariance,cavitySpectralBlockCovariance,
    cavitySpectralGroupBlock,spectralBlockView] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarStrictCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fresh-Haar replica tests match strict interior finite
cascades with recalculated covariances. This supplies nondegenerate
finite approximants even when the limiting quantile has tied levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_strict_cascade_match {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun k =>
      (∫ x, ∫ U, F (cavitySpectralGroupBlock m r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) -
      ∫ x, ∫ z, F (B (cavityStrictUniformPath p k) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B (cavityStrictUniformPath p k) x))
        ∂(cascadeCompactLaw k (chainExponent (uniformCut k))
          (fun i => cavityStrictUniformLevels p k (cavityFiniteLevel k i)) : Measure JointArray))
      atTop (𝓝 0) := by
  intro p B
  have hLp : Tendsto (fun _ : ℕ => ∫ s, |p s - p s| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hb := cavity_haar_recalculated_cascade_match N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
    (fun _ => p) hLp F
  have hs := cavity_strict_recalculated_gaussian_error ρ eig hρ hρsum p F
  simpa only [sub_sub_sub_cancel_right, sub_self, B, p, cavity_uniform_chain_law] using hb.sub hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictMarkedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite strict-cascade law with its recalculated Gaussian
marks, including the spectral block labels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma continuous_cavityPathReplicaBlock {m r : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (cavityPathReplicaBlock (r := r) ρ eig hρ hsum p) :=
  (continuous_cavitySynchronizedBlock _ _ (continuous_cavityCanonicalLabel ρ eig hρ hsum p)).comp
    (by unfold arrayBlock spinArray; fun_prop)

lemma cavityStrictMarkedLaw_integral {m r q : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) (n : ℕ)
    (f : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, f z ∂(cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hsum p n : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))) =
      ∫ x, ∫ y, f (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n) x,y)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ
          (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n) x))
        ∂(cascadeCompactLaw n (chainExponent (uniformCut n))
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray) :=
  cavityBlockMarkedLaw_integral _ _ _
    (continuous_cavityPathReplicaBlock _ _ _ _ _).measurable f hf hbound

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictMarkedLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict finite Gaussian cavity laws and the physical Haar marks
have the same weak limit. The identification uses the proved spectral
GG and Ward consequences through the finite cascade comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_strict_marked_law_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
 :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k => cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hρsum p k)
      atTop (𝓝 (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r))) := by
  intro p
  have hH := cavity_spectral_haar_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram
    v hvM C hv ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hH F
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x)] at ht
  have hdifference := cavity_haar_strict_cascade_match N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag F
  have hout := ht.sub hdifference
  simp_rw [cavityStrictMarkedLaw_integral ρ eig hρ hρsum p _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x)]
  simpa only [sub_sub_cancel,sub_zero,p,cavityPathReplicaBlock] using hout

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedSpinMatch
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hard-restricted physical Haar spin moments match the strict
finite Gaussian cavity moments. The cutoff is taken at a common
continuity radius of the limiting marked law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_strict_restricted_spin_match_oai {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)

    {dim kspin : ℕ}
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin dim)))
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    (hnull : (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r) : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius J z = B} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ x, ∫ U, cavityRestrictedSpinReplicaValue K L Cspin T B J π F
        (cavitySpectralGroupBlock m r (a k x),
          cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k) ∂P k) -
      ∫ z, cavityRestrictedSpinReplicaValue K L Cspin T B J π F z
        ∂(cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hρsum p k : Measure
          (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))))
      atTop (𝓝 0) := by
  intro p
  have hH := cavity_spectral_haar_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram
    v hvM C hv ρs ρ hρlim hρs hρ hcov Q Q₀ hQ hlim
  have hS := cavity_strict_marked_law_tendsto N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
  have hHR := cavity_restricted_spin_replica_tendsto _ _ hH K L Cspin T hB J π F hnull
  have hSR := cavity_restricted_spin_replica_tendsto _ _ hS K L Cspin T hB J π F hnull
  have hout := hHR.sub hSR
  simp only [sub_self] at hout
  simp_rw [cavityHaarMarkedLaw_integral _ _ _ _ _ _ _ _
    (measurable_cavityRestrictedSpinReplicaValue K L Cspin T hB J π F)
    (cavityRestrictedSpinReplicaValue_bound K L Cspin T hB J π F)] at hout
  exact hout

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match_oai.{u_1} := @OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match_oai.{u_1}
