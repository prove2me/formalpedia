-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:25.238194+00:00
-- url     : https://prove2.me/submissions/9c320f0c-3b80-4648-a0be-fb2cc5f4c281
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
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_compact_block
import Theorems.Thm_OAI_InvariantIsing_cavity_haar_strict_restricted_spin_match
import Theorems.Thm_OAI_InvariantIsing_continuous_cavityCanonicalLabel
import Theorems.Thm_OAI_InvariantIsing_continuous_cavitySynchronizedBlock
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_integral
import Theorems.Thm_OAI_IsingPerceptron_replicaLaw_integral_prefix

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
    all_goals try with_reducible_and_instances rfl
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, sub_zero]
  field_simp [hx'.ne']

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

end IsingPerceptron

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

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

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
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAddress_injective (n : ℕ) : Function.Injective (nodeAddress n) := by
  induction n with
  | zero =>
    intro v w _
    cases v with
    | none => cases w with
      | none => rfl
      | some w => exact w.elim
    | some v => exact v.elim
  | succ n ih =>
    intro v w h
    cases v with
    | none => cases w with
      | none => rfl
      | some w => simp [nodeAddress] at h
    | some v => cases w with
      | none => simp [nodeAddress] at h
      | some w =>
        rcases v with ⟨m,i,v⟩
        rcases w with ⟨m',i',w⟩
        simp only [nodeAddress,List.cons.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,h⟩
        rw [ih h]


lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_prefix_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ i) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp (fun {i j : Fin r} h => Fin.val_injective h)).map_fun_eq_pi_map
    (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous bounded extension of the spectral path density. -/

noncomputable section

open Set Filter
open scoped Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_spectralPathDensity
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) :
    Continuous (spectralPathDensity ρ eig hρ hρsum p a) :=
  (continuous_projectedResolventDerivative ρ eig hρ hρsum a).comp (continuous_deficit p)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

theorem continuousOn_projectedResolvent
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) {c : ℝ} :
    ContinuousOn (projectedResolvent ρ eig hρ hρsum a) (Icc 0 c) := by
  intro x hx
  exact (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx.1).continuousWithinAt.mono
    (fun _ hy => hy.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {A : Type} [MeasurableSpace A]

lemma noiseLeafMark_labeled (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (v : LabeledLeaf n) (i : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) i = g (edgeAt n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [noiseLeafMark,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_zero]
    · simpa only [noiseLeafMark,Fin.cases_succ,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_succ] using
        ih (ω.2 v.1.1 v.1.2) (fun w => g (v.1.1,v.1.2,some w)) v.2 j

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ContactFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Faces. -/

noncomputable section

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
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma floor_on_uniformCell (n : ℕ) (i : Fin (n+1)) {u : ℝ}
    (hu : uniformCut n i.castSucc<u ∧ u<uniformCut n i.succ) : ⌊(n+1:ℕ)*u⌋₊=i.val := by
  have hleft : (i.val:ℝ)<(n+1:ℕ)*u := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mp hu.1
    simpa [uniformCut,mul_comm] using this
  apply (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i.val) hleft.le)).mpr
  constructor
  · exact hleft.le
  · have := (lt_div_iff₀ (by positivity)).mp hu.2
    simpa [uniformCut,mul_comm] using this

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariancePositive
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWeightedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial approximation of reciprocal normalizers in bounded
replica tests. Extra-replica mixed moments determine the limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

lemma cavity_weighted_comp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Integrable (fun ω => A ω * f (Z ω)) P := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hzs : Measurable (fun ω => (⟨Z ω, hZb ω⟩ : Icc a b)) := hZ.subtype_mk
  have hm : Measurable (fun ω => f (Z ω)) := hf.domRestrict.measurable.comp hzs
  apply Integrable.of_bound (hA.mul hm).aestronglyMeasurable (B * C)
  exact ae_of_all _ fun ω => by
    change ‖A ω * f (Z ω)‖ ≤ B * C
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hAb ω) (hC _ (hZb ω)) (norm_nonneg _) ((abs_nonneg _).trans (hAb ω))

lemma cavity_weighted_polynomial_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B) (p : ℝ[X]) :
    (∫ ω, A ω * p.eval (Z ω) ∂P) =
      ∑ k ∈ p.support, p.coeff k * ∫ ω, A ω * Z ω ^ k ∂P := by
  have he (ω : Ω) : A ω * p.eval (Z ω) =
      ∑ k ∈ p.support, p.coeff k * (A ω * Z ω ^ k) := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ =>
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb
      (fun x => x ^ k) (continuous_pow k).continuousOn).const_mul (p.coeff k))]
  simp only [integral_const_mul]

lemma cavity_weighted_approx_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z A : Ω → ℝ)
    (hZ : Measurable Z) (hA : Measurable A) {a b B η : ℝ}
    (hZb : ∀ ω, Z ω ∈ Icc a b) (hAb : ∀ ω, |A ω| ≤ B)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    |(∫ ω, A ω * f (Z ω) ∂P) - ∫ ω, A ω * g (Z ω) ∂P| ≤ B * η := by
  rw [← integral_sub (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb f hf)
    (cavity_weighted_comp_integrable P Z A hZ hA hZb hAb g hg), ← Real.norm_eq_abs]
  have ht := norm_integral_le_of_norm_le_const (μ := P) (C := B * η)
    (f := fun ω => A ω * f (Z ω) - A ω * g (Z ω)) (ae_of_all _ fun ω => by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hAb ω) (hfg _ (hZb ω)) (abs_nonneg _) ((abs_nonneg _).trans (hAb ω)))
  simpa only [probReal_univ, mul_one] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityExtraReplicas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products of a replica numerator and powers of its normalizer are
single expectations over additional replicas of the same prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_extra_replica_identity {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    (∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)) *
      (∫ x, w x ∂ν) ^ k =
    ∫ ξ : (Fin r ⊕ Fin k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))
      ∂Measure.pi (fun _ => ν) := by
  let f : (Fin r → X) → ℝ := fun σ => (∏ i, w (σ i)) * F σ
  let g : (Fin k → X) → ℝ := fun τ => ∏ i, w (τ i)
  have hk : (∫ x, w x ∂ν) ^ k = ∫ τ : Fin k → X, g τ ∂Measure.pi (fun _ => ν) := by
    simpa only [g, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν) w).symm
  rw [hk, ← integral_prod_mul f g]
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => X)
  have hp : MeasurePreserving e (Measure.pi (fun _ : Fin r ⊕ Fin k => ν))
      ((Measure.pi (fun _ : Fin r => ν)).prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => ν)
  have hfg : Measurable (fun p : (Fin r → X) × (Fin k → X) => f p.1 * g p.2) := by
    apply Measurable.mul
    · exact ((Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).mul hF).comp
        measurable_fst
    · exact (Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).comp measurable_snd
  rw [← hp.hasLaw.integral_comp hfg.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    change ((∏ i : Fin r, w (ξ (.inl i))) * F (fun i => ξ (.inl i))) *
      (∏ j : Fin k, w (ξ (.inr j))) = _
    dsimp only
    rw [Fintype.prod_sum_type]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma measurable_cavityWeightNormalizer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) :
    Measurable (fun ω => cavityWeightNormalizer (ν ω) (fun x => w (ω, x))) := by
  let κ : Kernel Ω X := ⟨ν, hν⟩
  let : IsMarkovKernel κ := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  exact (hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma measurable_cavityWeightNumerator {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityWeightNumerator (ν ω) (fun x => w (ω, x)) (fun σ => F (ω, σ))) := by
  let κ : Kernel Ω (Fin r → X) :=
    ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω), measurable_probability_pi hν⟩
  let : IsMarkovKernel κ := ⟨fun ω =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω)))⟩
  have hm : Measurable (fun p : Ω × (Fin r → X) => (∏ i, w (p.1, p.2 i)) * F p) :=
    (Finset.measurable_prod _ fun i _ => hw.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul hF
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityWeightNormalizer_mem {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {a b : ℝ} (ha : 0 ≤ a) (hwb : ∀ x, w x ∈ Icc a b) :
    cavityWeightNormalizer ν w ∈ Icc a b := by
  have hi : Integrable w ν := Integrable.of_bound hw.aestronglyMeasurable b
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans (hwb x).1)]
      exact (hwb x).2)
  constructor
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const a) hi (fun x => (hwb x).1)
  · simpa only [cavityWeightNormalizer, integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const b) (fun x => (hwb x).2)

lemma cavityWeightNumerator_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) {r : ℕ}
    (F : (Fin r → X) → ℝ) {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hw : ∀ x, |w x| ≤ M) (hF : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * M ^ r := by
  have hp (σ : Fin r → X) : |∏ i, w (σ i)| ≤ M ^ r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ : Fin r, M := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        (fun i _ => hw (σ i))
      _ = _ := by simp
  have ht := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => ν))
    (f := fun σ => (∏ i, w (σ i)) * F σ) (C := B * M ^ r)
    (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hp σ) (hF σ) (abs_nonneg _) (pow_nonneg hM r)).trans_eq (mul_comm _ _))
  simpa only [cavityWeightNumerator, Real.norm_eq_abs, probReal_univ, mul_one] using ht

lemma cavityWeightNumerator_mul_normalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    cavityWeightNumerator ν w F * cavityWeightNormalizer ν w ^ k =
      ∫ ξ : (Fin r ⊕ Fin k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))
        ∂Measure.pi (fun _ => ν) := cavity_extra_replica_identity ν w F hw hF k

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDeficitGap
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a gap in the finite overlap support, the deficit is affine with
slope equal to minus the mass below the gap. Endpoints may be atoms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma deficit_antitone_argument (p : OverlapPath) : Antitone (deficit p) := by
  intro a b hab
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_mono (p.integrable_complement_max b) (p.integrable_complement_max a)
  intro s
  exact sub_le_sub_left (max_le_max_left (p s) hab) 1

lemma deficit_lower_of_ae_le (p : OverlapPath) {M r : ℝ}
    (hM : ∀ᵐ s ∂pathMeasure, p s ≤ M) (hr : r ≤ M) :
    1 - M ≤ deficit p r := by
  rw [deficit_eq_integral]
  calc
    1 - M = ∫ _s : ℝ, (1 - M) ∂pathMeasure := by simp
    _ ≤ ∫ s, 1 - max (p s) r ∂pathMeasure := by
      apply integral_mono_ae (integrable_const _) (p.integrable_complement_max r)
      filter_upwards [hM] with s hs
      exact sub_le_sub_left (max_le hs hr) 1

lemma deficit_constant_below_ae_lower (p : OverlapPath) {a r : ℝ}
    (ha : ∀ᵐ s ∂pathMeasure, a ≤ p s) (hr : r ≤ a) :
    deficit p r = deficit p a := by
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_congr_ae
  filter_upwards [ha] with s hs
  rw [max_eq_left (hr.trans hs), max_eq_left hs]

theorem deficit_affine_on_gap (p : OverlapPath) {a b : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    {r : ℝ} (hr : r ∈ Icc a b) :
    deficit p r = deficit p a - pathMeasure.real {s | p s ≤ a} * (r - a) := by
  let A : Set ℝ := {s | p s ≤ a}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  have he : (fun s => (1 - max (p s) r) - (1 - max (p s) a)) =ᵐ[pathMeasure]
      A.indicator (fun _ => a - r) := by
    filter_upwards [hgap] with s hs
    by_cases hsa : p s ≤ a
    · rw [max_eq_right (hsa.trans hr.1), max_eq_right hsa,
        indicator_of_mem (show s ∈ A from hsa)]
      ring
    · have hbs : b ≤ p s := hs.resolve_left hsa
      rw [max_eq_left (hr.2.trans hbs), max_eq_left (hr.1.trans (hr.2.trans hbs)),
        indicator_of_notMem (show s ∉ A from hsa)]
      ring
  have hi : deficit p r - deficit p a = pathMeasure.real A * (a - r) := by
    rw [deficit_eq_integral, deficit_eq_integral,
      ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max a),
      integral_congr_ae he, integral_indicator_const (a - r) hA]
    rfl
  change deficit p r = deficit p a - pathMeasure.real A * (r - a)
  linarith

theorem hasDerivAt_deficit_on_gap (p : OverlapPath) {a b r : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s) (hr : r ∈ Ioo a b) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ a}) r := by
  have hd : HasDerivAt
      (fun t => deficit p a - pathMeasure.real {s | p s ≤ a} * (t - a))
      (-pathMeasure.real {s | p s ≤ a}) r := by
    convert! (((hasDerivAt_id r).sub_const a).const_mul
      (pathMeasure.real {s | p s ≤ a})).const_sub (deficit p a) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  exact deficit_affine_on_gap p hgap ⟨ht.1.le, ht.2.le⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalSpectralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precision assumptions in the rooted Gaussian calculation follow
from the actual upper spectral gap when the base matrix is diagonal. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma finiteInverse_antitone_pos {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    finiteInverse ρ eig hρ hsum x ≤ finiteInverse ρ eig hρ hsum y := by
  have hx := hy.trans_le hyx
  by_contra! h
  have hh := finiteResolvent_strictAnti (fun a => (hρ a).le) hsum
    (finiteInverse_spec ρ eig hρ hsum hy).1 h
  rw [(finiteInverse_spec ρ eig hρ hsum hx).2,
    (finiteInverse_spec ρ eig hρ hsum hy).2] at hh
  exact (not_lt_of_ge hyx) hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded finite-prefix integration while retaining the same disorder
that determines both the Gibbs kernel and the spectral projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_disorder_replica_prefix_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) {C : ℝ}
    (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F (p.1, fun i : Fin r => p.2 i) ∂disorderReplicaLaw P ν hν) =
      ∫ ω, ∫ σ, F (ω, σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  have hm : Measurable (fun p : Ω × (ℕ → X) => F (p.1, fun i : Fin r => p.2 i)) :=
    hF.comp (measurable_fst.prodMk (Measurable.of_eval fun i =>
      (measurable_pi_apply (i : ℕ)).comp measurable_snd))
  have hi : Integrable (fun p : Ω × (ℕ → X) => F (p.1, fun i : Fin r => p.2 i))
      (disorderReplicaLaw P ν hν) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => hbound _)
  rw [disorderReplicaLaw, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ fun ω =>
    (HasLaw.mk ((Measurable.of_eval fun i : Fin r => measurable_pi_apply (i : ℕ)).aemeasurable)
      (replica_prefix_map (ν ω) r)).integral_comp
      (hF.comp measurable_prodMk_left).aestronglyMeasurable


lemma cavity_disorder_replica_prefix_swap {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (Q : Measure U) [IsProbabilityMeasure Q] {r : ℕ}
    (G : (Ω × (Fin r → X)) × U → ℝ) (hG : Measurable G) {C : ℝ}
    (hb : ∀ p, ‖G p‖ ≤ C) :
    (∫ ω, ∫ u, ∫ σ, G ((ω, σ), u) ∂Measure.pi (fun _ : Fin r => ν ω) ∂Q ∂P) =
      ∫ p, ∫ u, G ((p.1, fun i : Fin r => p.2 i), u) ∂Q ∂disorderReplicaLaw P ν hν := by
  let H : Ω × (Fin r → X) → ℝ := fun p => ∫ u, G (p, u) ∂Q
  have hH : Measurable H := hG.stronglyMeasurable.integral_prod_right'.measurable
  have hHb p : ‖H p‖ ≤ C := by
    simpa only [H, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := Q) (ae_of_all _ fun u => hb (p, u)))
  have hp := cavity_disorder_replica_prefix_integral P ν hν H hH hHb
  change _ = ∫ p, H (p.1, fun i : Fin r => p.2 i) ∂disorderReplicaLaw P ν hν
  rw [hp]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    have hm : Measurable (fun p : (Fin r → X) × U => G ((ω, p.1), p.2)) :=
      hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hi : Integrable (fun p : (Fin r → X) × U => G ((ω, p.1), p.2))
        ((Measure.pi (fun _ : Fin r => ν ω)).prod Q) :=
      (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => hb ((ω, p.1), p.2))
    exact (integral_integral_swap hi).symm

lemma cavity_disorder_replica_prefix_swap_raw {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (Q : Measure U) [IsProbabilityMeasure Q] {r : ℕ}
    (G : (Ω × U) × (Fin r → X) → ℝ) (hG : Measurable G) {C : ℝ}
    (hb : ∀ p, ‖G p‖ ≤ C) :
    (∫ ω, ∫ u, ∫ σ, G ((ω, u), σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂Q ∂P) =
      ∫ p, ∫ u, G ((p.1, u), fun i : Fin r => p.2 i) ∂Q ∂disorderReplicaLaw P ν hν := by
  exact cavity_disorder_replica_prefix_swap P ν hν Q
    (fun p => G ((p.1.1, p.2), p.1.2))
    (hG.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
    (fun p => hb ((p.1.1, p.2), p.1.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavityFiniteCovariance_diagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance rho lam hrho hsum g x =
      Matrix.diagonal (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹) := by
  unfold cavityFiniteCovariance
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [he, Matrix.diagonal_mul_diagonal]
  have hg (i : Fin d) : finiteInverse rho lam hrho hsum x - lam (g i) ≠ 0 :=
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))).ne'
  simp [hg]

lemma cavityFiniteCovariance_posDef (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  exact Matrix.PosDef.diagonal (fun i => inv_pos.mpr
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))))

lemma cavityFiniteCovariance_sub_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply sub_nonneg.mpr
  exact inv_anti₀ (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum
    (hy.trans_le hyx)).1 (g i)))
    (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)

lemma cavityFiniteCovariance_root_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x q₀ : ℝ} (hx : 0 < x) (hq₀ : 0 ≤ q₀) :
    (q₀ • ((1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) •
      (cavityFiniteCovariance rho lam hrho hsum g x *
        cavityFiniteCovariance rho lam hrho hsum g x))).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx, Matrix.diagonal_mul_diagonal]
  have hM : 0 < finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x) :=
    finiteSecondResolvent_pos (fun a => (hrho a).le) hsum
      (finiteInverse_spec rho lam hrho hsum hx).1
  exact ((Matrix.PosSemidef.diagonal (fun i => mul_self_nonneg _)).smul
    (one_div_nonneg.mpr hM.le)).smul hq₀

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

lemma finite_overlap_ae_bounds {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    ∀ᵐ s ∂pathMeasure, q 0 ≤ p s ∧ p s ≤ q (Fin.last n) := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  exact ⟨hq (Fin.zero_le _), hq (Fin.le_last _)⟩

lemma finite_overlap_deficit_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) {r : ℝ} (hr : r ≤ q (Fin.last n)) :
    0 < deficit p r := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.2)
  exact (sub_pos.mpr htop).trans_le (deficit_lower_of_ae_le p hbound hr)

theorem finite_overlap_cumulative_mass {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (j : Fin (n + 1)) :
    pathMeasure.real {s | p s ≤ q j} = cut j.succ := by
  have he : {s | p s ≤ q j} =ᵐ[pathMeasure] Iic (cut j.succ) := by
    filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
    obtain ⟨k, hk⟩ := hs
    apply propext
    change p s ≤ q j ↔ s ≤ cut j.succ
    rw [hp k s hk]
    by_cases hkj : k ≤ j
    · exact iff_of_true (hq.monotone hkj)
        (hk.2.le.trans (hcut.monotone (by simpa using hkj)))
    · have hjk : j < k := lt_of_not_ge hkj
      have hindex : j.succ ≤ k.castSucc := by
        change j.val + 1 ≤ k.val
        exact hjk
      exact iff_of_false (not_le.mpr (hq hjk))
        (not_le.mpr ((hcut.monotone hindex).trans_lt hk.1))
  have hb : cut j.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hfirst]
      exact hcut.monotone (Fin.zero_le _)
    · rw [← hlast]
      exact hcut.monotone (Fin.le_last _)
  rw [measureReal_def, measure_congr he]
  change (IsingPerceptron.unitUniform (Iic (cut j.succ))).toReal = cut j.succ
  rw [IsingPerceptron.unitUniform_Iic hb, ENNReal.toReal_ofReal hb.1]

theorem finite_overlap_value_gap {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    ∀ᵐ s ∂pathMeasure, p s ≤ q i.castSucc ∨ q i.succ ≤ p s := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  by_cases hji : j ≤ i.castSucc
  · exact Or.inl (hq hji)
  · change ¬j.val ≤ i.val at hji
    exact Or.inr (hq (by change i.val + 1 ≤ j.val; omega))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

lemma cavityFiniteLevel_castSucc {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n i = i.castSucc := by
  apply Fin.ext
  exact min_eq_left i.isLt.le

lemma cavityFiniteLevel_succ {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n (i + 1) = i.succ := by
  apply Fin.ext
  exact min_eq_left i.isLt

lemma cavityFiniteDeficitPath_antitone {n : ℕ} (p : OverlapPath)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) : Antitone (cavityFiniteDeficitPath p q) :=
  (deficit_antitone_argument p).comp_monotone (hq.comp (cavityFiniteLevel_monotone n))

lemma cavityFiniteDeficitPath_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : ℕ) : 0 < cavityFiniteDeficitPath p q i :=
  finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop (hq (Fin.le_last _))

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariancePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hfirst hlast hq hp htop in
lemma cavityFiniteCovariancePath_posDef (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).PosDef :=
  cavityFiniteCovariance_posDef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal ordinary residual covariance is the remaining tail of
the field-density integral; it is not an additional cascade level. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma deficit_eq_one_sub_of_ae_le (p : OverlapPath) {r : ℝ}
    (hr : ∀ᵐ s ∂pathMeasure, p s ≤ r) : deficit p r = 1 - r := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] (fun _ => 0) :=
    hr.mono (fun _ hs => max_eq_right (sub_nonpos.mpr hs))
  rw [deficit, integral_congr_ae he, integral_zero, sub_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralDensityIntegral
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrals of the spectral-group density on the root interval,
finite overlap gaps, and ordinary terminal residual. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma integral_spectralPathDensity_root (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ᵐ s ∂pathMeasure, q ≤ p s) :
    (∫ r in 0..q, spectralPathDensity rho lam hrho hsum p a r) =
      q * projectedResolventDerivative rho lam hrho hsum a (deficit p q) := by
  calc
    _ = ∫ _r in 0..q,
        projectedResolventDerivative rho lam hrho hsum a (deficit p q) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro r hr
      dsimp only [spectralPathDensity]
      rw [deficit_constant_below_ae_lower p hbound hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

lemma integral_spectralPathDensity_gap (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {u v : ℝ} (huv : u < v)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ u ∨ v ≤ p s)
    (hpos : 0 < deficit p v) (hmass : pathMeasure.real {s | p s ≤ u} ≠ 0) :
    (∫ r in u..v, spectralPathDensity rho lam hrho hsum p a r) =
      (projectedResolvent rho lam hrho hsum a (deficit p u) -
        projectedResolvent rho lam hrho hsum a (deficit p v)) /
          pathMeasure.real {s | p s ≤ u} := by
  let F := projectedResolvent rho lam hrho hsum a
  let ζ := pathMeasure.real {s | p s ≤ u}
  have hp (r : ℝ) (hr : r ∈ Icc u v) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => F (deficit p r)) (Icc u v) := by
    intro r hr
    exact (((hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (hp r hr)).hasDerivAt.continuousAt).comp
        (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo u v, HasDerivAt (fun r => F (deficit p r))
      ((-ζ) * spectralPathDensity rho lam hrho hsum p a r) r := by
    intro r hr
    have hF := (hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (hp r ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    convert hF.comp r hD using 1 <;>
      first | rfl | simp only [F, Function.comp_def, ζ, spectralPathDensity]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le hc hd
    (((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable u v).const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in u..v, spectralPathDensity rho lam hrho hsum p a r) * ζ =
    F (deficit p u) - F (deficit p v)
  linarith

lemma integral_spectralPathDensity_tail (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {top : ℝ} (htop : top ≤ 1)
    (hbound : ∀ᵐ s ∂pathMeasure, p s ≤ top) :
    (∫ r in top..1, spectralPathDensity rho lam hrho hsum p a r) =
      projectedResolvent rho lam hrho hsum a (deficit p top) := by
  let F := projectedResolvent rho lam hrho hsum a
  have he (r : ℝ) (hr : r ∈ Icc top 1) : deficit p r = 1 - r :=
    deficit_eq_one_sub_of_ae_le p (hbound.mono (fun _ hs => hs.trans hr.1))
  have hc : ContinuousOn (fun r => F (1 - r)) (Icc top 1) :=
    (continuousOn_projectedResolvent rho lam hrho hsum a).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun _ hr => ⟨sub_nonneg.mpr hr.2, sub_le_sub_left hr.1 1⟩)
  have hd : ∀ r ∈ Ioo top 1, HasDerivAt (fun r => F (1 - r))
      (-spectralPathDensity rho lam hrho hsum p a r) r := by
    intro r hr
    have hF := (hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (sub_pos.mpr hr.2)).hasDerivAt
    convert hF.comp r ((hasDerivAt_id r).const_sub 1) using 1 <;>
      first | rfl | simp only [F, Function.comp_def, spectralPathDensity, he r ⟨hr.1.le, hr.2.le⟩]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htop hc hd
    (((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable top 1).neg)
  rw [intervalIntegral.integral_neg] at hf
  change -(∫ r in top..1, spectralPathDensity rho lam hrho hsum p a r) =
    F (1 - 1) - F (1 - top) at hf
  rw [sub_self, show F 0 = 0 by simp [F, projectedResolvent]] at hf
  rw [deficit_eq_one_sub_of_ae_le p hbound]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteSpectralIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-level spectral integrals. The covariance of a shared
prefix is the canonical spectral path evaluated at its overlap value. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_prefix_sum_differences {n : ℕ} (f : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) :
    f 0 + (∑ i : Fin n, if (i : ℕ) + 1 ≤ (l : ℕ) then
      f i.succ - f i.castSucc else 0) = f l := by
  refine Fin.induction ?_ ?_ l
  · simp
  · intro j hj
    have hs : (∑ i : Fin n, if (i : ℕ) + 1 ≤ (j.succ : ℕ) then
        f i.succ - f i.castSucc else 0) =
        (∑ i : Fin n, if (i : ℕ) + 1 ≤ (j.castSucc : ℕ) then
          f i.succ - f i.castSucc else 0) + (f j.succ - f j.castSucc) := by
      calc
        _ = ∑ i : Fin n,
            ((if (i : ℕ) + 1 ≤ (j.castSucc : ℕ) then f i.succ - f i.castSucc else 0) +
            (if i = j then f j.succ - f j.castSucc else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          · subst i
            simp
          · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
            by_cases hlt : (i : ℕ) + 1 ≤ (j : ℕ)
            · have hlt' : (i : ℕ) + 1 ≤ (j.succ : ℕ) := by simp; omega
              simp only [hlt, hlt', Fin.val_castSucc, ite_true, if_true, hij, ite_false, if_false, add_zero]
            · have hlt' : ¬ (i : ℕ) + 1 ≤ (j.succ : ℕ) := by simp; omega
              simp only [hlt, hlt', Fin.val_castSucc, ite_false, if_false, hij, add_zero]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [hs]
    linarith

variable {ι : Type*} [Fintype ι]

lemma finite_overlap_spectral_increment (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (a : ι) (i : Fin n) :
    (∫ r in q i.castSucc..q i.succ, spectralPathDensity rho lam hrho hsum p a r) =
      (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
        projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
          cut i.castSucc.succ := by
  have hm := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
  have hc : 0 < cut i.castSucc.succ := by
    rw [← hfirst]
    exact hcut (Fin.succ_pos _)
  have he := integral_spectralPathDensity_gap rho lam hrho hsum p a
    (hq (Fin.castSucc_lt_succ (i := i)))
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
    (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))) (by rw [hm]; exact hc.ne')
  rwa [hm] at he

theorem finite_overlap_spectral_prefix (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (a : ι) (l : Fin (n + 1)) :
    (∫ r in 0..q l, spectralPathDensity rho lam hrho hsum p a r) =
      q 0 * projectedResolventDerivative rho lam hrho hsum a (deficit p (q 0)) +
      ∑ i : Fin n, if (i : ℕ) + 1 ≤ (l : ℕ) then
        (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
          projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
            cut i.castSucc.succ else 0 := by
  let F (j : Fin (n + 1)) := ∫ r in 0..q j, spectralPathDensity rho lam hrho hsum p a r
  have hroot : F 0 = q 0 * projectedResolventDerivative rho lam hrho hsum a
      (deficit p (q 0)) :=
    integral_spectralPathDensity_root rho lam hrho hsum p a
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.1))
  have hstep (i : Fin n) : F i.succ - F i.castSucc =
      (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
        projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
          cut i.castSucc.succ := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable 0 (q i.castSucc))
      ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable
        (q i.castSucc) (q i.succ))
    have hi := finite_overlap_spectral_increment rho lam hrho hsum p cut hcut hfirst hlast
      q hq hp htop a i
    dsimp only [F]
    linarith
  have he := cavity_prefix_sum_differences F l
  rw [hroot] at he
  simp_rw [hstep] at he
  exact he.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteSpectralEntries
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise conversion of the actual finite spectral Gaussian
covariances to the weighted spectral resolvent and its derivative. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

variable {m d : ℕ}

lemma cavity_finite_covariance_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) (i j : Fin d) :
    rho (g i) * cavityFiniteCovariance rho lam hrho hsum g x i j =
      if i = j then projectedResolvent rho lam hrho hsum (g i) x else 0 := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  by_cases hij : i = j
  · subst j
    simp [projectedResolvent, hx, div_eq_mul_inv]
  · simp [hij]

lemma cavity_finite_root_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {n : ℕ} (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (hx : 0 < deficit p (q 0)) (i j : Fin d) :
    rho (g i) * cavityFiniteRootCovariance rho lam hrho hsum g p q i j =
      if i = j then q 0 * projectedResolventDerivative rho lam hrho hsum (g i)
        (deficit p (q 0)) else 0 := by
  have hdiag : cavityFiniteCovariancePath rho lam hrho hsum g p q 0 =
      Matrix.diagonal (fun i =>
        (finiteInverse rho lam hrho hsum (deficit p (q 0)) - lam (g i))⁻¹) := by
    simpa only [cavityFiniteCovariancePath, cavityFiniteDeficitPath,
      cavityFiniteLevel_zero] using cavityFiniteCovariance_diagonal rho lam hrho hsum g hx
  unfold cavityFiniteRootCovariance
  rw [hdiag, Matrix.diagonal_mul_diagonal]
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_zero, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, ite_true, if_true, projectedResolventDerivative,
      hx, ite_true, div_eq_mul_inv, mul_inv_rev, pow_two]
    ring
  · simp [hij]

lemma cavity_finite_noise_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (q : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < deficit p (q j)) (k : Fin n) (i j : Fin d) :
    rho (g i) * cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q k i j =
      if i = j then
        (projectedResolvent rho lam hrho hsum (g i) (deficit p (q k.castSucc)) -
          projectedResolvent rho lam hrho hsum (g i) (deficit p (q k.succ))) /
            cut k.castSucc.succ else 0 := by
  have hleft := cavity_finite_covariance_weighted_entry rho lam hrho hsum g
    (hx k.castSucc) i j
  have hright := cavity_finite_covariance_weighted_entry rho lam hrho hsum g
    (hx k.succ) i j
  simp only [cavityFiniteNoiseCovariance, cavityFiniteCovariancePath,
    cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut k.isLt, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  calc
    _ = (cut k.castSucc.succ)⁻¹ *
        (rho (g i) * cavityFiniteCovariance rho lam hrho hsum g
          (deficit p (q k.castSucc)) i j -
        rho (g i) * cavityFiniteCovariance rho lam hrho hsum g
          (deficit p (q k.succ)) i j) := by
      change rho (g i) * ((cut k.castSucc.succ)⁻¹ *
        (cavityFiniteCovariance rho lam hrho hsum g (deficit p (q k.castSucc)) i j -
          cavityFiniteCovariance rho lam hrho hsum g (deficit p (q k.succ)) i j)) = _
      ring
    _ = _ := by
      rw [hleft, hright]
      by_cases hij : i = j <;> simp [hij, div_eq_mul_inv, mul_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodeLaw
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite projections of independent Gaussian nodes. Repeated use of a
node retains its covariance, as required by the shared prefixes of replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators RealInnerProductSpace

namespace InvariantIsing

variable {d r : ℕ}

lemma cavity_gaussian_node_coordinate_memLp {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (a : J) (i : Fin d) :
    MemLp (fun z : J → EuclideanSpace ℝ (Fin d) => z a i) 2
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
  have hp := measurePreserving_eval (fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
  exact ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S a))).map
    (EuclideanSpace.proj i)).memLp_two.comp_measurePreserving hp

lemma cavity_gaussian_node_coordinate_covariance {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (a b : J) (i j : Fin d) :
    cov[fun z : J → EuclideanSpace ℝ (Fin d) => z a i,
      fun z => z b j; Measure.pi (fun a => multivariateGaussian 0 (S a))] =
        if a = b then S a i j else 0 := by
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    have hp := measurePreserving_eval (fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
    exact (hp.hasLaw.covariance_fun_comp
      (f := fun x : EuclideanSpace ℝ (Fin d) => x i)
      (g := fun x : EuclideanSpace ℝ (Fin d) => x j)
      (by fun_prop) (by fun_prop)).trans
        (covariance_eval_multivariateGaussian (hS a) i j)
  · rw [ite_eq_right hab]
    have hind := (iIndepFun_pi (μ := fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hab
    exact (hind.comp (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x i))
      (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j))).covariance_eq_zero
        (cavity_gaussian_node_coordinate_memLp S a i)
        (cavity_gaussian_node_coordinate_memLp S b j)

lemma cavity_gaussian_node_sum_hasGaussianLaw {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    HasGaussianLaw (cavityGaussianNodeSum (d := d) w)
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
  have hx (a : J) : HasGaussianLaw (fun z : J → EuclideanSpace ℝ (Fin d) => z a)
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
    refine ⟨?_⟩
    · rw [(measurePreserving_eval (fun a => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S a)) a).map_eq]
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hj := (iIndepFun_pi (μ := fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) (X := fun _ => id)
    (fun _ => aemeasurable_id)).hasGaussianLaw hx
  let L : (J → EuclideanSpace ℝ (Fin d)) →L[ℝ] (Fin r × Fin d → ℝ) :=
    ContinuousLinearMap.pi (fun p => ∑ a, w p.1 a •
      ((EuclideanSpace.proj p.2).comp (ContinuousLinearMap.proj a)))
  have hh := (hj.map L).toLp_pi 2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext z p
  simp [cavityGaussianNodeSum, L]

lemma cavity_gaussian_node_sum_covariance {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ) (p q : Fin r × Fin d) :
    cov[fun z : J → EuclideanSpace ℝ (Fin d) => cavityGaussianNodeSum w z p,
      fun z => cavityGaussianNodeSum w z q;
      Measure.pi (fun a => multivariateGaussian 0 (S a))] =
        ∑ a, w p.1 a * w q.1 a * S a p.2 q.2 := by
  change cov[fun z : J → EuclideanSpace ℝ (Fin d) => ∑ a, w p.1 a * z a p.2,
    fun z => ∑ a, w q.1 a * z a q.2;
    Measure.pi (fun a => multivariateGaussian 0 (S a))] = _
  rw [covariance_fun_sum_fun_sum
    (fun a => (cavity_gaussian_node_coordinate_memLp S a p.2).const_mul _)
    (fun a => (cavity_gaussian_node_coordinate_memLp S a q.2).const_mul _)]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    cavity_gaussian_node_coordinate_covariance S hS]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, if_true]
    ring
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

lemma cavity_gaussian_node_coordinate_mean {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (a : J) (i : Fin d) :
    (∫ z : J → EuclideanSpace ℝ (Fin d), z a i
      ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0 := by
  have hp := measurePreserving_eval (fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
  have hmap := hp.hasLaw.integral_comp
    (f := fun x : EuclideanSpace ℝ (Fin d) => x i) (by fun_prop)
  have hm := (EuclideanSpace.proj i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)))
  change (∫ x : EuclideanSpace ℝ (Fin d), x i ∂multivariateGaussian 0 (S a)) =
    (∫ x : EuclideanSpace ℝ (Fin d), x ∂multivariateGaussian 0 (S a)) i at hm
  rw [integral_id_multivariateGaussian] at hm
  exact hmap.trans hm

lemma cavity_gaussian_node_sum_mean {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    (∫ z, cavityGaussianNodeSum w z
      ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0 := by
  have hy := cavity_gaussian_node_sum_hasGaussianLaw S w
  ext p
  have he := (EuclideanSpace.proj p).integral_comp_comm hy.integrable
  change (∫ z, cavityGaussianNodeSum w z p
    ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) =
      (∫ z, cavityGaussianNodeSum w z
        ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) p at he
  rw [← he]
  change (∫ z : J → EuclideanSpace ℝ (Fin d), ∑ a, w p.1 a * z a p.2
    ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0
  rw [integral_finsetSum _ (fun a _ =>
    ((cavity_gaussian_node_coordinate_memLp S a p.2).const_mul _).integrable (by norm_num))]
  simp_rw [integral_const_mul, cavity_gaussian_node_coordinate_mean, mul_zero]
  exact Finset.sum_const_zero

/-- The covariance of a finite collection of linear node sums determines
its full joint law, including singular covariances. -/
theorem cavity_gaussian_node_sum_law {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ)
    (Q : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (hQ : Q.PosSemidef)
    (hcov : ∀ p q, Q p q = ∑ a, w p.1 a * w q.1 a * S a p.2 q.2) :
    (Measure.pi (fun a => multivariateGaussian 0 (S a))).map
      (cavityGaussianNodeSum w) = multivariateGaussian 0 Q := by
  let P := Measure.pi (fun a => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S a))
  let Y := cavityGaussianNodeSum (d := d) w
  have hy := cavity_gaussian_node_sum_hasGaussianLaw S w
  have := hy.isGaussian_map
  apply IsGaussian.ext
  · calc
      (∫ z, z ∂P.map Y) = ∫ z, Y z ∂P :=
        integral_map hy.aemeasurable aestronglyMeasurable_id
      _ = 0 := cavity_gaussian_node_sum_mean S w
      _ = ∫ z, z ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin r × Fin d)) Q :=
        integral_id_multivariateGaussian.symm
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin r × Fin d) ℝ).toBasis fun p q => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
    · have he (p : Fin r × Fin d) :
          (fun x : EuclideanSpace ℝ (Fin r × Fin d) =>
            inner ℝ ((EuclideanSpace.basisFun (Fin r × Fin d) ℝ).toBasis p) x) =
          fun x => x p := by
        ext x
        simp [PiLp.inner_apply]
      simp_rw [he]
      rw [covariance_map_fun (by fun_prop) (by fun_prop) hy.aemeasurable,
        covariance_eval_multivariateGaussian hQ,
        cavity_gaussian_node_sum_covariance S hS w, hcov]
    · exact IsGaussian.memLp_two_id
    · exact IsGaussian.memLp_two_id

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodeCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The covariance of a finite linear Gaussian node projection is
positive semidefinite directly from its independent node covariances. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityGaussianNodeCovariance_posSemidef {J : Type*} [Fintype J] {r d : ℕ}
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ) : (cavityGaussianNodeCovariance S w).PosSemidef := by
  classical
  let A : J → Matrix (Fin r × Fin d) (Fin d) ℝ :=
    fun a p j => if p.2 = j then w p.1 a else 0
  have hentry (a : J) (p q : Fin r × Fin d) :
      (A a * S a * (A a).transpose) p q = w p.1 a * w q.1 a * S a p.2 q.2 := by
    change (∑ k : Fin d, (∑ l : Fin d,
      (if p.2 = l then w p.1 a else 0) * S a l k) *
        (if q.2 = k then w q.1 a else 0)) = _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
      mul_ite, mul_zero]
    ring
  have he : cavityGaussianNodeCovariance S w = ∑ a, A a * S a * (A a).transpose := by
    ext p q
    simp only [cavityGaussianNodeCovariance, Matrix.sum_apply, hentry]
  rw [he]
  apply Matrix.posSemidef_sum Finset.univ
  intro a _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hS a).mul_mul_conjTranspose_same (A a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOneReplicaPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sampled innovation path has independent Gaussian increments.
This is the marginal needed by the remaining linear-tilt moment bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityLeafSum_eq_mark_sum {d : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n s v = s + ∑ i : Fin n, noiseLeafMark n v i := by
  induction n generalizing s with
  | zero => simp [cavityLeafSum]
  | succ n ih =>
    rw [cavityLeafSum, ih, Fin.sum_univ_succ]
    simp only [noiseLeafMark, Fin.cases_zero, Fin.cases_succ]
    abel

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianForestLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite restrictions of the independent Gaussian forest, and the
literal sum of its marks along a labeled cavity leaf. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavity_labeled_leaf_sum {d : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) (v : LabeledLeaf n)
    (s : EuclideanSpace ℝ (Fin d)) :
    cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) v) =
      s + ∑ i : Fin n, g (edgeAt n v i) := by
  rw [cavityLeafSum_eq_mark_sum]
  simp_rw [noiseLeafMark_labeled]

/-- A finite set of distinct nodes can be sampled from the full product
law before taking any linear replica projections. -/
theorem cavity_gaussian_finite_node_law {A J : Type*} [Fintype J] [DecidableEq J]
    {d r : ℕ} (e : J → A) (he : Function.Injective e)
    (S : A → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ)
    (Q : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (hQ : Q.PosSemidef)
    (hcov : ∀ p q, Q p q = ∑ a, w p.1 a * w q.1 a * S (e a) p.2 q.2) :
    (Measure.infinitePi (fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a))).map
        (fun z => cavityGaussianNodeSum w (fun a => z (e a))) =
          multivariateGaussian 0 Q := by
  have hm : Measurable (fun z : J → EuclideanSpace ℝ (Fin d) =>
      cavityGaussianNodeSum w z) := by
    unfold cavityGaussianNodeSum
    fun_prop
  rw [show (fun z : A → EuclideanSpace ℝ (Fin d) =>
      cavityGaussianNodeSum w (fun a => z (e a))) =
      cavityGaussianNodeSum w ∘ (fun z a => z (e a)) from rfl,
    ← Measure.map_map hm (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj he, Measure.infinitePi_eq_pi]
  exact cavity_gaussian_node_sum_law (fun a => S (e a)) (fun a => hS (e a)) w Q hQ hcov

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodePrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the actual shared Gaussian root, independent forest, and
replica-specific ordinary residuals as one independent node family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

private theorem cavity_infinitePi_sum_join {I J E : Type*} [MeasurableSpace E]
    (μ : I → Measure E) (ν : J → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) =
        Measure.infinitePi (Sum.elim μ ν) := by
  classical
  have hm : Measurable (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  let : ∀ a : I ⊕ J, IsProbabilityMeasure (Sum.elim μ ν a) := by
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (.pi s.countable_toSet (fun a _ => ht a))]
  have he : (fun p : (I → E) × (J → E) => Sum.elim p.1 p.2) ⁻¹'
      ((s : Set (I ⊕ J)).pi t) =
      ((s.toLeft : Set I).pi (fun i => t (.inl i))) ×ˢ
        ((s.toRight : Set J).pi (fun j => t (.inr j))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi, fun j hj => h (.inr j) hj⟩
    · rintro ⟨hI, hJ⟩ a ha
      cases a with
      | inl i => exact hI i ha
      | inr j => exact hJ j ha
  rw [he, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi _ (fun j _ => ht (.inr j)),
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  rfl

lemma measurable_cavityReplicaNodeJoin {d : ℕ} (n r : ℕ) :
    Measurable (cavityReplicaNodeJoin (d := d) n r) := by
  unfold cavityReplicaNodeJoin
  apply Measurable.of_eval
  intro a
  cases a with
  | inl a =>
    cases a <;> dsimp only [Sum.elim_inl, Option.elim_none, Option.elim_some] <;> fun_prop
  | inr a => dsimp only [Sum.elim_inr]; fun_prop

theorem cavity_replica_node_prior_law {d : ℕ} (n r : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R))).map (cavityReplicaNodeJoin n r) =
      Measure.infinitePi (fun a : CavityReplicaNode n r => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (cavityReplicaNodeCovariance n r S₀ R S a)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let μ := fun a : Option (ForestVertex n) =>
    a.elim (multivariateGaussian (0 : E) S₀)
      (fun v => multivariateGaussian (0 : E) (S (forestVertexDepth n v)))
  let : ∀ a, IsProbabilityMeasure (μ a) := by
    intro a
    cases a <;> dsimp only [μ, Option.elim_none, Option.elim_some] <;> infer_instance
  let ν := fun _ : Fin r => multivariateGaussian (0 : E) R
  let F : E × (ForestVertex n → E) → (Option (ForestVertex n) → E) :=
    fun p a => a.elim p.1 p.2
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [F, Option.elim_none, Option.elim_some] <;> fun_prop
  have hbase : ((multivariateGaussian (0 : E) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : E) (S (forestVertexDepth n v))))).map F =
      Measure.infinitePi μ := by
    simpa only [F, μ] using infinitePi_option_join
      (multivariateGaussian (0 : E) S₀)
      (fun v : ForestVertex n => multivariateGaussian (0 : E) (S (forestVertexDepth n v)))
  have hm : Measurable (fun p : (Option (ForestVertex n) → E) × (Fin r → E) =>
      Sum.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro a
    cases a <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hC : (fun a : CavityReplicaNode n r => multivariateGaussian
      (0 : E) (cavityReplicaNodeCovariance n r S₀ R S a)) = Sum.elim μ ν := by
    funext a
    cases a with
    | inl a => cases a <;> rfl
    | inr a => rfl
  rw [hC]
  rw [show cavityReplicaNodeJoin (d := d) n r =
      (fun p : (Option (ForestVertex n) → E) × (Fin r → E) => Sum.elim p.1 p.2) ∘
        Prod.map F id from rfl,
    ← Measure.map_map hm (hF.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hF measurable_id, hbase, Measure.map_id,
    ← Measure.infinitePi_eq_pi]
  exact cavity_infinitePi_sum_join μ ν

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaNodeProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite set of Gaussian nodes visited by a tuple of cavity leaves.
Each replica keeps the common root and shared edges, and receives its own
ordinary terminal residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_nodeAt_injective (n : ℕ) (v : LabeledLeaf n) :
    Function.Injective (nodeAt n v) := by
  intro i j h
  apply Fin.ext
  have hl := congrArg (fun a => (nodeAddress n a).length) h
  simpa only [nodeAddress_nodeAt_length] using hl

lemma cavityReplicaNodePath_subset {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (i : Fin r) : cavityReplicaNodePath n (σ i) i ⊆ cavityReplicaNodeSupport n σ := by
  classical
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩

lemma cavity_replica_node_sum {r d : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (z : CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) (i : Fin r) (j : Fin d) :
    cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a => z a) (i, j) =
        (z (.inl none)) j + (∑ k : Fin n, z (.inl (some (edgeAt n (σ i) k))) j) +
          z (.inr i) j := by
  classical
  change (∑ a : cavityReplicaNodeSupport n σ,
    (if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
      z a j) = _
  have he : (∑ a : cavityReplicaNodeSupport n σ,
      (if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
        z a j) = ∑ a ∈ cavityReplicaNodeSupport n σ,
      (if a ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) * z a j :=
    Finset.sum_coe_sort (cavityReplicaNodeSupport n σ)
      (fun a : CavityReplicaNode n r =>
        (if a ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) * z a j)
  rw [he]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (cavityReplicaNodeSupport n σ).filter
      (fun a => a ∈ cavityReplicaNodePath n (σ i) i) = cavityReplicaNodePath n (σ i) i := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cavityReplicaNodePath_subset n σ i h, h⟩⟩
  rw [hf, cavityReplicaNodePath, Finset.sum_insert]
  · rw [Finset.sum_image]
    · rw [Fin.sum_univ_succ]
      simp only [nodeAt_zero, nodeAt_succ]
      ring
    · intro k _ l _ hkl
      exact cavity_nodeAt_injective n (σ i) (Sum.inl.inj hkl)
  · simp

/-- The node representation is pointwise the original root-plus-forest
field, including the independent residual of each replica. -/
theorem cavity_replica_node_field {r d : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (T : LabeledTree n)
    (p : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a => cavityReplicaNodeJoin n r p a) =
      WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2) := by
  ext q
  change cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
    (fun a => cavityReplicaNodeJoin n r p a) q =
      (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
        (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2
  rw [cavity_replica_node_sum, cavity_labeled_leaf_sum]
  simp [cavityReplicaNodeJoin]

/-- Joint law of the actual cavity fields for any fixed tuple of leaves.
The same root is retained in every replica; ordinary residuals are independent. -/
theorem cavity_replica_gaussian_field_law {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (T : LabeledTree n) (σ : Fin r → LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R))).map
      (fun p => WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2)) =
      multivariateGaussian 0 (cavityReplicaGaussianCovariance n S₀ R S σ) := by
  classical
  let V := cavityReplicaNodeSupport n σ
  let C := cavityReplicaNodeCovariance n r S₀ R S
  let w := cavityReplicaNodeWeight n σ
  let F : (CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin r × Fin d) :=
    fun z => cavityGaussianNodeSum w (fun a : V => z a)
  have hC (a : CavityReplicaNode n r) : (C a).PosSemidef := by
    cases a with
    | inl a => cases a with
      | none => exact hS₀
      | some a => exact hS _
    | inr a => exact hR
  have hQ := cavityGaussianNodeCovariance_posSemidef (fun a : V => C a)
    (fun a => hC a) w
  have hp := cavity_gaussian_finite_node_law
    (fun a : V => (a : CavityReplicaNode n r)) Subtype.val_injective C hC w
    (cavityReplicaGaussianCovariance n S₀ R S σ) hQ (fun _ _ => rfl)
  have hF : Measurable F := by
    unfold F cavityGaussianNodeSum
    fun_prop
  rw [← cavity_replica_node_prior_law n r S₀ R S,
    Measure.map_map hF (measurable_cavityReplicaNodeJoin n r)] at hp
  have he : F ∘ cavityReplicaNodeJoin (d := d) n r =
      fun p => WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2) := by
    funext p
    exact cavity_replica_node_field n σ T p
  simpa only [he] using hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaNodeCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared-prefix covariance of the actual Gaussian cavity replica fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_nodeAt_eq_iff (n : ℕ) (v w : LabeledLeaf n) (i j : Fin (n + 1)) :
    nodeAt n v i = nodeAt n w j ↔
      i = j ∧ (i : ℕ) ≤ labeledCommonDepth n v w := by
  constructor
  · intro h
    have hij : i = j := by
      apply Fin.ext
      have he := congrArg (fun a => (nodeAddress n a).length) h
      simpa only [nodeAddress_nodeAt_length] using he
    subst j
    refine ⟨rfl, ?_⟩
    apply (labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.isLt)).mp
    simpa only [nodeAddress_nodeAt] using congrArg (nodeAddress n) h
  · rintro ⟨rfl, h⟩
    apply nodeAddress_injective n
    simpa only [nodeAddress_nodeAt] using
      (labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.isLt)).mpr h

lemma cavity_edgeAt_depth (n : ℕ) (v : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n v i) = i := by
  have he := nodeAddress_nodeAt_length n v i.succ
  rw [nodeAt_succ, nodeAddress_length_some] at he
  exact Nat.add_right_cancel he

lemma cavity_nodeAt_mem_replicaPath {r : ℕ} (n : ℕ)
    (v w : LabeledLeaf n) (j : Fin r) (i : Fin (n + 1)) :
    (Sum.inl (nodeAt n v i) : CavityReplicaNode n r) ∈ cavityReplicaNodePath n w j ↔
      (i : ℕ) ≤ labeledCommonDepth n v w := by
  classical
  simp only [cavityReplicaNodePath, Finset.mem_insert, Sum.inl.injEq,
    Sum.inl_ne_inr, false_or, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact ((cavity_nodeAt_eq_iff n v w i k).mp hk.symm).2
  · intro hi
    exact ⟨i, ((cavity_nodeAt_eq_iff n v w i i).mpr ⟨rfl, hi⟩).symm⟩

lemma cavityReplicaGaussianCovariance_entry {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin r → LabeledLeaf n) (i j : Fin r) (a b : Fin d) :
    cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      S₀ a b + (∑ k : Fin n,
        if (k : ℕ) + 1 ≤ labeledCommonDepth n (σ i) (σ j) then S k a b else 0) +
          if i = j then R a b else 0 := by
  classical
  let V := cavityReplicaNodeSupport n σ
  let C := cavityReplicaNodeCovariance n r S₀ R S
  change (∑ v : V, cavityReplicaNodeWeight n σ i v *
    cavityReplicaNodeWeight n σ j v * C v a b) = _
  simp only [cavityReplicaNodeWeight]
  rw [Finset.sum_coe_sort V (fun v : CavityReplicaNode n r =>
    (if v ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
    (if v ∈ cavityReplicaNodePath n (σ j) j then (1 : ℝ) else 0) * C v a b)]
  have hf (v : CavityReplicaNode n r) :
      (if v ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
      (if v ∈ cavityReplicaNodePath n (σ j) j then 1 else 0) * C v a b =
      if v ∈ cavityReplicaNodePath n (σ i) i then
        (if v ∈ cavityReplicaNodePath n (σ j) j then C v a b else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hf]
  rw [← Finset.sum_filter]
  have hs : V.filter (fun v => v ∈ cavityReplicaNodePath n (σ i) i) =
      cavityReplicaNodePath n (σ i) i := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cavityReplicaNodePath_subset n σ i h, h⟩⟩
  rw [hs, cavityReplicaNodePath, Finset.sum_insert]
  · rw [Finset.sum_image]
    · simp_rw [cavity_nodeAt_mem_replicaPath]
      rw [Fin.sum_univ_succ]
      simp only [nodeAt_zero, nodeAt_succ, Fin.val_zero, zero_le,
        ite_true, if_true, Fin.val_succ, C, cavityReplicaNodeCovariance, Sum.elim_inl,
        Option.elim_none, Option.elim_some, cavity_edgeAt_depth]
      have hr : (if (Sum.inr i : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ j) j
          then cavityReplicaNodeCovariance n r S₀ R S (.inr i) a b else 0) =
          if i = j then R a b else 0 := by
        simp [cavityReplicaNodePath, cavityReplicaNodeCovariance]
      change (if (Sum.inr i : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ j) j
          then cavityReplicaNodeCovariance n r S₀ R S (.inr i) a b else 0) +
        (S₀ a b + ∑ k : Fin n,
          if (k : ℕ) + 1 ≤ labeledCommonDepth n (σ i) (σ j) then S k a b else 0) = _
      rw [hr]
      ring
    · intro k _ l _ hkl
      exact cavity_nodeAt_injective n (σ i) (Sum.inl.inj hkl)
  · simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteReplicaCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cavity Gaussian replica covariance is the canonical
spectral covariance, with its full diagonal including the ordinary residual. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

variable {m d n r : ℕ}
variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_prefix (σ : Fin r → LabeledLeaf n)
    (i j : Fin r) (a b : Fin d) :
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let R := cavityFiniteCovariancePath rho lam hrho hsum g p q n
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    rho (g a) * cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      if a = b then
        (∫ t in 0..q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))),
          spectralPathDensity rho lam hrho hsum p (g a) t) +
        (if i = j then projectedResolvent rho lam hrho hsum (g a)
          (deficit p (q (Fin.last n))) else 0) else 0 := by
  dsimp only
  have hx (l : Fin (n + 1)) : 0 < deficit p (q l) :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))
  have hR : rho (g a) * cavityFiniteCovariancePath rho lam hrho hsum g p q n a b =
      if a = b then projectedResolvent rho lam hrho hsum (g a)
        (deficit p (q (Fin.last n))) else 0 := by
    simpa only [cavityFiniteCovariancePath, cavityFiniteDeficitPath, cavityFiniteLevel_last]
      using cavity_finite_covariance_weighted_entry rho lam hrho hsum g (hx (Fin.last n)) a b
  rw [cavityReplicaGaussianCovariance_entry, mul_add, mul_add, Finset.mul_sum]
  simp_rw [mul_ite, mul_zero, cavity_finite_root_weighted_entry rho lam hrho hsum g p q (hx 0),
    cavity_finite_noise_weighted_entry rho lam hrho hsum g p cut q hx, hR]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, if_true]
    have hl : (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j)) : ℕ) =
        labeledCommonDepth n (σ i) (σ j) :=
      min_eq_left (labeledCommonDepth_le n (σ i) (σ j))
    rw [finite_overlap_spectral_prefix rho lam hrho hsum p cut hcut hfirst hlast q hq hp htop]
    simp only [hl]
  · simp [hab]

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_canonical (σ : Fin r → LabeledLeaf n)
    (i j : Fin r) (a b : Fin d) :
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let R := cavityFiniteCovariancePath rho lam hrho hsum g p q n
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    rho (g a) * cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      if a = b then
        (if i = j then spectralGroupDiagonal rho lam hrho hsum p (g a) else
          cavityCanonicalCoordinate rho lam hrho hsum p (g a)
            (q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))))) else 0 := by
  dsimp only
  rw [cavity_finite_replica_covariance_prefix rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, if_true]
    by_cases hij : i = j
    · subst j
      simp only [labeledCommonDepth_self, cavityFiniteLevel_last, ite_true, if_true]
      have ht := integral_spectralPathDensity_tail rho lam hrho hsum p (g a) htop.le
        ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((continuous_spectralPathDensity rho lam hrho hsum p (g a)).intervalIntegrable 0 (q (Fin.last n)))
        ((continuous_spectralPathDensity rho lam hrho hsum p (g a)).intervalIntegrable (q (Fin.last n)) 1)
      rw [ht] at hadd
      exact hadd
    · simp only [hij, ite_false, if_false, add_zero, cavityCanonicalCoordinate]
      rw [Set.projIcc_of_mem zero_le_one
        (finite_overlap_value_mem_unit p cut hcut q hp _)]
  · simp only [hab, ite_false, if_false]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gaussian law used on the finite spectral side of the
physical replica comparison, with every covariance fixed by the overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

variable {m d n r : ℕ}
variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_eq (σ : Fin r → LabeledLeaf n) :
    cavityReplicaGaussianCovariance n
      (cavityFiniteRootCovariance rho lam hrho hsum g p q)
      (cavityFiniteCovariancePath rho lam hrho hsum g p q n)
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) σ =
      cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ := by
  ext u v
  have he := cavity_finite_replica_covariance_canonical rho lam hrho hsum g p cut hcut
    hfirst hlast q hq hp htop σ u.1 v.1 u.2 v.2
  apply (mul_left_cancel₀ (hrho (g u.2)).ne')
  rw [he]
  dsimp only [cavityFiniteCanonicalReplicaCovariance]
  by_cases huv : u.2 = v.2
  · simp only [huv, ite_true, if_true]
    field_simp [(hrho (g v.2)).ne']
  · simp only [huv, ite_false, if_false, mul_zero]

include hcut hfirst hlast hq hp htop in
/-- The finite cavity root, actual independent forest, and replica-specific
ordinary residuals have the canonical spectral Gaussian block law. -/
theorem cavity_finite_replica_field_law (T : LabeledTree n) (σ : Fin r → LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d))
        (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))).map
      (fun z => WithLp.toLp 2 (fun u : Fin r × Fin d =>
        (cavityLeafSum n z.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n z.1.2) (σ u.1)) + z.2 u.1) u.2)) =
      multivariateGaussian 0 (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
  have hS₀ := cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop 0)
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  have hR := (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast
    q hq hp htop n).posSemidef
  have hS := cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop
  have he := cavity_replica_gaussian_field_law n
    (cavityFiniteRootCovariance rho lam hrho hsum g p q)
    (cavityFiniteCovariancePath rho lam hrho hsum g p q n)
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) hS₀ hR hS T σ
  rw [cavity_finite_replica_covariance_eq rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop σ] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianCoordinateMap
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate projection needed to select the physical
special axes from the Gaussian spectral-group block. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
lemma cavity_gaussian_coordinate_hasGaussianLaw (S : Matrix I I ℝ) (e : J → I) :
    HasGaussianLaw (cavityGaussianCoordinateMap e) (multivariateGaussian 0 S) := by
  let L : EuclideanSpace ℝ I →L[ℝ] (J → ℝ) :=
    ContinuousLinearMap.pi (fun j => EuclideanSpace.proj (e j))
  have h := ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian
    (0 : EuclideanSpace ℝ I) S)).map L).toLp_pi 2
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext z j
  rfl

omit [DecidableEq J] in
lemma cavity_gaussian_coordinate_mean (S : Matrix I I ℝ) (e : J → I) :
    (∫ z, cavityGaussianCoordinateMap e z ∂multivariateGaussian 0 S) = 0 := by
  have hy := cavity_gaussian_coordinate_hasGaussianLaw S e
  ext j
  have he := (EuclideanSpace.proj j).integral_comp_comm hy.integrable
  change (∫ z, cavityGaussianCoordinateMap e z j ∂multivariateGaussian 0 S) =
    (∫ z, cavityGaussianCoordinateMap e z ∂multivariateGaussian 0 S) j at he
  rw [← he]
  have hz := (EuclideanSpace.proj (e j)).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ I) S))
  change (∫ z : EuclideanSpace ℝ I, z (e j) ∂multivariateGaussian 0 S) =
    (∫ z : EuclideanSpace ℝ I, z ∂multivariateGaussian 0 S) (e j) at hz
  rw [integral_id_multivariateGaussian] at hz
  exact hz

/-- Coordinate selection retains the corresponding covariance submatrix,
including degenerate Gaussian laws. -/
theorem cavity_gaussian_coordinate_law (S : Matrix I I ℝ) (hS : S.PosSemidef)
    (e : J → I) :
    (multivariateGaussian (0 : EuclideanSpace ℝ I) S).map (cavityGaussianCoordinateMap e) =
      multivariateGaussian 0 (S.submatrix e e) := by
  classical
  have hy := cavity_gaussian_coordinate_hasGaussianLaw S e
  have := hy.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hy.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq]
    rw [cavity_gaussian_coordinate_mean, integral_id_multivariateGaussian]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
    · have he (i : J) : (fun x : EuclideanSpace ℝ J =>
          inner ℝ ((EuclideanSpace.basisFun J ℝ).toBasis i) x) = fun x => x i := by
        ext x
        simp [PiLp.inner_apply]
      simp_rw [he]
      rw [covariance_map_fun (by fun_prop) (by fun_prop) hy.aemeasurable,
        covariance_eval_multivariateGaussian (hS.submatrix e)]
      change cov[fun z : EuclideanSpace ℝ I => z (e i), fun z => z (e j);
        multivariateGaussian 0 S] = S (e i) (e j)
      exact covariance_eval_multivariateGaussian hS (e i) (e j)
    · exact IsGaussian.memLp_two_id
    · exact IsGaussian.memLp_two_id

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGroupSelection
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySelectedGroupProjection_apply _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting the assigned special axes from the Gaussian spectral-group
block gives precisely the finite cavity field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavity_finite_group_covariance_posSemidef {m n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (σ : Fin r → LabeledLeaf n) :
    (cavityGroupBlockCovariance k rho
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)).PosSemidef := by
  classical
  let v₀ : LabeledLeaf n := Classical.choice inferInstance
  let σ' := Function.extend Fin.val σ (fun _ => v₀)
  have hs (i : Fin r) : σ' i = σ i := Fin.val_injective.extend_apply σ (fun _ => v₀) i
  have hq' : Monotone (fun i => q (cavityFiniteLevel n i)) :=
    hq.comp (cavityFiniteLevel_monotone n)
  have hG (a : Fin m) := cavity_cascade_transformed_gram n hq'
    (cavityCanonicalCoordinate rho lam hrho hsum p a)
    (cavityCanonicalCoordinate_monotone rho lam hrho hsum p a)
    (cavityCanonicalCoordinate_nonneg rho lam hrho hsum p a _)
    (cavityCanonicalCoordinate_le_diagonal rho lam hrho hsum p a _) σ' r
  apply cavityGroupReplicaCovariance_posSemidef
  intro a
  have hh := (hG a).smul (inv_nonneg.mpr (hrho a).le)
  have heq : (fun i j : Fin r =>
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ i j a : ℝ) / rho a) =
      (rho a)⁻¹ • (fun i j : Fin r => if i = j then spectralGroupDiagonal rho lam hrho hsum p a
        else cavityCanonicalCoordinate rho lam hrho hsum p a
          (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ' i j)) := by
    funext i j
    simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock,
      cavityCanonicalDiagonal, cavityCanonicalLabel, cascadeScalarArray, hs,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    by_cases hij : i = j <;> simp [hij, mul_comm]
  rw [heq]
  exact hh

lemma cavity_selected_group_covariance {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin r → LabeledLeaf n) :
    (cavityGroupBlockCovariance k rho
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)).submatrix
        (cavitySelectedGroupIndex e) (cavitySelectedGroupIndex e) =
      cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ := by
  classical
  ext u v
  have haxes : (e u.2).1 = (e v.2).1 ∧ (e u.2).2 = (e v.2).2 ↔ u.2 = v.2 := by
    constructor
    · intro h
      exact he (Prod.ext h.1 h.2)
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  change (if (e u.2).1 = (e v.2).1 ∧ (e u.2).2 = (e v.2).2 then
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ u.1 v.1 (e u.2).1 : ℝ) /
        rho (e u.2).1 else 0) = _
  simp only [haxes]
  by_cases huv : u.2 = v.2
  · by_cases hij : u.1 = v.1 <;>
      simp [cavityFiniteCanonicalReplicaCovariance, huv, cavityFiniteReplicaSpectralBlock,
        cavitySynchronizedBlock, cavityCanonicalDiagonal, cavityCanonicalLabel, heg, hij]
  · simp [cavityFiniteCanonicalReplicaCovariance, huv]

/-- The physical selected coordinates have exactly the covariance of
root-plus-forest cavity replicas. Unselected axes integrate out. -/
theorem cavity_selected_group_gaussian_law {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (σ : Fin r → LabeledLeaf n) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × (Fin r × Fin k)))
      (cavityGroupBlockCovariance k rho
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))).map
      (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e)) =
      multivariateGaussian 0 (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
  have hh := cavity_gaussian_coordinate_law _
    (cavity_finite_group_covariance_posSemidef rho lam hrho hsum p q hq σ)
    (cavitySelectedGroupIndex e)
  rwa [cavity_selected_group_covariance rho lam hrho hsum g e he heg p q σ] at hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaGaussianAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded replica tests may be averaged over the actual Gaussian
root and forest before, or after, sampling the labeled leaves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma measurable_cavityReplicaField {r d : ℕ} (n : ℕ) (T : LabeledTree n)
    (σ : Fin r → LabeledLeaf n) : Measurable (cavityReplicaField (d := d) n T σ) := by
  let F : (CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin r × Fin d) :=
    fun z => cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a : cavityReplicaNodeSupport n σ => z a)
  have hF : Measurable F := by
    unfold F cavityGaussianNodeSum
    fun_prop
  have he : F ∘ cavityReplicaNodeJoin (d := d) n r = cavityReplicaField n T σ := by
    funext z
    exact cavity_replica_node_field n σ T z
  rw [← he]
  exact hF.comp (measurable_cavityReplicaNodeJoin n r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedReplicaTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable tests of the physical selected axes can be evaluated
under the original finite Gaussian root/forest/residual law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_selected_group_gaussian_test {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (F : EuclideanSpace ℝ (Fin r × Fin d) → ℝ) (hF : Measurable F) :
    (∫ z, F (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))) =
      ∫ z, F (cavityReplicaField n T σ z)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))) := by
  have hselect := cavity_selected_group_gaussian_law rho lam hrho hsum g e he heg
    p q hq.monotone σ
  have hfield := cavity_finite_replica_field_law rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop T σ
  calc
    _ = ∫ y, F y ∂multivariateGaussian 0
        (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
      rw [← hselect]
      exact (integral_map (by unfold cavityGaussianCoordinateMap; fun_prop)
        hF.aestronglyMeasurable).symm
    _ = _ := by
      rw [← hfield]
      exact integral_map (measurable_cavityReplicaField n T σ).aemeasurable
        hF.aestronglyMeasurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedCappedSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped spin factor in the Haar comparison is exactly the
finite root/forest/residual spin factor after selecting its assigned axes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityCappedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) : Measurable (cavityCappedFlatSpinValue K L C τ π F) := by
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin r × Fin d) × (Fin r → Spin k) =>
      (∏ i, Real.exp (min (cavityLogFactor K L C
        (WithLp.toLp 2 (fun a => z.1 (i, a))) (z.2 i)) τ)) * F z.2) := by
    apply measurable_from_prod_countable_left
    intro ε
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      apply Measurable.exp
      apply Measurable.min _ measurable_const
      exact (continuous_cavityLogFactor K L C (ε i)).measurable.comp (by fun_prop)
    · change Measurable (fun _ : EuclideanSpace ℝ (Fin r × Fin d) => F ε)
      exact measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma cavity_capped_selected_eq_flat {m r d k q : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (e : Fin d → Fin m × Fin q) (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (B : SpectralBlock m r) (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F (B, z) =
      cavityCappedFlatSpinValue K L C τ π (fun ε => F (B, ε))
        (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z) := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedCappedAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded capped spin factors may be averaged in either Gaussian-first
or leaf-first order, so the physical Gaussian block and finite cavity
factor have the same averaged replica numerator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavityCappedFlatSpinValue_bound {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) {M : ℝ} (hF : ∀ ε, ‖F ε‖ ≤ M)
    (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    ‖cavityCappedFlatSpinValue K L C τ π F y‖ ≤ (Real.exp τ)^r * M := by
  have hb (ε : Fin r → Spin k) :
      ‖(∏ i, Real.exp (min (cavityLogFactor K L C
        (WithLp.toLp 2 (fun a => y (i, a))) (ε i)) τ)) * F ε‖ ≤ (Real.exp τ)^r * M := by
    rw [norm_mul]
    apply mul_le_mul _ (hF ε) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hi := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => π)) (ae_of_all _ hb)
  simpa only [cavityCappedFlatSpinValue, probReal_univ, mul_one] using hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite replica product measures may be separated into their leaf,
ordinary residual and spin coordinates before normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_replica_product_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {r : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : (Fin r → X × Y) → ℝ) (hF : Measurable F) {M : ℝ}
    (hbound : ∀ ξ, ‖F ξ‖ ≤ M) :
    (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin r => μ.prod ν)) =
      ∫ x, ∫ y, F (fun i => (x i, y i))
        ∂Measure.pi (fun _ : Fin r => ν) ∂Measure.pi (fun _ : Fin r => μ) := by
  let G : (Fin r → X) × (Fin r → Y) → ℝ := fun p => F (fun i => (p.1 i, p.2 i))
  have hG : Measurable G := hF.comp (Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hi : Integrable G ((Measure.pi (fun _ : Fin r => μ)).prod
      (Measure.pi (fun _ : Fin r => ν))) :=
    (integrable_const M).mono' hG.aestronglyMeasurable (ae_of_all _ fun p => hbound _)
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin r)
    (fun _ => μ) (fun _ => ν)).hasLaw.integral_comp hG.aestronglyMeasurable
  calc
    _ = ∫ p, G p ∂(Measure.pi (fun _ : Fin r => μ)).prod
        (Measure.pi (fun _ : Fin r => ν)) := by
      simpa [G, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow] using he
    _ = _ := integral_prod G hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cavity model in a fixed measurable state space:
the tree, Gaussian root and forest are disorder; the leaf, ordinary
residual and Ising spin form the configuration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma measurable_cavityLabeledField {d : ℕ} (n : ℕ) :
    Measurable (fun p : CavityLabeledDisorder d n × LabeledLeaf n =>
      cavityLabeledField n p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro α
  change Measurable (fun ω : CavityLabeledDisorder d n =>
    ω.2.1 + ∑ i : Fin n, ω.2.2 (edgeAt n α i))
  exact measurable_snd.fst.add (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply (edgeAt n α i)).comp measurable_snd.snd)

lemma measurable_cavityLabeledEndpoint {d k : ℕ} (n : ℕ) :
    Measurable (cavityLabeledEndpoint (d := d) (k := k) n) := by
  have ha : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      (p.1, p.2.1.1)) := measurable_fst.prodMk measurable_snd.fst.fst
  have hf : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1) := (measurable_cavityLabeledField (d := d) n).comp ha
  have hr : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.1.2) := measurable_snd.fst.snd
  have hy : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1 + p.2.1.2) := hf.add hr
  have hs : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.2) := measurable_snd.snd
  exact hy.prodMk hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModelNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and the literal product-prior formula for the finite
cavity numerator used in extra-replica normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityLabeledReplicaTest {m r d k n : ℕ}
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledReplicaTest (d := d) B F) := by
  have hl : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).1.1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).fst.fst
  have hs : Measurable (fun p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n) =>
      fun i => (p.2 i).2) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd).snd
  exact F.continuous.measurable.comp (((measurable_of_countable B).comp hl).prodMk hs)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityExtraReplicaPrefix
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extra replicas are tested by restriction to the original prefix.
This preserves the actual finite spectral observable when passing from
numerator moments to normalized cavity-spin expectations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_extra_replica_identity_fin {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    (∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)) *
      (∫ x, w x ∂ν) ^ k =
    ∫ ξ : Fin (r + k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (Fin.castAdd k i))
      ∂Measure.pi (fun _ => ν) := by
  rw [cavity_extra_replica_identity ν w F hw hF k]
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin r ⊕ Fin k => X) finSumFinEquiv.symm
  have hp : MeasurePreserving e (Measure.pi (fun _ : Fin (r + k) => ν))
      (Measure.pi (fun _ : Fin r ⊕ Fin k => ν)) :=
    measurePreserving_piCongrLeft (fun _ : Fin r ⊕ Fin k => ν) finSumFinEquiv.symm
  have hf : Measurable (fun ξ : (Fin r ⊕ Fin k) → X =>
      (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))) :=
    (Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).mul
      (hF.comp (Measurable.of_eval fun i : Fin r => measurable_pi_apply (Sum.inl i : Fin r ⊕ Fin k)))
  rw [← hp.hasLaw.integral_comp hf.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    have heq (i : Fin r ⊕ Fin k) : e ξ i = ξ (finSumFinEquiv i) := by
      simpa only [Equiv.symm_apply_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r ⊕ Fin k => X) finSumFinEquiv.symm ξ (finSumFinEquiv i))
    dsimp only [Function.comp_apply]
    simp_rw [heq]
    rw [finSumFinEquiv.prod_comp (fun i => w (ξ i))]
    rfl

lemma cavityFiniteReplicaSpectralBlock_prefix {m n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin (r + k) → LabeledLeaf n) :
    (fun i j => cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
      (Fin.castAdd k i) (Fin.castAdd k j)) =
      cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ (Fin.castAdd k i)) := by
  funext i j a
  simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, Fin.castAdd_inj]

lemma cavityLabeledReplicaTest_prefix {m n r k d qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ)
    (ω : CavityLabeledDisorder qdim n) (ξ : Fin (r + k) → CavityLabeledState qdim d n) :
    cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
      (cavityReplicaPrefixTest k F) (ω, ξ) =
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        F (ω, fun i => ξ (Fin.castAdd k i)) := by
  simp only [cavityLabeledReplicaTest, cavityReplicaPrefixTest,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    cavityFiniteReplicaSpectralBlock_prefix]


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteMeasurableAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cascade averaging for bounded measurable tests. This includes
the hard spatial restrictions used before normalizer regularization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_finite_block_measurable_average {m n r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (H : SpectralBlock m r → ℝ) (hH : Measurable H) {M : ℝ}
    (hbound : ∀ x, ‖H x‖ ≤ M) :
    (∫ x, H (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
        (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n,
        H (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hm : Measurable (fun x : JointArray => H
      (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
        (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x))) :=
    hH.comp ((continuous_cavitySynchronizedBlock _ _
      (continuous_cavityCanonicalLabel ρ eig hρ hsum p)).measurable.comp
      (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block ρ eig hρ hsum p q hq hq0 hq1]
  exact replicaLaw_integral_prefix (labeledCascadeLaw n b : Measure (LabeledTree n))
    (labeledLeafLaw n) (measurable_labeledLeafLaw n) _
    (fun σ => by simpa only [Real.norm_eq_abs] using
      (hbound (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ)))

theorem cavity_finite_gaussian_measurable_average {m n r k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) → ℝ)
    (hF : Measurable F) {M : ℝ} (hbound : ∀ x, ‖F x‖ ≤ M) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal ρ eig hρ hsum p)
      (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, F (B x,z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n, ∫ z,
        F (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ,z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ))
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  let κ := (cavityGaussianKernel (a := Fin m × (Fin r × Fin k))
    (L := SpectralBlock m r)).comap (fun x => (x,cavityGroupBlockCovariance k ρ x))
      (measurable_id.prodMk (continuous_cavityGroupBlockCovariance k ρ).measurable)
  let H : SpectralBlock m r → ℝ := fun x => ∫ z, F (x,z)
    ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ x)
  have hH : Measurable H :=
    hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ) |>.measurable
  have hb x : ‖H x‖ ≤ M := by
    have h := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × (Fin r × Fin k)))
        (cavityGroupBlockCovariance k ρ x)) (ae_of_all _ fun z => hbound (x,z))
    simpa only [H,probReal_univ,mul_one] using h
  exact cavity_finite_block_measurable_average ρ eig hρ hsum p q hq hq0 hq1 b H hH hb

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedRestrictedSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected finite Gaussian field preserves the hard replica
cutoff, as well as its capped spin factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityRestrictedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ B : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) :
    Measurable (cavityRestrictedFlatSpinValue K L C τ B π F) := by
  apply Measurable.ite _ (measurable_cavityCappedFlatSpinValue K L C τ π F) measurable_const
  have he : {y : EuclideanSpace ℝ (Fin r × Fin d) |
      ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2} =
      ⋂ i : Fin r, {y | 1+‖(WithLp.toLp 2 (fun a => y (i,a)) :
        EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2} := by ext y; simp
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le _ measurable_const
  fun_prop

lemma cavity_restricted_selected_eq_flat {m r d k q : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (e : Fin d → Fin m × Fin q) (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (block : SpectralBlock m r) (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityRestrictedSpinReplicaValue K L C τ B (cavitySelectedGroupProjection e) π F (block,z) =
      cavityRestrictedFlatSpinValue K L C τ B π (fun ε => F (block,ε))
        (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C τ hB]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  simp only [cavityReplicaRadius_le_iff _ _ hB,cavity_capped_selected_eq_flat]
  rfl

theorem cavity_selected_restricted_spin_test {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho B)) =
      ∫ z, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B, ε))
        (cavityReplicaField n T σ z)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))) := by
  intro B
  simp_rw [cavity_restricted_selected_eq_flat K L C τ hBcut]
  exact cavity_selected_group_gaussian_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop T σ _ (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary boundedness and product identities for the restricted
finite-spin factor used in the actual cavity Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityRestrictedFactor_mem {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    cavityRestrictedFactor K L C T B y ε ∈ Icc 0 (Real.exp T) := by
  unfold cavityRestrictedFactor
  split_ifs
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr (min_le_right _ _)⟩
  · exact ⟨le_rfl,(Real.exp_pos _).le⟩

lemma measurable_cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityRestrictedFactor K L C T B p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro ε
  apply Measurable.ite _ _ measurable_const
  · apply measurableSet_le _ measurable_const
    fun_prop
  · exact (((continuous_cavityLogFactor K L C ε).measurable).min measurable_const).exp

lemma measurable_cavityRestrictedFactor_comp {d k : ℕ} {E : Type*} [MeasurableSpace E]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (Y : E → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (ε : E → Spin k) (hε : Measurable ε) :
    Measurable (fun x => cavityRestrictedFactor K L C T B (Y x) (ε x)) := by
  have hp : Measurable (fun x => (Y x,ε x)) := hY.prodMk hε
  change Measurable ((fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ (fun x => (Y x,ε x)))
  exact Measurable.comp (g := fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) (f := fun x => (Y x,ε x))
      (measurable_cavityRestrictedFactor K L C T B) hp

lemma cavityRestrictedFlatSpinValue_bound {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) {M : ℝ} (hF : ∀ ε, ‖F ε‖ ≤ M)
    (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    ‖cavityRestrictedFlatSpinValue K L C T B π F y‖ ≤ (Real.exp T)^r * M := by
  unfold cavityRestrictedFlatSpinValue
  split_ifs
  · exact cavityCappedFlatSpinValue_bound K L C T π F hF y
  · rw [norm_zero]
    exact mul_nonneg (by positivity) ((norm_nonneg (F default)).trans (hF default))

lemma cavityRestrictedFlatSpinValue_eq {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    cavityRestrictedFlatSpinValue K L C T B π F y =
      ∫ ε : Fin r → Spin k, (∏ i, cavityRestrictedFactor K L C T B
        (WithLp.toLp 2 (fun a => y (i,a))) (ε i)) * F ε ∂Measure.pi (fun _ => π) := by
  classical
  by_cases hy : ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2
  · simp only [cavityRestrictedFlatSpinValue,hy,ite_true, if_true,cavityRestrictedFactor,
      cavityCappedFlatSpinValue]
    simp
  · obtain ⟨i,hi⟩ := not_forall.mp hy
    have hp (ε : Fin r → Spin k) : (∏ j, cavityRestrictedFactor K L C T B
        (WithLp.toLp 2 (fun a => y (j,a))) (ε j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [cavityRestrictedFactor,hi,ite_false, if_false])
    simp only [cavityRestrictedFlatSpinValue,hy,ite_false, if_false,hp,zero_mul,integral_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedRestrictedAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exchange of leaf and Gaussian integration for hard-restricted spin factors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_selected_restricted_spin_average {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n)
    (ν : Measure (Fin r → LabeledLeaf n)) [IsProbabilityMeasure ν]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun σ => cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, ∫ σ, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B σ, ε))
        (cavityReplicaField n T σ z) ∂ν
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n))))) =
      ∫ σ, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B σ, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B σ)) ∂ν := by
  intro B
  let P := ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
    (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
    (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
        (Measure.pi (fun _ : Fin r => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))
  have hm : Measurable (fun zσ :
      ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (Fin r → EuclideanSpace ℝ (Fin d))) × (Fin r → LabeledLeaf n) =>
      cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B zσ.2, ε))
        (cavityReplicaField n T zσ.2 zσ.1)) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B σ, ε))).comp
      (measurable_cavityReplicaField n T σ)
  have hi : Integrable (fun zσ => cavityRestrictedFlatSpinValue K L C τ Bcut π
      (fun ε => F (B zσ.2, ε)) (cavityReplicaField n T zσ.2 zσ.1)) (P.prod ν) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => cavityRestrictedFlatSpinValue_bound K L C τ Bcut π _
        (fun _ => F.norm_coe_le_norm _) _)
  rw [integral_integral_swap hi]
  exact integral_congr_ae (ae_of_all _ fun σ =>
    (cavity_selected_restricted_spin_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
      q hq hp htop T σ K L C τ hBcut π F).symm)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRestrictedAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped Gaussian-marked spectral cascade numerator is exactly
the numerator of the actual finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_cascade_restricted_spin_average {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (b : ℕ → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ z, ∫ σ : Fin r → LabeledLeaf n,
        cavityRestrictedFlatSpinValue K L C τ Bcut π
          (fun ε => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, ε))
          (cavityReplicaField n T σ z)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  have hav := cavity_finite_gaussian_measurable_average rho lam hrho hsum p q hq.monotone
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 htop.le b
    (cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F)
    (measurable_cavityRestrictedSpinReplicaValue K L C τ hBcut (cavitySelectedGroupProjection e) π F)
    (cavityRestrictedSpinReplicaValue_bound K L C τ hBcut (cavitySelectedGroupProjection e) π F)
  change (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) = _ at hav
  rw [hav]
  exact integral_congr_ae (ae_of_all _ fun T =>
    (cavity_selected_restricted_spin_average rho lam hrho hsum g e he heg p cut hcut hfirst hlast
      q hq hp htop T (Measure.pi (fun _ : Fin r => labeledLeafLaw n T)) K L C τ hBcut π F).symm)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedSpinNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spin-prior numerators for the selected physical Haar projections.
The shared projection matrix remains outside the replica product measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavitySelectedSiteProjection_replica {m r q d : ℕ} {N : Fin m → ℕ} {X : Type*}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) (σ : Fin r → X) :
    cavitySelectedGroupProjection e
      (cavityGroupMatrixProjection (fun a i => v a (σ i)) A) =
      fun i => cavitySelectedSiteProjection e v A (σ i) := by
  funext i
  ext j
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarNumeratorAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical capped numerator is the fresh-Haar test under the
infinite replica law, retaining the common original disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGroupMatrixProjection_uncurry {m r q : ℕ} (N : Fin m → ℕ) :
    Measurable (fun p : ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
      ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) => cavityGroupMatrixProjection p.1 p.2) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hc : Continuous (fun p : ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
      ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) => cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  exact hc.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarPriorMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary fourth moment bound after averaging over the original
Gibbs prior and the independent fresh Haar frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × X =>
      cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  dsimp only [cavitySelectedSiteProjection]
  apply Finset.measurable_sum
  intro l _
  exact (((measurable_pi_apply l).comp ((measurable_pi_apply (e j).1).comp
    ((hv x).comp measurable_fst))).mul
      (((measurable_pi_apply (e j).2).comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply (e j).1).comp
          ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma cavityUniformLevel_on_cell (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityUniformLevel n s = i := by
  apply Fin.ext
  change min n ⌊(n + 1 : ℕ) * s⌋₊ = i.val
  rw [floor_on_uniformCell n i hs, min_eq_right (Nat.le_of_lt_succ i.isLt)]

lemma cavityStrictUniformPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityStrictUniformPath p n s = cavityStrictUniformLevels p n i := by
  change cavityStrictUniformLevels p n (cavityUniformLevel n s) = _
  rw [cavityUniformLevel_on_cell n i hs]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySampledBlocks
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral arrays and finite blocks sampled from the same original
Gibbs configurations, with their disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavitySampledGroupBlock {m r : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω]
    (B : Ω → X → X → SpectralEntry (m + 1))
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) (σ : Fin r → X) :
    Measurable (fun ω => cavitySampledGroupBlock B ω σ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.castSucc).comp (hB (σ i) (σ j))

lemma measurable_cavitySampledGroupVectors {m r : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x)) :
    Measurable (fun p : Ω × (ℕ → X) => fun a (i : Fin r) => v p.1 a (p.2 i)) := by
  have hvj : Measurable (fun p : Ω × X => fun a => v p.1 a p.2) := by
    apply measurable_from_prod_countable_left
    exact hv
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply a).comp hvj).comp
    (measurable_fst.prodMk ((measurable_pi_apply (i : ℕ)).comp measurable_snd))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable physical cavity model, with original disorder and fresh
Haar frames outside the replica prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityHaarSpinReplicaTest {m r k : ℕ} {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityHaarSpinReplicaTest (U := U) B F) := by
  apply measurable_from_prod_countable_left
  intro σ
  change Measurable (fun z : Ω × U => F (B z.1 (fun i => (σ i).1), fun i => (σ i).2))
  exact F.continuous.measurable.comp
    (((hB (fun i => (σ i).1)).comp measurable_fst).prodMk
      (show Measurable (fun _ : Ω × U => fun i => (σ i).2) from measurable_const))

lemma cavityHaarSpinReplicaTest_bound {m r k : ℕ} {Ω X U : Type*}
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : (Ω × U) × (Fin r → X × Spin k)) :
    |cavityHaarSpinReplicaTest B F p| ≤ ‖F‖ := by
  exact (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded restricted factor as a measurable function of the
original disorder, fresh group rotation, base state and cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityHaarRestrictedWeight e v A₀ K L C T B) := by
  apply measurable_from_prod_countable_left
  intro x
  have hy : Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavitySelectedSiteProjection e (v z.1) (cavityGroupHaarFrames A₀ z.2) x.1) :=
    (measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const))
  exact measurable_cavityRestrictedFactor_comp K L C T B _ hy (fun _ => x.2) measurable_const

lemma cavityHaarRestrictedWeight_mem {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) :
    cavityHaarRestrictedWeight e v A₀ K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledRestrictedModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite labeled Gibbs numerator with its hard spatial
restriction and fixed logarithmic cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityLabeledRestrictedWeight {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityLabeledRestrictedWeight n K L C T B) :=
  (measurable_cavityRestrictedFactor K L C T B).comp (measurable_cavityLabeledEndpoint n)

lemma cavityLabeledRestrictedWeight_mem {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : CavityLabeledDisorder d n × CavityLabeledState d k n) :
    cavityLabeledRestrictedWeight n K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

lemma measurable_cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityLabeledRestrictedNumerator n K R L C π T Bcut B F) :=
  measurable_cavityWeightNumerator (cavityLabeledPriorKernel n R π)
    (cavityLabeledPriorKernel n R π).measurable _
    (measurable_cavityLabeledRestrictedWeight n K L C T Bcut) _
    (measurable_cavityLabeledReplicaTest B F)

lemma cavityLabeledRestrictedNumerator_bound {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    ‖cavityLabeledRestrictedNumerator n K R L C π T Bcut B F ω‖ ≤ ‖F‖*(Real.exp T)^r := by
  rw [Real.norm_eq_abs]
  apply cavityWeightNumerator_abs_le (cavityLabeledPriorKernel n R π ω) _ _
    (Real.exp_pos T).le (norm_nonneg F)
  · intro x
    rw [abs_of_nonneg (cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x)).1]
    exact (cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x)).2
  · intro ξ
    simpa only [cavityLabeledReplicaTest,Real.norm_eq_abs] using F.norm_coe_le_norm _

lemma cavityLabeledRestrictedNumerator_eq {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) :
    cavityLabeledRestrictedNumerator n K R L C π T Bcut B F ω =
      cavityWeightNumerator (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C T Bcut
          (cavityLeafSum n ω.2.1 (labeledNoiseLeaf _ n
            (ω.1,markForestOfCoords _ n ω.2.2) p.1.1)+p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1),fun i => (ξ i).2)) := by
  simp only [cavityLabeledRestrictedNumerator,cavityLabeledPriorKernel_apply,
    cavityLabeledRestrictedWeight,Function.comp_apply,cavityLabeledEndpoint,
    cavityLabeledReplicaTest,cavityLabeledField,cavity_labeled_leaf_sum]

lemma integral_cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ Bcut : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F ω
      ∂cavityLabeledDisorderLaw n b S₀ S) =
      ∫ T, ∫ sg, cavityWeightNumerator
        (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C τ Bcut
          (cavityLeafSum n sg.1 (labeledNoiseLeaf _ n
            (T, markForestOfCoords _ n sg.2) p.1.1) + p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hi : Integrable (cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F)
      (cavityLabeledDisorderLaw n b S₀ S) :=
    (integrable_const (‖F‖ * (Real.exp τ)^r)).mono'
      (measurable_cavityLabeledRestrictedNumerator n K R L C π τ Bcut B F).aestronglyMeasurable
      (ae_of_all _ (cavityLabeledRestrictedNumerator_bound n K R L C π τ Bcut B F))
  rw [cavityLabeledDisorderLaw, integral_prod _ hi]
  simp_rw [cavityLabeledRestrictedNumerator_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matching replica moments compare two varying models directly.
This applies to the physical system and a refining finite cascade without
postulating a limiting random probability measure for either model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

theorem cavity_moving_weighted_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : ∀ n, Measurable (W n)) (hD : ∀ n, Measurable (D n))
    {a b B : ℝ} (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc a b) (hWb : ∀ n ω, W n ω ∈ Icc a b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ n ω, |D n ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, A n ω * Z n ω ^ k ∂P n) - ∫ ω, D n ω * W n ω ^ k ∂Q n) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => (∫ ω, A n ω * f (Z n ω) ∂P n) -
      ∫ ω, D n ω * f (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (3 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηb : B * η < ε / 3 := by
    have he : 3 * (B + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf η hη
  have ht : Tendsto (fun n => (∫ ω, A n ω * p.eval (Z n ω) ∂P n) -
      ∫ ω, D n ω * p.eval (W n ω) ∂Q n) atTop (𝓝 0) := by
    simp_rw [cavity_weighted_polynomial_integral (P _) (Z _) (A _) (hZ _) (hA _)
        (hZb _) (hAb _) p,
      cavity_weighted_polynomial_integral (Q _) (W _) (D _) (hW _) (hD _)
        (hWb _) (hDb _) p, ← Finset.sum_sub_distrib, ← mul_sub]
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum p.support (fun k _ => (hmom k).const_mul (p.coeff k))
  have hclose := ht.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h1 := cavity_weighted_approx_error (P n) (Z n) (A n) (hZ n) (hA n)
    (hZb n) (hAb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have h2 := cavity_weighted_approx_error (Q n) (W n) (D n) (hW n) (hD n)
    (hWb n) (hDb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have htri := abs_sub_le (∫ ω, A n ω * f (Z n ω) ∂P n)
    (∫ ω, A n ω * p.eval (Z n ω) ∂P n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, A n ω * p.eval (Z n ω) ∂P n)
    (∫ ω, D n ω * p.eval (W n ω) ∂Q n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  rw [abs_sub_comm] at h1
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extra-replica comparison for a finite system and a refining cascade.
A positive denominator regularizer makes the matching-moment passage continuous. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_moving_regularized_reweighted_test
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : (n : ℕ) → Ξ n × Y n → ℝ) (hv : ∀ n, Measurable (v n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hG : ∀ n, Measurable (G n))
    {δ M B : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ n ω x, w n (ω, x) ∈ Icc 0 M) (hvb : ∀ n ω x, v n (ω, x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hGb : ∀ n ω σ, |G n (ω, σ)| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → X n,
        (∏ i, w n (ω, ξ i)) * F n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : (Fin r ⊕ Fin k) → Y n,
        (∏ i, v n (ω, ξ i)) * G n (ω, fun i => ξ (.inl i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean (ν n ω)
        (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) δ ∂P n) -
      ∫ ω, cavityRegularizedReplicaMean (ρ n ω)
        (fun x => v n (ω, x)) (fun σ => G n (ω, σ)) δ ∂Q n) atTop (𝓝 0) := by
  have hwabs n ω x : |w n (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hwb n ω x).1]
    exact (hwb n ω x).2
  have hvabs n ω x : |v n (ω, x)| ≤ M := by
    rw [abs_of_nonneg (hvb n ω x).1]
    exact (hvb n ω x).2
  have hmixed k : Tendsto (fun n =>
      (∫ ω, cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)) *
        cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)) ^ k ∂P n) -
      ∫ ω, cavityWeightNumerator (ρ n ω) (fun x => v n (ω, x)) (fun σ => G n (ω, σ)) *
        cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)) ^ k ∂Q n) atTop (𝓝 0) := by
    have hp n ω := cavityWeightNumerator_mul_normalizer (ν n ω) (fun x => w n (ω, x))
      (fun σ => F n (ω, σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) k
    have hq n ω := cavityWeightNumerator_mul_normalizer (ρ n ω) (fun x => v n (ω, x))
      (fun σ => G n (ω, σ)) ((hv n).comp measurable_prodMk_left)
      ((hG n).comp measurable_prodMk_left) k
    simpa only [hp, hq] using hmom k
  have hc : ContinuousOn (fun z : ℝ => 1 / (z + δ) ^ r) (Icc 0 M) :=
    continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow r)
      (fun z hz => pow_ne_zero _ (by linarith [hz.1]))
  have ht := cavity_moving_weighted_moments P Q
    (fun n ω => cavityWeightNormalizer (ν n ω) (fun x => w n (ω, x)))
    (fun n ω => cavityWeightNumerator (ν n ω) (fun x => w n (ω, x)) (fun σ => F n (ω, σ)))
    (fun n ω => cavityWeightNormalizer (ρ n ω) (fun x => v n (ω, x)))
    (fun n ω => cavityWeightNumerator (ρ n ω) (fun x => v n (ω, x)) (fun σ => G n (ω, σ)))
    (fun n => measurable_cavityWeightNormalizer (ν n) (hν n) (w n) (hw n))
    (fun n => measurable_cavityWeightNumerator (ν n) (hν n) (w n) (hw n) (F n) (hF n))
    (fun n => measurable_cavityWeightNormalizer (ρ n) (hρ n) (v n) (hv n))
    (fun n => measurable_cavityWeightNumerator (ρ n) (hρ n) (v n) (hv n) (G n) (hG n))
    (mul_nonneg hB (pow_nonneg hM r))
    (fun n ω => cavityWeightNormalizer_mem (ν n ω) _ ((hw n).comp measurable_prodMk_left)
      le_rfl (hwb n ω))
    (fun n ω => cavityWeightNormalizer_mem (ρ n ω) _ ((hv n).comp measurable_prodMk_left)
      le_rfl (hvb n ω))
    (fun n ω => cavityWeightNumerator_abs_le (ν n ω) _ _ hM hB (hwabs n ω) (hFb n ω))
    (fun n ω => cavityWeightNumerator_abs_le (ρ n ω) _ _ hM hB (hvabs n ω) (hGb n ω))
    hmixed _ hc
  simpa only [cavityRegularizedReplicaMean, one_div, ← div_eq_mul_inv] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingRestrictedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded nonnegative restricted weights can be normalized after the
extra-replica limit with a fixed positive denominator regularizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_moving_regularized_test_fin
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : (n : ℕ) → Ξ n × Y n → ℝ) (hv : ∀ n, Measurable (v n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hG : ∀ n, Measurable (G n))
    {δ M B : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ n ω x, w n (ω,x) ∈ Icc 0 M) (hvb : ∀ n ω x, v n (ω,x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω,σ)| ≤ B) (hGb : ∀ n ω σ, |G n (ω,σ)| ≤ B)
    (hmom : ∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin (r+j) → X n,
        (∏ i, w n (ω,ξ i)) * F n (ω,fun i => ξ (Fin.castAdd j i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : Fin (r+j) → Y n,
        (∏ i, v n (ω,ξ i)) * G n (ω,fun i => ξ (Fin.castAdd j i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean (ν n ω) (fun x => w n (ω,x))
        (fun σ => F n (ω,σ)) δ ∂P n) -
      ∫ ω, cavityRegularizedReplicaMean (ρ n ω) (fun x => v n (ω,x))
        (fun σ => G n (ω,σ)) δ ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_regularized_reweighted_test P Q ν hν ρ hρ w hw v hv F hF G hG
    hδ hM hB hwb hvb hFb hGb
  intro j
  have hp n ω := (cavity_extra_replica_identity (ν n ω) (fun x => w n (ω,x))
    (fun σ => F n (ω,σ)) ((hw n).comp measurable_prodMk_left)
    ((hF n).comp measurable_prodMk_left) j).symm.trans
    (cavity_extra_replica_identity_fin (ν n ω) (fun x => w n (ω,x))
      (fun σ => F n (ω,σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) j)
  have hq n ω := (cavity_extra_replica_identity (ρ n ω) (fun x => v n (ω,x))
    (fun σ => G n (ω,σ)) ((hv n).comp measurable_prodMk_left)
    ((hG n).comp measurable_prodMk_left) j).symm.trans
    (cavity_extra_replica_identity_fin (ρ n ω) (fun x => v n (ω,x))
      (fun σ => G n (ω,σ)) ((hv n).comp measurable_prodMk_left)
      ((hG n).comp measurable_prodMk_left) j)
  simpa only [hp,hq] using hmom j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRestrictedComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-floor normalization of the actual physical and finite-cascade
restricted spin numerators. All weight bounds are proved pointwise. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_spin_comparison {m q d k r : ℕ}
    (N : ℕ → Fin m → ℕ)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (B : (n : ℕ) → Ω n → X n → X n → SpectralEntry m)
    (hB : ∀ n x y, Measurable (fun ω => B n ω x y))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut δ : ℝ) (hδ : 0 < δ) (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (hraw : ∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, cavityWeightNumerator ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut (ω,x))
        (cavityProjectedSpinTest (fun σ i l => B n ω.1 (σ i) (σ l))
          (cavityReplicaPrefixTest j F)) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityLabeledRestrictedNumerator n K
        (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
          (cavityStrictUniformLevels p n) n) L C π T Bcut
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
          (cavityStrictUniformLevels p n)) (cavityReplicaPrefixTest j F) ω
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut (ω,x))
        (cavityProjectedSpinTest (fun σ i l => B n ω.1 (σ i) (σ l)) F) δ
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityRegularizedReplicaMean
        (cavityLabeledPriorKernel n
          (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n) n) π ω)
        (fun x => cavityLabeledRestrictedWeight n K L C T Bcut (ω,x))
        (fun σ => cavityLabeledReplicaTest
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n)) F (ω,σ)) δ
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0) := by
  let Q n := cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
    (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n))
    (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n) (uniformCut n)
      (cavityStrictUniformLevels p n))
  let ν₁ n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a)) (ν n) (hν n) π
  let ν₂ n := cavityLabeledPriorKernel n
    (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n) n) π
  let w n := cavityHaarRestrictedWeight e (v n) (A₀ n) K L C T Bcut
  let w₂ n := cavityLabeledRestrictedWeight n K L C T Bcut
  let F₁ n := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a))
    (fun ω σ i l => B n ω (σ i) (σ l)) F
  let F₂ n := cavityLabeledReplicaTest (d := d)
    (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum (cavityStrictUniformPath p n)
      (cavityStrictUniformLevels p n)) F
  have hfB n (σ : Fin r → X n) : Measurable (fun ω => fun (i l : Fin r) => B n ω (σ i) (σ l)) :=
    Measurable.of_eval fun i => Measurable.of_eval fun l => hB n (σ i) (σ l)
  have hout := cavity_moving_regularized_test_fin
    (fun n => (P n).prod (Measure.pi (μ n))) Q (fun n ω => ν₁ n ω)
    (fun n => (ν₁ n).measurable)
    (fun n ω => ν₂ n ω) (fun n => (ν₂ n).measurable) w
    (fun n => measurable_cavityHaarRestrictedWeight e (v n) (hvM n) (A₀ n) K L C T Bcut)
    w₂ (fun n => measurable_cavityLabeledRestrictedWeight n K L C T Bcut)
    F₁ (fun n => measurable_cavityHaarSpinReplicaTest _ (hfB n) F)
    F₂ (fun n => measurable_cavityLabeledReplicaTest _ F)
    hδ (Real.exp_pos T).le (norm_nonneg F)
    (fun n ω x => cavityHaarRestrictedWeight_mem e (v n) (A₀ n) K L C T Bcut (ω,x))
    (fun n ω x => cavityLabeledRestrictedWeight_mem n K L C T Bcut (ω,x))
    (fun n ω σ => cavityHaarSpinReplicaTest_bound _ F (ω,σ))
    (fun n ω σ => (Real.norm_eq_abs _).symm.trans_le (F.norm_coe_le_norm _)) ?_
  · simpa only [ν₁,ν₂,cavityHaarSpinPriorKernel_apply,w,w₂,F₁,F₂,cavityHaarSpinReplicaTest,Q] using hout
  · intro j
    convert hraw j using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    congr 1
    · apply integral_congr_ae
      filter_upwards [] with ω
      unfold cavityWeightNumerator
      simp only [ν₁,cavityHaarSpinPriorKernel_apply]
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [w,F₁,cavityHaarSpinReplicaTest,cavityProjectedSpinTest,cavityReplicaPrefixTest]
      rfl
    · apply integral_congr_ae
      filter_upwards [] with ω
      unfold cavityLabeledRestrictedNumerator cavityWeightNumerator
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [w₂,F₂,cavityLabeledReplicaTest_prefix]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledRestrictedNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hard-restricted finite cavity numerators expressed using the genuine product
prior on labeled leaves, ordinary Gaussian residuals and Ising spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_labeled_restricted_numerator {m n r d k : ℕ}
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (R : Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (Y : LabeledLeaf n → EuclideanSpace ℝ (Fin d))
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator ((ν.prod (multivariateGaussian 0 R)).prod π)
      (fun p => cavityRestrictedFactor K L C τ Bcut (Y p.1.1 + p.1.2) p.2)
      (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)) =
      ∫ z, ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
        (WithLp.toLp 2 (fun u => (Y (α u.1) + z u.1) u.2))
        ∂Measure.pi (fun _ : Fin r => ν)
        ∂Measure.pi (fun _ : Fin r => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) := by
  classical
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R
  let V := fun ξ : Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
    (∏ i, cavityRestrictedFactor K L C τ Bcut (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) *
      F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)
  have hlabel : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      fun i => (ξ i).1.1) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).fst.fst
  have hspin : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      fun i => (ξ i).2) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).snd
  have hw (i : Fin r) : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityRestrictedFactor K L C τ Bcut (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) := by
    have hy : Measurable (fun ξ :
        Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        Y (ξ i).1.1 + (ξ i).1.2) := ((measurable_of_countable Y).comp
      ((measurable_pi_apply i).fst.fst)).add ((measurable_pi_apply i).fst.snd)
    exact measurable_cavityRestrictedFactor_comp K L C τ Bcut _ hy _ (measurable_pi_apply i).snd
  have hV : Measurable V :=
    (Finset.measurable_prod _ (fun i _ => hw i)).mul
      (F.continuous.measurable.comp (((measurable_of_countable B).comp hlabel).prodMk hspin))
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    have hwpos i := (cavityRestrictedFactor_mem K L C τ Bcut
      (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2).1
    have hwle i := (cavityRestrictedFactor_mem K L C τ Bcut
      (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2).2
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun i _ => hwpos i))]
    exact (Finset.prod_le_prod (fun i _ => hwpos i) (fun i _ => hwle i)).trans_eq (by simp)
  let G := fun p : (Fin r → LabeledLeaf n) × (Fin r → EuclideanSpace ℝ (Fin d)) =>
    cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B p.1, ε))
      (WithLp.toLp 2 (fun u => (Y (p.1 u.1) + p.2 u.1) u.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro α
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))).comp
      (by fun_prop)
  have hGb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityRestrictedFlatSpinValue_bound K L C τ Bcut π _ (fun _ => F.norm_coe_le_norm _) _
  let H := fun x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d) =>
    G (fun i => (x i).1, fun i => (x i).2)
  have hH : Measurable H := hG.comp (by fun_prop)
  have heH (x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d)) :
      (∫ ε : Fin r → Spin k, V (fun i => (x i, ε i)) ∂Measure.pi (fun _ => π)) = H x := by
    simp only [H,G,cavityRestrictedFlatSpinValue_eq]
    rfl
  change (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin r => (ν.prod μ).prod π)) = _
  rw [cavity_replica_product_integral (ν.prod μ) π V hV hb]
  simp_rw [heH]
  rw [cavity_replica_product_integral ν μ H hH (fun x => hGb _)]
  have hi : Integrable G ((Measure.pi (fun _ : Fin r => ν)).prod
      (Measure.pi (fun _ : Fin r => μ))) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hG.aestronglyMeasurable
      (ae_of_all _ hGb)
  exact integral_integral_swap hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRestrictedNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-first hard-restricted formula is the ordinary replica numerator
of the full labeled cavity prior, with one residual sampled per replica. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_gaussian_restricted_numerator {m n r d k : ℕ}
    (T : LabeledTree n) (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ z, ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
        (cavityReplicaField n T α z) ∂Measure.pi (fun _ : Fin r => ν)
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
            (Measure.pi (fun _ : Fin r => multivariateGaussian
              (0 : EuclideanSpace ℝ (Fin d)) R)))) =
      ∫ sg, cavityWeightNumerator ((ν.prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C τ Bcut
          (cavityLeafSum n sg.1
            (labeledNoiseLeaf _ n (T, markForestOfCoords _ n sg.2) p.1.1) + p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))) := by
  let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  let μ := Measure.pi (fun _ : Fin r => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) R)
  let V := fun z : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d)) =>
    ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
      (cavityReplicaField n T α z) ∂Measure.pi (fun _ : Fin r => ν)
  have hm : Measurable (fun zα :
      ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (Fin r → EuclideanSpace ℝ (Fin d))) × (Fin r → LabeledLeaf n) =>
      cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B zα.2, ε))
        (cavityReplicaField n T zα.2 zα.1)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))).comp
      (measurable_cavityReplicaField n T α)
  have hV : Measurable V := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hb (z) : ‖V z‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    have hh := norm_integral_le_of_norm_le_const
      (μ := Measure.pi (fun _ : Fin r => ν)) (ae_of_all _ fun α =>
        cavityRestrictedFlatSpinValue_bound K L C τ Bcut π (fun ε => F (B α, ε))
          (fun ε => F.norm_coe_le_norm (B α, ε)) (cavityReplicaField n T α z))
    simpa only [V, probReal_univ, mul_one] using hh
  have hi : Integrable V (P.prod μ) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hV.aestronglyMeasurable (ae_of_all _ hb)
  change (∫ z, V z ∂P.prod μ) = _
  rw [integral_prod V hi]
  apply integral_congr_ae
  exact ae_of_all _ fun sg =>
    (cavity_labeled_restricted_numerator ν R K L C τ Bcut π
      (fun α => cavityLeafSum n sg.1 (labeledNoiseLeaf _ n
        (T, markForestOfCoords _ n sg.2) α)) B F).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRestrictedNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the capped spectral-block spin observable
with the ordinary finite cavity replica numerator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_numerator {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (b : ℕ → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ sg, cavityWeightNumerator
        (((labeledLeafLaw n T).prod (multivariateGaussian 0
          (cavityFiniteCovariancePath rho lam hrho hsum g p q n))).prod π)
        (fun v => cavityRestrictedFactor K L C τ Bcut
          (cavityLeafSum n sg.1
            (labeledNoiseLeaf _ n (T, markForestOfCoords _ n sg.2) v.1.1) + v.1.2) v.2)
        (fun ξ => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q
          (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  rw [cavity_finite_cascade_restricted_spin_average rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop b K L C τ hBcut π F]
  exact integral_congr_ae (ae_of_all _ fun T => cavity_gaussian_restricted_numerator T
    (labeledLeafLaw n T) _ _ _ K L C τ Bcut π
    (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRestrictedModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral Gaussian numerator in the measurable finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_finite_restricted_model_numerator {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (b : ℕ → ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ ω, cavityLabeledRestrictedNumerator n K
        (cavityFiniteCovariancePath rho lam hrho hsum g p q n) L C π τ Bcut
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q) F ω
        ∂cavityLabeledDisorderLaw n b
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)
          (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) := by
  intro B
  rw [integral_cavityLabeledRestrictedNumerator]
  exact cavity_finite_restricted_numerator rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop b K L C τ hBcut π F

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted physical Haar moments converge to the actual
finite labeled Gibbs numerators, including all Gaussian residuals. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_model_numerator_match {m r q dim kspin : ℕ}
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
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (hnull : (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r) : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = Bcut} = 0) :
    let F := cavityRestrictedSpinReplicaValue K L Cspin T Bcut (cavitySelectedGroupProjection e) π Fspin
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ x, ∫ U, F (cavitySpectralGroupBlock m r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) -
      ∫ ω, cavityLabeledRestrictedNumerator k K
        (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k) k) L Cspin π T Bcut
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k)) Fspin ω
        ∂cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (uniformCut k) (cavityStrictUniformLevels p k)))
      atTop (𝓝 0) := by
  intro F p
  have hh := cavity_haar_strict_restricted_spin_match N hN μ A₀ hA₀ X P a ha hGram v hvM C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
    K L Cspin T hBcut (cavitySelectedGroupProjection e) π Fspin hnull
  dsimp only at hh
  have heval (k : ℕ) := cavity_finite_restricted_model_numerator ρ eig hρ hρsum g e he heg
    (cavityStrictUniformPath p k) (uniformCut k) (uniformCut_strict k)
    (uniformCut_zero k) (uniformCut_last k) (cavityStrictUniformLevels p k)
    (cavityStrictUniformLevels_strict p k)
    (fun i s hs => cavityStrictUniformPath_on_cell p k i hs)
    (cavityStrictUniformLevels_mem p k (Fin.last k)).2
    (chainExponent (uniformCut k)) K L Cspin T hBcut π Fspin
  apply hh.congr'
  filter_upwards [] with k
  congr 1
  exact (cavityStrictMarkedLaw_integral ρ eig hρ hρsum p k _
    (measurable_cavityRestrictedSpinReplicaValue K L Cspin T hBcut
      (cavitySelectedGroupProjection e) π Fspin)
    (cavityRestrictedSpinReplicaValue_bound K L Cspin T hBcut
      (cavitySelectedGroupProjection e) π Fspin)).trans (heval k)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedRestrictedNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hard-restricted marked spin moment is the actual Gibbs
numerator with the same restriction on every replica. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_projected_restricted_spin_numerator {m r q d k : ℕ} {N : Fin m → ℕ}
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (B : (Fin r → X) → SpectralBlock m r)
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator (ν.prod π)
      (fun x => if 1+‖cavitySelectedSiteProjection e v A x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C
          (cavitySelectedSiteProjection e v A x.1) x.2) τ) else 0)
      (cavityProjectedSpinTest B F) =
    ∫ σ : Fin r → X, cavityRestrictedSpinReplicaValue K L C τ Bcut
      (cavitySelectedGroupProjection e) π F
      (B σ, cavityGroupMatrixProjection (fun a i => v a (σ i)) A)
      ∂Measure.pi (fun _ => ν) := by
  let V := fun ξ : Fin r → X × Spin k =>
    (∏ i, if 1+‖cavitySelectedSiteProjection e v A (ξ i).1‖^2 ≤ 1+Bcut^2 then
      Real.exp (min (cavityLogFactor K L C
        (cavitySelectedSiteProjection e v A (ξ i).1) (ξ i).2) τ) else 0) *
      cavityProjectedSpinTest B F ξ
  have hw (x : X × Spin k) :
      (if 1+‖cavitySelectedSiteProjection e v A x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C (cavitySelectedSiteProjection e v A x.1) x.2) τ)
        else 0) ∈ Set.Icc 0 (Real.exp τ) := by
    split_ifs
    · exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
    · exact ⟨le_rfl,(Real.exp_pos _).le⟩
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V,cavityProjectedSpinTest]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hw (ξ i)).1))]
    exact (Finset.prod_le_prod (fun i _ => (hw (ξ i)).1)
      (fun i _ => (hw (ξ i)).2)).trans_eq (by simp)
  change (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin r => ν.prod π)) = _
  rw [cavity_replica_product_integral ν π V (measurable_of_countable V) hb]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    simp only [cavityRestrictedSpinReplicaValue, cavitySelectedSiteProjection_replica]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical hard-restricted numerator is the fresh-Haar test under the
infinite replica law, retaining the common original disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityRestrictedHaarReplicaValue {m r q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
      cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
        (B p.1.1 p.2, cavityGroupMatrixProjection (fun a i => v p.1.1 a (p.2 i))
          (cavityGroupHaarFrames A₀ p.1.2))) := by
  apply measurable_from_prod_countable_left
  intro σ
  have hvec : Measurable (fun ω : Ω => fun a i => v ω a (σ i)) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => (measurable_pi_apply a).comp (hv (σ i))
  have hg : Measurable (fun p : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavityGroupMatrixProjection (fun a i => v p.1 a (σ i)) (cavityGroupHaarFrames A₀ p.2)) :=
    (measurable_cavityGroupMatrixProjection_uncurry N).comp
      ((hvec.comp measurable_fst).prodMk
        ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))
  exact (measurable_cavityRestrictedSpinReplicaValue K L C τ hBcut (cavitySelectedGroupProjection e) π F).comp
    (((hB σ).comp measurable_fst).prodMk hg)

theorem cavity_haar_restricted_spin_numerator_average {m r q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (hB : ∀ σ, Measurable (fun ω => B ω σ))
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ω, ∫ U, cavityWeightNumerator ((ν ω).prod π)
      (fun x => if 1+‖cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ U) x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C
          (cavitySelectedSiteProjection e (v ω) (cavityGroupHaarFrames A₀ U) x.1) x.2) τ) else 0)
      (cavityProjectedSpinTest (B ω) F) ∂Measure.pi μ ∂P) =
    ∫ z, ∫ U, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
      (B z.1 (fun i : Fin r => z.2 i),
        cavityGroupMatrixProjection (fun a i => v z.1 a (z.2 i)) (cavityGroupHaarFrames A₀ U))
      ∂Measure.pi μ ∂disorderReplicaLaw P ν hν := by
  let G := fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (Fin r → X) =>
    cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F
      (B p.1.1 p.2, cavityGroupMatrixProjection (fun a i => v p.1.1 a (p.2 i))
        (cavityGroupHaarFrames A₀ p.1.2))
  have hG : Measurable G := measurable_cavityRestrictedHaarReplicaValue
    (m := m) (r := r) (q := q) (d := d) (k := k) (N := N) (Ω := Ω) (X := X)
    A₀ B hB e v hv K L C τ hBcut π F
  have hb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityRestrictedSpinReplicaValue_bound K L C τ hBcut (cavitySelectedGroupProjection e) π F _
  have hswap := cavity_disorder_replica_prefix_swap_raw (Ω := Ω) (X := X)
    (U := (a : Fin m) → Orthogonal (N a)) (r := r) P ν hν (Measure.pi μ) G hG hb
  calc
    _ = ∫ ω, ∫ U, ∫ σ : Fin r → X, G ((ω, U), σ)
        ∂Measure.pi (fun _ => ν ω) ∂Measure.pi μ ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun U =>
        cavity_projected_restricted_spin_numerator (m := m) (r := r) (q := q) (d := d) (k := k)
          (N := N) (X := X) (ν ω) (B ω) e (v ω)
          (cavityGroupHaarFrames A₀ U) K L C τ Bcut π F)
    _ = _ := hswap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedGibbs
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical fresh-Haar limit for actual Gibbs-kernel numerators.
The original disorder is retained in every sampled spectral array. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_gibbs_numerator_match {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ k (x : Ω k × (ℕ → X k)) j i l, |cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin r) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
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
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T : ℝ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (hnull : (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m r) : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = Bcut} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun k =>
      (∫ ω, ∫ U, cavityWeightNumerator ((ν k ω).prod π)
        (fun x => if 1+‖cavitySelectedSiteProjection e (v₀ k ω) (cavityGroupHaarFrames (A₀ k) U) x.1‖^2 ≤ 1+Bcut^2 then
          Real.exp (min (cavityLogFactor K L Cspin
            (cavitySelectedSiteProjection e (v₀ k ω) (cavityGroupHaarFrames (A₀ k) U) x.1) x.2) T) else 0)
        (cavityProjectedSpinTest (cavitySampledGroupBlock (B k) ω) Fspin)
        ∂Measure.pi (μ k) ∂P k) -
      ∫ ω, cavityLabeledRestrictedNumerator k K
        (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k) k) L Cspin π T Bcut
        (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p k)
          (cavityStrictUniformLevels p k)) Fspin ω
        ∂cavityLabeledDisorderLaw k (chainExponent (uniformCut k))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (cavityStrictUniformLevels p k))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p k)
            (uniformCut k) (cavityStrictUniformLevels p k)))
      atTop (𝓝 0) := by
  intro p
  let v := fun k (x : Ω k × (ℕ → X k)) j (i : Fin r) => v₀ k x.1 j (x.2 i)
  have hh := cavity_haar_restricted_model_numerator_match N hN μ A₀ hA₀
    (fun k => Ω k × (ℕ → X k)) (fun k => disorderReplicaLaw (P k) (ν k) (hν k))
    (fun k => cavitySampledEntryArray (B k)) (fun k => measurable_cavitySampledEntryArray (B k) (hB k))
    hGram v (fun k => measurable_cavitySampledGroupVectors (v₀ k) (hvM k)) C hv
    ρs ρ eig hρs hρ hρlim hρsum hcov Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag
    g e he heg K L Cspin T π Fspin hBcut hnull
  have heval k := cavity_haar_restricted_spin_numerator_average (P k) (ν k) (hν k) (μ k) (A₀ k)
    (cavitySampledGroupBlock (B k))
    (fun σ => measurable_cavitySampledGroupBlock (B k) (hB k) σ)
    e (v₀ k) (hvM k) K L Cspin T hBcut π Fspin
  apply hh.congr'
  filter_upwards [] with k
  congr 1
  exact (heval k).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProductDisorder
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for the retained disorder and independent fresh rotations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma cavity_product_disorder_numerator {Ω U X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure U) [IsProbabilityMeasure Q]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {k r : ℕ} (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (w : (Ω × U) × (X × Spin k) → ℝ) (hw : Measurable w)
    (F : (Ω × U) × (Fin r → X × Spin k) → ℝ) (hF : Measurable F)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    (∫ ω, ∫ u, cavityWeightNumerator ((ν ω).prod π)
      (fun x => w ((ω,u),x)) (fun σ => F ((ω,u),σ)) ∂Q ∂P) =
    ∫ p, cavityWeightNumerator ((ν p.1).prod π)
      (fun x => w (p,x)) (fun σ => F (p,σ)) ∂P.prod Q := by
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν π
  have hm := measurable_cavityWeightNumerator (fun p => κ p) κ.measurable w hw F hF
  have hb p : |cavityWeightNumerator (κ p) (fun x => w (p,x))
      (fun σ => F (p,σ))| ≤ B * M^r :=
    cavityWeightNumerator_abs_le (κ p) _ _ hM hB
      (fun x => by rw [abs_of_nonneg (hwb p x).1]; exact (hwb p x).2) (hFb p)
  have hi := Integrable.of_bound (μ := P.prod Q) hm.aestronglyMeasurable
    (B * M^r) (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  simpa only [κ,cavityHaarSpinPriorKernel_apply] using (integral_prod _ hi).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedRegularized
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical Haar Gibbs means and the finite cascade agree after
spatial restriction and fixed positive denominator regularization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_gibbs_regularized_match_oai {m r q dim kspin : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (Ω X : ℕ → Type*) [∀ k, MeasurableSpace (Ω k)] [∀ k, MeasurableSpace (X k)]
    [∀ k, Countable (X k)] [∀ k, MeasurableSingletonClass (X k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (ν : (k : ℕ) → Ω k → Measure (X k)) (hν : ∀ k, Measurable (ν k))
    [∀ k ω, IsProbabilityMeasure (ν k ω)]
    (B : (k : ℕ) → Ω k → X k → X k → SpectralEntry (m + 1))
    (hB : ∀ k x y, Measurable (fun ω => B k ω x y))
    (hGram : ∀ k x, SpectralGram (cavitySampledEntryArray (B k) x))
    (v₀ : (k : ℕ) → Ω k → (j : Fin m) → X k → Fin (N k j) → ℝ)
    (hvM : ∀ k x, Measurable (fun ω j => v₀ k ω j x))
    (C : ℝ)
    (hv : ∀ s k (x : Ω k × (ℕ → X k)) j (i l : Fin s), |cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i)) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ eig : Fin m → ℝ)
    (hρs : ∀ k j, 0 < ρs k j) (hρ : ∀ j, 0 < ρ j)
    (hρlim : Tendsto ρs atTop (𝓝 ρ)) (hρsum : ∑ j, ρ j = 1)
    (hcov : ∀ s k (x : Ω k × (ℕ → X k)), cavityGroupReplicaCovariance q (cavityGroupReplicaGram (fun j (i : Fin s) => v₀ k x.1 j (x.2 i))) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) s (cavitySampledEntryArray (B k) x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (disorderReplicaLaw (P k) (ν k) (hν k)).map (cavitySampledEntryArray (B k)))
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
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (K : Matrix (Fin dim) (Fin dim) ℝ) (L : Matrix (Fin dim) (Fin kspin) ℝ)
    (Cspin : Matrix (Fin kspin) (Fin kspin) ℝ) (T δ : ℝ) (hδ : 0 < δ)
    (π : Measure (Spin kspin)) [IsProbabilityMeasure π]
    (Fspin : SpectralBlock m r × (Fin r → Spin kspin) →ᵇ ℝ)
    {Bcut : ℝ} (hBcut : 0 ≤ Bcut)
    (hnull : ∀ s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = Bcut} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean ((ν n ω.1).prod π)
        (fun x => cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin T Bcut (ω,x))
        (cavityProjectedSpinTest (cavitySampledGroupBlock (B n) ω.1) Fspin) δ
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, cavityRegularizedReplicaMean
        (cavityLabeledPriorKernel n
          (cavityFiniteCovariancePath ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n) n) π ω)
        (fun x => cavityLabeledRestrictedWeight n K L Cspin T Bcut (ω,x))
        (fun σ => cavityLabeledReplicaTest
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hρsum (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n)) Fspin (ω,σ)) δ
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hρsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) atTop (𝓝 0) := by
  intro p
  have hBg n x y : Measurable (fun (ω : Ω n) (a : Fin m) => B n ω x y a.castSucc) :=
    Measurable.of_eval fun a => (measurable_pi_apply a.castSucc).comp (hB n x y)
  apply cavity_finite_restricted_spin_comparison N μ Ω X P ν hν e v₀ hvM A₀
    (fun n ω x y a => B n ω x y a.castSucc) hBg ρ eig hρ hρsum g p
    K L Cspin π T Bcut δ hδ Fspin
  intro j
  have h := cavity_haar_restricted_gibbs_numerator_match N hN μ A₀ hA₀ Ω X P ν hν B hB
    hGram v₀ hvM C (hv (r+j)) ρs ρ eig hρs hρ hρlim hρsum (hcov (r+j))
    Q Q₀ hQ hlim hgg hG d hd0 hd hE hP hn hoff hdiag g e he heg
    K L Cspin T π (cavityReplicaPrefixTest j Fspin) hBcut (hnull (r+j))
  apply h.congr'
  filter_upwards [] with n
  congr 1
  let w := cavityHaarRestrictedWeight e (v₀ n) (A₀ n) K L Cspin T Bcut
  let f := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a))
    (cavitySampledGroupBlock (B n)) (cavityReplicaPrefixTest j Fspin)
  have hf := measurable_cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N n a)) (cavitySampledGroupBlock (B n))
    (measurable_cavitySampledGroupBlock (B n) (hB n)) (cavityReplicaPrefixTest j Fspin)
  have hi := cavity_product_disorder_numerator (P n) (Measure.pi (μ n)) (ν n) (hν n) π
    w (measurable_cavityHaarRestrictedWeight e (v₀ n) (hvM n) (A₀ n) K L Cspin T Bcut)
    f hf (Real.exp_pos T).le (norm_nonneg (cavityReplicaPrefixTest j Fspin))
    (fun ω x => cavityHaarRestrictedWeight_mem e (v₀ n) (A₀ n) K L Cspin T Bcut (ω,x))
    (fun ω σ => cavityHaarSpinReplicaTest_bound _ (cavityReplicaPrefixTest j Fspin) (ω,σ))
  exact hi

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match_oai.{u_1, u_2} := @OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match_oai.{u_1, u_2}
