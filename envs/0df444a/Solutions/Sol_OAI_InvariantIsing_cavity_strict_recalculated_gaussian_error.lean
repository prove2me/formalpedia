-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:41.109204+00:00
-- url     : https://prove2.me/submissions/44b7e49e-7ef2-4bf0-b36f-1c10080f8243

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
import Mathlib.MeasureTheory.Measure.Tilted
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
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_finite_compact_block
import Theorems.Thm_OAI_InvariantIsing_continuous_cavityCanonicalLabel
import Theorems.Thm_OAI_InvariantIsing_continuous_cavitySynchronizedBlock
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_integral
import Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_spin

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero
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

theorem projectedResolventDerivative_le_one (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) :
    projectedResolventDerivative ρ eig hρ hρsum a x ≤ 1 := by
  rw [← sum_projectedResolventDerivative ρ eig hρ hρsum x]
  exact Finset.single_le_sum
    (fun b _ => (projectedResolventDerivative_pos ρ eig hρ hρsum b x).le)
    (Finset.mem_univ a)

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
namespace IsingPerceptron

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

lemma uniformCell_right_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ)) atTop (𝓝 u) := by
  simpa only [add_div,Nat.cast_add,Nat.cast_one,add_zero] using
    (uniformCell_left_tendsto hu).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellAverage_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) (hc : ContinuousAt q u) :
    Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hc.tendsto.comp (uniformCell_left_tendsto hu)) (hc.tendsto.comp (uniformCell_right_tendsto hu))
    (fun n => (uniformCellAverage_bounds hq hb n _).1) (fun n => (uniformCellAverage_bounds hq hb n _).2)

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

lemma uniformCellAverage_ae_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  filter_upwards [monotone_ae_continuous_unit hq,ae_restrict_mem measurableSet_Ioo] with u hc hu
  exact uniformCellAverage_tendsto hq hb ⟨hu.1.le,hu.2⟩ hc

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariancePositive
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCascadeCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

theorem spectralPathDensity_le_one
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) (r : ℝ) :
    spectralPathDensity ρ eig hρ hρsum p a r ≤ 1 :=
  projectedResolventDerivative_le_one ρ eig hρ hρsum a (deficit p r)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteHeightContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform continuity of finite spectral replica blocks in their
scalar overlap levels, including tied levels and the endpoint one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavityCanonicalCoordinate_dist_le {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : Fin m) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |cavityCanonicalCoordinate rho lam hrho hsum p a s -
      cavityCanonicalCoordinate rho lam hrho hsum p a t| ≤ |s - t| := by
  simp only [cavityCanonicalCoordinate, Set.projIcc_of_mem zero_le_one hs,
    Set.projIcc_of_mem zero_le_one ht]
  rw [intervalIntegral.integral_interval_sub_left
    (spectralPathDensity_intervalIntegrable rho lam hrho hsum p a hs)
    (spectralPathDensity_intervalIntegrable rho lam hrho hsum p a ht)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 1)
    (f := spectralPathDensity rho lam hrho hsum p a) (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (spectralPathDensity_nonneg rho lam hrho hsum p a r)]
      exact spectralPathDensity_le_one rho lam hrho hsum p a r)
  simpa only [Real.norm_eq_abs, one_mul] using hb

lemma cavity_finite_block_dist_le {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q q' : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc 0 1) (hq' : ∀ i, q' i ∈ Icc 0 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ i, |q i - q' i| ≤ δ)
    (σ : Fin r → LabeledLeaf n) :
    dist (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q' σ) ≤ δ := by
  apply (dist_pi_le_iff hδ).mpr
  intro i
  apply (dist_pi_le_iff hδ).mpr
  intro j
  apply (dist_pi_le_iff hδ).mpr
  intro a
  by_cases hij : i = j
  · simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, ite_eq_left hij, dist_self]
    exact hδ
  · simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, ite_eq_right hij]
    change |cavityCanonicalCoordinate rho lam hrho hsum p a _ -
      cavityCanonicalCoordinate rho lam hrho hsum p a _| ≤ δ
    exact (cavityCanonicalCoordinate_dist_le rho lam hrho hsum p a (hq _) (hq' _)).trans (hclose _)

lemma cavity_finite_height_test_uniform {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (F : SpectralBlock m r →ᵇ ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ n (q q' : Fin (n + 1) → ℝ),
      (∀ i, q i ∈ Icc 0 1) → (∀ i, q' i ∈ Icc 0 1) →
      (∀ i, |q i - q' i| ≤ δ) → ∀ σ : Fin r → LabeledLeaf n,
      |F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ) -
        F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q' σ)| < ε := by
  intro ε hε
  have hu := (isCompact_univ : IsCompact (univ : Set (SpectralBlock m r))).uniformContinuousOn_of_continuous
    F.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ / 2, half_pos hδ, fun n q q' hq hq' hc σ => ?_⟩
  apply hmod _ (mem_univ _) _ (mem_univ _)
  exact (cavity_finite_block_dist_le rho lam hrho hsum p q q' hq hq'
    (half_pos hδ).le hc σ).trans_lt (half_lt_self hδ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteHeightLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small uniform changes of overlap levels do not change the limiting
spectral-block tests, even when the finite cascade depth grows. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_finite_block_replica_average {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (F : SpectralBlock m r →ᵇ ℝ) :
    (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ σ, F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i))
        ∂replicaLaw (labeledCascadeLaw n b : Measure (LabeledTree n)) (labeledLeafLaw n)
          (measurable_labeledLeafLaw n) := by
  have hm : Measurable (fun x : JointArray => F
      (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))) :=
    F.continuous.measurable.comp
      ((continuous_cavitySynchronizedBlock _ _
        (continuous_cavityCanonicalLabel rho lam hrho hsum p)).measurable.comp
        (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block rho lam hrho hsum p q hq hq0 hq1]
  rfl

theorem cavity_finite_height_integral_error {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q q' : (n : ℕ) → Fin (n + 1) → ℝ)
    (hq : ∀ n, Monotone (q n)) (hq' : ∀ n, Monotone (q' n))
    (hqunit : ∀ n i, q n i ∈ Icc 0 1) (hq'unit : ∀ n i, q' n i ∈ Icc 0 1)
    (b : ℕ → ℕ → ℝ) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hclose : ∀ n i, |q n i - q' n i| ≤ η n) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (b n) (fun i => q n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (b n) (fun i => q' n (cavityFiniteLevel n i)) : Measure JointArray))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := cavity_finite_height_test_uniform rho lam hrho hsum p F
    (ε / 2) (half_pos hε)
  filter_upwards [hη.eventually (Iio_mem_nhds hδ)] with n hn
  rw [Real.dist_eq, sub_zero,
    cavity_finite_block_replica_average rho lam hrho hsum p (q n) (hq n)
      (hqunit n 0).1 (hqunit n (Fin.last n)).2 (b n) F,
    cavity_finite_block_replica_average rho lam hrho hsum p (q' n) (hq' n)
      (hq'unit n 0).1 (hq'unit n (Fin.last n)).2 (b n) F]
  let μ := replicaLaw (labeledCascadeLaw n (b n) : Measure (LabeledTree n)) (labeledLeafLaw n)
    (measurable_labeledLeafLaw n)
  let G := fun σ : ℕ → LabeledLeaf n =>
    F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q n) (fun i => σ i))
  let G' := fun σ : ℕ → LabeledLeaf n =>
    F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q' n) (fun i => σ i))
  have hm (q₀ : Fin (n + 1) → ℝ) : Measurable (fun σ : ℕ → LabeledLeaf n =>
      F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q₀ (fun i => σ i))) := by
    have hprefix : Measurable (fun σ : ℕ → LabeledLeaf n => fun i : Fin r => σ i) := by fun_prop
    exact (measurable_of_countable
      (fun ξ : Fin r → LabeledLeaf n => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q₀ ξ))).comp hprefix
  have hi : Integrable G μ := integrable_of_measurable_abs_le (hm (q n))
    (fun σ => by simpa only [Real.norm_eq_abs] using (F.norm_coe_le_norm
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q n) (fun i => σ i))))
  have hi' : Integrable G' μ := integrable_of_measurable_abs_le (hm (q' n))
    (fun σ => by simpa only [Real.norm_eq_abs] using (F.norm_coe_le_norm
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q' n) (fun i => σ i))))
  change |(∫ σ, G σ ∂μ) - ∫ σ, G' σ ∂μ| < ε
  rw [← integral_sub hi hi']
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun σ => G σ - G' σ)
    (C := ε / 2) (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs]
      exact (hmod n (q n) (q' n) (hqunit n) (hq'unit n)
        (fun i => (hclose n i).trans hn.le) (fun i => σ i)).le)
  have hb' : |∫ σ, G σ - G' σ ∂μ| ≤ ε / 2 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  exact hb'.trans_lt (half_lt_self hε)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRecalculatedFiniteCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recalculation of Gaussian covariance along a path approximation
for the varying finite cascades, including strict interior level approximations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_recalculated_finite_cascade_error {m r k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (b a : ℕ → ℕ → ℝ) (ha : ∀ n, Monotone (a n))
    (ha0 : ∀ n, 0 ≤ a n 0) (ha1 : ∀ n, a n n ≤ 1)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p')
        (cavityCanonicalLabel ρ eig hρ hρsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (q n) x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B (q n) x))
        ∂(cascadeCompactLaw n (b n) (a n) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B p x))
        ∂(cascadeCompactLaw n (b n) (a n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  let P n := cascadeCompactLaw n (b n) (a n)
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k ρ x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k ρ)⟩
  have hpos (n : ℕ) (p' : OverlapPath) : ∀ᵐ x ∂(P n : Measure JointArray),
      (cavityGroupBlockCovariance k ρ (B p' x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (b n) (a n) (ha n) (ha0 n) (ha1 n)
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

lemma cavityStrictLevels_dist {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin (n + 1)) : |cavityStrictLevels q ε i - q i| ≤ ε := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hd : |cavityInteriorLevel i - q i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2, hq'.1, hq'.2]
  have he : cavityStrictLevels q ε i - q i = ε * (cavityInteriorLevel i - q i) := by
    dsimp only [cavityStrictLevels]
    ring
  rw [he, abs_mul, abs_of_nonneg hε]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hε

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

lemma cavityStrictUniformPath_dist (p : OverlapPath) (n : ℕ) (s : ℝ) :
    |cavityStrictUniformPath p n s - uniformCellAverage p n (uniformCellIndex n s)| ≤
      1 / ((n : ℝ) + 1) :=
  cavityStrictLevels_dist _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n).1.le (cavityUniformLevel n s)

lemma cavityStrictUniformPath_ae_tendsto (p : OverlapPath) :
    ∀ᵐ s ∂pathMeasure, Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) := by
  have ha := uniformCellAverage_ae_tendsto p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩)
  change ∀ᵐ s ∂pathMeasure, _ at ha
  filter_upwards [ha] with s hs
  have hd : Tendsto (fun n => cavityStrictUniformPath p n s -
      uniformCellAverage p n (uniformCellIndex n s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Real.norm_eq_abs] using cavityStrictUniformPath_dist p n s
  simpa only [sub_add_cancel, zero_add] using hd.add hs

lemma cavityStrictUniformPath_l1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |cavityStrictUniformPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have ha := cavityStrictUniformPath_ae_tendsto p
  have hd := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |cavityStrictUniformPath p n s - p s|) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (((cavityStrictUniformPath p n).measurable.sub p.measurable).abs).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith [(cavityStrictUniformPath p n).nonneg s,
        (cavityStrictUniformPath p n).le_one s, p.nonneg s, p.le_one s])
    (ha.mono fun s hs => by simpa only [sub_self, abs_zero] using (hs.sub_const (p s)).abs)
  simpa only [integral_zero] using hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictCascadeLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict interior overlap approximations retain the same finite
spectral-block limit as the uniform cell-average cascades. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_cascade_clamp_law (n : ℕ) (b a : ℕ → ℝ) :
    cascadeCompactLaw n b (fun i => a (cavityFiniteLevel n i)) = cascadeCompactLaw n b a := by
  have he : (fun σ : ℕ → LabeledLeaf n => compactScalarArray (diagonalPatch 1
      (cascadeScalarArray n (fun i => a (cavityFiniteLevel n i)) σ))) =
      (fun σ => compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) := by
    funext σ
    congr 1
    funext i j
    dsimp only [diagonalPatch, cascadeScalarArray]
    split_ifs
    · rfl
    · change a (min (labeledCommonDepth n (σ i) (σ j)) n) = _
      rw [min_eq_left (labeledCommonDepth_le n _ _)]
  simp only [cascadeCompactLaw, he]
  rfl

theorem cavity_strict_uniform_block_error {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  have he := cavity_finite_height_integral_error rho lam hrho hsum p
    (cavityStrictUniformLevels p) (fun n i => uniformCellAverage p n i)
    (fun n => (cavityStrictUniformLevels_strict p n).monotone)
    (fun n i j hij => uniformCellAverage_monotone p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n hij)
    (fun n i => ⟨(cavityStrictUniformLevels_mem p n i).1.le,
      (cavityStrictUniformLevels_mem p n i).2.le⟩)
    (fun n i => uniformCellAverage_mem p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    uniformExponent (fun n => 1 / ((n : ℝ) + 1))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (fun n i => cavityStrictLevels_dist _
      (fun i => uniformCellAverage_mem p.monotone
        (fun s => ⟨p.nonneg s, p.le_one s⟩) n i) (cavity_uniform_epsilon n).1.le i) F
  simpa only [cavity_cascade_clamp_law] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictGaussianLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict finite overlap levels and recalculated covariance leave all
bounded Gaussian-marked spectral-block limits unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_strict_uniform_gaussian_error {m r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun x : JointArray => cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance k rho x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance k rho)⟩
  have hpos (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1) :
      ∀ᵐ x ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray),
        (cavityGroupBlockCovariance k rho (B x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) a ha ha0 ha1
      (cavityCanonicalDiagonal rho lam hrho hsum p) (cavityCanonicalLabel rho lam hrho hsum p)
      (continuous_cavityCanonicalLabel rho lam hrho hsum p)
      (cavityCanonicalCoordinate_monotone rho lam hrho hsum p)
      (fun j => cavityCanonicalCoordinate_nonneg rho lam hrho hsum p j _)
      (fun j => cavityCanonicalCoordinate_le_diagonal rho lam hrho hsum p j _)
      rho (fun j => (hrho j).le)
  have he (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1) :
      (∫ x, H (B x) ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray)) =
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) a : Measure JointArray) :=
    integral_congr_ae ((hpos n a ha ha0 ha1).mono (fun x hx => hExt _ _ hx))
  have hs n := he n (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))
    ((cavityStrictUniformLevels_strict p n).monotone.comp (cavityFiniteLevel_monotone n))
    (cavityStrictUniformLevels_mem p n _).1.le (cavityStrictUniformLevels_mem p n _).2.le
  have hb n := he n (uniformCellAverage p n)
    (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
    (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
    (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
  have ht := cavity_strict_uniform_block_error rho lam hrho hsum p H
  simpa only [hs, hb, B] using ht

theorem cavity_strict_recalculated_gaussian_error_oai {m r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p')
        (cavityCanonicalLabel rho lam hrho hsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (cavityStrictUniformPath p n) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B (cavityStrictUniformPath p n) x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B p x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  intro B
  have hr := cavity_recalculated_finite_cascade_error rho lam hrho hsum p
    (cavityStrictUniformPath p) (cavityStrictUniformPath_l1_tendsto p)
    uniformExponent (fun n i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))
    (fun n => (cavityStrictUniformLevels_strict p n).monotone.comp (cavityFiniteLevel_monotone n))
    (fun n => (cavityStrictUniformLevels_mem p n _).1.le)
    (fun n => (cavityStrictUniformLevels_mem p n _).2.le) F
  have hs := cavity_strict_uniform_gaussian_error rho lam hrho hsum p F
  simpa only [sub_add_sub_cancel, zero_add, B] using hr.add hs

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error_oai := @OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error_oai
