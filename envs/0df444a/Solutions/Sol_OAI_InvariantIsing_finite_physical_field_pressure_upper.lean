-- Prove2me | solution 1 for OAI.InvariantIsing.finite_physical_field_pressure_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:04.1332+00:00
-- url     : https://prove2.me/submissions/de516ff4-1d0c-4e6c-b675-f83f32c0ff6a

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteSpectrum_restrictedPressure_entropy_upper
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_magneticEntropyFunctional_lower
import Theorems.Thm_OAI_InvariantIsing_magneticGroupValue_parameters_uniform

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
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

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

end IsingPerceptron

 

 

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

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

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

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_last {n : ℕ} (a : Fin (n+1) → ℝ) : finiteFieldPath a n = ∑ j, a j := by
  simp only [finiteFieldPath,show ∀ j : Fin (n+1), j.val ≤ n from fun j => by omega,ite_true, if_true]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

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

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma measurable_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) :
    Measurable (finiteStepFunction ζ v) := by
  unfold finiteStepFunction
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





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

lemma lowerGrid_le {p : ℝ → ℝ} (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1)
    (n : ℕ) {u : ℝ} (hu : 0≤u) : lowerGrid p n u ≤ p u := by
  have hf : (⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ)≤u :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hu))
  have hv := hp hf
  have hb' := (hb ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ))).1
  dsimp only [lowerGrid]
  nlinarith [show (0:ℝ)≤1/(n+1:ℕ) by positivity]

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

lemma lowerGrid_ae_tendsto {p : ℝ → ℝ} (hp : Monotone p) :
    ∀ᵐ u ∂pathMeasure, Tendsto (fun n => lowerGrid p n u) atTop (𝓝 (p u)) := by
  have hc : ∀ᵐ u ∂pathMeasure, ContinuousAt p u := monotone_ae_continuous_unit hp
  filter_upwards [hc,ae_restrict_mem measurableSet_Ioo] with u hc hu
  have hf := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl := hc.tendsto.comp (uniformCell_left_tendsto ⟨hu.1.le,hu.2⟩)
  simpa only [lowerGrid,uniformCellIndex_eq_floor _ ⟨hu.1.le,hu.2⟩,
    Nat.cast_add,Nat.cast_one,sub_zero,one_mul,Function.comp_apply] using hf.mul hl

lemma lowerGrid_integral_tendsto {p : ℝ → ℝ} (hp : Monotone p)
    (hb : ∀ u, p u∈Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ u, lowerGrid p n u ∂pathMeasure) atTop (𝓝 (∫ u, p u ∂pathMeasure)) := by
  let : IsFiniteMeasure pathMeasure := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)))
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (lowerGrid_monotone hp n).measurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (lowerGrid_mem hb n u).1]; exact (lowerGrid_mem hb n u).2)
  · exact lowerGrid_ae_tendsto hp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-depth Gaussian marking input used in the one-site functional.
The logarithmic terminal is unbounded; the linear-growth cascade theorem
supplies its integrability. This is the Gaussian specialization of
Bolthausen--Sznitman (1998), Appendix Proposition A.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma gaussianOperator_eq_gaussian_logMean {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0)
    {F : ℝ → ℝ} (hF : Measurable F) (x : ℝ) :
    gaussianOperator a v F x =
      IsingPerceptron.logMean a (gaussianReal 0 v) (fun g => F (x + g)) := by
  simp only [gaussianOperator, ha, ite_false, if_false, IsingPerceptron.logMean]
  have hm : Measurable (fun g : ℝ => Real.exp (a * F (x + g))) :=
    (((hF.comp (measurable_const.add measurable_id)).const_mul a).exp)
  rw [integral_gaussianReal_zero_eq_standard v hm]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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

/-- Uniform cube entropy is `N log 2`. -/
lemma log_card_spin (N : ℕ) : Real.log (Fintype.card (Spin N)) = N * Real.log 2 := by
  simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureLipschitz
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact factorization of the Ising reference at zero interaction. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma sum_exp_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    (∑ σ : Spin N, Real.exp (fieldEnergy c σ)) = ∏ i, 2 * Real.cosh (c i) := by
  simp only [fieldEnergy, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) => Real.exp (c i * spinValue b))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  norm_num [spinValue, Real.cosh_eq]
  ring

/-- The site factorization used before the backward Gaussian cascade recursion. -/
theorem logPartition_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    logPartition (fieldEnergy c) = ∑ i, Real.log (Real.cosh (c i)) := by
  have hcard : (Fintype.card (Spin N) : ℝ) = ∏ _ : Fin N, (2 : ℝ) := by
    simp [Spin]
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, sum_exp_fieldEnergy, Finset.prod_mul_distrib, ← hcard,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact Real.log_prod (fun i _ => (Real.cosh_pos (c i)).ne')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Site factorization through the finite Gaussian backward recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

theorem vectorCascade_logCosh_sum (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (c z : Fin N → ℝ) :
    IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
      (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) z =
    ∑ i, IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks (v := v) j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y)) (c i + z i) := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let F := IsingPerceptron.cascadeRecursion n bs (fun j => gaussianCascadeMarks vs j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
    have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun j => gaussianCascadeMarks vs j) (fun _ => measurable_fst.add measurable_snd)
      IsingPerceptron.measurable_logCosh
    have hg : IsingPerceptron.HasLinearGrowth F :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun j => gaussianCascadeMarks vs j)
        (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (vs j))
        IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth hbs
    have he : (fun g : Fin N → ℝ => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
        (fun g => ∑ i, F ((c i + z i) + g i)) := by
      funext g
      rw [ih bs vs hbs]
      simp only [F, Pi.add_apply, add_assoc]
    change IsingPerceptron.logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun g => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
      ∑ i, IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
        (fun g => F ((c i + z i) + g))
    rw [he]
    exact IsingPerceptron.logMean_independent_sum (fun _ : Fin N => gaussianReal 0 (v 0))
      (fun i g => F ((c i + z i) + g)) (hb 0 (by omega)).ne'
      (fun _ => hm.comp (measurable_const.add measurable_id))
      (fun i => IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left (c i + z i)) (b 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar contribution to the enriched pressure variance. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace InvariantIsing

/-- Integrating the Gaussian tail of a deviation gives its second moment.
The proof applies layer cake to the squared deviation, so only the elementary
exponential integral on the positive half-line is needed. -/
lemma integral_sq_sub_le_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    Integrable (fun ω => (f ω - m) ^ 2) μ ∧
      (∫ ω, (f ω - m) ^ 2 ∂μ) ≤ C / a := by
  let g := fun ω => (f ω - m) ^ 2
  have hgm : Measurable g := (hf.sub_const m).pow_const 2
  have hgn : ∀ ω, 0 ≤ g ω := fun ω => sq_nonneg _
  have hk : Integrable (fun t : ℝ => C * Real.exp (-a * t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).const_mul C
  have hkn : ∀ t : ℝ, 0 ≤ C * Real.exp (-a * t) := fun _ => mul_nonneg hC (Real.exp_pos _).le
  have hki : (∫ t : ℝ in Ioi 0, C * Real.exp (-a * t)) = C / a := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -a < 0) 0]
    simp [div_eq_mul_inv]
  have hlin : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (C / a) := by
    calc
      _ = ∫⁻ t : ℝ in Ioi 0, μ {ω | t ≤ g ω} :=
        lintegral_eq_lintegral_meas_le μ (ae_of_all _ hgn) hgm.aemeasurable
      _ ≤ ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (C * Real.exp (-a * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have he : {ω | t ≤ g ω} = {ω | Real.sqrt t ≤ |f ω - m|} := by
          ext ω
          simp only [mem_ofPred_eq, g, Real.sqrt_le_left (abs_nonneg _), sq_abs]
        rw [he, ← ofReal_measureReal]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.sq_sqrt ht.le] using htail (Real.sqrt t) (Real.sqrt_pos.mpr ht)
      _ = ENNReal.ofReal (C / a) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ hkn), hki]
  have hgi : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (ae_of_all _ hgn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hgi, ?_⟩
  have hI : ENNReal.ofReal (∫ ω, g ω ∂μ) ≤ ENNReal.ofReal (C / a) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn)]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C / a)).mp hI

lemma variance_le_of_gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    variance f μ ≤ C / a := by
  rw [← variance_sub_const hf.aestronglyMeasurable m]
  exact (variance_le_expectation_sq (hf.sub_const m).aestronglyMeasurable).trans
    (integral_sq_sub_le_of_gaussian_tail μ f hf m C a hC ha htail).2

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar variance for the Frobenius moduli used by the perturbed model. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma haar_frobeniusLipschitz_memLp_two (hpub : HaarConcentrationInput)
    (N : ℕ) (hN : 3 ≤ N) (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (hμinv : μ.IsMulLeftInvariant) (f : SpecialOrthogonal N → ℝ) (hf : Measurable f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) : MemLp f 2 μ := by
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  obtain ⟨m, _, _, ht⟩ := hp N hN μ inferInstance hμinv f hf L hL hLip
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd := (integral_sq_sub_le_of_gaussian_tail μ f hf m C
    (a * N / L ^ 2) hC.le (by positivity) (fun r hr => by
      simpa only [show -a * (N : ℝ) * r ^ 2 / L ^ 2 = -(a * N / L ^ 2) * r ^ 2 by ring]
        using ht r hr)).1
  have hD := (memLp_two_iff_integrable_sq (hf.sub_const m).aestronglyMeasurable).mpr hd
  convert hD.add (memLp_const m) using 1
  all_goals try with_reducible_and_instances rfl
  ext U
  simp only [Pi.add_apply, sub_add_cancel]

/-- The published concentration input bounds every measurable Frobenius
Lipschitz observable, with constants independent of dimension. -/
theorem haar_frobeniusLipschitz_variance (hpub : HaarConcentrationInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
    ∀ L : ℝ, 0 < L →
      (∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) →
      variance f μ ≤ C * L ^ 2 / N := by
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  refine ⟨C / a, by positivity, ?_⟩
  intro N hN μ hμ hμinv f hf L hL hLip
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m, _, _, ht⟩ := hp N hN μ hμ hμinv f hf L hL hLip
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := variance_le_of_gaussian_median_tail μ f hf m C
    (a * N / L ^ 2) hC.le (by positivity) (fun r hr => by
      simpa only [show -a * (N : ℝ) * r ^ 2 / L ^ 2 = -(a * N / L ^ 2) * r ^ 2 by ring]
        using ht r hr)
  refine hb.trans_eq ?_
  field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteSpectralSlope ρ eig hρ hρsum) := by
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_projectedResolventDerivative ρ eig hρ hρsum a)

theorem finiteSpectralSlope_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    finiteSpectralSlope ρ eig hρ hρsum 0 = ∑ a, ρ a * eig a := by
  simp only [finiteSpectralSlope, projectedResolventDerivative, lt_self_iff_false, ite_false, if_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finiteSpectralSlope_bounds (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteSpectralSlope ρ eig hρ hρsum x ∧ finiteSpectralSlope ρ eig hρ hρsum x ≤ u := by
  have hw := sum_projectedResolventDerivative ρ eig hρ hρsum x
  constructor
  · calc
      l = ∑ a, l * projectedResolventDerivative ρ eig hρ hρsum a x := by
        rw [← Finset.mul_sum, hw, mul_one]
      _ ≤ finiteSpectralSlope ρ eig hρ hρsum x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hl a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
  · calc
      finiteSpectralSlope ρ eig hρ hρsum x ≤
          ∑ a, u * projectedResolventDerivative ρ eig hρ hρsum a x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hu a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
      _ = u := by rw [← Finset.mul_sum, hw, mul_one]

theorem sum_eig_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, eig a * projectedResolvent ρ eig hρ hρsum a x) =
      x * finiteR ρ eig hρ hρsum x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero,
      Finset.sum_const_zero, zero_mul]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hterm : ∀ a, eig a * (ρ a / (B - eig a)) = B * (ρ a / (B - eig a)) - ρ a := by
      intro a
      have hgap : B - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
      field_simp [hgap]
      ring
    simp only [projectedResolvent, finiteR, ite_eq_left h]
    change (∑ a, eig a * (ρ a / (B - eig a))) = x * (B - 1 / x)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hρsum]
    change B * finiteResolvent ρ eig B - 1 = x * (B - 1 / x)
    rw [hs.2]
    field_simp

theorem hasDerivWithinAt_mul_finiteR_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
  have hd : HasDerivWithinAt
      (fun y => ∑ a, eig a * projectedResolvent ρ eig hρ hρsum a y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
    convert! HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx).const_mul (eig a)) using 1
    all_goals try with_reducible_and_instances rfl
  exact hd.congr (fun y hy => (sum_eig_projectedResolvent ρ eig hρ hρsum hy).symm)
    (sum_eig_projectedResolvent ρ eig hρ hρsum hx).symm

theorem hasDerivWithinAt_finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum t)
      (finiteSpectralSlope ρ eig hρ hρsum (t * x)) (Ici 0) x := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_mul, finiteSpectralSlope_zero]
    have hd := (hasDerivAt_id x).mul_const (∑ a, ρ a * eig a)
    convert! hd.hasDerivWithinAt using 1
    · funext y
      simp [finiteThermalScalar, finiteR]
    · simp
  · have hdH := hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum (mul_nonneg h.le hx)
    have hdlin : HasDerivWithinAt (fun y : ℝ => t * y) t (Ici 0) x := by
      convert! ((hasDerivAt_id x).const_mul t).hasDerivWithinAt using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd := (hdH.comp x hdlin (fun y hy => mul_nonneg h.le hy)).const_mul (1 / t)
    convert! hd using 1
    · funext y
      dsimp [finiteThermalScalar, Function.comp_def]
      field_simp [h.ne']
    · field_simp [h.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSampling
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spin sampling and Gaussian transitions for the scalar Ising
recursion. The transition kernels remain probabilities at zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldTransitionKernel_eq_tilted (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel ζ v F hF z = (gaussianReal z v).tilted (fun u => ζ * F u) := by
  exact normalizeMass_exp _ _ (hF.const_mul ζ)
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)

lemma fieldTransitionKernel_integral (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (a : ℝ → ℝ) (z : ℝ) :
    (∫ u, a u ∂fieldTransitionKernel ζ v F hF z) = fieldSpinTransition ζ v F a z := by
  rw [fieldTransitionKernel_eq_tilted ζ v F hF hG z]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A separable scalar cavity tilt preserves independence of the Gaussian
site coordinates. This identifies the actual vector transition law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldGaussian_product_tilt {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    (Measure.pi (fun i => gaussianReal (z i) v)).tilted
      (fun y => ζ * ∑ i, F (y i)) =
      Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i)) := by
  let μ := fun i : Fin N => gaussianReal (z i) v
  let Z := fun i : Fin N => ∫ u, Real.exp (ζ * F u) ∂μ i
  have hZpos (i : Fin N) : 0 < Z i := integral_exp_pos
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments (z i) v) hF hG ζ)
  have hZ : (∫ y, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) = ∏ i, Z i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  have hS (s : Fin N → Set ℝ) :
      (∫ y in univ.pi s, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) =
        ∏ i, ∫ u in s i, Real.exp (ζ * F u) ∂μ i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  apply (Measure.pi_eq (μ := fun i => fieldTransitionKernel ζ v F hF (z i)) ?_).symm
  intro s hs
  change ((Measure.pi μ).tilted (fun y => ζ * ∑ i, F (y i))) (univ.pi s) = _
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs), integral_div, hS, hZ]
  rw [← Finset.prod_div_distrib, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => div_nonneg (integral_nonneg (fun u => (Real.exp_pos _).le)) (hZpos i).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [fieldTransitionKernel_eq_tilted ζ v F hF hG,
    tilted_apply_eq_ofReal_integral' _ (hs i), integral_div]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltTransport
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized quadratic tilts commute with the Gaussian factor map. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X → Y) (hF : Measurable F)
    (f : Y → ℝ) (hf : Measurable f) :
    (μ.tilted (f ∘ F)).map F = (μ.map F).tilted f := by
  ext s hs
  rw [Measure.map_apply hF hs, tilted_apply_eq_ofReal_integral' _ (hF hs),
    tilted_apply_eq_ofReal_integral' _ hs,
    integral_map hF.aemeasurable hf.exp.aestronglyMeasurable,
    setIntegral_map hs ((hf.exp.div_const _).aestronglyMeasurable) hF.aemeasurable]
  rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedFamily
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDomain
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma measurable_fieldFunction (h : FieldStep) : Measurable (fieldFunction h) :=
  IsingPerceptron.measurable_finiteStepFunction h.cut h.height

lemma fieldFunction_le_last (h : FieldStep) (s : ℝ) :
    fieldFunction h s ≤ h.height (Fin.last h.depth) := by
  classical
  by_cases hex : ∃ i : Fin (h.depth + 1), h.cut i.castSucc < s ∧ s < h.cut i.succ
  · obtain ⟨i, hi⟩ := hex
    have he := IsingPerceptron.finiteStepFunction_on_cell h.ordered_cut h.height hi
    change IsingPerceptron.finiteStepFunction h.cut h.height s ≤ _
    rw [he]
    exact h.ordered_height (Fin.le_last _)
  · have he : fieldFunction h s = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hex ⟨i, hi⟩)
    rw [he]
    exact h.nonneg _

lemma integrable_fieldFunction (h : FieldStep) : Integrable (fieldFunction h) pathMeasure := by
  apply (integrable_const (h.height (Fin.last h.depth))).mono'
    (measurable_fieldFunction h).aestronglyMeasurable
  filter_upwards [] with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fieldFunction_nonneg h s)] using
    fieldFunction_le_last h s

lemma integrable_path_mul_field (p : OverlapPath) (h : FieldStep) :
    Integrable (fun s => p s * fieldFunction h s) pathMeasure := by
  apply (integrable_fieldFunction h).mono'
    (p.measurable.mul (measurable_fieldFunction h)).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (p.nonneg s),
    abs_of_nonneg (fieldFunction_nonneg h s)]
  exact mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)

/-- Summation by parts for the finite height increments. -/
lemma sum_finite_height_difference (n : ℕ) (H F : ℕ → ℝ) :
    (∑ i : Fin (n + 1), (H i - if i.val = 0 then 0 else H (i.val - 1)) * F i) =
      H n * F n + ∑ i : Fin n, H i * (F i - F (i.val + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_ne_zero, ite_false, if_false,
      Nat.add_sub_cancel]
    rw [ih]
    ring

lemma fieldIncrement_eq_heightSequence (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 = heightSequence h i -
      if i.val = 0 then 0 else heightSequence h (i.val - 1) := by
  rw [heightSequence_eq h _ (by omega)]
  unfold fieldIncrement
  split_ifs with hi
  · rfl
  · rw [heightSequence_eq h _ (by omega)]

lemma fieldCutSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth + 1) :
    fieldCutSequence h i = h.cut ⟨i, by omega⟩ := by
  simp only [fieldCutSequence, min_eq_left hi]

lemma fieldIncrement_weighted_sum (h : FieldStep) (F : ℝ → ℝ) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2 * F (h.cut i.castSucc)) =
      h.height (Fin.last h.depth) * F (h.cut (Fin.last h.depth).castSucc) +
        ∑ i : Fin h.depth, h.height i.castSucc *
          (F (h.cut i.castSucc.castSucc) - F (h.cut i.succ.castSucc)) := by
  have hs := sum_finite_height_difference h.depth (heightSequence h)
    (fun i => F (fieldCutSequence h i))
  convert (config := {transparency := .instances, preTransparency := .instances}) hs using 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [fieldIncrement_eq_heightSequence, fieldCutSequence_eq h _ (by omega)]
    rfl
  · congr 1
    · rw [heightSequence_eq h _ le_rfl, fieldCutSequence_eq h _ (by omega)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      rw [heightSequence_eq h _ (by omega), fieldCutSequence_eq h _ (by omega),
        fieldCutSequence_eq h _ (by omega)]
      rfl

lemma fieldIncrement_sum (h : FieldStep) :
    (∑ i : Fin (h.depth + 1), (fieldIncrement h i).2) =
      h.height (Fin.last h.depth) := by
  simpa using fieldIncrement_weighted_sum h (fun _ => 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted spin sums retain the original cube mass. A deterministic
map of slices costs its energy error and the logarithm of its largest fiber. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinLog_univ {N : ℕ} (H : Spin N → ℝ) :
    restrictedSpinLog Finset.univ H = logPartition H := by
  rw [restrictedSpinLog, logPartition_eq, log_card_spin]

lemma sum_exp_le_of_fiber_bound {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (H : X → ℝ) (K : Y → ℝ)
    (c B : ℝ) (hf : ∀ x ∈ S, f x ∈ T)
    (hE : ∀ x ∈ S, H x ≤ K (f x) + c)
    (hB : ∀ y ∈ T, ((S.filter fun x => f x = y).card : ℝ) ≤ B) :
    ∑ x ∈ S, Real.exp (H x) ≤ Real.exp c * B * ∑ y ∈ T, Real.exp (K y) := by
  rw [← Finset.sum_fiberwise_of_maps_to hf, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ ≤ ∑ _x ∈ S.filter (fun x => f x = y), Real.exp (K y + c) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
      apply Real.exp_le_exp.mpr
      simpa only [hxy] using hE x hxS
    _ = ((S.filter fun x => f x = y).card : ℝ) * Real.exp (K y + c) := by
      simp
    _ ≤ B * Real.exp (K y + c) :=
      mul_le_mul_of_nonneg_right (hB y hy) (Real.exp_pos _).le
    _ = Real.exp c * B * Real.exp (K y) := by rw [Real.exp_add]; ring

lemma restrictedSpinLog_le_of_map {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (H K : Spin N → ℝ) (c B : ℝ) (hB0 : 0 < B)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hE : ∀ σ ∈ S, H σ ≤ K (f σ) + c)
    (hB : ∀ τ ∈ T, ((S.filter fun σ => f σ = τ).card : ℝ) ≤ B) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K + c + Real.log B := by
  have h := Real.log_le_log (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS)
    (sum_exp_le_of_fiber_bound S T f H K c B hf hE hB)
  have hp : 0 < ∑ τ ∈ T, Real.exp (K τ) :=
    Finset.sum_pos (fun τ _ => Real.exp_pos (K τ)) hT
  rw [Real.log_mul (mul_pos (Real.exp_pos c) hB0).ne' hp.ne',
    Real.log_mul (Real.exp_ne_zero c) hB0.ne', Real.log_exp] at h
  unfold restrictedSpinLog
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupSlice
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not _root_.OAI.InvariantIsing.spinVector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite magnetization slices for an arbitrary grouping of the sites.
Constant group fields factor exactly, with the original cube mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma sum_spinValue_eq_count {N : ℕ} (S : Finset (Fin N)) (σ : Spin N) :
    (∑ i ∈ S, spinValue (σ i)) =
      2 * ((S.filter fun i => σ i = true).card : ℝ) - S.card := by
  have hi (i : Fin N) : spinValue (σ i) = (if σ i = true then 2 else 0) - 1 := by
    cases hσ : σ i <;> norm_num [spinValue]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite, mul_comm]

lemma fieldEnergy_group_counts {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (b : A → ℝ) (σ : Spin N) :
    fieldEnergy (fun i => b (group i)) σ =
      ∑ a, b a * (2 * (spinGroupCount group σ a : ℝ) - spinGroupSize group a) := by
  rw [fieldEnergy, ← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => group i = a), b a * spinValue (σ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = b a * (∑ i ∈ Finset.univ.filter (fun i => group i = a), spinValue (σ i)) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_spinValue_eq_count]
      simp only [Finset.filter_filter, spinGroupCount, spinGroupSize]

lemma fieldEnergy_on_group_slice {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (b : A → ℝ) {σ : Spin N}
    (hσ : σ ∈ spinGroupSlice group k) :
    fieldEnergy (fun i => b (group i)) σ = spinGroupFieldConstant group k b := by
  have hk := (Finset.mem_filter.mp hσ).2
  rw [fieldEnergy_group_counts]
  simp only [hk, spinGroupFieldConstant]

lemma restrictedSpinLog_group_field {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (b : A → ℝ) (H : Spin N → ℝ) :
    restrictedSpinLog (spinGroupSlice group k) (fun σ => H σ + fieldEnergy (fun i => b (group i)) σ) =
      restrictedSpinLog (spinGroupSlice group k) H + spinGroupFieldConstant group k b := by
  rw [← restrictedSpinLog_add_const _ (spinGroupSlice_nonempty group k hk)]
  unfold restrictedSpinLog
  congr 2
  apply Finset.sum_congr rfl
  intro σ hσ
  dsimp only
  rw [fieldEnergy_on_group_slice group k b hσ]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinHammingEnergy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic energy cost of changing a prescribed number of
spins. These bounds apply to the slice comparisons in the magnetic theorem. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma spinVector_sub_norm_sq {N : ℕ} (σ τ : Spin N) :
    ‖spinVector σ - spinVector τ‖ ^ 2 = 4 * (hammingDist σ τ : ℝ) := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (spinValue (σ i) - spinValue (τ i)) ^ 2) = _
  have hi (i : Fin N) : (spinValue (σ i) - spinValue (τ i)) ^ 2 =
      if σ i ≠ τ i then 4 else 0 := by
    cases hσ : σ i <;> cases hτ : τ i <;> norm_num [spinValue]
  simp_rw [hi]
  simp [hammingDist, Finset.sum_ite, mul_comm]

lemma sum_abs_spinValue_sub {N : ℕ} (σ τ : Spin N) :
    (∑ i, |spinValue (σ i) - spinValue (τ i)|) = 2 * (hammingDist σ τ : ℝ) := by
  classical
  have hi (i : Fin N) : |spinValue (σ i) - spinValue (τ i)| =
      if σ i ≠ τ i then 2 else 0 := by
    cases hσ : σ i <;> cases hτ : τ i <;> norm_num [spinValue]
  simp_rw [hi]
  simp [hammingDist, Finset.sum_ite, mul_comm]

lemma abs_fieldEnergy_sub_spin_le {N : ℕ} (c : Fin N → ℝ) (σ τ : Spin N)
    {C : ℝ} (hc : ∀ i, |c i| ≤ C) :
    |fieldEnergy c σ - fieldEnergy c τ| ≤ 2 * C * (hammingDist σ τ : ℝ) := by
  have he : fieldEnergy c σ - fieldEnergy c τ =
      ∑ i, c i * (spinValue (σ i) - spinValue (τ i)) := by
    simp only [fieldEnergy, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |c i * (spinValue (σ i) - spinValue (τ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C * |spinValue (σ i) - spinValue (τ i)| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    _ = 2 * C * (hammingDist σ τ : ℝ) := by
      rw [← Finset.mul_sum, sum_abs_spinValue_sub]
      ring

lemma abs_rotatedEnergy_sub_spin_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (σ τ : Spin N) {K : ℝ} (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedEnergy eig U σ - rotatedEnergy eig U τ| ≤
      2 * K * Real.sqrt ((N : ℝ) * (hammingDist σ τ : ℝ)) := by
  let x := U (spinVector σ)
  let y := U (spinVector τ)
  let D : ℝ := hammingDist σ τ
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hx : ∑ i, x i ^ 2 = N := rotated_spin_sq_sum U σ
  have hy : ∑ i, y i ^ 2 = N := rotated_spin_sq_sum U τ
  have hm : (∑ i, (x i - y i) ^ 2) = 4 * D := by
    calc
      _ = ‖x - y‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
      _ = 4 * D := by
        change ‖U (spinVector σ) - U (spinVector τ)‖ ^ 2 = _
        rw [← U.map_sub, U.norm_map, spinVector_sub_norm_sq]
  have hp : (∑ i, (x i + y i) ^ 2) ≤ 4 * (N : ℝ) := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (x i + y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2 by
        nlinarith [sq_nonneg (x i - y i)])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy] at hi
    linarith
  have hw : (∑ i, (eig i * (x i - y i)) ^ 2) ≤ K ^ 2 * (4 * D) := by
    rw [← hm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    have hb : eig i ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (heig i)
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => eig i * (x i - y i)) (fun i => x i + y i)
  have hs : (∑ i, (eig i * (x i - y i)) * (x i + y i)) ^ 2 ≤
      (4 * K * Real.sqrt ((N : ℝ) * D)) ^ 2 := by
    calc
      _ ≤ (∑ i, (eig i * (x i - y i)) ^ 2) * ∑ i, (x i + y i) ^ 2 := hcs
      _ ≤ (K ^ 2 * (4 * D)) * (4 * (N : ℝ)) :=
        mul_le_mul hw hp (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have ha : |∑ i, (eig i * (x i - y i)) * (x i + y i)| ≤
      4 * K * Real.sqrt ((N : ℝ) * D) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  have he : rotatedEnergy eig U σ - rotatedEnergy eig U τ =
      (1 / 2 : ℝ) * ∑ i, (eig i * (x i - y i)) * (x i + y i) := by
    rw [rotatedEnergy, rotatedEnergy, ← mul_sub, ← Finset.sum_sub_distrib]
    change (1 / 2 : ℝ) * (∑ i, (eig i * x i ^ 2 - eig i * y i ^ 2)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_eq (by dsimp [D] <;> ring)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nearest projection to all group constraints at once. Its number of
changed spins is exactly the sum of the group count discrepancies. -/

noncomputable section
open scoped BigOperators symmDiff

namespace InvariantIsing

lemma spinGroupProjection_mem {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    spinGroupProjection group k hk σ ∈ spinGroupSlice group k :=
  (Classical.choose_spec (exists_spin_group_projection group k hk σ)).1

lemma spinGroupProjection_distance {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    hammingDist σ (spinGroupProjection group k hk σ) =
      ∑ a, ((spinGroupCount group σ a - k a) + (k a - spinGroupCount group σ a)) :=
  (Classical.choose_spec (exists_spin_group_projection group k hk σ)).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupProjectionMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expected number of flips in the nearest group-slice projection.
The input consists of ordinary count variances, which can be checked
under the independent canonical site law. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cast_nat_distance_eq_abs (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - b| := by
  by_cases h : b ≤ a
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · have h' : a ≤ b := (Nat.le_of_not_ge h)
    rw [Nat.sub_eq_zero_of_le h', zero_add, Nat.cast_sub h',
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h'))]
    ring

lemma spinGroupProjection_distance_real {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    (hammingDist σ (spinGroupProjection group k hk σ) : ℝ) =
      ∑ a, |(spinGroupCount group σ a : ℝ) - k a| := by
  rw [spinGroupProjection_distance, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact cast_nat_distance_eq_abs _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_value (h : FieldStep) (z : ℝ) :
    fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
      h.height (Fin.last h.depth) / 2 = fieldValue h z := by
  unfold fieldScalarValue fieldAllIncrements fieldValue
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldAllIncrements_root (h : FieldStep) :
    fieldAllIncrements h = (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
      scalarFieldIncrements h := by
  unfold fieldAllIncrements scalarFieldIncrements
  rw [List.ofFn_succ]
  congr 1
  apply Prod.ext
  · exact h.first
  · apply Subtype.ext
    simp [fieldIncrement]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldBias
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical mean spin is the bias derivative of the actual finite
field functional, including its zero-exponent root Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldValue_root (h : FieldStep) (b : ℝ) :
    fieldValue h b =
      gaussianOperator 0 (h.height 0)
        (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b -
      h.height (Fin.last h.depth) / 2 := by
  rw [← fieldAllIncrements_value h b, fieldAllIncrements_root]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-site canonical endpoint law and its final spin draw. The
ordinary root Gaussian is retained explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldTransitionKernel_zero (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F)
    (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel 0 v F hF z = gaussianReal z v := by
  rw [fieldTransitionKernel_eq_tilted 0 v F hF hG]
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_KernelExponentialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential endpoint bounds compose additively over Markov kernels.
The proof includes integrability, so no undefined Bochner integral is
used in the recursive Gaussian moment estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

theorem kernel_exp_bound_comp (κ η : Kernel ℝ ℝ) [IsMarkovKernel κ] [IsMarkovKernel η]
    (t A B : ℝ)
    (hκ : ∀ z, Integrable (fun y => Real.exp (t * y)) (κ z) ∧
      (∫ y, Real.exp (t * y) ∂κ z) ≤ Real.exp (t * z + A))
    (hη : ∀ z, Integrable (fun y => Real.exp (t * y)) (η z) ∧
      (∫ y, Real.exp (t * y) ∂η z) ≤ Real.exp (t * z + B)) (z : ℝ) :
    Integrable (fun y => Real.exp (t * y)) ((η ∘ₖ κ) z) ∧
      (∫ y, Real.exp (t * y) ∂(η ∘ₖ κ) z) ≤ Real.exp (t * z + A + B) := by
  have hm : StronglyMeasurable (fun y : ℝ => Real.exp (t * y)) := by fun_prop
  have hH : Integrable (fun x => ∫ y, Real.exp (t * y) ∂η x) (κ z) := by
    apply ((hκ z).1.const_mul (Real.exp B)).mono' hm.integral_kernel.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le))]
    simpa only [Real.exp_add, mul_comm] using (hη x).2
  have hI : Integrable (fun y => Real.exp (t * y)) ((η ∘ₖ κ) z) := by
    apply (ProbabilityTheory.integrable_comp_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => (hη x).1), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hH
  refine ⟨hI, ?_⟩
  rw [Kernel.integral_comp hI]
  calc
    _ ≤ ∫ x, Real.exp B * Real.exp (t * x) ∂κ z :=
      integral_mono hH ((hκ z).1.const_mul (Real.exp B))
        (fun x => by simpa only [Real.exp_add, mul_comm] using (hη x).2)
    _ = Real.exp B * (∫ x, Real.exp (t * x) ∂κ z) := integral_const_mul _ _
    _ ≤ Real.exp B * Real.exp (t * z + A) :=
      mul_le_mul_of_nonneg_left (hκ z).2 (Real.exp_pos B).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldTerminal
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained-block terminal payoff. Its prior mass is not
renormalized; the Lipschitz and growth estimates include that fixed mass. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma restrictedFieldTerminal_univ {N : ℕ} (z : Fin N → ℝ) :
    restrictedFieldTerminal Finset.univ z = ∑ i, Real.log (Real.cosh (z i)) := by
  rw [restrictedFieldTerminal, restrictedSpinLog_univ, logPartition_fieldEnergy]

lemma restrictedFieldTerminal_group_bias {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (b : A → ℝ) (z : Fin N → ℝ) :
    restrictedFieldTerminal (spinGroupSlice group k) (z + fun i => b (group i)) =
      restrictedFieldTerminal (spinGroupSlice group k) z + spinGroupFieldConstant group k b := by
  have he : fieldEnergy (z + fun i => b (group i)) =
      fun σ => fieldEnergy z σ + fieldEnergy (fun i => b (group i)) σ := by
    funext σ
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [restrictedFieldTerminal, he, restrictedSpinLog_group_field group k hk]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldRecursion
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vector Gaussian recursion for a constrained cavity block.
Regularity follows from the terminal's finite-spin estimates, with no
assumption on the number of cascade levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma integrable_exp_restrictedFieldRecursion {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (root : ℝ≥0) (t : ℝ) (z : Fin N → ℝ) :
    Integrable (fun w => Real.exp (t * restrictedFieldRecursion S n b v (z + w)))
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  obtain ⟨hm, hg⟩ := restrictedFieldRecursion_regular hN S hS n b v hb
  exact integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN root)
    (hm.comp (measurable_const.add measurable_id)) (hg.add_left z) t

lemma restrictedFieldRecursion_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (root : ℝ≥0) :
    Integrable (restrictedFieldRecursion S n b v)
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  obtain ⟨hm, C, L, _, hL, hbound⟩ := restrictedFieldRecursion_regular hN S hS n b v hb
  apply ((integrable_const C).add (((vectorGaussianLaw_moments hN root) 1).const_mul L)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ C + L * ‖z‖ := hbound z
    _ ≤ C + L * Real.exp (1 * ‖z‖) := by
      gcongr
      simpa only [one_mul] using (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp ‖z‖)

lemma constrainedBlockValue_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) :
    Integrable (restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h))
      (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) :=
  restrictedFieldRecursion_root_integrable hN S hS _ _ _
    (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1) _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTiltLinearGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear-growth observables are integrable under finite Gaussian tilts
with linear-growth potentials. This supplies the actual recursive loss
integrals, without extra moment hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma exponentialNormMoments_tilted {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (hμ : ExponentialNormMoments μ)
    (F : E → ℝ) (hF : Measurable F) (hFG : HasLinearGrowth F) (b : ℝ) :
    ExponentialNormMoments (μ.tilted (fun x => b * F x)) := by
  have he := integrable_exp_of_linearGrowth μ hμ hF hFG b
  obtain ⟨C, L, _, _, hbF⟩ := hFG
  intro a
  rw [integrable_tilted_iff he]
  change Integrable (fun x => Real.exp (b * F x) * Real.exp (a * ‖x‖)) μ
  apply ((hμ (|b| * L + a)).const_mul (Real.exp (|b| * C))).mono'
    (((hF.const_mul b).exp).mul ((measurable_norm.const_mul a).exp)).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖Real.exp (b * F x) * Real.exp (a * ‖x‖)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : b * F x ≤ |b| * (C + L * ‖x‖) := by
    calc
      _ ≤ |b| * |F x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbF x) (abs_nonneg b)
  nlinarith

lemma integrable_linearGrowth_tilted {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure E) (hμ : ExponentialNormMoments μ)
    (F G : E → ℝ) (hF : Measurable F) (hFG : HasLinearGrowth F)
    (hG : Measurable G) (hGG : HasLinearGrowth G) (b : ℝ) :
    Integrable G (μ.tilted (fun x => b * F x)) := by
  have he := integrable_exp_of_linearGrowth μ hμ hF hFG b
  rw [integrable_tilted_iff he]
  obtain ⟨C, L, hC, hL, hbF⟩ := hFG
  obtain ⟨D, K, hD, hK, hbG⟩ := hGG
  have henv := (hμ (|b| * L + 1)).const_mul (Real.exp (|b| * C) * (D + K))
  apply henv.mono' (((hF.const_mul b).exp).mul hG).aestronglyMeasurable
  apply ae_of_all
  intro x
  have hexp : Real.exp (b * F x) ≤ Real.exp (|b| * C + (|b| * L) * ‖x‖) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |b| * |F x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |b| * (C + L * ‖x‖) := mul_le_mul_of_nonneg_left (hbF x) (abs_nonneg _)
      _ = _ := by ring
  have hn : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
  have h1 : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg _)
  have hg : |G x| ≤ (D + K) * Real.exp ‖x‖ := by
    have hd := mul_le_mul_of_nonneg_left h1 hD
    have hk := mul_le_mul_of_nonneg_left hn hK
    nlinarith [hbG x]
  change ‖Real.exp (b * F x) * G x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (|b| * C + (|b| * L) * ‖x‖) * ((D + K) * Real.exp ‖x‖) :=
      mul_le_mul hexp hg (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|b| * C) * (D + K) * Real.exp ((|b| * L + 1) * ‖x‖) := by
      rw [Real.exp_add, show (|b| * L + 1) * ‖x‖ = (|b| * L) * ‖x‖ + ‖x‖ by ring,
        Real.exp_add]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianExponentialShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completing the square under the finite scalar Gaussian law. This is
the shift identity used to control canonical increments uniformly in the
number and size of the cascade steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma gaussianPDFReal_exp_linear {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (t * x) =
      Real.exp (t ^ 2 * v / 2) * gaussianPDFReal (t * v) v x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have he : -(x ^ 2) / (2 * v) + t * x =
      t ^ 2 * v / 2 + -(x - t * v) ^ 2 / (2 * v) := by
    field_simp
    ring
  simp only [gaussianPDFReal, sub_zero]
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem gaussian_exp_linear_shift (v : ℝ≥0) (t : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ x, Real.exp (t * x) * F x ∂gaussianReal 0 v) =
      Real.exp (t ^ 2 * v / 2) *
        ∫ x, F (x + t * v) ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · subst v
    simp
  have hshift : (∫ x, F x ∂gaussianReal (t * v) v) =
      ∫ x, F (x + t * v) ∂gaussianReal 0 v := by
    have he := integral_map (μ := gaussianReal 0 v)
      (f := F) (by fun_prop : AEMeasurable (fun x : ℝ => x + t * v)
        (gaussianReal 0 v)) hF.aestronglyMeasurable
    simpa only [gaussianReal_map_add_const, zero_add] using he
  rw [← hshift, integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [smul_eq_mul]
  rw [← mul_assoc, gaussianPDFReal_exp_linear hv]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTiltIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical one-step Gaussian increment satisfies the sharp
exponential bound from the magnetic replacement argument. Its cost is
proportional to variance, so it can be summed over arbitrary depths. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem gaussian_tilt_increment_mgf (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (hLip : ∀ x y, |F x - F y| ≤ |x - y|) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ x, Real.exp (t * x)
      ∂(gaussianReal 0 v).tilted (fun x => b * F (z + x))) ≤
        Real.exp ((t ^ 2 / 2 + |t|) * v) := by
  let U := fun x => Real.exp (b * F (z + x))
  have hi : Integrable U (gaussianReal 0 v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 v)
      (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) b
  have hp : 0 < ∫ x, U x ∂gaussianReal 0 v :=
    integral_exp_pos _ (fun x => F (z + x)) hi
  have hs : Integrable (fun x => U (x + t * v)) (gaussianReal 0 v) := by
    have hx := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 v)
      (hF.comp (measurable_const.add measurable_id)) (hG.add_left (z + t * v)) b
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change Real.exp (b * F (z + (x + t * v))) =
      Real.exp (b * F ((z + t * v) + x))
    rw [show z + (x + t * v) = (z + t * v) + x by ring]
  have hbound (x : ℝ) : U (x + t * v) ≤ Real.exp (|t| * v) * U x := by
    dsimp only [U]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := (abs_le.mp (hLip (z + (x + t * v)) (z + x))).2
    rw [show z + (x + t * v) - (z + x) = t * v by ring,
      abs_mul, abs_of_nonneg v.coe_nonneg] at hl
    have hmul := mul_le_mul_of_nonneg_left hl hb0
    have hb := mul_le_mul_of_nonneg_right hb1 (mul_nonneg (abs_nonneg t) v.coe_nonneg)
    nlinarith
  have hshift : (∫ x, U (x + t * v) ∂gaussianReal 0 v) ≤
      Real.exp (|t| * v) * ∫ x, U x ∂gaussianReal 0 v := by
    simpa only [integral_const_mul] using integral_mono hs (hi.const_mul _) hbound
  rw [integral_tilted_eq_div]
  have he : (∫ x, Real.exp (b * F (z + x)) * Real.exp (t * x) ∂gaussianReal 0 v) =
      Real.exp (t ^ 2 * v / 2) * ∫ x, U (x + t * v) ∂gaussianReal 0 v := by
    rw [show (fun x => Real.exp (b * F (z + x)) * Real.exp (t * x)) =
      (fun x => Real.exp (t * x) * U x) by funext x; exact mul_comm _ _]
    exact gaussian_exp_linear_shift v t U ((hF.comp (measurable_const.add measurable_id)).const_mul b).exp
  rw [he]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ Real.exp (t ^ 2 * v / 2) * (Real.exp (|t| * v) * ∫ x, U x ∂gaussianReal 0 v) :=
      mul_le_mul_of_nonneg_left hshift (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldIncrementMgf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moment bounds for the actual scalar canonical transition
kernels, including the unweighted root step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCosh_dist_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (x y : ℝ) :
    |fieldScalarValue L (fun z => Real.log (Real.cosh z)) x -
      fieldScalarValue L (fun z => Real.log (Real.cosh z)) y| ≤ |x - y| := by
  have hb := (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one).2
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (C := 1)
    (fun z _ => (hasDerivAt_fieldScalarLogCosh L hL z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using he

lemma fieldSpinTransition_exp_shift (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) :
    fieldSpinTransition b v F (fun u => Real.exp (t * u)) z =
      Real.exp (t * z) * (∫ x, Real.exp (t * x)
        ∂(gaussianReal 0 v).tilted (fun x => b * F (z + x))) := by
  have hm : Measurable (fun u => Real.exp (b * F u) * Real.exp (t * u)) := by fun_prop
  rw [fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_integral_shift v z hm,
    field_gaussian_integral_shift v z (hF.const_mul b).exp]
  have he : (fun x : ℝ => Real.exp (b * F (z + x)) * Real.exp (t * (z + x))) =
      fun x => Real.exp (t * z) * (Real.exp (b * F (z + x)) * Real.exp (t * x)) := by
    funext x
    rw [mul_add, Real.exp_add]
    ring
  rw [he, integral_const_mul]
  ring

theorem fieldTransitionKernel_mgf (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (hLip : ∀ x y, |F x - F y| ≤ |x - y|) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ u, Real.exp (t * u) ∂fieldTransitionKernel b v F hF z) ≤
      Real.exp (t * z + (t ^ 2 / 2 + |t|) * v) := by
  rw [fieldTransitionKernel_integral b v F hF hG,
    fieldSpinTransition_exp_shift v z b t F hF]
  have he := mul_le_mul_of_nonneg_left
    (gaussian_tilt_increment_mgf v z b t F hF hG hLip hb0 hb1) (Real.exp_pos (t * z)).le
  simpa only [Real.exp_add] using he

theorem fieldScalarTransition_mgf (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) (z b t : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let hF := (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (∫ u, Real.exp (t * u)
      ∂fieldTransitionKernel b v (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF z) ≤
        Real.exp (t * z + (t ^ 2 / 2 + |t|) * v) :=
  fieldTransitionKernel_mgf v z b t _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).2
    (fieldScalarLogCosh_dist_le L hL) hb0 hb1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTailMgf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical endpoint exponential moments depend only on the sum of
increment variances. Arbitrarily small positive exponents and arbitrarily
many levels are allowed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldTransitionKernel_integrable_exp (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable (fun y => Real.exp (t * y)) (fieldTransitionKernel b v F hF z) := by
  rw [fieldTransitionKernel_eq_tilted b v F hF hG]
  apply integrable_exp_of_linearGrowth _
    (exponentialNormMoments_tilted (gaussianReal z v)
      (gaussianReal_exponentialNormMoments z v) F hF hG b) measurable_id
  refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
  intro x
  simp [Real.norm_eq_abs]

theorem fieldTailEndpointKernel_mgf (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1) (t z : ℝ) :
    Integrable (fun y => Real.exp (t * y)) (fieldTailEndpointKernel L hL z) ∧
      (∫ y, Real.exp (t * y) ∂fieldTailEndpointKernel L hL z) ≤
        Real.exp (t * z + (t ^ 2 / 2 + |t|) * fieldTailVariance L) := by
  induction L generalizing z with
  | nil =>
    constructor
    · change Integrable (fun y => Real.exp (t * y)) (Measure.dirac z)
      exact integrable_dirac (by simp)
    · simp [fieldTailEndpointKernel, Kernel.id_apply, fieldTailVariance]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hBt := fun bv hb => hB bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hκ (x : ℝ) := And.intro
      (fieldTransitionKernel_integrable_exp av.2 x av.1 t _ hreg.1 hreg.2)
      (fieldScalarTransition_mgf L ht av.2 x av.1 t
        (hL av (List.mem_cons_self)).le (hB av (List.mem_cons_self)))
    have he := kernel_exp_bound_comp
      (fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hreg.1)
      (fieldTailEndpointKernel L ht) t ((t ^ 2 / 2 + |t|) * av.2)
      ((t ^ 2 / 2 + |t|) * fieldTailVariance L) hκ (ih ht hBt) z
    refine ⟨he.1, he.2.trans_eq ?_⟩
    congr 1
    simp only [fieldTailVariance, List.map_cons, List.sum_cons]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldInverseConvex
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite conditional overlap is convex in prescribed mean spin.
The ordinary root Gaussian is included in this identification. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma scalarFieldIncrements_exponent_le_one (h : FieldStep) :
    ∀ av ∈ scalarFieldIncrements h, av.1 ≤ 1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  change h.cut i.succ.castSucc ≤ 1
  rw [← h.last]
  exact h.ordered_cut.monotone (Fin.le_last _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEndpointMoment
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical terminal field has a depth-independent second moment,
controlled by the initial bias and the final covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma fieldTailVariance_total (h : FieldStep) :
    h.height 0 + fieldTailVariance (scalarFieldIncrements h) =
      h.height (Fin.last h.depth) := by
  have hs := fieldIncrement_sum h
  rw [Fin.sum_univ_succ] at hs
  have htail : fieldTailVariance (scalarFieldIncrements h) =
      ∑ i : Fin h.depth, (fieldIncrement h i.succ).2 := by
    simp only [fieldTailVariance, scalarFieldIncrements, List.map_ofFn,
      Function.comp_apply, NNReal.coe_mk, List.sum_ofFn]
  rw [htail]
  simpa [fieldIncrement] using hs

theorem fieldCanonicalEndpointLaw_mgf (h : FieldStep) (b t : ℝ) :
    Integrable (fun y => Real.exp (t * y)) (fieldCanonicalEndpointLaw h b) ∧
      (∫ y, Real.exp (t * y) ∂fieldCanonicalEndpointLaw h b) ≤
        Real.exp (t * b + (t ^ 2 / 2 + |t|) * h.height (Fin.last h.depth)) := by
  let L := scalarFieldIncrements h
  have hL := scalarFieldIncrements_positive h
  have hB := scalarFieldIncrements_exponent_le_one h
  have hreg := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let root : ℝ≥0 := ⟨h.height 0, h.nonneg 0⟩
  let κ := fieldTransitionKernel 0 root
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hreg.1
  have hκ (z : ℝ) := And.intro
    (fieldTransitionKernel_integrable_exp root z 0 t _ hreg.1 hreg.2)
    (fieldScalarTransition_mgf L hL root z 0 t le_rfl zero_le_one)
  have he := kernel_exp_bound_comp κ (fieldTailEndpointKernel L hL) t
    ((t ^ 2 / 2 + |t|) * root) ((t ^ 2 / 2 + |t|) * fieldTailVariance L)
    hκ (fieldTailEndpointKernel_mgf L hL hB t) b
  have hlaw : (fieldTailEndpointKernel L hL ∘ₖ κ) b = fieldCanonicalEndpointLaw h b := by
    rw [Kernel.comp_apply]
    dsimp only [κ]
    rw [fieldTransitionKernel_zero _ _ hreg.1 hreg.2]
    rfl
  rw [hlaw] at he
  refine ⟨he.1, he.2.trans_eq ?_⟩
  congr 1
  change t * b + (t ^ 2 / 2 + |t|) * h.height 0 +
    (t ^ 2 / 2 + |t|) * fieldTailVariance (scalarFieldIncrements h) = _
  calc
    _ = t * b + (t ^ 2 / 2 + |t|) *
        (h.height 0 + fieldTailVariance (scalarFieldIncrements h)) := by ring
    _ = _ := by rw [fieldTailVariance_total]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinHammingBall
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential bounds for Hamming balls and for the fibers of a
nearest-slice map. The bound is uniform over the target configuration. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma sum_exp_hamming {N : ℕ} (τ : Spin N) (t : ℝ) :
    (∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ : ℝ))) =
      (1 + Real.exp (-t)) ^ N := by
  classical
  have he (σ : Spin N) : (hammingDist σ τ : ℝ) =
      ∑ i, if σ i ≠ τ i then (1 : ℝ) else 0 := by
    simp [hammingDist, Finset.sum_ite]
  simp_rw [he, Finset.mul_sum, Real.exp_sum]
  have hp := Fintype.prod_sum (fun (i : Fin N) (b : Bool) =>
    Real.exp (-t * (if b ≠ τ i then (1 : ℝ) else 0)))
  rw [← hp]
  have hi (i : Fin N) : (∑ b : Bool, Real.exp (-t * (if b ≠ τ i then (1 : ℝ) else 0))) =
      1 + Real.exp (-t) := by
    cases τ i <;> simp [add_comm]
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma card_spinHammingBall_le {N : ℕ} (τ : Spin N) (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((spinHammingBall τ d).card : ℝ) ≤
      Real.exp (t * d) * (1 + Real.exp (-t)) ^ N := by
  have hsum : ((spinHammingBall τ d).card : ℝ) ≤
      Real.exp (t * d) * ∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ : ℝ)) := by
    calc
      _ = ∑ _σ ∈ spinHammingBall τ d, (1 : ℝ) := by simp
      _ ≤ ∑ σ ∈ spinHammingBall τ d,
          Real.exp (t * d) * Real.exp (-t * (hammingDist σ τ : ℝ)) := by
        apply Finset.sum_le_sum
        intro σ hσ
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hd : (hammingDist σ τ : ℝ) ≤ d := by
          exact_mod_cast (Finset.mem_filter.mp hσ).2
        nlinarith
      _ ≤ ∑ σ : Spin N, Real.exp (t * d) * Real.exp (-t * (hammingDist σ τ : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun σ _ _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)
      _ = _ := (Finset.mul_sum _ _ _).symm
  rwa [sum_exp_hamming] at hsum

lemma spin_map_fiber_bound {N : ℕ} (S : Finset (Spin N)) (f : Spin N → Spin N)
    (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (hf : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d)
    (τ : Spin N) :
    ((S.filter fun σ => f σ = τ).card : ℝ) ≤
      Real.exp (t * d) * (1 + Real.exp (-t)) ^ N := by
  have hsub : (S.filter fun σ => f σ = τ) ⊆ spinHammingBall τ d := by
    intro σ hσ
    obtain ⟨hS, he⟩ := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [← he] using hf σ hS⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (card_spinHammingBall_le τ d ht)

lemma restrictedSpinLog_le_of_hamming_map {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (H K : Spin N → ℝ) (c : ℝ) (d : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hd : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d)
    (hE : ∀ σ ∈ S, H σ ≤ K (f σ) + c) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K + c +
      t * d + N * Real.log (1 + Real.exp (-t)) := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  have hh := restrictedSpinLog_le_of_map S T hS hT f H K c
    (Real.exp (t * d) * (1 + Real.exp (-t)) ^ N) (by positivity) hf hE
    (fun τ _ => spin_map_fiber_bound S f d ht hd τ)
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_pos hpos N).ne',
    Real.log_exp, Real.log_pow] at hh
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEndpointProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full endpoint kernel preserves independence across the sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma kernel_comp_real {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (s : Set Y) (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∫ x, (κ x).real s ∂μ := by
  have hi : Integrable (s.indicator (fun _ : Y => (1 : ℝ))) (κ ∘ₘ μ) :=
    (integrable_const 1).indicator hs
  have he := integral_indicator_one (μ := κ ∘ₘ μ) hs
  rw [Measure.comp_eq_comp_const_apply] at hi
  have hc := Kernel.integral_comp hi
  simp only [Kernel.const_apply] at hc
  rw [← Measure.comp_eq_comp_const_apply] at hc
  have ht (x : X) : (∫ y, s.indicator (fun _ : Y => (1 : ℝ)) y ∂κ x) =
      (κ x).real s := integral_indicator_one (μ := κ x) hs
  simp_rw [ht] at hc
  exact he.symm.trans hc

lemma product_kernel_comp {N : ℕ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (K : Kernel (Fin N → ℝ) (Fin N → ℝ)) [IsMarkovKernel K]
    (hK : ∀ z, K z = Measure.pi (fun i => κ (z i)))
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    K ∘ₘ Measure.pi ν = Measure.pi (fun i => κ ∘ₘ ν i) := by
  apply (Measure.pi_eq (μ := fun i => κ ∘ₘ ν i) ?_).symm
  intro s hs
  suffices hreal : ((K ∘ₘ Measure.pi ν) (univ.pi s)).toReal =
      (∏ i, (κ ∘ₘ ν i) (s i)).toReal by
    have he := congrArg ENNReal.ofReal hreal
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _))] at he
    exact he
  rw [← measureReal_def, kernel_comp_real K (Measure.pi ν) _ (MeasurableSet.univ_pi hs)]
  have he (z : Fin N → ℝ) : (K z).real (univ.pi s) =
      ∏ i, (κ (z i)).real (s i) := by
    rw [hK, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    rfl
  simp_rw [he]
  change (∫ z : Fin N → ℝ, ∏ i,
    (fun y : ℝ => (κ y).real (s i)) (z i) ∂Measure.pi ν) = _
  rw [integral_fintype_prod_eq_prod (fun i y => (κ y).real (s i)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernel_comp_real κ (ν i) (s i) (hs i)).symm

theorem fieldVectorTailEndpointKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : Fin N → ℝ) :
    fieldVectorTailEndpointKernel N L hL z =
      Measure.pi (fun i => fieldTailEndpointKernel L hL (z i)) := by
  induction L generalizing z with
  | nil =>
    change Measure.dirac z = Measure.pi (fun i => Measure.dirac (z i))
    apply (Measure.pi_eq (μ := fun i => Measure.dirac (z i)) ?_).symm
    intro s hs
    simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Measure.dirac_apply' _ (hs _)]
    have hz : (z ∈ univ.pi s) ↔ (∀ i ∈ (Finset.univ : Finset (Fin N)), z i ∈ s i) := by
      change (∀ i ∈ (Set.univ : Set (Fin N)), z i ∈ s i) ↔ _
      simp only [Set.mem_univ, Finset.mem_univ, true_implies]
    simp only [Set.indicator, Pi.one_apply, Finset.prod_boole]
    by_cases h : z ∈ univ.pi s
    · simp only [ite_eq_left h, ite_eq_left (hz.mp h)]
    · have hn : ¬ ∀ i ∈ (Finset.univ : Finset (Fin N)), z i ∈ s i := fun hh => h (hz.mpr hh)
      simp only [ite_eq_right h, ite_eq_right hn]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (fieldVectorTailEndpointKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2 _ hreg.1) z = _
    rw [Kernel.comp_apply]
    change fieldVectorTailEndpointKernel N L ht ∘ₘ
      Measure.pi (fun i => fieldTransitionKernel av.1 av.2 _ hreg.1 (z i)) = _
    rw [product_kernel_comp (fieldTailEndpointKernel L ht)
      (fieldVectorTailEndpointKernel N L ht) (ih ht)]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEndpointIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of linear-growth vector observables under the actual
canonical endpoint law, uniformly allowing zero-variance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma integrable_linearGrowth_pi {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i))
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (Measure.pi ν) := by
  obtain ⟨C, L, _, hL, hb⟩ := hG
  have hi (i : Fin N) : Integrable (fun z : Fin N → ℝ => |z i|) (Measure.pi ν) := by
    exact (measurePreserving_eval ν i).integrable_comp_of_integrable (hν i).abs
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  apply ((integrable_const C).add (hsum.const_mul L)).mono' hF.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  apply (hb z).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hL
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (z i)))).mpr
  intro i
  simpa only [Real.norm_eq_abs] using
    (Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i))

lemma fieldTailEndpointKernel_integrable_id (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    Integrable (fun y : ℝ => y) (fieldTailEndpointKernel L hL z) := by
  have hp := (fieldTailEndpointKernel_mgf L hL hB 1 z).1
  have hn := (fieldTailEndpointKernel_mgf L hL hB (-1) z).1
  apply (hp.add hn).mono' measurable_id.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply, id_eq]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
  · rw [abs_of_nonpos (le_of_not_ge hy)]
    linarith [Real.add_one_le_exp (-y), Real.exp_pos y]

lemma fieldVectorTailEndpointKernel_integrable (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1)
    (z : Fin N → ℝ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (fieldVectorTailEndpointKernel N L hL z) := by
  rw [fieldVectorTailEndpointKernel_product]
  exact integrable_linearGrowth_pi _ (fun i => fieldTailEndpointKernel_integrable_id L hL hB (z i))
    F hF hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalRootLaw
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The biased Gaussian root followed by the full canonical recursion
has exactly the product endpoint law used in the terminal estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldCanonicalVectorLaw_root (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    fieldVectorTailEndpointKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₘ
      Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0))) =
        fieldCanonicalVectorLaw N h b := by
  rw [product_kernel_comp (fieldTailEndpointKernel (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h)) _
    (fieldVectorTailEndpointKernel_product N _ _)]
  rfl

lemma fieldCanonicalEndpointLaw_integrable_id (h : FieldStep) (b : ℝ) :
    Integrable (fun y : ℝ => y) (fieldCanonicalEndpointLaw h b) := by
  have hp := (fieldCanonicalEndpointLaw_mgf h b 1).1
  have hn := (fieldCanonicalEndpointLaw_mgf h b (-1)).1
  apply (hp.add hn).mono' measurable_id.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply, id_eq]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
  · rw [abs_of_nonpos (le_of_not_ge hy)]
    linarith [Real.add_one_le_exp (-y), Real.exp_pos y]

lemma fieldCanonicalVectorLaw_linear_integrable (N : ℕ) (h : FieldStep) (b : Fin N → ℝ)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (fieldCanonicalVectorLaw N h b) :=
  integrable_linearGrowth_pi _ (fun i => fieldCanonicalEndpointLaw_integrable_id h (b i)) F hF hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted recursion and its canonical transition are exactly
products of the scalar field recursions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldScalarValue_ofFn (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    fieldScalarValue (List.ofFn (fun i : Fin n => (b i, v i)))
      (fun y => Real.log (Real.cosh y)) =
      cascadeRecursion n b (fun i => gaussianCascadeMarks v i)
        (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y)) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have ht : ∀ i < n, 0 < b (i + 1) := fun i hi => hb (i + 1) (by omega)
    rw [List.ofFn_succ]
    change gaussianOperator (b 0) (v 0)
      (fieldScalarValue (List.ofFn (fun i : Fin n => (b (i + 1), v (i + 1))))
        (fun y => Real.log (Real.cosh y))) = _
    rw [ih (fun i => b (i + 1)) (fun i => v (i + 1)) ht]
    funext z
    exact gaussianOperator_eq_gaussian_logMean (hb 0 (by omega)).ne' _
      (measurable_cascadeRecursion n _ _ (fun _ => measurable_fst.add measurable_snd)
        measurable_logCosh) z

theorem restrictedFieldRecursion_univ {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ n b v z =
      ∑ i, fieldScalarValue (List.ofFn (fun j : Fin n => (b j, v j)))
        (fun y => Real.log (Real.cosh y)) (z i) := by
  have ht : restrictedFieldTerminal (Finset.univ : Finset (Spin N)) =
      (fun z => ∑ i, Real.log (Real.cosh (z i))) := by
    funext y
    exact restrictedFieldTerminal_univ y
  rw [restrictedFieldRecursion, ht]
  have he := vectorCascade_logCosh_sum N n b v hb (fun _ => 0) z
  simp only [zero_add] at he
  rw [he, fieldScalarValue_ofFn n b v hb]

lemma vectorGaussian_shift {N : ℕ} (v : ℝ≥0) (z : Fin N → ℝ) :
    MeasurePreserving (fun w : Fin N → ℝ => z + w)
      (vectorGaussianLaw N v : Measure (Fin N → ℝ))
      (Measure.pi (fun i => gaussianReal (z i) v)) := by
  apply measurePreserving_pi
  intro i
  refine ⟨measurable_const.add measurable_id, ?_⟩
  change (gaussianReal 0 v).map (fun x : ℝ => z i + x) = gaussianReal (z i) v
  simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) (z i)

lemma vectorGaussian_tilt_transition {N : ℕ} (a : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    ((vectorGaussianLaw N v : Measure (Fin N → ℝ)).tilted
      (fun w => a * ∑ i, F ((z + w) i))).map (fun w => z + w) =
        fieldVectorTransitionKernel N a v F hF z := by
  have hm : Measurable (fun y : Fin N → ℝ => a * ∑ i, F (y i)) := by fun_prop
  have he := cavity_tilt_map (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => z + w) (measurable_const.add measurable_id) (fun y => a * ∑ i, F (y i)) hm
  rw [(vectorGaussian_shift v z).map_eq, fieldGaussian_product_tilt a v F hF hG z] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inclusion and exact bias transport through the constrained Gaussian
recursion, before normalizing per cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem restrictedFieldRecursion_mono {N : ℕ} (hN : 0 < N)
    (S T : Finset (Spin N)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion S n b v z ≤ restrictedFieldRecursion T n b v z := by
  induction n generalizing b v z with
  | zero => exact restrictedSpinLog_mono hS hST (fun _ _ => le_rfl)
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion S n bs vs (z + w)) ≤
      logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion T n bs vs (z + w))
    exact logMean_mono _ (hb 0 (by omega))
      (integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z)
      (integrable_exp_restrictedFieldRecursion hN T hT n bs vs hbs (v 0) (b 0) z)
      (fun w => ih bs vs hbs (z + w))

theorem restrictedFieldRecursion_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion (spinGroupSlice group k) n b v (z + fun i => bias (group i)) =
      restrictedFieldRecursion (spinGroupSlice group k) n b v z +
        spinGroupFieldConstant group k bias := by
  induction n generalizing b v z with
  | zero => exact restrictedFieldTerminal_group_bias group k hk bias z
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion (spinGroupSlice group k) n bs vs
        ((z + fun i => bias (group i)) + w)) =
      logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
        (fun w => restrictedFieldRecursion (spinGroupSlice group k) n bs vs (z + w)) + _
    have he : (fun w : Fin N → ℝ => restrictedFieldRecursion (spinGroupSlice group k) n bs vs
        ((z + fun i => bias (group i)) + w)) =
        fun w => spinGroupFieldConstant group k bias +
          restrictedFieldRecursion (spinGroupSlice group k) n bs vs (z + w) := by
      funext w
      have hz : (z + fun i => bias (group i)) + w = (z + w) + fun i => bias (group i) := by abel
      rw [hz, ih bs vs hbs]
      ring
    rw [he, logMean_const_add _ (hb 0 (by omega)).ne'
      (integrable_exp_restrictedFieldRecursion hN _ (spinGroupSlice_nonempty group k hk)
        n bs vs hbs (v 0) (b 0) z)]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_LogMeanLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Gaussian backward step propagates a terminal loss by expectation
under its canonical tilted transition. No lower bound on its positive
exponent is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integral_le_log_integral_exp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (hF : Integrable F μ) (he : Integrable (fun x => Real.exp (F x)) μ) :
    (∫ x, F x ∂μ) ≤ Real.log (∫ x, Real.exp (F x) ∂μ) := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all μ (fun _ => Set.mem_univ _)) hF he
  have hl := Real.log_le_log (Real.exp_pos (∫ x, F x ∂μ)) hj
  rwa [Real.log_exp] at hl

theorem logMean_loss_le_tilted_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hD : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * F x))) :
    logMean b μ F - logMean b μ G ≤
      ∫ x, F x - G x ∂μ.tilted (fun x => b * F x) := by
  let ν := μ.tilted (fun x => b * F x)
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hF
  have hE : Integrable (fun x => Real.exp (-b * (F x - G x))) ν := by
    apply (integrable_tilted_iff hF _).mpr
    convert hG using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hi := integral_le_log_integral_exp ν (fun x => -b * (F x - G x))
    (hD.const_mul (-b)) hE
  have he : (∫ x, Real.exp (-b * (F x - G x)) ∂ν) =
      (∫ x, Real.exp (b * G x) ∂μ) / ∫ x, Real.exp (b * F x) ∂μ := by
    rw [integral_exp_tilted]
    congr 2
    funext x
    congr 1
    change b * F x + -b * (F x - G x) = b * G x
    ring
  rw [integral_const_mul, he, Real.log_div (integral_exp_pos μ G hG).ne'
    (integral_exp_pos μ F hF).ne'] at hi
  change Real.log (∫ x, Real.exp (b * F x) ∂μ) / b -
    Real.log (∫ x, Real.exp (b * G x) ∂μ) / b ≤ _
  rw [← sub_div]
  apply (div_le_iff₀ hb).mpr
  dsimp only [ν] at hi
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldStepLoss
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical transition propagates the actual constrained-block
loss by expectation. All integrability obligations follow from the
finite-spin terminal and Gaussian exponential moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedFieldRecursion_tilt_integrable {N : ℕ} (hN : 0 < N)
    (S T : Finset (Spin N)) (hS : S.Nonempty) (hT : T.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (root : ℝ≥0) (q : ℝ) (z : Fin N → ℝ) :
    Integrable (fun w => restrictedFieldRecursion T n b v (z + w))
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).tilted
        (fun w => q * restrictedFieldRecursion S n b v (z + w))) := by
  have hF := restrictedFieldRecursion_regular hN S hS n b v hb
  have hG := restrictedFieldRecursion_regular hN T hT n b v hb
  exact integrable_linearGrowth_tilted (vectorGaussianLaw N root : Measure (Fin N → ℝ))
    (vectorGaussianLaw_moments hN root)
    (fun w : Fin N → ℝ => restrictedFieldRecursion S n b v (z + w))
    (fun w : Fin N → ℝ => restrictedFieldRecursion T n b v (z + w))
    (hF.1.comp (measurable_const.add measurable_id)) (hF.2.add_left z)
    (hG.1.comp (measurable_const.add measurable_id)) (hG.2.add_left z) q

theorem restrictedFieldRecursion_step_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n + 1, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ (n + 1) b v z -
        restrictedFieldRecursion S (n + 1) b v z ≤
      ∫ w, restrictedFieldRecursion Finset.univ n (fun i => b (i + 1))
          (fun i => v (i + 1)) (z + w) -
        restrictedFieldRecursion S n (fun i => b (i + 1)) (fun i => v (i + 1)) (z + w)
        ∂(vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
          (fun w => b 0 * restrictedFieldRecursion Finset.univ n (fun i => b (i + 1))
            (fun i => v (i + 1)) (z + w)) := by
  let bs := fun i => b (i + 1)
  let vs := fun i => v (i + 1)
  have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
  let F := fun w => restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs (z + w)
  let G := fun w => restrictedFieldRecursion S n bs vs (z + w)
  change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) F -
    logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) G ≤
      ∫ w, F w - G w ∂(vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
        (fun w => b 0 * F w)
  have hiF := integrable_exp_restrictedFieldRecursion hN (Finset.univ : Finset (Spin N))
    Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z
  have hiG := integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z
  have hiFF := restrictedFieldRecursion_tilt_integrable hN Finset.univ Finset.univ
    Finset.univ_nonempty Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z
  have hiFG := restrictedFieldRecursion_tilt_integrable hN Finset.univ S
    Finset.univ_nonempty hS n bs vs hbs (v 0) (b 0) z
  have hD : Integrable (fun w => F w - G w)
      ((vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted (fun w => b 0 * F w)) :=
    hiFF.sub hiFG
  exact logMean_loss_le_tilted_mean (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) F G
    (hb 0 (by omega)) hiF hiG hD

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldEndpointLoss
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating the canonical one-step inequality carries the constrained
recursion loss to the actual terminal endpoint law, with no depth factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma linearGrowth_difference {E : Type*} [SeminormedAddCommGroup E]
    {F G : E → ℝ} (hF : HasLinearGrowth F) (hG : HasLinearGrowth G) :
    HasLinearGrowth (fun x => F x - G x) := by
  obtain ⟨C, L, hC, hL, hF⟩ := hF
  obtain ⟨D, K, hD, hK, hG⟩ := hG
  refine ⟨C + D, L + K, by positivity, by positivity, fun x => ?_⟩
  calc
    _ ≤ |F x| + |G x| := abs_sub _ _
    _ ≤ (C + L * ‖x‖) + (D + K * ‖x‖) := add_le_add (hF x) (hG x)
    _ = _ := by ring

lemma restrictedFieldTerminal_loss_regular {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Measurable (fun z => restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z) ∧
      HasLinearGrowth (fun z => restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z) :=
  ⟨(continuous_restrictedFieldTerminal Finset.univ Finset.univ_nonempty).measurable.sub
      (continuous_restrictedFieldTerminal S hS).measurable,
    linearGrowth_difference (restrictedFieldTerminal_linearGrowth Finset.univ Finset.univ_nonempty)
      (restrictedFieldTerminal_linearGrowth S hS)⟩

theorem restrictedFieldRecursion_endpoint_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (hb1 : ∀ i < n, b i ≤ 1) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ n b v z - restrictedFieldRecursion S n b v z ≤
      ∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
        ∂fieldVectorTailEndpointKernel N (List.ofFn (fun i : Fin n => (b i, v i)))
          (by
            intro av hav
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
            exact hb i i.isLt) z := by
  induction n generalizing b v z with
  | zero =>
    simp only [List.ofFn_zero, fieldVectorTailEndpointKernel, Kernel.id_apply, integral_dirac]
    exact le_rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let L := List.ofFn (fun i : Fin n => (bs i, vs i))
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hbs1 : ∀ i < n, bs i ≤ 1 := fun i hi => hb1 (i + 1) (by omega)
    have hL : ∀ av ∈ L, 0 < av.1 := by
      intro av hav
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
      exact hbs i i.isLt
    have hL1 : ∀ av ∈ L, av.1 ≤ 1 := by
      intro av hav
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
      exact hbs1 i i.isLt
    let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
    have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
    let κ := fieldVectorTransitionKernel N (b 0) (v 0) F hF.1
    let η := fieldVectorTailEndpointKernel N L hL
    let D := fun y => restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
    have hD := restrictedFieldTerminal_loss_regular S hS
    have hInt : Integrable D ((η ∘ₖ κ) z) := by
      have hfull : ∀ av ∈ (b 0, v 0) :: L, 0 < av.1 := by
        simpa only [List.forall_mem_cons] using And.intro (hb 0 (by omega)) hL
      have hfull1 : ∀ av ∈ (b 0, v 0) :: L, av.1 ≤ 1 := by
        simpa only [List.forall_mem_cons] using And.intro (hb1 0 (by omega)) hL1
      exact fieldVectorTailEndpointKernel_integrable N _ hfull hfull1 z D hD.1 hD.2
    have hOuter : Integrable (fun y => ∫ w, D w ∂η y) (κ z) := hInt.integral_comp
    let d := fun y => restrictedFieldRecursion Finset.univ n bs vs y -
      restrictedFieldRecursion S n bs vs y
    have hregF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hregS := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    have hdM : Measurable d := hregF.1.sub hregS.1
    let μ := (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
      (fun w => b 0 * restrictedFieldRecursion Finset.univ n bs vs (z + w))
    have hmap : μ.map (fun w => z + w) = κ z := by
      have he : (fun w => b 0 * restrictedFieldRecursion Finset.univ n bs vs (z + w)) =
          (fun w => b 0 * ∑ i, F ((z + w) i)) := by
        funext w
        rw [restrictedFieldRecursion_univ n bs vs hbs]
      change ((vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted _).map _ = _
      rw [he]
      exact vectorGaussian_tilt_transition (b 0) (v 0) F hF.1 hF.2 z
    have hdInt : Integrable d (κ z) := by
      rw [← hmap]
      apply (integrable_map_measure hdM.aestronglyMeasurable
        (measurable_const.add measurable_id).aemeasurable).mpr
      exact (restrictedFieldRecursion_tilt_integrable hN Finset.univ Finset.univ
        Finset.univ_nonempty Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z).sub
        (restrictedFieldRecursion_tilt_integrable hN Finset.univ S
          Finset.univ_nonempty hS n bs vs hbs (v 0) (b 0) z)
    have hm : (∫ w, d (z + w) ∂μ) = ∫ y, d y ∂κ z := by
      rw [← hmap]
      exact (integral_map (show AEMeasurable (fun w : Fin N → ℝ => z + w) μ from
        (measurable_const.add measurable_id).aemeasurable) hdM.aestronglyMeasurable).symm
    calc
      _ ≤ ∫ w, d (z + w) ∂μ := restrictedFieldRecursion_step_loss hN S hS n b v hb z
      _ = ∫ y, d y ∂κ z := hm
      _ ≤ ∫ y, ∫ w, D w ∂η y ∂κ z := by
        apply integral_mono hdInt hOuter
        intro y
        exact ih bs vs hbs hbs1 y
      _ = ∫ y, D y ∂(η ∘ₖ κ) z := (Kernel.integral_comp hInt).symm
      _ = _ := by
        simp only [List.ofFn_succ, fieldVectorTailEndpointKernel]
        rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldRootLoss
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained recursion loss, averaged over the actual biased root,
is bounded by the averaged terminal loss. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepIncrements (h : FieldStep) :
    List.ofFn (fun i : Fin h.depth => (chainExponent h.cut i, fieldStepVariance h i)) =
      scalarFieldIncrements h := by
  unfold scalarFieldIncrements
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · rw [chainExponent_apply h.cut i.isLt]
    rfl
  · simp only [fieldStepVariance, dite_eq_left i.isLt, scalarFieldIncrements, List.get_ofFn]
    congr 3


lemma restrictedFieldRecursion_biased_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    Integrable (restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h))
      (Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) := by
  have hr := restrictedFieldRecursion_regular hN S hS h.depth (chainExponent h.cut)
    (fieldStepVariance h) (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
  exact integrable_linearGrowth_pi _ (fun _ => IsGaussian.integrable_id) _ hr.1 hr.2

theorem restrictedFieldRecursion_root_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    (∫ z, restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut) (fieldStepVariance h) z -
      restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h) z
      ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) ≤
    ∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
      ∂fieldCanonicalVectorLaw N h b := by
  let μ := Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))
  let η := fieldVectorTailEndpointKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
  let D := fun y => restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
  have hD := restrictedFieldTerminal_loss_regular S hS
  have hi : Integrable D (η ∘ₘ μ) := by
    rw [fieldCanonicalVectorLaw_root]
    exact fieldCanonicalVectorLaw_linear_integrable N h b D hD.1 hD.2
  have ho : Integrable (fun z => ∫ y, D y ∂η z) μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi
    simpa only [Kernel.const_apply] using hi.integral_comp
  have hl := (restrictedFieldRecursion_biased_root_integrable hN Finset.univ
    Finset.univ_nonempty h b).sub (restrictedFieldRecursion_biased_root_integrable hN S hS h b)
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  calc
    _ ≤ ∫ z, ∫ y, D y ∂η z ∂μ := by
      apply integral_mono hl ho
      intro z
      have he := restrictedFieldRecursion_endpoint_loss hN S hS h.depth
        (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1)
        (fun i hi => (hb.1 i hi).2.le) z
      change restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut)
        (fieldStepVariance h) z - restrictedFieldRecursion S h.depth (chainExponent h.cut)
        (fieldStepVariance h) z ≤ _
      simpa only [fieldStepIncrements] using he
    _ = ∫ y, D y ∂(η ∘ₘ μ) := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      exact (Kernel.integral_comp hi).symm
    _ = _ := by rw [fieldCanonicalVectorLaw_root]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_ConstrainedBlockBias
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact bias cancellation on a constrained block and identification of
the unrestricted block with the average scalar field functional. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldValue_gaussian_integral (h : FieldStep) (b : ℝ) :
    (∫ z, fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) z
      ∂gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))) =
      fieldValue h b + h.height (Fin.last h.depth) / 2 := by
  have he := gaussianOperator_eq_gaussian_integral (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).1 b
  change gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y))) b = _ at he
  rw [fieldValue_root]
  linarith [he]

theorem biasedConstrainedBlockValue_univ {N : ℕ} (hN : 0 < N) (h : FieldStep) (b : Fin N → ℝ) :
    biasedConstrainedBlockValue Finset.univ h b = (N : ℝ)⁻¹ * ∑ i, fieldValue h (b i) := by
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have hrec : restrictedFieldRecursion (Finset.univ : Finset (Spin N)) h.depth
      (chainExponent h.cut) (fieldStepVariance h) = fun z => ∑ i,
        fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i) := by
    funext z
    simpa only [fieldStepIncrements] using restrictedFieldRecursion_univ h.depth
      (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1) z
  have hreg := fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth
  have hi (i : Fin N) : Integrable (fun z : Fin N → ℝ =>
      fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i))
      (Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))) :=
    (measurePreserving_eval _ i).integrable_comp_of_integrable
      (field_gaussian_linear_integrable _ (b i) hreg.1 hreg.2)
  rw [biasedConstrainedBlockValue, hrec, integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin N) : (∫ z : Fin N → ℝ,
      fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) (z i)
      ∂Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))) =
      fieldValue h (b i) + h.height (Fin.last h.depth) / 2 := by
    rw [integral_comp_eval (μ := fun j : Fin N =>
      gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0))) (i := i) hreg.1.aestronglyMeasurable]
    exact fieldValue_gaussian_integral h (b i)
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem biasedConstrainedBlockValue_group {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ) (h : FieldStep) :
    biasedConstrainedBlockValue (spinGroupSlice group k) h (fun i => bias (group i)) =
      constrainedBlockValue (spinGroupSlice group k) h +
        (N : ℝ)⁻¹ * spinGroupFieldConstant group k bias := by
  let S := spinGroupSlice group k
  let F := restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h)
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  have hreg := restrictedFieldRecursion_regular hN S (spinGroupSlice_nonempty group k hk)
    h.depth (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1)
  have he : (∫ z, F z ∂Measure.pi (fun i => gaussianReal (bias (group i))
      (NNReal.mk (h.height 0) (h.nonneg 0)))) =
      ∫ z, F z + spinGroupFieldConstant group k bias
        ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) := by
    rw [← (vectorGaussian_shift _ (fun i => bias (group i))).map_eq,
      integral_map (show AEMeasurable (fun z : Fin N → ℝ => (fun i => bias (group i)) + z)
        (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) from
          (measurable_const.add measurable_id).aemeasurable) hreg.1.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change F ((fun i => bias (group i)) + z) = _
    rw [add_comm]
    exact restrictedFieldRecursion_group_bias hN group k hk bias _ _ _
      (fun i hi => (hb.1 i hi).1) z
  change (N : ℝ)⁻¹ * (∫ z, F z ∂_) - _ = (N : ℝ)⁻¹ * (∫ z, F z ∂_) - _ + _
  rw [he, integral_add (constrainedBlockValue_root_integrable hN S
    (spinGroupSlice_nonempty group k hk) h) (integrable_const _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical pressure on a fixed spin constraint, retaining its original
cube mass. The Haar Lipschitz constant is independent of the constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma restrictedRotatedPressure_univ {N : ℕ} (eig : Fin N → ℝ)
    (U : Rotation N) (c : Fin N → ℝ) :
    restrictedRotatedPressure Finset.univ eig U c = rotatedPressure eig U c := by
  rw [restrictedRotatedPressure, restrictedSpinLog_univ]
  rfl

lemma abs_restrictedRotatedPressure_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |restrictedRotatedPressure S eig (specialRotation U) c -
      restrictedRotatedPressure S eig (specialRotation V) c| ≤ K * frobeniusDistance U V := by
  have he := abs_restrictedSpinLog_sub_le S hS
    (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)
    (K * N * frobeniusDistance U V) (fun σ _ => by
      simpa only [add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig σ)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  calc
    _ = (N : ℝ)⁻¹ * |restrictedSpinLog S
        (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) -
        restrictedSpinLog S (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)| := by
      rw [restrictedRotatedPressure, restrictedRotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (K * N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp

lemma measurable_restrictedRotatedPressure {N : ℕ} (S : Finset (Spin N))
    (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => restrictedRotatedPressure S eig (specialRotation U) c) := by
  have hE (σ : Spin N) : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul
        (eig i)).const_mul (1 / 2 : ℝ)).add_const _
  unfold restrictedRotatedPressure restrictedSpinLog
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).log.sub_const _).const_mul _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveFieldPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A repeated constrained block contributes its exact deterministic
external-field term to the full pressure. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinGroupFieldConstant_magnetization {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (b γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (hk : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2)) :
    spinGroupFieldConstant group k b=(n : ℝ)*∑ a, γ a*b a*mag a := by
  unfold spinGroupFieldConstant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hk, hcount]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergyPrimitive
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature primitive of the finite-spectrum interaction energy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralSlope_temperature (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (∫ u in 0..t, finiteSpectralSlope ρ eig hρ hρsum (u * x)) =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  have hc : Continuous (finiteThermalScalar ρ eig hρ hρsum x) :=
    continuous_id.mul ((continuous_finiteR ρ eig hρ hρsum).comp
      (continuous_const.mul continuous_id))
  have hd : ∀ u ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum x)
        (finiteSpectralSlope ρ eig hρ hρsum (u * x)) (Ioi u) u := by
    intro u hu
    have h := hasDerivWithinAt_finiteThermalScalar ρ eig hρ hρsum hx hu.1.le
    rw [mul_comm x u] at h
    exact h.mono fun y hy => (lt_trans hu.1 (show u < y from hy)).le
  have hint : IntervalIntegrable (fun u => finiteSpectralSlope ρ eig hρ hρsum (u * x))
      volume 0 t :=
    ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
      (continuous_id.mul continuous_const)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc.continuousOn hd hint
  simpa only [finiteThermalScalar, zero_mul, sub_zero, mul_comm x t] using hFTC

/-- Equation `up:primitive`, for the actual finite atomic spectral transform. -/
theorem integral_finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    (∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p) =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p := by
  let K := ∑ a, |eig a|
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hS : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  let f : ℝ → ℝ → ℝ := fun u r => finiteSpectralSlope ρ eig hρ hρsum (u * deficit p r)
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (Function.uncurry f) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).measurable.comp
      (measurable_fst.mul ((continuous_deficit p).measurable.comp measurable_snd))
  have hi : Integrable (Function.uncurry f) ((volume.restrict (uIoc 0 t)).prod pathMeasure) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖finiteSpectralSlope ρ eig hρ hρsum (z.1 * deficit p z.2)‖ ≤ K
      simpa only [Real.norm_eq_abs] using hS (z.1 * deficit p z.2)
  have hswap := intervalIntegral_integral_swap hi
  unfold finiteInteractionEnergy spectralFunctional
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in 0..t, ∫ r, f u r ∂pathMeasure) =
    (1 / 2 : ℝ) * ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact integral_finiteSpectralSlope_temperature ρ eig hρ hρsum ht (deficit_nonneg p hr.2.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperatureFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteTemperatureFunctional_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {t : ℝ} (ht : 0 ≤ t) :
    finiteTemperatureFunctional ρ eig hρ hρsum p t =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p :=
  integral_finiteInteractionEnergy ρ eig hρ hρsum ht p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPathLimit
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 approximation of the trial path preserves the finite spectral
interaction functional, as required when removing a finite partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma finiteTemperatureFunctional_tendsto_of_L1 {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun k => ∫ s, |q k s - p s| ∂pathMeasure) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => finiteTemperatureFunctional ρ eig hρ hρsum (q k) t) atTop
      (𝓝 (finiteTemperatureFunctional ρ eig hρ hρsum p t)) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun b _ => abs_nonneg (eig b)) (Finset.mem_univ a)
  have hbound (x : ℝ) : |finiteR ρ eig hρ hρsum x| ≤ K :=
    abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hd (r : ℝ) : Tendsto (fun k => deficit (q k) r) atTop (𝓝 (deficit p r)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ hL
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [Real.norm_eq_abs] using abs_deficit_sub_path_le (q k) p r)
  have hi : Tendsto (fun k => ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit (q k) r)
      ∂pathMeasure) atTop
      (𝓝 (∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => t * K)
    · intro k
      exact (continuous_const.mul ((continuous_finiteR ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit (q k))))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left (hbound _) ht)
    · exact ae_of_all _ (fun r =>
        (((continuous_finiteR ρ eig hρ hρsum).tendsto _).comp ((hd r).const_mul t)).const_mul t)
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ ht,
    spectralFunctional] using hi.const_mul (1 / 2 : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TrialGridApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower finite-grid trials approximate each monotone overlap path in L1,
remain below one, and do not increase the entropy functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma lowerGridPath_below_one (p : OverlapPath) (n : ℕ) (s : ℝ) :
    lowerGridPath p n s ≤ 1 - 1 / (n + 1 : ℕ) := by
  change (1 - 1 / (n + 1 : ℕ) : ℝ) * _ ≤ _
  exact mul_le_of_le_one_right (lowerGrid_factor_nonneg n) (p.le_one _)

lemma lowerGridPath_le (p : OverlapPath) (n : ℕ) :
    (lowerGridPath p n).val ≤ᵐ[pathMeasure] p.val := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact lowerGrid_le p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩) n hs.1.le

lemma lowerGridPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1))
    (s : ℝ) (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    lowerGridPath p n s = (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)) := by
  change lowerGrid p.val n s = _
  simp only [lowerGrid, floor_on_uniformCell n i hs]

lemma lowerGridPath_L1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have hi := lowerGrid_integral_tendsto p.monotone (fun u => ⟨p.nonneg u, p.le_one u⟩)
  change Tendsto (fun n => ∫ s, lowerGridPath p n s ∂pathMeasure) atTop
    (𝓝 (∫ s, p s ∂pathMeasure)) at hi
  have he (n : ℕ) : (∫ s, |lowerGridPath p n s - p s| ∂pathMeasure) =
      (∫ s, p s ∂pathMeasure) - ∫ s, lowerGridPath p n s ∂pathMeasure := by
    rw [← integral_sub p.integrable (lowerGridPath p n).integrable]
    apply integral_congr_ae
    filter_upwards [lowerGridPath_le p n] with s hs
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    ring
  simpa only [he, sub_self] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ s, p s ∂pathMeasure)
      atTop (𝓝 (∫ s, p s ∂pathMeasure))).sub hi)

lemma lowerGridPath_spectral_tendsto {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Tendsto (fun n => spectralFunctional (finiteR ρ eig hρ hρsum) (lowerGridPath p n))
      atTop (𝓝 (spectralFunctional (finiteR ρ eig hρ hρsum) p)) := by
  have ht := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hρsum p
    (lowerGridPath p) (lowerGridPath_L1_tendsto p) zero_le_one
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ zero_le_one, one_mul] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRoundedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding an interior magnetization to an attainable spin count. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma magneticRoundedCount_le (G : ℕ) {s : ℝ} (hs : |s|≤1) :
    magneticRoundedCount G s ≤ G := by
  have h := Nat.floor_le (show 0≤(G:ℝ)*((1+s)/2) by
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hs).1]))
  have ht : (G:ℝ)*((1+s)/2)≤G := by
    nlinarith [(Nat.cast_nonneg G : (0:ℝ)≤G),(abs_le.mp hs).2]
  exact_mod_cast h.trans ht

lemma magneticRoundedCount_value (G : ℕ) {s : ℝ} (_hs : |s|≤1) :
    (magneticRoundedCount G s : ℝ)=(G:ℝ)*((1+magneticRoundedValue G s)/2) := by
  by_cases hG : G=0
  · simp [hG,magneticRoundedCount,magneticRoundedValue]
  · simp only [magneticRoundedValue,ite_eq_right hG]
    have hn : (G:ℝ)≠0 := Nat.cast_ne_zero.mpr hG
    field_simp
    ring

lemma magneticRoundedValue_error {G : ℕ} (hG : 0<G) {s : ℝ} (hs : |s|≤1) :
    |magneticRoundedValue G s-s|≤2/(G:ℝ) := by
  have hp : (0:ℝ)<G := Nat.cast_pos.mpr hG
  have hx : 0≤(G:ℝ)*((1+s)/2) :=
    mul_nonneg hp.le (by linarith [(abs_le.mp hs).1])
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one ((G:ℝ)*((1+s)/2))
  have he : magneticRoundedValue G s-s=
      2*((magneticRoundedCount G s : ℝ)-(G:ℝ)*((1+s)/2))/G := by
    simp only [magneticRoundedValue,ite_eq_right (Nat.ne_of_gt hG)]
    field_simp
    ring
  rw [he,abs_div,abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have ha : |(magneticRoundedCount G s : ℝ)-(G:ℝ)*((1+s)/2)|≤1 := by
    apply abs_le.mpr
    dsimp only [magneticRoundedCount]
    constructor <;> linarith
  nlinarith

lemma magneticRoundedValue_tendsto (G : ℕ → ℕ) (hG : Tendsto G atTop atTop)
    {s : ℝ} (hs : |s|≤1) :
    Tendsto (fun k => magneticRoundedValue (G k) s) atTop (𝓝 s) := by
  have hpos : ∀ᶠ k in atTop, 0<G k := hG.eventually (eventually_gt_atTop 0)
  have he : Tendsto (fun k => 2/(G k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hG))
  have hzero : Tendsto (fun k => magneticRoundedValue (G k) s-s) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ he
    · filter_upwards [hpos] with k hk
      simpa only [Real.norm_eq_abs] using magneticRoundedValue_error hk hs
  simpa only [sub_add_cancel,zero_add] using hzero.add_const s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinCountMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real magnetization associated with an attainable integer count. -/
noncomputable section
namespace InvariantIsing

lemma spinCountMagnetization_bounds {G k : ℕ} (hk : k≤G) :
    |spinCountMagnetization G k|≤1 := by
  by_cases hG : G=0
  · simp [spinCountMagnetization,hG]
  · have hp : (0:ℝ)<G := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hG)
    have hk' : (k:ℝ)≤G := Nat.cast_le.mpr hk
    simp only [spinCountMagnetization,ite_eq_right hG]
    apply abs_le.mpr
    constructor
    · have : (0:ℝ)≤2*k/G := by positivity
      linarith
    · have : 2*(k:ℝ)/G≤2 := (div_le_iff₀ hp).mpr (by linarith)
      linarith

lemma spinCountMagnetization_count {G k : ℕ} (hk : k≤G) :
    (k:ℝ)=(G:ℝ)*((1+spinCountMagnetization G k)/2) := by
  by_cases hG : G=0
  · have : k=0 := by omega
    simp [spinCountMagnetization,hG,this]
  · simp only [spinCountMagnetization,ite_eq_right hG]
    have hn : (G:ℝ)≠0 := Nat.cast_ne_zero.mpr hG
    field_simp
    ring

lemma rounded_count_distance {G k : ℕ} (hk : k≤G) {q δ : ℝ}
    (hq : |q|≤1) (hd : |spinCountMagnetization G k-q|≤δ) :
    |(k:ℝ)-(magneticRoundedCount G q:ℝ)|≤(G:ℝ)*δ/2+1 := by
  have hx : 0≤(G:ℝ)*((1+q)/2) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hq).1])
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one ((G:ℝ)*((1+q)/2))
  have ha : |(G:ℝ)*((1+q)/2)-(magneticRoundedCount G q:ℝ)|≤1 := by
    apply abs_le.mpr
    dsimp only [magneticRoundedCount]
    constructor <;> linarith
  have he : (k:ℝ)-(G:ℝ)*((1+q)/2)=
      (G:ℝ)/2*(spinCountMagnetization G k-q) := by
    rw [spinCountMagnetization_count hk]
    ring
  calc
    _ ≤ |(k:ℝ)-(G:ℝ)*((1+q)/2)|+
        |(G:ℝ)*((1+q)/2)-(magneticRoundedCount G q:ℝ)| := abs_sub_le _ _ _
    _ ≤ (G:ℝ)/2*δ+1 := by
      rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(G:ℝ)/2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hd (by positivity)) ha
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinSliceComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic comparison of restricted pressures through bounded
spin-flip maps, including the multiplicity cost of those maps. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma rotated_spin_energy_map_bound {N : ℕ} (eig c : Fin N → ℝ) (U : Rotation N)
    (σ τ : Spin N) (d : ℕ) (hd : hammingDist σ τ ≤ d)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C) :
    |(rotatedEnergy eig U σ + fieldEnergy c σ) -
      (rotatedEnergy eig U τ + fieldEnergy c τ)| ≤
      2 * K * Real.sqrt ((N : ℝ) * d) + 2 * C * d := by
  have hd' : (hammingDist σ τ : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hquad := abs_rotatedEnergy_sub_spin_le eig U σ τ hK heig
  have hfield := abs_fieldEnergy_sub_spin_le c σ τ hc
  have hsqrt : Real.sqrt ((N : ℝ) * (hammingDist σ τ : ℝ)) ≤
      Real.sqrt ((N : ℝ) * d) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg _))
  have he : (rotatedEnergy eig U σ + fieldEnergy c σ) -
      (rotatedEnergy eig U τ + fieldEnergy c τ) =
      (rotatedEnergy eig U σ - rotatedEnergy eig U τ) +
        (fieldEnergy c σ - fieldEnergy c τ) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (hquad.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity)))
    (hfield.trans (mul_le_mul_of_nonneg_left hd' (by positivity))))

lemma restricted_spin_pressure_map_le {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (eig c : Fin N → ℝ) (U : Rotation N) (d : ℕ)
    {K C t : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hd : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d) :
    restrictedSpinLog S (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) ≤
      restrictedSpinLog T (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) +
      (2 * K * Real.sqrt ((N : ℝ) * d) + 2 * C * d) +
      t * d + N * Real.log (1 + Real.exp (-t)) := by
  apply restrictedSpinLog_le_of_hamming_map S T hS hT f _ _ _ d ht hf hd
  intro σ hσ
  have hh := rotated_spin_energy_map_bound eig c U σ (f σ) d (hd σ hσ) hK hC heig hc
  linarith [(le_abs_self _).trans hh]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinFiniteCover
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite unions of spin constraints approximate the full partition function
with an explicit spin-projection error and a finite-union cost. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma sum_biUnion_le_sum_of_nonneg {X J : Type*} [DecidableEq X]
    (B : Finset J) (S : J → Finset X) (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    ∑ x ∈ B.biUnion S, f x ≤ ∑ j ∈ B, ∑ x ∈ S j, f x := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert j B hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have hu := Finset.sum_union_inter (s₁ := S j) (s₂ := B.biUnion S) (f := f)
    have hp : 0≤∑ x ∈ S j ∩ B.biUnion S, f x :=
      Finset.sum_nonneg (fun x _ => hf x)
    linarith

lemma restrictedSpinLog_finite_union_le {N : ℕ} {J : Type*}
    (B : Finset J) (hB : B.Nonempty) (S : J → Finset (Spin N))
    (hS : ∀ j ∈ B, (S j).Nonempty) (H : Spin N → ℝ) (M : ℝ)
    (hM : ∀ j ∈ B, restrictedSpinLog (S j) H ≤ M) :
    restrictedSpinLog (B.biUnion S) H ≤ M+Real.log B.card := by
  classical
  have hU : (B.biUnion S).Nonempty := by
    obtain ⟨j,hj⟩ := hB
    obtain ⟨σ,hσ⟩ := hS j hj
    exact ⟨σ, Finset.mem_biUnion.mpr ⟨j,hj,hσ⟩⟩
  have hsum (j : J) (hj : j∈B) :
      (∑ σ ∈ S j, Real.exp (H σ)) ≤ Real.exp (M+N*Real.log 2) := by
    have hp : 0<∑ σ ∈ S j, Real.exp (H σ) :=
      Finset.sum_pos (fun σ _ => Real.exp_pos _) (hS j hj)
    have he := Real.exp_le_exp.mpr (show Real.log (∑ σ ∈ S j, Real.exp (H σ)) ≤
      M+N*Real.log 2 by have := hM j hj; unfold restrictedSpinLog at this; linarith)
    rwa [Real.exp_log hp] at he
  have hb : (0:ℝ)<B.card := Nat.cast_pos.mpr hB.card_pos
  have hu : 0<∑ σ ∈ B.biUnion S, Real.exp (H σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) hU
  have he : (∑ σ ∈ B.biUnion S, Real.exp (H σ)) ≤
      (B.card : ℝ)*Real.exp (M+N*Real.log 2) := by
    apply (sum_biUnion_le_sum_of_nonneg B S (fun σ => Real.exp (H σ))
      (fun _ => (Real.exp_pos _).le)).trans
    simpa using Finset.sum_le_sum hsum
  have hl := Real.log_le_log hu he
  rw [Real.log_mul hb.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  unfold restrictedSpinLog
  linarith

lemma full_pressure_le_finite_cover {N : ℕ} (hN : 0<N) {J : Type*}
    (B : Finset J) (hB : B.Nonempty) (S : J → Finset (Spin N))
    (hS : ∀ j ∈ B, (S j).Nonempty) (f : Spin N → Spin N) (d : ℕ)
    (hf : ∀ σ, f σ ∈ B.biUnion S) (hd : ∀ σ, hammingDist σ (f σ) ≤ d)
    (eig c : Fin N → ℝ) (U : Rotation N) {K C t M : ℝ}
    (hK : 0≤K) (hC : 0≤C) (ht : 0≤t)
    (heig : ∀ i, |eig i|≤K) (hc : ∀ i, |c i|≤C)
    (hM : ∀ j ∈ B, restrictedRotatedPressure (S j) eig U c ≤ M) :
    rotatedPressure eig U c ≤ M+(N:ℝ)⁻¹*(Real.log B.card+
      2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) := by
  classical
  have hU : (B.biUnion S).Nonempty := ⟨f (fun _ => false), hf _⟩
  have hb := restricted_spin_pressure_map_le Finset.univ (B.biUnion S)
    Finset.univ_nonempty hU f eig c U d hK hC ht heig hc
    (fun σ _ => hf σ) (fun σ _ => hd σ)
  have hm : ∀ j∈B, restrictedSpinLog (S j)
      (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤ N*M := by
    intro j hj
    have h := hM j hj
    unfold restrictedRotatedPressure at h
    exact (inv_mul_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mp h
  have hu := restrictedSpinLog_finite_union_le B hB S hS _ ((N:ℝ)*M) hm
  rw [restrictedSpinLog_univ] at hb
  have hi : (0:ℝ)≤(N:ℝ)⁻¹ := by positivity
  have hb' : logPartition (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤
      N*M+Real.log B.card+(2*K*Real.sqrt ((N:ℝ)*d)+2*C*d)+
        t*d+N*Real.log (1+Real.exp (-t)) := by linarith
  have hh := mul_le_mul_of_nonneg_left hb' hi
  change (N:ℝ)⁻¹*logPartition (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤ _
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPressureFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mean absolute fluctuations for constrained Haar pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma integral_abs_sub_mean_le_sqrt_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  let g := fun x => f x-∫ y, f y ∂μ
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hga : MemLp (fun x => |g x|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  have hv := variance_nonneg (fun x => |g x|) μ
  rw [variance_eq_sub hga] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have he : (∫ x, g x^2 ∂μ)=variance f μ :=
    (variance_eq_integral hf.aemeasurable).symm
  rw [he] at hv
  apply (sq_le_sq₀ (integral_nonneg (fun _ => abs_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (variance_nonneg f μ)]
  linarith

theorem haar_restrictedPressure_mean_fluctuation (hpub : HaarConcentrationInput) :
    ∃ B : ℝ, 0<B ∧ ∀ N, 3≤N →
      ∀ (μ : Measure (SpecialOrthogonal N)), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
      ∀ (S : Finset (Spin N)), S.Nonempty → ∀ (eig c : Fin N → ℝ) (K : ℝ),
      0<K → (∀ i, |eig i|≤K) →
      Integrable (fun U => restrictedRotatedPressure S eig (specialRotation U) c) μ ∧
      (∫ U, |restrictedRotatedPressure S eig (specialRotation U) c-
        ∫ V, restrictedRotatedPressure S eig (specialRotation V) c ∂μ| ∂μ) ≤
        Real.sqrt (B*K^2/N) := by
  obtain ⟨B,hB,hv⟩ := haar_frobeniusLipschitz_variance hpub
  refine ⟨B,hB,?_⟩
  intro N hN μ hμ hμinv S hS eig c K hK heig
  have : IsProbabilityMeasure μ := hμ
  let f := fun U => restrictedRotatedPressure S eig (specialRotation U) c
  have hm : Measurable f := measurable_restrictedRotatedPressure S eig c
  have hLip : ∀ U V, |f U-f V| ≤ K*frobeniusDistance U V :=
    fun U V => abs_restrictedRotatedPressure_sub_rotation_le (by omega) S hS eig U V c K hK.le heig
  have hf := haar_frobeniusLipschitz_memLp_two hpub N hN μ hμinv f hm K hK hLip
  exact ⟨hf.integrable (by norm_num), (integral_abs_sub_mean_le_sqrt_variance μ f hf).trans
    (Real.sqrt_le_sqrt (hv N hN μ hμ hμinv f hm K hK hLip))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinFiniteCoverMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar fluctuations allow a fixed finite spin cover to be used inside
the expectation of the full pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

theorem haar_finite_cover_mean_pressure_upper (hpub : HaarConcentrationInput) :
    ∃ B : ℝ, 0<B ∧ ∀ N, 3≤N →
    ∀ (μ : Measure (SpecialOrthogonal N)), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ (J : Type*) (Q : Finset J), Q.Nonempty → ∀ S : J → Finset (Spin N),
    (∀ j∈Q, (S j).Nonempty) → ∀ (f : Spin N → Spin N) (d : ℕ),
    (∀ σ, f σ∈Q.biUnion S) → (∀ σ, hammingDist σ (f σ)≤d) →
    ∀ (eig c : Fin N → ℝ) (K C t V : ℝ), 0<K → 0≤C → 0≤t →
    (∀ i, |eig i|≤K) → (∀ i, |c i|≤C) →
    (∀ j∈Q, (∫ U, restrictedRotatedPressure (S j) eig (specialRotation U) c ∂μ)≤V) →
    (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) ≤
      V+Q.card*Real.sqrt (B*K^2/N)+(N:ℝ)⁻¹*(Real.log Q.card+
        2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) := by
  obtain ⟨B,hB,hfluc⟩ := haar_restrictedPressure_mean_fluctuation hpub
  refine ⟨B,hB,?_⟩
  intro N hN μ hμ hμinv J Q hQ S hS f d hf hd eig c K C t V hK hC ht heig hc hmean
  classical
  have : IsProbabilityMeasure μ := hμ
  let F := fun j U => restrictedRotatedPressure (S j) eig (specialRotation U) c
  let D := fun U => ∑ j∈Q, |F j U-∫ V, F j V ∂μ|
  have hFi j (hj : j∈Q) : Integrable (F j) μ :=
    (hfluc N hN μ hμ hμinv (S j) (hS j hj) eig c K hK heig).1
  have hDi : Integrable D μ := by
    exact integrable_finsetSum _ (fun j hj => ((hFi j hj).sub (integrable_const _)).abs)
  have hD : (∫ U, D U ∂μ)≤Q.card*Real.sqrt (B*K^2/N) := by
    change (∫ U, ∑ j∈Q, |F j U-∫ V, F j V ∂μ| ∂μ)≤_
    rw [integral_finsetSum _ (fun j hj =>
      (show Integrable (fun U => |F j U-∫ V, F j V ∂μ|) μ from
        ((hFi j hj).sub (integrable_const _)).abs))]
    calc
      _ ≤ ∑ _j∈Q, Real.sqrt (B*K^2/N) := Finset.sum_le_sum (fun j hj =>
        (hfluc N hN μ hμ hμinv (S j) (hS j hj) eig c K hK heig).2)
      _ = _ := by simp
  have hi : Integrable (fun U => rotatedPressure eig (specialRotation U) c) μ := by
    simpa only [restrictedRotatedPressure_univ] using
      (hfluc N hN μ hμ hμinv Finset.univ Finset.univ_nonempty eig c K hK heig).1
  let E : ℝ := (N:ℝ)⁻¹*(Real.log Q.card+2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+
    Real.log (1+Real.exp (-t))
  have hp (U : SpecialOrthogonal N) : rotatedPressure eig (specialRotation U) c ≤ V+D U+E := by
    have hm : ∀ j∈Q, restrictedRotatedPressure (S j) eig (specialRotation U) c≤V+D U := by
      intro j hj
      have hb : |F j U-∫ V, F j V ∂μ|≤D U :=
        Finset.single_le_sum (fun a _ => abs_nonneg (F a U-∫ V, F a V ∂μ)) hj
      have ha := le_abs_self (F j U-∫ V, F j V ∂μ)
      have hme := hmean j hj
      change F j U≤V+D U
      linarith
    have hh := full_pressure_le_finite_cover (by omega) Q hQ S hS f d hf hd eig c
      (specialRotation U) hK.le hC ht heig hc hm
    simpa only [E,add_assoc] using hh
  have hh := integral_mono hi (((integrable_const V).add hDi).add (integrable_const E)) hp
  change (∫ U, rotatedPressure eig (specialRotation U) c ∂μ)≤∫ U, V+D U+E ∂μ at hh
  rw [integral_add (f := fun U => V+D U) (g := fun _ => E)
      ((integrable_const V).add hDi) (integrable_const E),
    integral_add (f := fun _ => V) (g := D) (integrable_const V) hDi] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  dsimp only [E] at hh
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinCoverError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the finite-cover error and its dimension limit. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma normalized_spinCover_error {N : ℕ} (hN : 0<N) (d Q : ℕ) (K C t : ℝ) :
    (N:ℝ)⁻¹*(Real.log Q+2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) =
      Real.log Q/(N:ℝ)+2*K*Real.sqrt ((d:ℝ)/N)+(2*C+t)*((d:ℝ)/N)+Real.log (1+Real.exp (-t)) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have he : (N:ℝ)*d=(N:ℝ)^2*((d:ℝ)/N) := by field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hnp]
  field_simp
  ring

lemma spinCover_error_tendsto (N d : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (hNlim : Tendsto N atTop atTop) (Q : ℕ) (B K C t δ : ℝ)
    (hd : Tendsto (fun k => (d k:ℝ)/(N k:ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun k => Q*Real.sqrt (B*K^2/(N k:ℝ))+
      (N k:ℝ)⁻¹*(Real.log Q+2*K*Real.sqrt ((N k:ℝ)*d k)+2*C*d k+t*d k)+
        Real.log (1+Real.exp (-t))) atTop
      (𝓝 (2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)))) := by
  have hn : Tendsto (fun k => (N k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNlim
  have hsq : Tendsto (fun k => Q*Real.sqrt (B*K^2/(N k:ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp (tendsto_const_nhds.div_atTop hn)).const_mul (Q:ℝ)
  have hlog : Tendsto (fun k => Real.log Q/(N k:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have he := ((hsq.add hlog).add ((Real.continuous_sqrt.tendsto δ |>.comp hd).const_mul (2*K))).add
    (hd.const_mul (2*C+t))
  have hh := he.add_const (Real.log (1+Real.exp (-t)))
  simp only [zero_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext k
  dsimp only [Function.comp_apply]
  linarith [normalized_spinCover_error (hN k) (d k) Q K C t]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinCoverParameters
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric and fiber-count costs of a fine spin cover can both be made small. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma exists_small_spinCover_error (K C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ t : ℝ, 0<δ ∧ 0≤t ∧
      2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t))<ε := by
  have he : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun n : ℕ => Real.log (1+Real.exp (-(n:ℝ)))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => 1+Real.exp (-(n:ℝ))) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add he
    simpa only [Function.comp_def,Real.log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hh
  obtain ⟨n,hn⟩ := (hl.eventually (Iio_mem_nhds (half_pos hε))).exists
  have hd := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hf : Tendsto (fun j : ℕ => 2*K*Real.sqrt (1/(j+1:ℝ))+
      (2*C+(n:ℝ))*(1/(j+1:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul (2*K)).add
      (hd.const_mul (2*C+(n:ℝ)))
  obtain ⟨j,hj⟩ := (hf.eventually (Iio_mem_nhds (half_pos hε))).exists
  exact ⟨1/(j+1:ℝ),(n:ℝ),by positivity,Nat.cast_nonneg n,by linarith⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupFieldPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field contribution on a prescribed group slice is deterministic. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma restrictedRotatedPressure_group_field {N : ℕ} (hN : 0<N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (count : A → ℕ)
    (hc : ∀ a, count a ≤ spinGroupSize group a)
    (γ mag b : A → ℝ)
    (hg : ∀ a, (spinGroupSize group a : ℝ)=N*γ a)
    (hm : ∀ a, (count a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (eig : Fin N → ℝ) (U : Rotation N) :
    restrictedRotatedPressure (spinGroupSlice group count) eig U (fun i => b (group i)) =
      restrictedRotatedPressure (spinGroupSlice group count) eig U (fun _ => 0)+
        ∑ a, γ a*b a*mag a := by
  have hS := spinGroupSlice_nonempty group count hc
  have hM := spinGroupFieldConstant_magnetization group count b γ mag hg hm
  have hlog : restrictedSpinLog (spinGroupSlice group count)
      (fun σ => rotatedEnergy eig U σ+fieldEnergy (fun i => b (group i)) σ) =
      restrictedSpinLog (spinGroupSlice group count) (fun σ => rotatedEnergy eig U σ)+
        N*(∑ a, γ a*b a*mag a) := by
    rw [← restrictedSpinLog_add_const _ hS]
    unfold restrictedSpinLog
    congr 2
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [fieldEnergy_on_group_slice group count b hσ, hM]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold restrictedRotatedPressure
  rw [hlog]
  simp only [fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  field_simp

lemma mean_restrictedRotatedPressure_group_field {N : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (count : A → ℕ)
    (hc : ∀ a, count a ≤ spinGroupSize group a)
    (γ mag b : A → ℝ)
    (hg : ∀ a, (spinGroupSize group a : ℝ)=N*γ a)
    (hm : ∀ a, (count a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (eig : Fin N → ℝ)
    (hi : Integrable (fun U : SpecialOrthogonal N =>
      restrictedRotatedPressure (spinGroupSlice group count) eig (specialRotation U) (fun _ => 0)) μ) :
    (∫ U, restrictedRotatedPressure (spinGroupSlice group count) eig
      (specialRotation U) (fun i => b (group i)) ∂μ) =
      (∫ U, restrictedRotatedPressure (spinGroupSlice group count) eig
        (specialRotation U) (fun _ => 0) ∂μ)+(∑ a, γ a*b a*mag a) := by
  simp_rw [restrictedRotatedPressure_group_field hN group count hc γ mag b hg hm]
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_ConstrainedBlockMagneticEstimate
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite constrained-block comparison with the actual scalar magnetic
functional. Every error term is independent of the cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma sum_sites_group {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (f : A → ℝ) :
    (∑ i, f (group i)) = ∑ a, spinGroupSize group a * f a := by
  rw [← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => group i = a), f a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp [spinGroupSize]

lemma spinGroupFieldConstant_of_means {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (m bias : A → ℝ)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2)) :
    spinGroupFieldConstant group k bias = ∑ i, bias (group i) * m (group i) := by
  rw [sum_sites_group group (fun a => bias a * m a)]
  unfold spinGroupFieldConstant
  apply Finset.sum_congr rfl
  intro a _
  rw [hc a]
  ring

theorem biasedConstrainedBlockValue_gap {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    0 ≤ biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b ∧
      biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b ≤
        (N : ℝ)⁻¹ * (∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
          ∂fieldCanonicalVectorLaw N h b) := by
  have hF := restrictedFieldRecursion_biased_root_integrable hN Finset.univ Finset.univ_nonempty h b
  have hS' := restrictedFieldRecursion_biased_root_integrable hN S hS h b
  have he : biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b =
      (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut)
        (fieldStepVariance h) z - restrictedFieldRecursion S h.depth (chainExponent h.cut)
        (fieldStepVariance h) z
        ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) := by
    rw [integral_sub hF hS']
    unfold biasedConstrainedBlockValue
    ring
  rw [he]
  constructor
  · apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro z
    apply sub_nonneg.mpr
    exact restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
      (Finset.subset_univ _) _ _ _
      (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1) z
  · exact mul_le_mul_of_nonneg_left (restrictedFieldRecursion_root_loss hN S hS h b) (by positivity)

lemma magneticBlockGap_eq_biasedGap {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2)) (h : FieldStep) :
    (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h =
      biasedConstrainedBlockValue Finset.univ h (fun i => magneticBias h (m (group i))) -
        biasedConstrainedBlockValue (spinGroupSlice group k) h (fun i => magneticBias h (m (group i))) := by
  rw [biasedConstrainedBlockValue_univ hN,
    biasedConstrainedBlockValue_group hN group k hk (fun a => magneticBias h (m a)),
    spinGroupFieldConstant_of_means group k m (fun a => magneticBias h (m a)) hc]
  simp_rw [constrainedFieldValue_magneticBias h (hm _)]
  rw [Finset.sum_sub_distrib]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSliceFieldBound
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact magnetization-slice field bound for the zero-temperature
boundary of the magnetic contact comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma constrainedBlockValue_group_le {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (mag γ : A → ℝ) (hmag : ∀ a, |mag a| < 1)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=N*γ a) (h : FieldStep) :
    constrainedBlockValue (spinGroupSlice group k) h ≤ magneticGroupValue γ mag h := by
  have hg := (biasedConstrainedBlockValue_gap hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun i => magneticBias h (mag (group i)))).1
  rw [← magneticBlockGap_eq_biasedGap hN group k hk mag hmag hc] at hg
  have he : (N : ℝ)⁻¹ * ∑ i, constrainedFieldValue h (mag (group i)) = magneticGroupValue γ mag h := by
    rw [sum_sites_group group (fun a => constrainedFieldValue h (mag a))]
    simp only [hcount, magneticGroupValue]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

  rw [he] at hg
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupEntropyLimit
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded-height entropy control for attainable groups whose proportions
and interior magnetizations converge. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem magnetic_group_entropy_limit {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγ : Tendsto γs atTop (𝓝 γ)) (hm : Tendsto mags atTop (𝓝 mag))
    {r : ℝ} (hr : r<1) (hmag : ∀ a, |mag a| ≤ r)
    (hmags : ∀ᶠ k in atTop, ∀ a, |mags k a| ≤ r)
    (hγs : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a)
    (hms : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (p : OverlapPath) (S : ℝ) (hS : magneticEntropyFunctional γ mag p ≤ (S : EReal))
    {n : ℕ} (cut : Fin (n+2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1) :
    ∀ H ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      ∀ (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i), (∑ i, a i) ≤ H →
        constrainedBlockValue (spinGroupSlice (group k) (count k)) (contactFieldStep cut hc hfirst hlast a ha)+
          fieldPairing p (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S+ε := by
  intro H ε hε
  have he := magneticGroupValue_parameters_uniform γs mags γ mag hγ hm hr hmag hmags H ε hε
  filter_upwards [he,hmags] with k hk hkm a ha hcap
  let step := contactFieldStep cut hc hfirst hlast a ha
  have hheight : step.height (Fin.last step.depth) ≤ H := by
    change finiteFieldPath a n ≤ H
    rw [finiteFieldPath_last]
    exact hcap
  have hv := hk step hheight
  have hb := constrainedBlockValue_group_le (hN k) (group k) (count k) (hcount k)
    (mags k) (γs k) (fun x => (hkm x).trans_lt hr) (hms k) (hγs k) step
  have hs' : magneticGroupValue γ mag step+fieldPairing p step/2 ≤ S := by
    apply EReal.coe_le_coe_iff.mp
    exact (le_iSup (fun h : FieldStep =>
      ((magneticGroupValue γ mag h+fieldPairing p h/2 : ℝ) : EReal)) step).trans hS
  change constrainedBlockValue (spinGroupSlice (group k) (count k)) step+fieldPairing p step/2 ≤ S+ε
  have hd := (le_abs_self _).trans hv.le
  linarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTrialApproximation
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower finite-grid trials preserve the magnetic entropy bound and
approximate the finite-spectrum magnetic variational infimum. -/
noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma magneticEntropyFunctional_mono {A : Type*} [Fintype A]
    (γ mag : A → ℝ) {p q : OverlapPath} (hpq : p.val ≤ᵐ[pathMeasure] q.val) :
    magneticEntropyFunctional γ mag p ≤ magneticEntropyFunctional γ mag q := by
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe_iff.mpr
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae (integrable_path_mul_field p h) (integrable_path_mul_field q h)
  filter_upwards [hpq] with s hs
  exact mul_le_mul_of_nonneg_right hs (fieldFunction_nonneg h s)

lemma lowerGridPath_magneticEntropy_le {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (p : OverlapPath) (n : ℕ) :
    magneticEntropyFunctional γ mag (lowerGridPath p n) ≤ magneticEntropyFunctional γ mag p :=
  magneticEntropyFunctional_mono γ mag (lowerGridPath_le p n)

theorem exists_finiteMagneticEntropy_trial {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a| ≤ 1) {ε : ℝ} (hε : 0<ε) :
    ∃ p : OverlapPath, ∃ S : ℝ, magneticEntropyFunctional γ mag p=(S : EReal) ∧
      S+spectralFunctional (finiteR ρ eig hρ hsum) p <
        (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε := by
  have hf := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum hmag
  have hlt : magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag <
      ((magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε : ℝ) := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    exact_mod_cast (show (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal <
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε by linarith)
  obtain ⟨p,hp⟩ := iInf_lt_iff.mp hlt
  have htop : magneticEntropyFunctional γ mag p ≠ ⊤ := by
    intro he
    simp only [he,EReal.top_add_coe,not_top_lt] at hp
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
  refine ⟨p,(magneticEntropyFunctional γ mag p).toReal,(EReal.coe_toReal htop hbot).symm,?_⟩
  rw [← EReal.coe_toReal htop hbot,← EReal.coe_add] at hp
  exact_mod_cast hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticConvergingUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Manuscript Proposition up:bound, in the equivalent eventual-epsilon
form against every trial of finite entropy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticPressure_converging_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγs : Tendsto γs atTop (𝓝 γ)) (hmags : Tendsto mags atTop (𝓝 mag))
    (hmag : ∀ a, |mag a|<1)
    (hc : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (hgroup : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a)
    (p : OverlapPath) (S : ℝ) (hS : magneticEntropyFunctional γ mag p ≤ (S : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (spinGroupSlice (group k) (count k)) (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hgrid := lowerGridPath_spectral_tendsto ρ lam hρpos hρsum p
  obtain ⟨n, hn⟩ := (hgrid.eventually (gt_mem_nhds
    (show spectralFunctional (finiteR ρ lam hρpos hρsum) p <
      spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε / 2 by linarith))).exists
  obtain ⟨r, hr, hmr, hmkr⟩ := exists_uniform_magnetization_radius mags mag hmags hmag
  have hup := finiteSpectrum_restrictedPressure_entropy_upper hhaar hgauss N hN hNlim m n
    μ hμinv (fun k => spinGroupSlice (group k) (count k))
    (fun k => spinGroupSlice_nonempty (group k) (count k) (hcount k)) eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (lowerGridPath p n)
    (fun i => (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)))
    (lowerGridPath_on_cell p n) (1 / (n + 1 : ℕ)) (by positivity)
    (ae_of_all _ (lowerGridPath_below_one p n)) S
    (magnetic_group_entropy_limit N (fun k => by have := hN k; omega)
      group count hcount γs mags γ mag hγs hmags hr hmr hmkr hgroup hc
      (lowerGridPath p n) S ((lowerGridPath_magneticEntropy_le γ mag p n).trans hS)
      (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)) (ε / 2) hhalf
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticConvergingVariationalUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticPressure_converging_variational_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγs : Tendsto γs atTop (𝓝 γ)) (hmags : Tendsto mags atTop (𝓝 mag))
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1)
    (hc : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (hgroup : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (spinGroupSlice (group k) (count k)) (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      (magneticVariationalFunctional (finiteR ρ lam hρpos hρsum) γ mag).toReal + ε := by
  intro ε hε
  obtain ⟨p, S, hS, hp⟩ := exists_finiteMagneticEntropy_trial
    ρ lam hρpos hρsum γ mag hγ hγsum (fun a => (hmag a).le) (half_pos hε)
  have hup := finiteSpectrum_magneticPressure_converging_upper hhaar hgauss N hN hNlim m μ hμinv
    eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ group count hcount γs mags γ mag hγs hmags hmag hc hgroup p S hS.le (ε / 2) (half_pos hε)
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticConvergingFieldUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticFieldPressure_converging_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγs : Tendsto γs atTop (𝓝 γ)) (hmags : Tendsto mags atTop (𝓝 mag))
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1)
    (hc : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (hgroup : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a) (b : A → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (spinGroupSlice (group k) (count k)) (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
      (magneticVariationalFunctional (finiteR ρ lam hρpos hρsum) γ mag).toReal +
        (∑ a, γ a*b a*mag a) + ε := by
  intro ε hε
  obtain ⟨B,hB,hfluc⟩ := haar_restrictedPressure_mean_fluctuation hhaar
  have hf : Tendsto (fun k => ∑ a, γs k a*b a*mags k a) atTop
      (𝓝 (∑ a, γ a*b a*mag a)) := by
    apply tendsto_finsetSum
    intro a _
    exact (((tendsto_pi_nhds.mp hγs) a).mul_const (b a)).mul ((tendsto_pi_nhds.mp hmags) a)
  have hup := finiteSpectrum_magneticPressure_converging_variational_upper hhaar hgauss
    N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    group count hcount γs mags γ mag hγs hmags hγ hγsum hmag hc hgroup (ε/2) (half_pos hε)
  filter_upwards [hup, hf.eventually (Iio_mem_nhds (show (∑ a, γ a*b a*mag a)<
    (∑ a, γ a*b a*mag a)+ε/2 by linarith))] with k hk hfk
  rw [mean_restrictedRotatedPressure_group_field (by have := hN k; omega) (μ k)
    (group k) (count k) (hcount k) (γs k) (mags k) b (hgroup k) (hc k) (eig k)
    (hfluc (N k) (hN k) (μ k) inferInstance (hμinv k) _
      (spinGroupSlice_nonempty (group k) (count k) (hcount k)) (eig k) (fun _ => 0) K hK (heig k)).1]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from attainable block proportions to the weighted
magnetic functional and overlap path. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma sum_grouped_sites {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (f : A → ℝ) :
    (∑ j, f (group j)) = ∑ a, (spinGroupSize group a : ℝ) * f a := by
  rw [← Finset.sum_fiberwise Finset.univ group]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ _j ∈ Finset.univ.filter (fun j => group j = a), f a := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, spinGroupSize]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRationalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every bounded magnetization profile is close to one of finitely many
rational interior profiles, including profiles at the boundary. -/
noncomputable section
open Set
open scoped Topology
namespace InvariantIsing

lemma exists_interior_rat_close {x δ : ℝ} (hx : |x|≤1) (hδ : 0<δ) :
    ∃ q : ℚ, |(q:ℝ)|<1 ∧ |x-(q:ℝ)|<δ := by
  have hl : max (-1:ℝ) (x-δ) < min 1 (x+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]
  obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hl
  refine ⟨q, abs_lt.mpr ⟨(le_max_left _ _).trans_lt hq₁,
    hq₂.trans_le (min_le_left _ _)⟩,?_⟩
  apply abs_lt.mpr
  constructor
  · have := hq₂.trans_le (min_le_right _ _)
    linarith
  · have := (le_max_right _ _).trans_lt hq₁
    linarith

lemma finite_rational_magnetization_cover {A : Type*} [Fintype A]
    {δ : ℝ} (hδ : 0<δ) :
    ∃ Q : Finset (RationalMagnetization A), Q.Nonempty ∧
      ∀ x : A → ℝ, (∀ a, |x a|≤1) →
        ∃ q∈Q, ∀ a, |x a-(q.val a:ℝ)|<δ := by
  classical
  let K : Set (A → ℝ) := Set.pi Set.univ (fun _ => Icc (-1:ℝ) 1)
  have hK : IsCompact K := by
    simpa only [K, Set.pi, Set.mem_univ, forall_const] using
      (isCompact_pi_infinite (s := fun _ : A => Icc (-1:ℝ) 1) (fun _ => isCompact_Icc))
  let U : RationalMagnetization A → Set (A → ℝ) :=
    fun q => {x | ∀ a, |x a-(q.val a:ℝ)|<δ}
  have ho (q : RationalMagnetization A) : IsOpen (U q) := by
    change IsOpen {x : A → ℝ | ∀ a, |x a-(q.val a:ℝ)|<δ}
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun a => isOpen_lt ((continuous_apply a).sub continuous_const).abs continuous_const)
  have hcover : K ⊆ ⋃ q, U q := by
    intro x hx
    have hx' a : |x a|≤1 := abs_le.mpr (hx a (mem_univ a))
    choose q hq hd using fun a => exists_interior_rat_close (hx' a) hδ
    exact mem_iUnion.mpr ⟨(⟨q,hq⟩ : RationalMagnetization A),hd⟩
  obtain ⟨Q,hQ⟩ := hK.elim_finite_subcover U ho hcover
  have hzero : (fun _ : A => (0:ℝ))∈K := by intro a _; constructor <;> norm_num
  have hne : Q.Nonempty := by
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hQ hzero)
    obtain ⟨hq,_⟩ := mem_iUnion.mp hq
    exact ⟨q,hq⟩
  refine ⟨Q,hne,?_⟩
  intro x hx
  have hxK : x∈K := by intro a _; exact abs_le.mp (hx a)
  obtain ⟨q,hq⟩ := mem_iUnion.mp (hQ hxK)
  obtain ⟨hq,hxq⟩ := mem_iUnion.mp hq
  exact ⟨q,hq,hxq⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGridProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational net of magnetizations gives an actual spin projection onto
a finite union of attainable group slices. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma spinGroupCount_le_size {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (σ : Spin N) (a : A) :
    spinGroupCount group σ a ≤ spinGroupSize group a := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.1⟩

lemma spinGroupSize_sum {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) : (∑ a, (spinGroupSize group a:ℝ))=N := by
  have h := sum_grouped_sites group (fun _ => (1:ℝ))
  simpa only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using h.symm

theorem magnetic_grid_projection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) {δ : ℝ} (hδ : 0<δ)
    (Q : Finset (RationalMagnetization A))
    (hQ : ∀ x : A → ℝ, (∀ a, |x a|≤1) → ∃ q∈Q, ∀ a, |x a-(q.val a:ℝ)|<δ) :
    ∃ f : Spin N → Spin N,
      (∀ σ, f σ∈Q.biUnion (fun q => spinGroupSlice group
        (fun a => magneticRoundedCount (spinGroupSize group a) (q.val a:ℝ)))) ∧
      ∀ σ, hammingDist σ (f σ)≤⌈δ*N+Fintype.card A⌉₊ := by
  classical
  let x := fun σ a => spinCountMagnetization (spinGroupSize group a) (spinGroupCount group σ a)
  choose q hq hclose using fun σ => hQ (x σ)
    (fun a => spinCountMagnetization_bounds (spinGroupCount_le_size group σ a))
  let cnt := fun q : RationalMagnetization A => fun a =>
    magneticRoundedCount (spinGroupSize group a) (q.val a:ℝ)
  have hc q a : cnt q a≤ spinGroupSize group a := magneticRoundedCount_le _ (q.property a).le
  let f := fun σ => spinGroupProjection group (cnt (q σ)) (hc (q σ)) σ
  refine ⟨f,fun σ => Finset.mem_biUnion.mpr ⟨q σ,hq σ,spinGroupProjection_mem _ _ _ _⟩,?_⟩
  intro σ
  have hb : (hammingDist σ (f σ):ℝ) ≤ δ*N+Fintype.card A := by
    rw [show f σ=spinGroupProjection group (cnt (q σ)) (hc (q σ)) σ from rfl,
      spinGroupProjection_distance_real]
    calc
      _ ≤ ∑ a, ((spinGroupSize group a:ℝ)*δ/2+1) := by
        apply Finset.sum_le_sum
        intro a _
        exact rounded_count_distance (spinGroupCount_le_size group σ a) ((q σ).property a).le
          (hclose σ a).le
      _ = (N:ℝ)*δ/2+Fintype.card A := by
        rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul,spinGroupSize_sum]
        simp
      _ ≤ _ := by nlinarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  exact_mod_cast hb.trans (Nat.le_ceil (δ*N+Fintype.card A))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCoverDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized radius of the magnetic grid projection converges to its mesh. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma magnetic_cover_distance_tendsto (N : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (hNlim : Tendsto N atTop atTop) (A : ℕ) {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun k => (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)) atTop (𝓝 δ) := by
  have he k : 0≤(⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ ∧
      (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ≤((A:ℝ)+1)/(N k:ℝ) := by
    have hp : (0:ℝ)<N k := Nat.cast_pos.mpr (hN k)
    have hx : 0≤δ*N k+A := by positivity
    have hl := Nat.le_ceil (δ*N k+A)
    have hu := Nat.ceil_lt_add_one hx
    constructor
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ hp).mpr
      linarith [(Nat.cast_nonneg A : (0:ℝ)≤A)]
    · have hdiff : (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ=
          ((⌈δ*N k+A⌉₊:ℝ)-δ*N k)/(N k:ℝ) := by field_simp
      rw [hdiff]
      exact div_le_div_of_nonneg_right (by linarith) hp.le
  have hz := squeeze_zero (fun k => (he k).1) (fun k => (he k).2)
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNlim))
  simpa only [sub_add_cancel,zero_add] using hz.add_const δ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each rational magnetic trial lies below the finite-field variational supremum. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma finiteMagnetic_trial_le {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0<ρ a) (hsum : ∑ a, ρ a=1)
    (γ b : A → ℝ) (hγ : ∀ a, 0≤γ a) (hγsum : ∑ a, γ a=1)
    (q : RationalMagnetization A) :
    (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ (fun a => (q.val a:ℝ))).toReal+
      (∑ a, γ a*b a*(q.val a:ℝ)) ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal := by
  have hm := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
    (fun a => (q.val a:ℝ)) hγ hγsum (fun a => (q.property a).le)
  have hv := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot (finiteR ρ eig hρ hsum) γ b hγ hγsum hv.1 hv.2
  have hi := le_iSup (fun q : RationalMagnetization A =>
    ((∑ a, γ a*b a*(q.val a:ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ (fun a => (q.val a:ℝ))) q
  change _≤finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b at hi
  rw [←EReal.coe_toReal hm.1 hm.2,←EReal.coe_toReal hf.1 hf.2,←EReal.coe_add] at hi
  have := EReal.coe_le_coe_iff.mp hi
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed interior targets round to converging attainable group profiles. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma group_size_tendsto_atTop (N G : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {γ : ℝ} (hγ : 0<γ)
    (hG : Tendsto (fun k => (G k:ℝ)/(N k:ℝ)) atTop (𝓝 γ)) :
    Tendsto G atTop atTop := by
  have hpos : ∀ᶠ k in atTop, 0<N k := hN.eventually (eventually_gt_atTop 0)
  have hg : ∀ᶠ k in atTop, γ/2<(G k:ℝ)/(N k:ℝ) :=
    hG.eventually (Ioi_mem_nhds (by linarith : γ/2<γ))
  apply tendsto_atTop.2
  intro B
  have hn : ∀ᶠ k in atTop, (B:ℝ)*2/γ < (N k:ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hN).eventually (eventually_gt_atTop _)
  filter_upwards [hpos,hg,hn] with k hk hg hn
  have hkn : (0:ℝ)<N k := Nat.cast_pos.mpr hk
  have hg' := (lt_div_iff₀ hkn).mp hg
  have hn' := (div_lt_iff₀ hγ).mp hn
  have hB : (B:ℝ)<G k := by nlinarith
  exact Nat.le_of_lt (Nat.cast_lt.mp hB)

lemma rounded_group_magnetizations_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (group : ∀ k, Fin (N k) → A)
    (γ mag : A → ℝ) (hγ : ∀ a, 0<γ a) (hmag : ∀ a, |mag a|≤1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun k a => magneticRoundedValue (spinGroupSize (group k) a) (mag a)) atTop (𝓝 mag) := by
  apply tendsto_pi_nhds.mpr
  intro a
  exact magneticRoundedValue_tendsto (fun k => spinGroupSize (group k) a)
    (group_size_tendsto_atTop N _ hN (hγ a) ((tendsto_pi_nhds.mp hgroup) a)) (hmag a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRoundedFieldUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticRoundedFieldPressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A)
    (γ b : A → ℝ) (hγ : ∀ a, 0<γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ))
    (q : RationalMagnetization A) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      (∫ U, restrictedRotatedPressure (spinGroupSlice (group k)
        (fun a => magneticRoundedCount (spinGroupSize (group k) a) (q.val a:ℝ)))
        (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
        (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal+ε := by
  let mag := fun a => (q.val a:ℝ)
  let γs := fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)
  let mags := fun k a => magneticRoundedValue (spinGroupSize (group k) a) (mag a)
  let cnt := fun k a => magneticRoundedCount (spinGroupSize (group k) a) (mag a)
  have hm : Tendsto mags atTop (𝓝 mag) := rounded_group_magnetizations_tendsto
    N hNlim group γ mag hγ (fun a => (q.property a).le) hgroup
  have hg k a : (spinGroupSize (group k) a:ℝ)=N k*γs k a := by
    dsimp only [γs]
    have hn : (N k:ℝ)≠0 := Nat.cast_ne_zero.mpr (by have := hN k; omega)
    field_simp
  have hu := finiteSpectrum_magneticFieldPressure_converging_upper hhaar hgauss
    N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    group cnt (fun k a => magneticRoundedCount_le _ (q.property a).le)
    γs mags γ mag hgroup hm (fun a => (hγ a).le) hγsum q.property
    (fun k a => magneticRoundedCount_value _ (q.property a).le) hg b
  intro ε hε
  filter_upwards [hu ε hε] with k hk
  have hb := finiteMagnetic_trial_le ρ lam hρpos hρsum γ b (fun a => (hγ a).le) hγsum q
  dsimp only [mag] at hk
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFullFieldUpper
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityOrthogonal_measurableMul _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableInv _root_.OAI.InvariantIsing.cavitySpecialOrthogonal_measurableMul _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_fullField_pressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A)
    (γ b : A → ℝ) (hγ : ∀ a, 0<γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ))
    : ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      (∫ U, rotatedPressure (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
        (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal+ε := by
  classical
  intro ε hε
  let V := (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal
  let C := ∑ a, |b a|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤C := Finset.single_le_sum (f := fun a => |b a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  obtain ⟨B,hB,hcoverBound⟩ := haar_finite_cover_mean_pressure_upper hhaar
  obtain ⟨δ,t,hδ,ht,hsmall⟩ := exists_small_spinCover_error K C (show 0<ε/3 by positivity)
  obtain ⟨Q,hQ,hnet⟩ := finite_rational_magnetization_cover (A := A) hδ
  let S := fun k (q : RationalMagnetization A) => spinGroupSlice (group k)
    (fun a => magneticRoundedCount (spinGroupSize (group k) a) (q.val a:ℝ))
  have hS k q : (S k q).Nonempty := spinGroupSlice_nonempty (group k) _
    (fun a => magneticRoundedCount_le _ (q.property a).le)
  let d := fun k => ⌈δ*N k+Fintype.card A⌉₊
  have hproj k := magnetic_grid_projection (group k) hδ Q hnet
  choose f hf hd using hproj
  have hmeans : ∀ᶠ k in atTop, ∀ q∈Q,
      (∫ U, restrictedRotatedPressure (S k q) (eig k) (specialRotation U)
        (fun i => b (group k i)) ∂μ k)≤V+ε/3 := by
    have hh (q : Q) := finiteSpectrum_magneticRoundedFieldPressure_upper hhaar hgauss
      N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
      group γ b hγ hγsum hgroup q.val (ε/3) (by positivity)
    have hh' := (Filter.eventually_all).mpr hh
    filter_upwards [hh'] with k hk q hq
    exact hk ⟨q,hq⟩
  have herr := spinCover_error_tendsto N d (fun k => by have := hN k; omega)
    hNlim Q.card B K C t δ
    (magnetic_cover_distance_tendsto N (fun k => by have := hN k; omega) hNlim (Fintype.card A) hδ)
  have hevent := herr.eventually (Iio_mem_nhds (show
    2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)) <
      (2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)))+ε/3 by linarith))
  filter_upwards [hmeans,hevent] with k hk he
  have hup := hcoverBound (N k) (hN k) (μ k) inferInstance (hμinv k)
    (RationalMagnetization A) Q hQ (S k) (fun q _ => hS k q) (f k) (d k) (hf k) (hd k)
    (eig k) (fun i => b (group k i)) K C t (V+ε/3) hK hC ht (heig k)
    (fun i => hb (group k i)) hk
  change (∫ U, rotatedPressure (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k)≤V+ε
  dsimp only [d] at he hup
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPhysicalFieldUpper
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-field upper bound for physical orthogonal Haar matrices,
with arbitrary finite eigenvalue and field labelings at every dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_physical_field_pressure_upper_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m : ℕ} (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    ∀ ε > 0, ∀ᶠ M in atTop,
      (∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M) ≤
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal+ε := by
  let N := fun k : ℕ => k+3
  have hN k : 0 < N k := by dsimp only [N]; omega
  let ν := fun k => cavityOrientedBaseLaw (hN k) (μ (N k))
  let K := 1+∑ a, |lam a|
  have hK : 0 < K := by dsimp only [K] <;> positivity
  have heig k i : |lam (e (N k) i)|≤K := by
    have hh := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (e (N k) i))
    dsimp only [K]
    linarith
  have hh := finiteSpectrum_fullField_pressure_upper hhaar hgauss N (fun _ => by dsimp only [N]; omega)
    (tendsto_add_atTop_nat 3) m ν
    (fun k => cavityOrientedBaseLaw_leftInvariant _ _) (fun k i => lam (e (N k) i)) K hK heig
    (fun k => cavitySpectralGroup (e (N k))) (fun _ => cavitySpectralGroup_pairwiseDisjoint _)
    (fun _ => cavitySpectralGroup_cover _) lam
    (by intro k a i hi; rw [(Finset.mem_filter.mp hi).2]) ρ hρ hsum
    (he.comp (tendsto_add_atTop_nat 3)) (fun k => g (N k)) γ b hγ hγsum
    (hg.comp (tendsto_add_atTop_nat 3))
  intro ε hε
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hh ε hε)
  apply eventually_atTop.mpr
  refine ⟨J+3,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+3 := ⟨M-3,(Nat.sub_add_cancel (by omega)).symm⟩
  have hx := hJ k (by omega)
  rw [cavity_oriented_pressure] at hx
  exact hx

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.finite_physical_field_pressure_upper_oai.{u_1} := @OAI.InvariantIsing.finite_physical_field_pressure_upper_oai.{u_1}
