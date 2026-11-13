-- Prove2me | solution 1 for OAI.InvariantIsing.magnetic_affine_increment_eventually_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:02:33.785821+00:00
-- url     : https://prove2.me/submissions/11fcf089-4981-448d-b544-26e8c0877106

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
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
import Theorems.Thm_OAI_InvariantIsing_magneticBias_uniform_bound
import Theorems.Thm_OAI_InvariantIsing_magneticBlockPath_l1_tendsto
import Theorems.Thm_OAI_InvariantIsing_magneticCanonical_projection_distance
import Theorems.Thm_OAI_InvariantIsing_magnetic_entropy_trial_eventually_lower
import Theorems.Thm_OAI_InvariantIsing_offset_window_minimum_trial_witness

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapPathCompact
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sequential L1 compactness of bounded monotone overlap paths. The
proof extracts the values on the rationals and discards only the
countable discontinuity set of the resulting monotone path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private lemma rational_le_lowerPath (f : ℚ → Icc (0 : ℝ) 1)
    {q : ℚ} {x : ℝ} (hq : (q : ℝ) < x) : (f q : ℝ) ≤ rationalLowerPath f x :=
  le_csSup (rationalLowerValues_bdd f x) ⟨q, hq, rfl⟩

private lemma rationalLowerPath_tendsto (p : ℕ → OverlapPath)
    (f : ℚ → Icc (0 : ℝ) 1)
    (hf : ∀ q : ℚ, Tendsto (fun n => p n (q : ℝ)) atTop (𝓝 (f q : ℝ)))
    (x : ℝ) (hx : ContinuousAt (rationalLowerPath f) x) :
    Tendsto (fun n => p n x) atTop (𝓝 (rationalLowerPath f x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨y, hy, hay⟩ := (lt_csSup_iff (rationalLowerValues_bdd f x)
      (rationalLowerValues_nonempty f x)).mp ha
    obtain ⟨q, hqx, rfl⟩ := hy
    filter_upwards [(hf q).eventually (Ioi_mem_nhds hay)] with n hn
    exact hn.trans_le ((p n).monotone hqx.le)
  · intro b hb
    have hnear : {y : ℝ | rationalLowerPath f y < b} ∈ 𝓝 x :=
      hx (Iio_mem_nhds hb)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let y := x + ε / 2
    have hxy : x < y := by dsimp [y] <;> linarith
    have hy : rationalLowerPath f y < b := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
      dsimp [y]
      linarith
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
    have hqb : (f q : ℝ) < b := (rational_le_lowerPath f hqy).trans_lt hy
    filter_upwards [(hf q).eventually (Iio_mem_nhds hqb)] with n hn
    exact ((p n).monotone hxq.le).trans_lt hn

/-- Every sequence of overlap quantiles has an L1-convergent subsequence
with another admissible bounded monotone representative. -/
theorem overlapPath_ae_l1_subsequence (p : ℕ → OverlapPath) :
    ∃ q : OverlapPath, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s))) ∧
      Tendsto (fun n => ∫ s, |p (φ n) s - q s| ∂pathMeasure) atTop (𝓝 0) := by
  let f : ℕ → ℚ → Icc (0 : ℝ) 1 := fun n r => ⟨p n r, (p n).nonneg r, (p n).le_one r⟩
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq f
  let q := rationalLowerPath g
  have hr (r : ℚ) : Tendsto (fun n => p (φ n) (r : ℝ)) atTop (𝓝 (g r : ℝ)) :=
    (continuous_subtype_val.tendsto (g r)).comp ((continuous_apply r).tendsto g |>.comp hg)
  have hc : ∀ᵐ s ∂pathMeasure, ContinuousAt q s := by
    let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
    have hz := q.monotone.countable_not_continuousAt.measure_zero (μ := pathMeasure)
    have hae : ∀ᵐ s ∂pathMeasure, s ∉ {x | ¬ContinuousAt q x} := compl_mem_ae_iff.mpr hz
    filter_upwards [hae] with s hs
    exact not_not.mp hs
  have hpoint : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s)) := by
    filter_upwards [hc] with s hs
    exact rationalLowerPath_tendsto (fun n => p (φ n)) g hr s hs
  refine ⟨q, φ, hφ, hpoint, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |p (φ n) s - q s|) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((p (φ n)).measurable.sub q.measurable).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_le.mpr ⟨by linarith [(p (φ n)).nonneg s, q.le_one s],
        by linarith [(p (φ n)).le_one s, q.nonneg s]⟩) (by
      filter_upwards [hpoint] with s hs
      simpa only [sub_self, abs_zero] using (hs.sub_const (q s)).abs)
  simpa only [integral_zero] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiberFactor
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tied overlap levels remain tied in an almost-everywhere limit. A
monotone factor through the overlap is then constructed explicitly;
no invertibility or absence of plateaus is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private lemma cavityFiberValues_bdd (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    BddAbove (cavityFiberValues p B D z) := by
  refine ⟨1, ?_⟩
  rintro y (rfl | ⟨s, _, rfl⟩)
  · norm_num
  · exact B.le_one s

private lemma cavityFiberFactor_mono (p B : OverlapPath) (D : Set ℝ) :
    Monotone (fun z => sSup (cavityFiberValues p B D z)) := by
  intro x y hxy
  apply csSup_le_csSup (cavityFiberValues_bdd p B D y) (insert_nonempty _ _)
  rintro z (rfl | ⟨s, hs, rfl⟩)
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨s, ⟨hs.1, hs.2.trans hxy⟩, rfl⟩

private lemma cavityFiberFactor_bounds (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    0 ≤ sSup (cavityFiberValues p B D z) ∧ sSup (cavityFiberValues p B D z) ≤ 1 := by
  constructor
  · exact le_csSup (cavityFiberValues_bdd p B D z) (mem_insert _ _)
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, _, rfl⟩)
    · norm_num
    · exact B.le_one s

private lemma cavityFiberFactor_eq (p B : OverlapPath) (D : Set ℝ)
    (hD : ∀ x ∈ D, ∀ y ∈ D, p x = p y → B x = B y)
    {x : ℝ} (hx : x ∈ D) : sSup (cavityFiberValues p B D (p x)) = B x := by
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, hs, rfl⟩)
    · exact B.nonneg x
    · rcases le_or_gt s x with h | h
      · exact B.monotone h
      · have he : p s = p x := le_antisymm hs.2 (p.monotone h.le)
        exact (hD s hs.1 x hx he).le
  · exact le_csSup (cavityFiberValues_bdd p B D (p x))
      (mem_insert_of_mem _ ⟨x, ⟨hx, le_rfl⟩, rfl⟩)

/-- An a.e. limit of functions constant on every overlap fiber is still
a measurable function of that overlap, even on positive-mass plateaus. -/
theorem cavity_limit_factors_through_overlap_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ n x, x ∈ D → ∀ y, y ∈ D → p x = p y → Bseq n x = Bseq n y)
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ x ∈ E, ∀ y ∈ E, p x = p y → B x = B y := by
    intro x hx y hy hxy
    have he : (fun n => Bseq n x) = (fun n => Bseq n y) :=
      funext (fun n => htied n x hx.1 y hy.1 hxy)
    exact tendsto_nhds_unique hx.2 (he ▸ hy.2)
  refine ⟨fun z => sSup (cavityFiberValues p B E z),
    cavityFiberFactor_mono p B E, cavityFiberFactor_bounds p B E, ?_⟩
  filter_upwards [hDae, hlim] with s hs hls
  exact (cavityFiberFactor_eq p B E hE ⟨hs, hls⟩).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableTests
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous overlap tests determine a bounded measurable residual
once it is known to be a function of that overlap. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_ae_zero_of_measurable_overlap_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ z, |f z| ≤ 1)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ x, Φ (p x) * f (p x) ∂μ) = 0) :
    ∀ᵐ x ∂μ, f (p x) = 0 := by
  let ν := μ.map p
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hs : Integrable (fun z => f z ^ 2) ν :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hb z) 2).trans_eq (one_pow 2))
  have hsmall (ε : ℝ) (hε : 0 < ε) : (∫ z, f z ^ 2 ∂ν) ≤ ε := by
    obtain ⟨Φ, hΦ, hiΦ⟩ := hi.exists_boundedContinuous_integral_sub_le hε
    have hicross : Integrable (fun z => Φ z * f z) ν := by
      apply Integrable.of_bound (Φ.continuous.measurable.mul hf).aestronglyMeasurable ‖Φ‖
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        exact (mul_le_mul (Φ.norm_coe_le_norm z) (hb z) (abs_nonneg _) (norm_nonneg _)).trans_eq
          (mul_one _)
    have herr : Integrable (fun z => (f z - Φ z) * f z) ν := by
      apply (hi.sub hiΦ).abs.mono'
        (((hf.sub Φ.continuous.measurable).mul hf).aestronglyMeasurable)
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb z)
    have hz : (∫ z, Φ z * f z ∂ν) = 0 := by
      change (∫ z, (Φ * f) z ∂μ.map p) = 0
      rw [integral_map hp.aemeasurable ((Φ.continuous.measurable.mul hf).aestronglyMeasurable)]
      exact htest Φ
    have he : (∫ z, f z ^ 2 ∂ν) = (∫ z, (f z - Φ z) * f z ∂ν) +
        ∫ z, Φ z * f z ∂ν := by
      rw [← integral_add herr hicross]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring
    rw [he, hz, add_zero]
    calc
      _ ≤ ∫ z, |f z - Φ z| ∂ν := integral_mono herr (hi.sub hiΦ).abs (fun z => by
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hb z)))
      _ ≤ ε := by simpa only [Real.norm_eq_abs] using hΦ
  have hzero : (∫ z, f z ^ 2 ∂ν) = 0 := by
    apply le_antisymm _ (integral_nonneg (fun z => sq_nonneg (f z)))
    by_contra hn
    have hpos : 0 < ∫ z, f z ^ 2 ∂ν := lt_of_not_ge hn
    have hh := hsmall ((∫ z, f z ^ 2 ∂ν) / 2) (half_pos hpos)
    linarith
  have hae : ∀ᵐ z ∂ν, f z = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z)) hs).mp hzero] with z hz
    exact sq_eq_zero_iff.mp hz
  exact (ae_map_iff hp.aemeasurable (hf (measurableSet_singleton 0))).mp hae

/-- This is the separation step in cavity self-consistency, including
positive-mass plateaus of the limiting total-overlap path. -/
theorem cavity_overlap_self_consistency (p B : OverlapPath) (g : ℝ → ℝ)
    (hg : Monotone g) (hgb : ∀ z, 0 ≤ g z ∧ g z ≤ 1)
    (hfactor : B.val =ᵐ[pathMeasure] fun s => g (p s))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ s, Φ (p s) * (B s - p s) ∂pathMeasure) = 0) :
    B.val =ᵐ[pathMeasure] p.val := by
  let f := fun z => g z - max 0 (min 1 z)
  have hf : Measurable f := hg.measurable.sub (measurable_const.max (measurable_const.min measurable_id))
  have hb (z : ℝ) : |f z| ≤ 1 := by
    have hc : 0 ≤ max 0 (min 1 z) ∧ max 0 (min 1 z) ≤ 1 := by
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    exact abs_le.mpr ⟨by dsimp [f] <;> linarith [(hgb z).1, hc.2],
      by dsimp [f] <;> linarith [(hgb z).2, hc.1]⟩
  have he (s : ℝ) : max 0 (min 1 (p s)) = p s :=
    (congrArg (max 0) (min_eq_right (p.le_one s))).trans (max_eq_right (p.nonneg s))
  have hz := cavity_ae_zero_of_measurable_overlap_tests pathMeasure p p.measurable f hf hb (by
    intro Φ
    rw [← htest Φ]
    apply integral_congr_ae
    filter_upwards [hfactor] with s hs
    simp only [f, he, hs])
  filter_upwards [hfactor, hz] with s hs hsz
  rw [hs]
  exact sub_eq_zero.mp (by simpa only [f, he] using hsz)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAsymptoticSelfConsistency
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic preservation of plateau values suffices for cavity
self-consistency. Exact ties at every approximation are unnecessary. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_limit_factors_asymptotic_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => Bseq n x - Bseq n y) atTop (𝓝 0))
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ᵐ s ∂pathMeasure, s ∈ E := hDae.and hlim
  have heq : ∀ x, x ∈ E → ∀ y, y ∈ E → p x = p y → B x = B y := by
    intro x hx y hy hxy
    exact sub_eq_zero.mp (tendsto_nhds_unique (hx.2.sub hy.2) (htied x hx.1 y hy.1 hxy))
  exact cavity_limit_factors_through_overlap_on p B (fun _ s => B s) E hE
    (fun _ x hx y hy hxy => heq x hx y hy hxy) (ae_of_all _ fun _ => tendsto_const_nhds)


theorem cavity_self_consistency_asymptotic_l1_on (p : OverlapPath) (B : ℕ → OverlapPath)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => B n x - B n y) atTop (𝓝 0))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg (fun s => abs_nonneg _))
  · intro ε hε
    by_contra hbad
    have hb : ∃ᶠ n in atTop, ε ≤ ∫ s, |B n s - p s| ∂pathMeasure := by
      simpa only [Filter.not_eventually, not_lt] using hbad
    obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hb
    obtain ⟨Q, ψ, hψ, hpoint, hL1⟩ := overlapPath_ae_l1_subsequence (fun n => B (φ n))
    obtain ⟨g, hg, hgb, hfactor⟩ := cavity_limit_factors_asymptotic_on p Q
      (fun n s => B (φ (ψ n)) s) D hDae (fun x hx y hy hxy => (htied x hx y hy hxy).comp
        (hφ.comp hψ).tendsto_atTop) hpoint
    have hQtests (Φ : ℝ →ᵇ ℝ) : (∫ s, Φ (p s) * (Q s - p s) ∂pathMeasure) = 0 := by
      have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
        (F := fun n s => Φ (p s) * (B (φ (ψ n)) s - p s))
        (f := fun s => Φ (p s) * (Q s - p s)) (fun _ => ‖Φ‖)
        (fun n => ((Φ.continuous.measurable.comp p.measurable).mul
          ((B (φ (ψ n))).measurable.sub p.measurable)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_mul]
          have hdiff : |B (φ (ψ n)) s - p s| ≤ 1 := abs_le.mpr
            ⟨by linarith [(B (φ (ψ n))).nonneg s, p.le_one s],
              by linarith [(B (φ (ψ n))).le_one s, p.nonneg s]⟩
          exact (mul_le_mul (Φ.norm_coe_le_norm _) hdiff (abs_nonneg _) (norm_nonneg _)).trans_eq
            (mul_one _)) (by
          filter_upwards [hpoint] with s hs
          exact tendsto_const_nhds.mul (hs.sub_const (p s)))
      exact tendsto_nhds_unique hlim ((htest Φ).comp (hφ.comp hψ).tendsto_atTop)
    have heq := cavity_overlap_self_consistency p Q g hg hgb hfactor hQtests
    have hsame (n : ℕ) : (∫ s, |B (φ (ψ n)) s - Q s| ∂pathMeasure) =
        ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with s hs
      rw [hs]
    have hzero : Tendsto (fun n => ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure) atTop (𝓝 0) := by
      simpa only [hsame] using hL1
    obtain ⟨n, hn⟩ := (hzero.eventually (Iio_mem_nhds hε)).exists
    exact (not_le_of_gt hn) (hφbad (ψ n))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRoundedSelfConsistency
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity identity is initially tested at the rounded overlap.
Passing those tests to the limiting overlap gives the L1 conclusion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_rounding_test_difference (p : OverlapPath)
    (q B : ℕ → OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure) atTop (𝓝 0) := by
  let F := fun n s => Φ (p s) * (B n s - p s) - Φ (q n s) * (B n s - q n s)
  have hΦ (z : ℝ) : |Φ z| ≤ ‖Φ‖ := by
    simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm z
  have hdiff (v w : OverlapPath) (s : ℝ) : |v s - w s| ≤ 1 :=
    abs_le.mpr ⟨by linarith [v.nonneg s, w.le_one s],
      by linarith [v.le_one s, w.nonneg s]⟩
  have hi (v w : OverlapPath) : Integrable (fun s => Φ (v s) * (w s - v s)) pathMeasure := by
    apply Integrable.of_bound ((Φ.continuous.measurable.comp v.measurable).mul
      (w.measurable.sub v.measurable)).aestronglyMeasurable ‖Φ‖
    exact ae_of_all _ fun s => by
      change |Φ (v s) * (w s - v s)| ≤ ‖Φ‖
      rw [abs_mul]
      exact (mul_le_mul (hΦ _) (hdiff w v s)
        (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hbound (n : ℕ) (s : ℝ) : |F n s| ≤
      |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s| := by
    have he : F n s = (Φ (p s) - Φ (q n s)) * (B n s - p s) +
        Φ (q n s) * (q n s - p s) := by dsimp only [F] <;> ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left (hdiff (B n) p s) (abs_nonneg _)).trans_eq (mul_one _))
      (mul_le_mul_of_nonneg_right (hΦ _) (abs_nonneg _))
  have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := F) (f := fun _ => (0 : ℝ)) (fun _ => 3 * ‖Φ‖)
    (fun n => ((hi p (B n)).sub (hi (q n) (B n))).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]
      have ha : |Φ (p s) - Φ (q n s)| ≤ 2 * ‖Φ‖ :=
        (abs_sub _ _).trans (by linarith [hΦ (p s), hΦ (q n s)])
      have hb := mul_le_mul_of_nonneg_left (hdiff (q n) p s) (norm_nonneg Φ)
      exact (hbound n s).trans (by linarith)) (by
      filter_upwards [hq] with s hs
      have hφ := Φ.continuous.continuousAt.tendsto.comp hs
      have hb : Tendsto (fun n => |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s|)
          atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => Φ (p s)) atTop (𝓝 (Φ (p s))) := tendsto_const_nhds
        simpa only [Function.comp_apply, sub_self, abs_zero, mul_zero, zero_add] using
          ((hc.sub hφ).abs.add ((hs.sub_const (p s)).abs.const_mul ‖Φ‖))
      apply squeeze_zero_norm (fun n => ?_) hb
      simpa only [Real.norm_eq_abs] using hbound n s)
  have he (n : ℕ) : (∫ s, F n s ∂pathMeasure) =
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure :=
    integral_sub (hi p (B n)) (hi (q n) (B n))
  simpa only [he, integral_zero] using hlim

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavityRDerivative_le (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {K : ℝ} (_hK : 0 ≤ K)
    (hlam : ∀ a, |lam a| ≤ K) (x : ℝ) :
    cavityRDerivative rho lam hrho hsum x ≤ 4 * K ^ 2 := by
  have hR := finiteR_mem_interval rho lam hrho hsum
    (fun a => (abs_le.mp (hlam a)).1) (fun a => (abs_le.mp (hlam a)).2) x
  calc
    cavityRDerivative rho lam hrho hsum x ≤
        ∑ a, projectedResolventDerivative rho lam hrho hsum a x * (4 * K ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (projectedResolventDerivative_pos rho lam hrho hsum a x).le
      have ha := abs_le.mp (hlam a)
      have hlow : -2 * K ≤ lam a - finiteR rho lam hrho hsum x := by linarith
      have hupp : lam a - finiteR rho lam hrho hsum x ≤ 2 * K := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)]
    _ = 4 * K ^ 2 := by rw [← Finset.sum_mul, sum_projectedResolventDerivative, one_mul]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true, if_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false, if_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true, if_true] using hi

lemma fieldLevelPath_on_cell (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) {s : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelPath h q hq hunit s = q i := by
  change q (fieldLevelIndex h s) = q i
  rw [fieldLevelIndex_on_cell h i hs]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinProduct
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Ising spin law with a scalar field at each site factors
into the actual one-site Gibbs kernels, including its two-spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma uniformSpinPrior_eq_product (N : ℕ) :
    (uniformSpinPrior N : Measure (Spin N)) =
      Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype Bool).toMeasure) := by
  apply Measure.ext_of_singleton
  intro σ
  rw [Measure.pi_singleton]
  simp only [uniformSpinPrior, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp [Spin, ENNReal.inv_pow]

theorem fieldSpinGibbs_eq_product {N : ℕ} (z : Fin N → ℝ) :
    gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) =
      Measure.pi (fun i => scalarSpinKernel (z i)) := by
  let π : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  have hz (i : Fin N) : 0 < ∫ σ, Real.exp (z i * spinValue σ) ∂π :=
    integral_exp_pos Integrable.of_finite
  have hZ : referencePartition (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) =
      ∏ i, ∫ σ, Real.exp (z i * spinValue σ) ∂π := by
    rw [referencePartition, uniformSpinPrior_eq_product]
    simp only [fieldEnergy, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun i σ => Real.exp (z i * spinValue σ))
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite]
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton, hZ, uniformSpinPrior_eq_product, Measure.pi_singleton,
    Measure.pi_singleton]
  have hi (i : Fin N) : scalarSpinKernel (z i) = π.tilted (fun σ => z i * spinValue σ) :=
    gibbsProbability_eq_tilted π _ Integrable.of_finite
  simp_rw [hi, tilted_singleton]
  simp only [referencePartition]
  rw [Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => div_nonneg (Real.exp_pos _).le (hz i).le),
    Finset.prod_div_distrib, fieldEnergy, Real.exp_sum]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear identities for the actual tilted scalar transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_add (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u + b u) z =
      fieldSpinTransition ζ v F a z + fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  exact integral_add
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbB u))

lemma fieldSpinTransition_const (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    fieldSpinTransition ζ v F (fun _ => c) z = c := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  simp only [fieldSpinTransition, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded strict-height approximation of an arbitrary finite field.
Every variance increment is increased by the same small scalar. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldIncrement_le_last (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 ≤ h.height (Fin.last h.depth) := by
  have hh := h.ordered_height (Fin.le_last i)
  change h.height i - (if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩) ≤ _
  split_ifs with hi
  · simpa only [sub_zero] using hh
  · exact (sub_le_self _ (h.nonneg _)).trans hh

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict bias convexity follows from the positive terminal curvature
and the nonnegative conditional variance terms in the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_pos (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ z, |a z| ≤ B) (hap : ∀ z, 0 < a z) (z : ℝ) :
    0 < fieldSpinTransition ζ v F a z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hG ζ
  let μ := (gaussianReal z v).tilted (fun u => ζ * F u)
  have : IsProbabilityMeasure μ := MeasureTheory.isProbabilityMeasure_tilted hw
  have hi : Integrable a μ := (integrable_const B).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hs : Function.support a = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hap u).ne'
  change 0 < ∫ u, a u ∂μ
  apply (integral_pos_iff_support_of_nonneg (fun u => (hap u).le) hi).mpr
  rw [hs, measure_univ]
  exact (zero_lt_one : (0 : ENNReal) < 1)

lemma fieldScalarLogCoshSecond_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    0 < fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos z))
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hs := fieldScalarLogCoshSecond_regular L ht
    have hp := fieldSpinTransition_pos av.1 av.2 hv.1 hv.2 hs.1 hs.2 (ih ht) z
    have hm : Measurable Real.tanh := by
      change Measurable (fun z : ℝ => Real.tanh z)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hc := fieldSpinTransition_square_le av.1 av.2 hv.1 hv.2 ha.1 ha.2 z
    have hζ := (hL av List.mem_cons_self).le
    change 0 < fieldSpinTransition av.1 av.2 _ _ z + av.1 *
      (fieldSpinTransition av.1 av.2 _ _ z - (fieldScalarMean (av :: L) _ _ z) ^ 2)
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hc))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCurvatureBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical curvature is bounded by the remaining spin variance.
Consequently its mean-coordinate representative vanishes at both endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldCurvatureTransform_le_spin_variance {ζ : ℝ} (hζ : ζ ≤ 1) (v : ℝ≥0)
    {F M Q : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    {K C : ℝ} (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (hbound : ∀ y, Q y + (M y) ^ 2 ≤ 1) (z : ℝ) :
    fieldCurvatureTransform ζ v F M Q z ≤ 1 - (fieldSpinTransition ζ v F M z) ^ 2 := by
  have bM2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have hle := fieldSpinTransition_mono_test ζ v F (hQ.add (hM.pow_const 2))
    measurable_const
    (fun y => (abs_add_le _ _).trans (add_le_add (bQ y) (bM2 y)))
    (fun _ => by norm_num : ∀ y : ℝ, |(1 : ℝ)| ≤ 1) hbound z
  change fieldSpinTransition ζ v F (fun y => Q y + M y ^ 2) z ≤
    fieldSpinTransition ζ v F (fun _ => 1) z at hle
  rw [fieldSpinTransition_add ζ v hF hG hQ (hM.pow_const 2) bQ bM2,
    fieldSpinTransition_const ζ v hF hG] at hle
  have hvar := fieldSpinTransition_square_le ζ v hF hG hM bM z
  have hc : ζ * (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2) ≤
      fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2 := by
    exact mul_le_of_le_one_left (sub_nonneg.mpr hvar) hζ
  unfold fieldCurvatureTransform
  linarith

lemma field_logCosh_spin_variance (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  have hc := (Real.cosh_pos z).ne'
  have hr := Real.cosh_sq_sub_sinh_sq z
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith

lemma fieldScalarLogCoshSecond_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) z ≤
      1 - (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh z) ^ 2 := by
  induction L generalizing z with
  | nil =>
    change 1 / (Real.cosh z) ^ 2 ≤ 1 - (Real.tanh z) ^ 2
    linarith [field_logCosh_spin_variance z]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hb : ∀ y, fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) y +
        (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh y) ^ 2 ≤ 1 := by
      intro y
      linarith [ih ht htζ y]
    exact fieldCurvatureTransform_le_spin_variance (hζ av List.mem_cons_self) av.2
      hv.1 hv.2 ha.1 hq.1 ha.2 hq.2 hb z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conditional spin mean is spatially one-Lipschitz,
uniformly in the number and variances of the finite field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCoshMean_dist_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (x y : ℝ) :
    |fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh x -
      fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y| ≤ |x - y| := by
  have hd z := hasDerivAt_fieldScalarLogCoshMean L hL z
  have hb (z : ℝ) :
      ‖fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
        (fun z => 1 / (Real.cosh z) ^ 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (fieldScalarLogCoshSecond_pos L hL z)]
    exact (fieldScalarLogCoshSecond_le_spin_variance L hL hζ z).trans
      (sub_le_self _ (sq_nonneg _))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (C := 1)
    (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hb z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative conditional-variance bound for a Lipschitz spin
mean. The constant depends only on an upper bound for the Gaussian
variance, rather than on the depth of the scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussianMomentCap_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ fieldGaussianMomentCap C := by
  have hb := (field_centered_tilt_second_moment (U := fun _ => 0) measurable_const
    (C := C) (fun u => by simpa using mul_nonneg hC (abs_nonneg u))).2
  exact (integral_nonneg (fun u => sq_nonneg (1 + |u|))).trans hb

lemma field_centered_spin_variance {U M : ℝ → ℝ}
    (hU : Measurable U) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    {C : ℝ} (hUb : ∀ u, |U u| ≤ C * |u|) (x : ℝ) (v : ℝ≥0) :
    variance (fun u => M (x + Real.sqrt (v : ℝ) * u)) ((gaussianReal 0 1).tilted U) ≤
      (v : ℝ) * fieldGaussianMomentCap C := by
  let μ := (gaussianReal 0 1).tilted U
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  let X := fun u => M (x + Real.sqrt (v : ℝ) * u)
  have hmX : Measurable X := hM.comp (by fun_prop)
  have hmD : AEStronglyMeasurable (fun u => X u - M x) μ :=
    (hmX.sub_const _).aestronglyMeasurable
  have hLp : MemLp (fun u => X u - M x) 2 μ :=
    MemLp.of_bound hmD 2 (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by dsimp only [X] <;> linarith [hMb (x + Real.sqrt (v : ℝ) * u), hMb x]))
  obtain ⟨hi, hb⟩ := field_centered_tilt_second_moment hU hUb
  have hp (u : ℝ) : (X u - M x)^2 ≤ (v : ℝ) * (1 + |u|)^2 := by
    have hl : |X u - M x| ≤ Real.sqrt (v : ℝ) * |u| := by
      simpa only [X, add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
        hML (x + Real.sqrt (v : ℝ) * u) x
    have hs := pow_le_pow_left₀ (abs_nonneg _) hl 2
    rw [sq_abs, mul_pow, Real.sq_sqrt v.coe_nonneg] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg u) (by linarith : |u| ≤ 1 + |u|) 2) v.coe_nonneg)
  calc
    variance X μ = variance (fun u => X u - M x) μ :=
      (variance_sub_const hmX.aestronglyMeasurable (M x)).symm
    _ ≤ ∫ u, (X u - M x)^2 ∂μ := variance_le_expectation_sq hmD
    _ ≤ ∫ u, (v : ℝ) * (1 + |u|)^2 ∂μ := integral_mono hLp.integrable_sq (hi.const_mul _) hp
    _ = (v : ℝ) * ∫ u, (1 + |u|)^2 ∂μ := integral_const_mul _ _
    _ ≤ (v : ℝ) * fieldGaussianMomentCap C := mul_le_mul_of_nonneg_left hb v.coe_nonneg

lemma fieldSpinTransition_centered_standard (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M) (x : ℝ) :
    fieldSpinTransition ζ v F M x =
      ∫ u, M (x + Real.sqrt (v : ℝ) * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)) := by
  rw [fieldSpinTransition_eq_standard ζ v hF hM, gaussianTiltAverage_eq_div,
    integral_tilted_eq_div]
  simp_rw [mul_sub, Real.exp_sub, div_mul_eq_mul_div]
  rw [integral_div, integral_div, div_div_div_cancel_right₀ (Real.exp_ne_zero _)]

lemma fieldSpinTransition_variance_bound (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    (x : ℝ) {C : ℝ}
    (hUb : ∀ u, |ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)| ≤ C * |u|) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
        (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap C := by
  let U := fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)
  have hU : Measurable U := by dsimp only [U]; fun_prop
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let μ := (gaussianReal 0 1).tilted U
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  have hm : Measurable (fun u => M (x + Real.sqrt (v : ℝ) * u)) := hM.comp (by fun_prop)
  have hLp : MemLp (fun u => M (x + Real.sqrt (v : ℝ) * u)) 2 μ :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun u => by
      simpa only [Real.norm_eq_abs] using hMb (x + Real.sqrt (v : ℝ) * u))
  rw [fieldSpinTransition_centered_standard ζ v hF (hM.pow_const 2),
    fieldSpinTransition_centered_standard ζ v hF hM]
  change (∫ u, (M (x + Real.sqrt (v : ℝ) * u))^2 ∂μ) -
    (∫ u, M (x + Real.sqrt (v : ℝ) * u) ∂μ)^2 ≤ _
  have heq := variance_eq_sub hLp
  simp only [Pi.pow_apply] at heq
  rw [← heq]
  exact field_centered_spin_variance hU hM hMb hML hUb x v

lemma fieldSpinTransition_variance_le (ζ : ℝ) (hζ : ζ ∈ Icc 0 1) (v : ℝ≥0)
    {V : ℝ} (hv : (v : ℝ) ≤ V) {F M : ℝ → ℝ}
    (hF : Measurable F) (hFL : ∀ x y, |F x - F y| ≤ |x - y|)
    (hM : Measurable M) (hMb : ∀ z, |M z| ≤ 1)
    (hML : ∀ x y, |M x - M y| ≤ |x - y|) (x : ℝ) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
      (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  apply fieldSpinTransition_variance_bound ζ v hF hM hMb hML x
  intro u
  rw [abs_mul, abs_of_nonneg hζ.1]
  have hf : |F (x + Real.sqrt (v : ℝ) * u) - F x| ≤ Real.sqrt V * |u| := by
    have hh := hFL (x + Real.sqrt (v : ℝ) * u) x
    simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv) (abs_nonneg u))
  exact (mul_le_mul_of_nonneg_left hf hζ.1).trans
    (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hζ.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCurvatureLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive exponential lower bound for the actual finite-step curvature.
The constant depends only on the finite covariance data, not on the bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCosh_lipschitz (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (x y : ℝ) :
    |fieldScalarValue L (fun z => Real.log (Real.cosh z)) x -
      fieldScalarValue L (fun z => Real.log (Real.cosh z)) y| ≤ |x - y| := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hb := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_fieldScalarLogCosh L hL z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hb.2 z)
      convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldOverlapIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional overlap increments are bounded by their variance
increments, uniformly in all preceding scalar-field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_sub (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u - b u) z =
      fieldSpinTransition ζ v F a z - fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  let : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    isProbabilityMeasure_tilted he
  exact integral_sub
    (Integrable.of_bound ha.aestronglyMeasurable A
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hbB u))

theorem fieldScalarSquares_increment_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1)
    {V : ℝ} (hV : ∀ av ∈ L, (av.2 : ℝ) ≤ V) (i : Fin L.length) (z : ℝ) :
    fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.succ z -
      fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.castSucc z ≤
        ((L.get i).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  induction L generalizing z with
  | nil => exact Fin.elim0 i
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have htV := fun bv hb => hV bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hmean := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    have hreg := fieldScalarSquares_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    refine Fin.cases ?_ (fun j => ?_) i
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0) z -
        (fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh) z)^2 ≤ _
      have hzero : fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0 =
          fun y => (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y)^2 := by
        funext y
        exact fieldScalarSquares_zero _ _ _ _
      rw [hzero]
      exact fieldSpinTransition_variance_le av.1
        ⟨(hL av List.mem_cons_self).le, hζ av List.mem_cons_self⟩ av.2
        (hV av List.mem_cons_self) hval.1 (fieldScalarLogCosh_lipschitz L ht)
        hmean.1 hmean.2 (fieldScalarLogCoshMean_dist_le L ht htζ) z
    · have hb (j : Fin (L.length + 1)) (u : ℝ) :
          |fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j u| ≤ 1 := by
        rw [abs_of_nonneg ((hreg j).2 u).1]
        exact ((hreg j).2 u).2
      change fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.succ) z -
        fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.castSucc) z ≤ _
      rw [← fieldSpinTransition_sub av.1 av.2 hval.1 hval.2
        (hreg j.succ).1 (hreg j.castSucc).1 (hb j.succ) (hb j.castSucc)]
      calc
        _ ≤ fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
            (fun _ => ((L.get j).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V)) z :=
          fieldSpinTransition_mono_test av.1 av.2 _
            ((hreg j.succ).1.sub (hreg j.castSucc).1) measurable_const
            (fun u => (abs_sub _ _).trans (add_le_add (hb j.succ u) (hb j.castSucc u)))
            (fun _ => le_rfl) (fun u => ih ht htζ htV j u) z
        _ = _ := fieldSpinTransition_const av.1 av.2 hval.1 hval.2 _ z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldModulus
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform plateau control for the actual strict finite cavity fields.
The spectral derivative bound and the conditional-variance estimate
turn convergence of overlap levels into asymptotic preservation of ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFieldPrimitive_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (s t : ℝ) :
    |cavityFieldPrimitive rho lam hrho hsum p s -
      cavityFieldPrimitive rho lam hrho hsum p t| ≤ 4 * K^2 * |s - t| := by
  rw [cavityFieldPrimitive_sub]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 4 * K^2)
    (f := cavityFieldDensity rho lam hrho hsum p) (fun u _ => by
      dsimp only [cavityFieldDensity]
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRDerivative_nonneg rho lam hrho hsum _)]
      exact cavityRDerivative_le rho lam hrho hsum hK hlam _)
  simpa only [Real.norm_eq_abs] using hb

lemma cavityStrictUniformField_height_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    (cavityStrictUniformField rho lam hrho hsum p n).height i ≤ 4 * K^2 := by
  have hb := cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n i) 0
  have hq := cavityStrictUniformLevels_mem p n i
  have hp0 : cavityFieldPrimitive rho lam hrho hsum (cavityStrictUniformPath p n) 0 = 0 := by
    simp only [cavityFieldPrimitive, intervalIntegral.integral_same]
  rw [hp0, sub_zero, abs_of_nonneg (cavityFieldPrimitive_nonneg _ _ _ _ _ hq.1.le),
    sub_zero, abs_of_pos hq.1] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity) hq.2.le)

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

lemma restrictedSpinLog_le_full {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) : restrictedSpinLog S H ≤ logPartition H := by
  rw [← restrictedSpinLog_univ]
  exact restrictedSpinLog_mono hS (Finset.subset_univ S) (fun _ _ => le_rfl)

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

lemma restrictedFieldTerminal_le_univ {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z : Fin N → ℝ) : restrictedFieldTerminal S z ≤ ∑ i, Real.log (Real.cosh (z i)) := by
  rw [restrictedFieldTerminal, ← logPartition_fieldEnergy]
  exact restrictedSpinLog_le_full S hS _

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSpinEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy and the log-sum variational bound used to project
canonical spins onto an attainable constrained block. Zero trial masses
are allowed and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma finite_relativeEntropy_nonneg_of_sum_le {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hqSum : ∑ x, q x ≤ 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) := by
  have hi (x : X) : p x - q x ≤ p x * Real.log (p x / q x) := by
    by_cases hx : p x = 0
    · simp only [hx, zero_sub, zero_mul]
      exact neg_nonpos.mpr (hq x).le
    have hxp : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    have hl := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hq x) hxp)) (hp x)
    have he : p x * (q x / p x - 1) = q x - p x := by field_simp
    rw [he, Real.log_div (hq x).ne' hx] at hl
    rw [Real.log_div hx (hq x).ne']
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hi x)
  rw [Finset.sum_sub_distrib, hpSum] at hs
  linarith

lemma finite_relativeEntropy_nonneg {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hqSum : ∑ x, q x = 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) :=
  finite_relativeEntropy_nonneg_of_sum_le p q hp hpSum hq hqSum.le

lemma finiteCanonicalWeights_pos {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (x : X) : 0 < finiteCanonicalWeights H x :=
  div_pos (Real.exp_pos _) (sum_exp_pos H)

lemma finiteCanonicalWeights_sum {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) : ∑ x, finiteCanonicalWeights H x = 1 := by
  simp only [finiteCanonicalWeights, ← Finset.sum_div]
  exact div_self (sum_exp_pos H).ne'

lemma log_sum_exp_ge_trial {X : Type*} [Fintype X] [Nonempty X]
    (H p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    (∑ x, p x * H x) + finiteShannonEntropy p ≤ Real.log (∑ x, Real.exp (H x)) := by
  have hk := finite_relativeEntropy_nonneg p (finiteCanonicalWeights H) hp hpSum
    (finiteCanonicalWeights_pos H) (finiteCanonicalWeights_sum H)
  have hi (x : X) : p x * Real.log (p x / finiteCanonicalWeights H x) =
      p x * Real.log (p x) - p x * H x + p x * Real.log (∑ y, Real.exp (H y)) := by
    by_cases hx : p x = 0
    · simp [hx]
    · rw [Real.log_div hx (finiteCanonicalWeights_pos H x).ne', finiteCanonicalWeights,
        Real.log_div (Real.exp_ne_zero _) (sum_exp_pos H).ne', Real.log_exp]
      ring
  simp_rw [hi] at hk
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hpSum, one_mul] at hk
  unfold finiteShannonEntropy
  linarith

lemma log_sum_exp_eq_canonical {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    Real.log (∑ x, Real.exp (H x)) =
      (∑ x, finiteCanonicalWeights H x * H x) + finiteShannonEntropy (finiteCanonicalWeights H) := by
  have he (x : X) : finiteCanonicalWeights H x * Real.log (finiteCanonicalWeights H x) =
      finiteCanonicalWeights H x * H x -
        finiteCanonicalWeights H x * Real.log (∑ y, Real.exp (H y)) := by
    conv_lhs => arg 2; rw [finiteCanonicalWeights, Real.log_div (Real.exp_ne_zero _)
      (sum_exp_pos H).ne', Real.log_exp]
    ring
  unfold finiteShannonEntropy
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, finiteCanonicalWeights_sum, one_mul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteWeightedCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite probability form of Cauchy--Schwarz, including zero atoms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma finite_weighted_sum_sq_le {X : Type*} [Fintype X]
    (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    (∑ x, p x * f x) ^ 2 ≤ ∑ x, p x * f x ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (p x)) (fun x => Real.sqrt (p x) * f x)
  have hm (x : X) : Real.sqrt (p x) * (Real.sqrt (p x) * f x) = p x * f x := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hp x)]
  simp_rw [hm, mul_pow, Real.sq_sqrt (hp _)] at hc
  simpa only [hpSum, one_mul] using hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinHammingEnergy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalEndpoint
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
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

lemma fieldTailSpinKernel_endpoint (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    fieldTailSpinKernel L hL = scalarSpinKernel ∘ₖ fieldTailEndpointKernel L hL := by
  induction L with
  | nil => simp [fieldTailSpinKernel, fieldTailEndpointKernel]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    change fieldTailSpinKernel L ht ∘ₖ _ = scalarSpinKernel ∘ₖ (fieldTailEndpointKernel L ht ∘ₖ _)
    rw [ih ht, Kernel.comp_assoc]

lemma fieldTransitionKernel_zero (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F)
    (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel 0 v F hF z = gaussianReal z v := by
  rw [fieldTransitionKernel_eq_tilted 0 v F hF hG]
  simp

theorem fieldCanonicalSpinLaw_endpoint (h : FieldStep) (b : ℝ) :
    fieldCanonicalSpinLaw h b = scalarSpinKernel ∘ₘ fieldCanonicalEndpointLaw h b := by
  have hreg := fieldScalarValue_regular (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
  rw [fieldCanonicalEndpointLaw, Measure.comp_assoc, ← fieldTailSpinKernel_endpoint]
  rw [fieldCanonicalSpinLaw, Kernel.comp_apply, fieldTransitionKernel_zero _ _ hreg.1 hreg.2]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalSpinWeights
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite canonical weights used in the projection estimates are
exactly the physical Gibbs probabilities, including the uniform prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma finiteCanonicalWeights_eq_mass {N : ℕ} (H : Spin N → ℝ) (σ : Spin N) :
    finiteCanonicalWeights H σ =
      (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real {σ} := by
  classical
  let A := fun τ : Spin N => if τ = σ then (1 : ℝ) else 0
  have he := integral_uniformSpinGibbs_canonical H A
  have hi : (∫ τ, A τ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real {σ} := by
    simpa only [Set.indicator, Set.mem_singleton_iff, A, Pi.one_apply] using
      (integral_indicator_one (μ := gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)
        (measurableSet_singleton σ))
  rw [hi] at he
  simpa [A] using he.symm

lemma fieldCanonicalWeights_product {N : ℕ} (z : Fin N → ℝ) (σ : Spin N) :
    finiteCanonicalWeights (fieldEnergy z) σ =
      ∏ i, (scalarSpinKernel (z i)).real {σ i} := by
  rw [finiteCanonicalWeights_eq_mass, fieldSpinGibbs_eq_product, measureReal_def,
    Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

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

lemma sq_le_exp_two_add (x : ℝ) : x ^ 2 ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
  have ha : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have hs := (sq_le_sq₀ (abs_nonneg x) (Real.exp_pos _).le).mpr ha
  rw [sq_abs] at hs
  rw [show (Real.exp |x|) ^ 2 = Real.exp (|x| + |x|) by
    rw [pow_two, Real.exp_add]] at hs
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, show x + x = 2 * x by ring] at hs
    linarith [Real.exp_pos (-2 * x)]
  · rw [abs_of_nonpos (le_of_not_ge hx), show -x + -x = -2 * x by ring] at hs
    linarith [Real.exp_pos (2 * x)]

theorem fieldCanonicalEndpointLaw_second_moment (h : FieldStep) (b : ℝ) :
    Integrable (fun y : ℝ => y ^ 2) (fieldCanonicalEndpointLaw h b) ∧
      (∫ y, y ^ 2 ∂fieldCanonicalEndpointLaw h b) ≤
        Real.exp (2 * b + 4 * h.height (Fin.last h.depth)) +
          Real.exp (-2 * b + 4 * h.height (Fin.last h.depth)) := by
  have hp := fieldCanonicalEndpointLaw_mgf h b 2
  have hn := fieldCanonicalEndpointLaw_mgf h b (-2)
  have hi : Integrable (fun y : ℝ => y ^ 2) (fieldCanonicalEndpointLaw h b) := by
    apply (hp.1.add hn.1).mono' (by fun_prop)
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_exp_two_add y)
  refine ⟨hi, ?_⟩
  have hle := integral_mono hi (hp.1.add hn.1) sq_le_exp_two_add
  simp only [Pi.add_apply] at hle
  rw [integral_add hp.1 hn.1] at hle
  norm_num at hp hn
  have hn' : (∫ y, Real.exp (-2 * y) ∂fieldCanonicalEndpointLaw h b) ≤
      Real.exp (-2 * b + 4 * h.height (Fin.last h.depth)) := by
    simpa only [neg_mul] using hn.2
  exact hle.trans (add_le_add hp.2 hn')

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalVectorMoments
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent canonical endpoint fields have a total second moment
linear in the block size, uniformly over the cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma fieldCanonicalVectorLaw_coordinate_integrable {N : ℕ} (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin N) :
    Integrable (fun z : Fin N → ℝ => z i ^ 2) (fieldCanonicalVectorLaw N h b) :=
  (measurePreserving_eval (fun j => fieldCanonicalEndpointLaw h (b j)) i).integrable_comp_of_integrable
    (fieldCanonicalEndpointLaw_second_moment h (b i)).1

lemma fieldCanonicalVectorLaw_square_integrable {N : ℕ} (h : FieldStep) (b : Fin N → ℝ) :
    Integrable (fun z : Fin N → ℝ => ∑ i, z i ^ 2) (fieldCanonicalVectorLaw N h b) := by
  exact integrable_finsetSum _ (fun i _ => fieldCanonicalVectorLaw_coordinate_integrable h b i)

theorem fieldCanonicalVectorLaw_second_moment {N : ℕ} (h : FieldStep) (b : Fin N → ℝ)
    {B H : ℝ} (hb : ∀ i, |b i| ≤ B) (hH : h.height (Fin.last h.depth) ≤ H) :
    (∫ z : Fin N → ℝ, ∑ i, z i ^ 2 ∂fieldCanonicalVectorLaw N h b) ≤
      N * (2 * Real.exp (2 * B + 4 * H)) := by
  rw [integral_finsetSum _ (fun i _ => fieldCanonicalVectorLaw_coordinate_integrable h b i)]
  calc
    _ ≤ ∑ _i : Fin N, 2 * Real.exp (2 * B + 4 * H) := by
      apply Finset.sum_le_sum
      intro i _
      have he := (fieldCanonicalEndpointLaw_second_moment h (b i)).2
      have hp : (∫ z : Fin N → ℝ, z i ^ 2 ∂fieldCanonicalVectorLaw N h b) =
          ∫ y : ℝ, y ^ 2 ∂fieldCanonicalEndpointLaw h (b i) :=
        (measurePreserving_eval (fun j => fieldCanonicalEndpointLaw h (b j)) i).hasLaw.integral_comp
          (f := fun y : ℝ => y ^ 2) (by fun_prop)
      rw [hp]
      apply he.trans
      have hab := abs_le.mp (hb i)
      have h₁ : Real.exp (2 * b i + 4 * h.height (Fin.last h.depth)) ≤
          Real.exp (2 * B + 4 * H) := Real.exp_le_exp.mpr (by linarith)
      have h₂ : Real.exp (-2 * b i + 4 * h.height (Fin.last h.depth)) ≤
          Real.exp (2 * B + 4 * H) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ = _ := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinProjectionEnergy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy lost by projection in a possibly unbounded external field.
The Euclidean estimate is suited to averaging under Gaussian path laws. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma fieldEnergy_projection_sq {N : ℕ} (z : Fin N → ℝ) (σ τ : Spin N) :
    (fieldEnergy z σ - fieldEnergy z τ) ^ 2 ≤
      4 * (∑ i, z i ^ 2) * (hammingDist σ τ : ℝ) := by
  have he : fieldEnergy z σ - fieldEnergy z τ =
      ∑ i, z i * (spinValue (σ i) - spinValue (τ i)) := by
    simp only [fieldEnergy, mul_sub, Finset.sum_sub_distrib]
  have hd : (∑ i, (spinValue (σ i) - spinValue (τ i)) ^ 2) =
      4 * (hammingDist σ τ : ℝ) := by
    have h := spinVector_sub_norm_sq σ τ
    rw [EuclideanSpace.real_norm_sq_eq] at h
    exact h
  rw [he]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z
    (fun i => spinValue (σ i) - spinValue (τ i))
  rw [hd] at hc
  nlinarith

theorem fieldEnergy_projection_mean_le {N : ℕ} (z : Fin N → ℝ)
    (f : Spin N → Spin N) (p : Spin N → ℝ)
    (hp : ∀ σ, 0 ≤ p σ) (hpSum : ∑ σ, p σ = 1) :
    |∑ σ, p σ * (fieldEnergy z σ - fieldEnergy z (f σ))| ≤
      2 * Real.sqrt ((∑ i, z i ^ 2) *
        (∑ σ, p σ * (hammingDist σ (f σ) : ℝ))) := by
  have hz : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hd : 0 ≤ ∑ σ, p σ * (hammingDist σ (f σ) : ℝ) :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg (hp σ) (Nat.cast_nonneg _))
  have he : (∑ σ, p σ * (fieldEnergy z σ - fieldEnergy z (f σ)) ^ 2) ≤
      4 * (∑ i, z i ^ 2) * (∑ σ, p σ * (hammingDist σ (f σ) : ℝ)) := by
    calc
      _ ≤ ∑ σ, p σ * (4 * (∑ i, z i ^ 2) * (hammingDist σ (f σ) : ℝ)) :=
        Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left
          (fieldEnergy_projection_sq z σ (f σ)) (hp σ))
      _ = _ := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (mul_nonneg hz hd)]
  norm_num
  exact (finite_weighted_sum_sq_le p
    (fun σ => fieldEnergy z σ - fieldEnergy z (f σ)) hp hpSum).trans (by nlinarith [he])

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FinitePushforwardEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite pushforward weights and their entropy averages. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma finitePushforwardWeights_nonneg {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    0 ≤ finitePushforwardWeights f p y :=
  Finset.sum_nonneg (fun x _ => hp x)

lemma finitePushforwardWeights_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) : ∑ y, finitePushforwardWeights f p y = ∑ x, p x :=
  Finset.sum_fiberwise Finset.univ f p

lemma finitePushforwardWeights_at_image {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (x : X) :
    p x ≤ finitePushforwardWeights f p (f x) :=
  Finset.single_le_sum (fun y _ => hp y) (by simp)

lemma finitePushforwardWeights_average {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (F : Y → ℝ) :
    (∑ y, finitePushforwardWeights f p y * F y) = ∑ x, p x * F (f x) := by
  simp only [finitePushforwardWeights, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => p x * F (f x))]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

lemma finitePushforwardWeights_entropy {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) :
    finiteShannonEntropy (finitePushforwardWeights f p) =
      -∑ x, p x * Real.log (finitePushforwardWeights f p (f x)) := by
  rw [finiteShannonEntropy, finitePushforwardWeights_average]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinProjectionEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy lost by a deterministic spin projection is controlled by its
expected Hamming distance. The estimate uses one finite conditional kernel,
so its constant does not depend on the depth of a Gaussian cascade. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma finitePushforwardWeights_pos_image {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 < p x) (x : X) :
    0 < finitePushforwardWeights f p (f x) :=
  (hp x).trans_le (finitePushforwardWeights_at_image f p (fun x => (hp x).le) x)

theorem finite_pushforward_entropy_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p C : X → ℝ) (hp : ∀ x, 0 < p x) (hpSum : ∑ x, p x = 1)
    (Z : ℝ) (hZ : 0 < Z)
    (hkernel : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y),
      Real.exp (-C x)) ≤ Z) :
    finiteShannonEntropy p - finiteShannonEntropy (finitePushforwardWeights f p) ≤
      (∑ x, p x * C x) + Real.log Z := by
  let q := finitePushforwardWeights f p
  let r := fun x => q (f x) * Real.exp (-C x) / Z
  have hq (y : Y) : 0 ≤ q y :=
    finitePushforwardWeights_nonneg f p (fun x => (hp x).le) y
  have hqi (x : X) : 0 < q (f x) := finitePushforwardWeights_pos_image f p hp x
  have hr (x : X) : 0 < r x := div_pos (mul_pos (hqi x) (Real.exp_pos _)) hZ
  have hrSum : ∑ x, r x ≤ 1 := by
    rw [← Finset.sum_fiberwise Finset.univ f r]
    calc
      _ = ∑ y, q y / Z *
          (∑ x ∈ Finset.univ.filter (fun x => f x = y), Real.exp (-C x)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [r]
        rw [(Finset.mem_filter.mp hx).2]
        ring
      _ ≤ ∑ y, q y / Z * Z := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hkernel y) (div_nonneg (hq y) hZ.le))
      _ = 1 := by
        simp only [div_mul_cancel₀ _ hZ.ne']
        exact (finitePushforwardWeights_sum f p).trans hpSum
  have hk := finite_relativeEntropy_nonneg_of_sum_le p r
    (fun x => (hp x).le) hpSum hr hrSum
  have hlog (x : X) : Real.log (r x) = Real.log (q (f x)) - C x - Real.log Z := by
    dsimp only [r]
    rw [Real.log_div (mul_ne_zero (hqi x).ne' (Real.exp_ne_zero _)) hZ.ne',
      Real.log_mul (hqi x).ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hi (x : X) : p x * Real.log (p x / r x) =
      p x * Real.log (p x) - p x * Real.log (q (f x)) +
        p x * C x + p x * Real.log Z := by
    rw [Real.log_div (hp x).ne' (hr x).ne', hlog]
    ring
  simp_rw [hi] at hk
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hpSum, one_mul] at hk
  rw [finiteShannonEntropy, finitePushforwardWeights_entropy]
  change -(∑ x, p x * Real.log (p x)) - (-(∑ x, p x * Real.log (q (f x)))) ≤ _
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteProjectionTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trial measure obtained by pushing canonical spins through a finite
map. The log-partition loss consists of the expected energy loss and the
entropy of the projection. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem log_sum_exp_projection_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq Y]
    (f : X → Y) (H : X → ℝ) (K : Y → ℝ) (C : X → ℝ)
    (Z : ℝ) (hZ : 0 < Z)
    (hkernel : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y),
      Real.exp (-C x)) ≤ Z) :
    Real.log (∑ x, Real.exp (H x)) ≤ Real.log (∑ y, Real.exp (K y)) +
      (∑ x, finiteCanonicalWeights H x * (H x - K (f x))) +
      (∑ x, finiteCanonicalWeights H x * C x) + Real.log Z := by
  let p := finiteCanonicalWeights H
  let q := finitePushforwardWeights f p
  have htrial := log_sum_exp_ge_trial K q
    (finitePushforwardWeights_nonneg f p (fun x => (finiteCanonicalWeights_pos H x).le))
    ((finitePushforwardWeights_sum f p).trans (finiteCanonicalWeights_sum H))
  have he := finite_pushforward_entropy_bound f p C
    (finiteCanonicalWeights_pos H) (finiteCanonicalWeights_sum H) Z hZ hkernel
  have hcan := log_sum_exp_eq_canonical H
  have hav := finitePushforwardWeights_average f p K
  have hsub : (∑ x, p x * (H x - K (f x))) =
      (∑ x, p x * H x) - ∑ x, p x * K (f x) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  change Real.log (∑ x, Real.exp (H x)) ≤ _
  change Real.log (∑ x, Real.exp (H x)) = (∑ x, p x * H x) + finiteShannonEntropy p at hcan
  change (∑ y, q y * K y) = ∑ x, p x * K (f x) at hav
  change finiteShannonEntropy p - finiteShannonEntropy q ≤ _ at he
  change _ ≤ Real.log (∑ y, Real.exp (K y)) at htrial
  change Real.log (∑ x, Real.exp (H x)) ≤ Real.log (∑ y, Real.exp (K y)) +
    (∑ x, p x * (H x - K (f x))) + (∑ x, p x * C x) + Real.log Z
  rw [hsub]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinProjectionTrial
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual restricted spin partitions admit the projected canonical law as
a trial law. The prior remains the mass inherited from the full cube. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem restrictedSpinLog_projection_bound {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (f : Spin N → Spin N)
    (hf : ∀ σ, f σ ∈ S) (H : Spin N → ℝ) (t : ℝ) :
    logPartition H - restrictedSpinLog S H ≤
      (∑ σ, finiteCanonicalWeights H σ * (H σ - H (f σ))) +
      t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) +
      N * Real.log (1 + Real.exp (-t)) := by
  classical
  let : Nonempty {τ // τ ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let g : Spin N → {τ // τ ∈ S} := fun σ => ⟨f σ, hf σ⟩
  have hkernel (τ : {τ // τ ∈ S}) :
      (∑ σ ∈ Finset.univ.filter (fun σ => g σ = τ),
        Real.exp (-(t * (hammingDist σ (f σ) : ℝ)))) ≤
          (1 + Real.exp (-t)) ^ N := by
    calc
      _ = ∑ σ ∈ Finset.univ.filter (fun σ => g σ = τ),
          Real.exp (-t * (hammingDist σ τ.val : ℝ)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        have he : f σ = τ.val := congrArg Subtype.val (Finset.mem_filter.mp hσ).2
        rw [he]
        congr 1
        ring
      _ ≤ ∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ.val : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => (Real.exp_pos _).le)
      _ = _ := sum_exp_hamming τ.val t
  have he := log_sum_exp_projection_bound g H (fun τ => H τ.val)
    (fun σ => t * (hammingDist σ (f σ) : ℝ)) _ (by positivity) hkernel
  have hsum : (∑ τ : {τ // τ ∈ S}, Real.exp (H τ.val)) =
      ∑ τ ∈ S, Real.exp (H τ) := by
    change (∑ τ ∈ S.attach, Real.exp (H τ.val)) = _
    exact Finset.sum_attach S (fun τ : Spin N => Real.exp (H τ))
  rw [hsum, Real.log_pow] at he
  have hcost : (∑ σ, finiteCanonicalWeights H σ * (t * (hammingDist σ (f σ) : ℝ))) =
      t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hcost] at he
  rw [logPartition_eq, log_card_spin, restrictedSpinLog]
  change Real.log (∑ σ, Real.exp (H σ)) - ↑N * Real.log 2 -
      (Real.log (∑ σ ∈ S, Real.exp (H σ)) - ↑N * Real.log 2) ≤ _
  change Real.log (∑ σ, Real.exp (H σ)) ≤ Real.log (∑ σ ∈ S, Real.exp (H σ)) +
    (∑ σ, finiteCanonicalWeights H σ * (H σ - H (f σ))) +
    t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) +
    ↑N * Real.log (1 + Real.exp (-t)) at he
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldProjectionLoss
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A depth-free terminal loss estimate for the actual constrained
partition function. It separates the field second moment from the
expected number of flips, before any Gaussian-path averaging. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma fieldProjectionDistance_nonneg {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) :
    0 ≤ fieldProjectionDistance f z :=
  Finset.sum_nonneg (fun σ _ => mul_nonneg (finiteCanonicalWeights_pos _ σ).le
    (Nat.cast_nonneg _))

lemma two_sqrt_mul_le_add_div {M D ε : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    2 * Real.sqrt (M * D) ≤ ε * M + D / ε := by
  have he : (ε * M) * (D / ε) = M * D := by field_simp
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hM hD)]
  nlinarith [sq_nonneg (ε * M - D / ε)]

theorem field_projection_terminal_loss {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S) (z : Fin N → ℝ) (t : ℝ) :
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ≤
      2 * Real.sqrt ((∑ i, z i ^ 2) * fieldProjectionDistance f z) +
        t * fieldProjectionDistance f z + N * Real.log (1 + Real.exp (-t)) := by
  have ht := restrictedSpinLog_projection_bound S hS f hf (fieldEnergy z) t
  have he := fieldEnergy_projection_mean_le z f (finiteCanonicalWeights (fieldEnergy z))
    (fun σ => (finiteCanonicalWeights_pos _ σ).le) (finiteCanonicalWeights_sum _)
  rw [logPartition_fieldEnergy] at ht
  exact ht.trans (add_le_add (add_le_add
    ((le_abs_self _).trans he) le_rfl) le_rfl)

theorem field_projection_terminal_loss_linear {N : ℕ} (S : Finset (Spin N))
    (hS : S.Nonempty) (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S)
    (z : Fin N → ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ≤
      ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z +
        N * Real.log (1 + Real.exp (-t)) := by
  have he := two_sqrt_mul_le_add_div
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (z i)))
    (fieldProjectionDistance_nonneg f z) hε
  have ht := field_projection_terminal_loss S hS f hf z t
  rw [div_eq_mul_inv] at he
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldProjectionMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the terminal loss requires only a field second moment and
the expected projection distance. The bound has no cascade-depth term. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma continuous_fieldCanonicalWeights {N : ℕ} (σ : Spin N) :
    Continuous (fun z : Fin N → ℝ => finiteCanonicalWeights (fieldEnergy z) σ) := by
  have hc (τ : Spin N) : Continuous (fun z : Fin N → ℝ => fieldEnergy z τ) := by
    unfold fieldEnergy
    fun_prop
  exact (Real.continuous_exp.comp (hc σ)).div
    (continuous_finsetSum _ (fun τ _ => Real.continuous_exp.comp (hc τ)))
    (fun z => (sum_exp_pos (fieldEnergy z)).ne')

lemma continuous_fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N) :
    Continuous (fieldProjectionDistance f) := by
  unfold fieldProjectionDistance
  exact continuous_finsetSum _ (fun σ _ => (continuous_fieldCanonicalWeights σ).mul_const _)

lemma fieldProjectionDistance_le {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) :
    fieldProjectionDistance f z ≤ N := by
  calc
    _ ≤ ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * N := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (finiteCanonicalWeights_pos _ σ).le
      exact_mod_cast (show hammingDist σ (f σ) ≤ N from
        hammingDist_le_card_fintype.trans_eq (Fintype.card_fin N))
    _ = _ := by rw [← Finset.sum_mul, finiteCanonicalWeights_sum, one_mul]

lemma integrable_fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fieldProjectionDistance f) μ := by
  apply (integrable_const (N : ℝ)).mono' (continuous_fieldProjectionDistance f).aestronglyMeasurable
  exact ae_of_all μ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fieldProjectionDistance_nonneg f z)]
    exact fieldProjectionDistance_le f z)

theorem field_projection_mean_loss {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hM : Integrable (fun z : Fin N → ℝ => ∑ i, z i ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ∂μ) ≤
      ε * (∫ z, ∑ i, z i ^ 2 ∂μ) +
      (ε⁻¹ + t) * (∫ z, fieldProjectionDistance f z ∂μ) +
      N * Real.log (1 + Real.exp (-t)) := by
  let L := fun z : Fin N → ℝ =>
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z
  let B := fun z : Fin N → ℝ => ε * (∑ i, z i ^ 2) +
    (ε⁻¹ + t) * fieldProjectionDistance f z + N * Real.log (1 + Real.exp (-t))
  have hA : Integrable (fun z : Fin N → ℝ => ε * (∑ i, z i ^ 2)) μ := hM.const_mul ε
  have hD : Integrable (fun z => (ε⁻¹ + t) * fieldProjectionDistance f z) μ :=
    (integrable_fieldProjectionDistance f μ).const_mul (ε⁻¹ + t)
  have hB : Integrable B μ :=
    (hA.add hD).add (integrable_const _)
  have hLmeas : AEStronglyMeasurable L μ := by
    have hc := (continuous_restrictedFieldTerminal Finset.univ Finset.univ_nonempty).sub
      (continuous_restrictedFieldTerminal S hS)
    have heq : (restrictedFieldTerminal Finset.univ - restrictedFieldTerminal S) = L := by
      funext z
      change restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z = _
      rw [restrictedFieldTerminal_univ]
    rw [heq] at hc
    exact hc.aestronglyMeasurable
  have hL : Integrable L μ := by
    apply hB.mono' hLmeas
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (restrictedFieldTerminal_le_univ S hS z))]
    exact field_projection_terminal_loss_linear S hS f hf z t hε
  have hi := integral_mono hL hB (fun z => field_projection_terminal_loss_linear S hS f hf z t hε)
  change (∫ z, L z ∂μ) ≤ _
  calc
    _ ≤ ∫ z, B z ∂μ := hi
    _ = _ := by
      dsimp only [B]
      have ho := integral_add (hA.add hD)
        (integrable_const ((N : ℝ) * Real.log (1 + Real.exp (-t))) (μ := μ))
      have hi := integral_add hA hD
      change (∫ z, ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z +
        N * Real.log (1 + Real.exp (-t)) ∂μ) = _ at ho
      change (∫ z, ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z ∂μ) = _ at hi
      simp only [Pi.add_apply] at ho
      rw [ho, hi, integral_const_mul, integral_const_mul, integral_const]
      simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldProductSpinAveraging
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent endpoint fields followed by their Gibbs spin draws have
the product of the averaged one-site spin laws. This identifies the
projection-distance average appearing in the terminal-loss estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma scalarSpinKernel_atom_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (b : Bool) :
    Integrable (fun z => (scalarSpinKernel z).real {b}) ν := by
  have hm : Measurable (fun z => (scalarSpinKernel z).real {b}) :=
    (scalarSpinKernel.measurable_coe (measurableSet_singleton b)).ennreal_toReal
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have he := ENNReal.toReal_mono
    (measure_ne_top (scalarSpinKernel z) Set.univ)
    (measure_mono (Set.subset_univ ({b} : Set Bool)))
  simpa only [measure_univ, ENNReal.toReal_one, measureReal_def] using he

lemma scalarSpinKernel_average_atom (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : Bool) :
    (∫ z, (scalarSpinKernel z).real {b} ∂ν) = (scalarSpinKernel ∘ₘ ν).real {b} := by
  let A : Bool → ℝ := Set.indicator {b} 1
  have he : (∫ σ, A σ ∂(scalarSpinKernel ∘ₘ ν)) =
      ∫ z, ∫ σ, A σ ∂scalarSpinKernel z ∂ν := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
    rfl
  have hp (z : ℝ) : (∫ σ, A σ ∂scalarSpinKernel z) = (scalarSpinKernel z).real {b} :=
    integral_indicator_one (μ := scalarSpinKernel z) (measurableSet_singleton b)
  simp_rw [hp] at he
  exact he.symm.trans (integral_indicator_one (μ := scalarSpinKernel ∘ₘ ν)
    (measurableSet_singleton b))

theorem field_product_spin_average {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (A : Spin N → ℝ) :
    (∫ z : Fin N → ℝ, ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * A σ ∂Measure.pi ν) =
      ∫ σ : Spin N, A σ ∂Measure.pi (fun i => scalarSpinKernel ∘ₘ ν i) := by
  have hp (σ : Spin N) : Integrable (fun z : Fin N → ℝ =>
      finiteCanonicalWeights (fieldEnergy z) σ) (Measure.pi ν) := by
    have hi := Integrable.fintype_prod_dep (fun i => scalarSpinKernel_atom_integrable (ν i) (σ i))
    simpa only [fieldCanonicalWeights_product] using hi
  rw [integral_finsetSum _ (fun σ _ => (hp σ).mul_const (A σ)), integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_mul_const]
  have he : (∫ z : Fin N → ℝ, finiteCanonicalWeights (fieldEnergy z) σ ∂Measure.pi ν) =
      (∏ i, (scalarSpinKernel ∘ₘ ν i).real {σ i}) := by
    simp_rw [fieldCanonicalWeights_product]
    change (∫ z : Fin N → ℝ, ∏ i,
      (fun y : ℝ => (scalarSpinKernel y).real {σ i}) (z i) ∂Measure.pi ν) = _
    rw [integral_fintype_prod_eq_prod (fun i y => (scalarSpinKernel y).real {σ i})]
    simp_rw [scalarSpinKernel_average_atom]
  rw [he]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockTerminalLoss
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual averaged constrained terminal loss, with constants
independent of the number of Gaussian steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma magnetic_projection_distance_mean {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) :
    (∫ z, fieldProjectionDistance (spinGroupProjection group k hk) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ∑ a, Real.sqrt (spinGroupSize group a) := by
  have he := field_product_spin_average
    (fun i : Fin N => fieldCanonicalEndpointLaw h (magneticBias h (m (group i))))
    (fun σ => (hammingDist σ (spinGroupProjection group k hk σ) : ℝ))
  simp only [← fieldCanonicalSpinLaw_endpoint] at he
  exact he.trans_le (magneticCanonical_projection_distance group k hk m hm hcount h)

theorem magnetic_block_terminal_loss {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal (spinGroupSlice group k) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
          (ε⁻¹ + t) * (∑ a, Real.sqrt (spinGroupSize group a)) +
          N * Real.log (1 + Real.exp (-t)) := by
  have hl := field_projection_mean_loss (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) (spinGroupProjection group k hk)
    (spinGroupProjection_mem group k hk)
    (fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i))))
    (fieldCanonicalVectorLaw_square_integrable h (fun i => magneticBias h (m (group i)))) hε t
  have hM := fieldCanonicalVectorLaw_second_moment h
    (fun i => magneticBias h (m (group i))) hB hH
  have hD := magnetic_projection_distance_mean group k hk m hm hcount h
  exact hl.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hM hε.le)
    (mul_le_mul_of_nonneg_left hD (by positivity))) le_rfl)

lemma sum_sqrt_spinGroupSize_le {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) :
    (∑ a, Real.sqrt (spinGroupSize group a)) ≤ Fintype.card A * Real.sqrt N := by
  calc
    _ ≤ ∑ _a : A, Real.sqrt (N : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show spinGroupSize group a ≤ N from by
        simpa only [spinGroupSize, Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_le (s := (Finset.univ : Finset (Fin N))) (fun i => group i = a))
    _ = _ := by simp

theorem magnetic_block_terminal_loss_size {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal (spinGroupSlice group k) z
      ∂fieldCanonicalVectorLaw N h (fun i => magneticBias h (m (group i)))) ≤
        ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
          (ε⁻¹ + t) * (Fintype.card A * Real.sqrt N) +
          N * Real.log (1 + Real.exp (-t)) :=
  (magnetic_block_terminal_loss group k hk m hm hcount h hB hH hε ht).trans
    (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sum_sqrt_spinGroupSize_le group) (by positivity))) le_rfl)

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

theorem magneticBlockGap_estimate {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) {B H ε t : ℝ} (hB : ∀ i, |magneticBias h (m (group i))| ≤ B)
    (hH : h.height (Fin.last h.depth) ≤ H) (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h ∧
      (N : ℝ)⁻¹ * (∑ i, constrainedFieldValue h (m (group i))) -
        constrainedBlockValue (spinGroupSlice group k) h ≤
      (N : ℝ)⁻¹ * (ε * (N * (2 * Real.exp (2 * B + 4 * H))) +
        (ε⁻¹ + t) * (Fintype.card A * Real.sqrt N) + N * Real.log (1 + Real.exp (-t))) := by
  rw [magneticBlockGap_eq_biasedGap hN group k hk m hm hc]
  have hg := biasedConstrainedBlockValue_gap hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun i => magneticBias h (m (group i)))
  refine ⟨hg.1, hg.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he := magnetic_block_terminal_loss_size group k hk m hm hc h hB hH hε ht
  simpa only [restrictedFieldTerminal_univ] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockError
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite block error vanishes uniformly over field partitions with
bounded final height and magnetizations in a fixed interior interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma normalized_magneticBlockError {N : ℕ} (hN : 0 < N) (C A ε t : ℝ) :
    (N : ℝ)⁻¹ * (ε * (N * C) + (ε⁻¹ + t) * (A * Real.sqrt N) +
      N * Real.log (1 + Real.exp (-t))) =
      ε * C + (ε⁻¹ + t) * A / Real.sqrt N + Real.log (1 + Real.exp (-t)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  field_simp
  linear_combination (ε⁻¹ + t) * A * hs2

lemma log_one_add_exp_neg_tendsto :
    Tendsto (fun t : ℝ => Real.log (1 + Real.exp (-t))) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hh := (tendsto_const_nhds.add he).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa only [add_zero, Real.log_one, Function.comp_apply] using hh

theorem tendsto_zero_of_magneticBlockError (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (C A : ℝ) (hC : 0 < C)
    (hb : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t → ∀ n,
      f n ≤ ε * C + (ε⁻¹ + t) * A / Real.sqrt (N n) + Real.log (1 + Real.exp (-t))) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hf n))
  · intro a ha
    let ε := a / (4 * C)
    have hε : 0 < ε := div_pos ha (by positivity)
    have hεC : ε * C = a / 4 := by dsimp [ε]; field_simp
    obtain ⟨t, ht, htl⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      (log_one_add_exp_neg_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 4)))).exists
    have hi : Tendsto (fun n => (Real.sqrt (N n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))
    have hm : Tendsto (fun n => (ε⁻¹ + t) * A / Real.sqrt (N n)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul ((ε⁻¹ + t) * A)
    filter_upwards [hm.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 4))] with n hn
    have h := hb ε hε t ht n
    rw [hεC] at h
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockConvergence
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual equivalence of constrained and canonical block values along
arbitrarily deep field partitions in a fixed bounded-height region. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

theorem magneticBlockGap_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H) :
    Tendsto (fun n => (N n : ℝ)⁻¹ * (∑ i, constrainedFieldValue (h n) (m n (group n i))) -
      constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n)) atTop (𝓝 0) := by
  let B := magneticUniformBiasBound H r
  let C := 2 * Real.exp (2 * B + 4 * H)
  have hC : 0 < C := mul_pos (by norm_num) (Real.exp_pos _)
  have hB (n : ℕ) (i : Fin (N n)) : |magneticBias (h n) (m n (group n i))| ≤ B :=
    magneticBias_uniform_bound (h n) hr (hm n _) (hH n)
  have hmi (n : ℕ) (a : A) : |m n a| < 1 := (hm n a).trans_lt hr
  let f := fun n => (N n : ℝ)⁻¹ * (∑ i, constrainedFieldValue (h n) (m n (group n i))) -
    constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n)
  have hf (n : ℕ) : 0 ≤ f n :=
    (magneticBlockGap_estimate (hN n) (group n) (k n) (hk n) (m n)
      (hmi n) (hc n) (h n) (hB n) (hH n) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 0)).1
  apply tendsto_zero_of_magneticBlockError N hNlim f hf C (Fintype.card A) hC
  intro ε hε t ht n
  have he := (magneticBlockGap_estimate (hN n) (group n) (k n) (hk n) (m n)
    (hmi n) (hc n) (h n) (hB n) (hH n) hε ht).2
  rw [normalized_magneticBlockError (hN n)] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticLevelModulus
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The overlap modulus is uniform in the root bias, including the
optimizing bias for a prescribed magnetization. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal
namespace InvariantIsing

lemma magneticLevelAtBias_increment_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i : Fin h.depth) :
    magneticLevelAtBias h b i.succ - magneticLevelAtBias h b i.castSucc ≤
      (h.height i.succ - h.height i.castSucc) * fieldGaussianMomentCap (Real.sqrt V) := by
  let L := scalarFieldIncrements h
  let j : Fin L.length := Fin.cast (scalarFieldIncrements_length h).symm i
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ L, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut k.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hvar : ∀ av ∈ L, (av.2 : ℝ) ≤ V := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    exact (fieldIncrement_le_last h k.succ).trans hV
  have hget : ((L.get j).2 : ℝ) = h.height i.succ - h.height i.castSucc := by
    have hg : L.get j = ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
      exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
        NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) j
    rw [hg]
    change (fieldIncrement h i.succ).2 = _
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
    rfl
  have hval := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hreg := fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hbnd (i : Fin (L.length+1)) (z : ℝ) :
      |fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i z| ≤ 1 := by
    rw [abs_of_nonneg ((hreg i).2 z).1]
    exact ((hreg i).2 z).2
  change fieldSpinTransition 0 _ _
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.succ) b -
    fieldSpinTransition 0 _ _
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.castSucc) b ≤ _
  rw [← fieldSpinTransition_sub 0 _ hval.1 hval.2
    (hreg j.succ).1 (hreg j.castSucc).1 (hbnd j.succ) (hbnd j.castSucc)]
  calc
    _ ≤ fieldSpinTransition 0 _ (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
        (fun _ => ((L.get j).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V)) b :=
      fieldSpinTransition_mono_test 0 _ _
        ((hreg j.succ).1.sub (hreg j.castSucc).1) measurable_const
        (fun z => (abs_sub _ _).trans (add_le_add (hbnd j.succ z) (hbnd j.castSucc z)))
        (fun _ => le_rfl) (fieldScalarSquares_increment_le L hL hζ hvar j) b
    _ = _ := by rw [fieldSpinTransition_const 0 _ hval.1 hval.2, hget]

theorem magneticLevelAtBias_sub_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V)
    (i j : Fin (h.depth + 1)) (hij : i ≤ j) :
    magneticLevelAtBias h b j - magneticLevelAtBias h b i ≤
      (h.height j - h.height i) * fieldGaussianMomentCap (Real.sqrt V) := by
  have hm : Monotone (fun i => h.height i * fieldGaussianMomentCap (Real.sqrt V) -
      magneticLevelAtBias h b i) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have hk := magneticLevelAtBias_increment_le h b hV k
    nlinarith
  have hh := hm hij
  nlinarith

theorem magneticLevelAtBias_abs_sub_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i j : Fin (h.depth + 1)) :
    |magneticLevelAtBias h b i - magneticLevelAtBias h b j| ≤
      |h.height i - h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (magneticLevelAtBias_monotone h b hij)), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr (h.ordered_height hij)), neg_sub]
    exact magneticLevelAtBias_sub_le h b hV i j hij
  · rw [abs_of_nonneg (sub_nonneg.mpr (magneticLevelAtBias_monotone h b hji)),
      abs_of_nonneg (sub_nonneg.mpr (h.ordered_height hji))]
    exact magneticLevelAtBias_sub_le h b hV j i hji


lemma magneticFieldLevel_abs_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (s : ℝ) (i j : Fin (h.depth+1)) :
    |magneticFieldLevel h s i - magneticFieldLevel h s j| ≤
      |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) :=
  magneticLevelAtBias_abs_sub_le h (magneticBias h s) hV i j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockModulus
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height continuity after block averaging, uniformly in block size
and in every optimizing root bias. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal
namespace InvariantIsing

lemma magneticBlockLevel_abs_sub_le {N : ℕ} (hN : 0 < N) (h : FieldStep)
    {V : ℝ} (hV : h.height (Fin.last h.depth) ≤ V) (m : Fin N → ℝ)
    (i j : Fin (h.depth+1)) :
    |magneticBlockLevel h m i-magneticBlockLevel h m j| ≤
      |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  unfold magneticBlockLevel
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ k, |magneticFieldLevel h (m k) i-magneticFieldLevel h (m k) j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ _k : Fin N,
        |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => magneticFieldLevel_abs_sub_le h hV (m k) i j) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

lemma magneticBlockPath_on_cell {N : ℕ} (hN : 0 < N) (h : FieldStep) (m : Fin N → ℝ)
    (i : Fin (h.depth+1)) {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    magneticBlockPath hN h m s = magneticBlockLevel h m i :=
  fieldLevelPath_on_cell h _ _ _ i hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMagneticBlockModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic ties and weak-to-L1 consistency for magnetic block
paths with varying block size and prescribed magnetizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

lemma cavityStrictUniformField_magneticBlock_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {N : ℕ} (hN : 0 < N) (mag : Fin N → ℝ) (p : OverlapPath) (n : ℕ) (i j : Fin (n + 1)) :
    |magneticBlockLevel (cavityStrictUniformField rho lam hrho hsum p n) mag i -
      magneticBlockLevel (cavityStrictUniformField rho lam hrho hsum p n) mag j| ≤
      (4 * K^2 * |cavityStrictUniformLevels p n i - cavityStrictUniformLevels p n j|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2)) := by
  have hb := magneticBlockLevel_abs_sub_le hN
    (cavityStrictUniformField rho lam hrho hsum p n)
    (cavityStrictUniformField_height_le rho lam hrho hsum hK hlam p n (Fin.last n)) mag i j
  refine hb.trans (mul_le_mul_of_nonneg_right ?_
    (fieldGaussianMomentCap_nonneg (Real.sqrt_nonneg _)))
  exact cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) _ _


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapTestTransport
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 replacement transports the physical constrained overlap tests
to the magnetic block paths used in the variational problem. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

lemma integrable_overlap_weighted_test (q a : OverlapPath) (Φ : ℝ →ᵇ ℝ) :
    Integrable (fun s => Φ (q s)*(a s-q s)) pathMeasure := by
  apply integrable_of_measurable_abs_le
    ((Φ.continuous.measurable.comp q.measurable).mul (a.measurable.sub q.measurable))
  intro s
  change |Φ (q s)*(a s-q s)| ≤ ‖Φ‖
  rw [abs_mul]
  have hd : |a s-q s| ≤ 1 := abs_le.mpr
    ⟨by linarith [a.nonneg s,q.le_one s], by linarith [a.le_one s,q.nonneg s]⟩
  exact (mul_le_mul (Φ.norm_coe_le_norm _) hd (abs_nonneg _) (norm_nonneg Φ)).trans_eq (mul_one _)

lemma overlap_weighted_test_sub_le (q a b : OverlapPath) (Φ : ℝ →ᵇ ℝ) :
    |(∫ s, Φ (q s)*(a s-q s) ∂pathMeasure) -
      ∫ s, Φ (q s)*(b s-q s) ∂pathMeasure| ≤
      ‖Φ‖ * ∫ s, |a s-b s| ∂pathMeasure := by
  rw [← integral_sub (integrable_overlap_weighted_test q a Φ)
    (integrable_overlap_weighted_test q b Φ)]
  have he : (fun s => Φ (q s)*(a s-q s)-Φ (q s)*(b s-q s)) =
      (fun s => Φ (q s)*(a s-b s)) := by funext s; ring
  rw [he]
  calc
    _ ≤ ∫ s, |Φ (q s)*(a s-b s)| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, ‖Φ‖ * |a s-b s| ∂pathMeasure := by
      apply integral_mono
      · have hi := (integrable_overlap_weighted_test q a Φ).sub
          (integrable_overlap_weighted_test q b Φ)
        change Integrable (fun s => Φ (q s)*(a s-q s)-Φ (q s)*(b s-q s)) pathMeasure at hi
        rw [he] at hi
        exact hi.abs
      · exact (a.integrable.sub b.integrable).abs.const_mul _
      · intro s
        change |Φ (q s)*(a s-b s)| ≤ ‖Φ‖ * |a s-b s|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (Φ.norm_coe_le_norm _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem overlap_weighted_test_l1_transport (q a b : ℕ → OverlapPath)
    (hab : Tendsto (fun n => ∫ s, |a n s-b n s| ∂pathMeasure) atTop (𝓝 0))
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n => (∫ s, Φ (q n s)*(a n s-q n s) ∂pathMeasure) -
      ∫ s, Φ (q n s)*(b n s-q n s) ∂pathMeasure) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hab.const_mul ‖Φ‖)
  simpa only [Real.norm_eq_abs] using overlap_weighted_test_sub_le (q n) (a n) (b n) Φ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySlowDepth
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing system sizes fast enough for a prescribed sequence of finite
cascade depths. Each row requires only finitely many error estimates. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

private lemma cavityDiagonalIndex_ge (M : ℕ → ℕ) (r : ℕ) : M r ≤ cavityDiagonalIndex M r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact le_max_right _ _

private lemma cavityDiagonalIndex_strict (M : ℕ → ℕ) : StrictMono (cavityDiagonalIndex M) := by
  apply strictMono_nat_of_lt_succ
  intro r
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

lemma cavity_choose_diagonal_errors (F : ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ r j, Tendsto (fun k => F r k j) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun r => F r (φ r) j) atTop (𝓝 0) := by
  have hrow r : ∃ M : ℕ, ∀ k≥M, ∀ j ≤ r, |F r k j|<1/((r : ℝ)+1) := by
    have he : 0<1/((r : ℝ)+1) := by positivity
    have hall : ∀ᶠ k in atTop, ∀ j : Fin (r+1), |F r k j|<1/((r : ℝ)+1) := by
      apply eventually_all.mpr
      intro j
      have ha : Tendsto (fun k => |F r k j|) atTop (𝓝 0) := by
        simpa only [abs_zero] using (hF r j).abs
      exact ha.eventually (gt_mem_nhds he)
    obtain ⟨M,hM⟩ := eventually_atTop.mp hall
    refine ⟨M, fun k hk j hj => ?_⟩
    exact hM k hk ⟨j, by omega⟩
  choose M hM using hrow
  let φ := cavityDiagonalIndex M
  refine ⟨φ, cavityDiagonalIndex_strict M, ?_⟩
  intro j
  apply squeeze_zero_norm' _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop j] with r hr
  rw [Real.norm_eq_abs]
  exact (hM r (φ r) (cavityDiagonalIndex_ge M r) j hr).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapTestDiagonal
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single diagonal of finite cavity depths works for every continuous
overlap test. Compactness is used only on the overlap interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

lemma compactOverlapTestExtension_apply (f : CompactOverlapTest) (q : OverlapPath) (s : ℝ) :
    compactOverlapTestExtension f (q s) = f ⟨q s,q.nonneg s,q.le_one s⟩ := by
  simp only [compactOverlapTestExtension, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    Set.projIcc_of_mem zero_le_one ⟨q.nonneg s,q.le_one s⟩]

lemma compact_overlap_test_difference_le (f g : CompactOverlapTest) (q B : OverlapPath) :
    |(∫ s, compactOverlapTestExtension f (q s)*(B s-q s) ∂pathMeasure) -
      ∫ s, compactOverlapTestExtension g (q s)*(B s-q s) ∂pathMeasure| ≤ ‖f-g‖ := by
  rw [← integral_sub (integrable_overlap_weighted_test q B (compactOverlapTestExtension f))
    (integrable_overlap_weighted_test q B (compactOverlapTestExtension g))]
  have hb := norm_integral_le_of_norm_le_const (μ := pathMeasure) (C := ‖f-g‖)
    (f := fun s => compactOverlapTestExtension f (q s)*(B s-q s) -
      compactOverlapTestExtension g (q s)*(B s-q s)) (ae_of_all _ fun s => by
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, compactOverlapTestExtension_apply,
          compactOverlapTestExtension_apply]
        have hf : |f ⟨q s,q.nonneg s,q.le_one s⟩-g ⟨q s,q.nonneg s,q.le_one s⟩| ≤ ‖f-g‖ :=
          (f-g).norm_coe_le_norm _
        have hd : |B s-q s| ≤ 1 := abs_le.mpr
          ⟨by linarith [B.nonneg s,q.le_one s],by linarith [B.le_one s,q.nonneg s]⟩
        exact (mul_le_mul hf hd (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hb

theorem exists_diagonal_overlap_tests (q B : ℕ → ℕ → OverlapPath)
    (htest : ∀ n (Φ : ℝ →ᵇ ℝ), Tendsto
      (fun k => ∫ s, Φ (q n k s)*(B n k s-q n k s) ∂pathMeasure) atTop (𝓝 0)) :
    ∃ d : ℕ → ℕ, StrictMono d ∧ ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (q n (d n) s)*(B n (d n) s-q n (d n) s) ∂pathMeasure)
      atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq CompactOverlapTest
  let F := fun n k j => ∫ s, compactOverlapTestExtension (u j) (q n k s)*
    (B n k s-q n k s) ∂pathMeasure
  obtain ⟨d, hd, hlim⟩ := cavity_choose_diagonal_errors F
    (fun n j => htest n (compactOverlapTestExtension (u j)))
  refine ⟨d, hd, ?_⟩
  intro Φ
  let f : CompactOverlapTest := ⟨fun x => Φ x, Φ.continuous.comp continuous_subtype_val⟩
  have he n : (∫ s, Φ (q n (d n) s)*(B n (d n) s-q n (d n) s) ∂pathMeasure) =
      ∫ s, compactOverlapTestExtension f (q n (d n) s)*
        (B n (d n) s-q n (d n) s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [] with s
    rw [compactOverlapTestExtension_apply]
    rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hu.exists_dist_lt f (half_pos hε)
  have hj' : ‖f-u j‖ < ε/2 := by simpa only [dist_eq_norm] using hj
  have ht := (hlim j).eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  filter_upwards [ht] with n hn
  rw [he, Real.dist_eq, sub_zero]
  have hn' : |F n (d n) j| < ε/2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hn
  have hb := compact_overlap_test_difference_le f (u j) (q n (d n)) (B n (d n))
  have ha := abs_add_le
    ((∫ s, compactOverlapTestExtension f (q n (d n) s)*
      (B n (d n) s-q n (d n) s) ∂pathMeasure)-F n (d n) j) (F n (d n) j)
  rw [sub_add_cancel] at ha
  change |(∫ s, compactOverlapTestExtension f (q n (d n) s)*
    (B n (d n) s-q n (d n) s) ∂pathMeasure)-F n (d n) j| ≤ ‖f-u j‖ at hb
  linarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMagneticDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The magnetic overlap argument permits the base quantile and the
finite depth to vary together with the constrained block size. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem cavity_magnetic_diagonal_asymptotic_ties {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N depth : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ)
    (base : ℕ → OverlapPath) (p : OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto
      (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s))) :
    ∃ D : Set ℝ, (∀ᵐ s ∂pathMeasure, s ∈ D) ∧
      ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
        Tendsto (fun n =>
          magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) x -
          magneticBlockPath (hN n) (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) y)
          atTop (𝓝 0) := by
  let D := {s | Tendsto (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s)) ∧
    ∀ n, ∃ i : Fin (depth n + 1), s ∈ Ioo (uniformCut (depth n) i.castSucc) (uniformCut (depth n) i.succ)}
  have hD : ∀ᵐ s ∂pathMeasure, s ∈ D := by
    filter_upwards [hq, ae_all_iff.mpr (fun n => ae_finite_overlap_cell
      (uniformCut (depth n)) (uniformCut_zero (depth n)) (uniformCut_last (depth n)))] with s hs hc
    exact ⟨hs, hc⟩
  refine ⟨D, hD, ?_⟩
  intro x hx y hy hxy
  have hlim : Tendsto (fun n =>
      (4 * K^2 * |cavityStrictUniformPath (base n) (depth n) x -
        cavityStrictUniformPath (base n) (depth n) y|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2))) atTop (𝓝 0) := by
    have hh := ((hx.1.sub hy.1).abs.const_mul (4 * K^2)).mul_const
      (fieldGaussianMomentCap (Real.sqrt (4 * K^2)))
    simpa only [hxy, sub_self, abs_zero, mul_zero, zero_mul] using hh
  apply squeeze_zero_norm (fun n => ?_) hlim
  obtain ⟨i, hi⟩ := hx.2 n
  obtain ⟨j, hj⟩ := hy.2 n
  rw [Real.norm_eq_abs,
    magneticBlockPath_on_cell (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) i hi,
    magneticBlockPath_on_cell (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) j hj,
    cavityStrictUniformPath_on_cell (base n) (depth n) i hi,
    cavityStrictUniformPath_on_cell (base n) (depth n) j hj]
  exact cavityStrictUniformField_magneticBlock_dist_le rho lam hrho hsum hK hlam
    (hN n) (mag n) (base n) (depth n) i j

theorem cavity_magnetic_diagonal_self_consistency {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (N depth : ℕ → ℕ) (hN : ∀ r, 0 < N r) (mag : (r : ℕ) → Fin (N r) → ℝ)
    (base : ℕ → OverlapPath) (p : OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto
      (fun n => cavityStrictUniformPath (base n) (depth n) s) atTop (𝓝 (p s)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun n =>
      ∫ s, Φ (cavityStrictUniformPath (base n) (depth n) s) *
        (magneticBlockPath (hN n)
          (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) s -
          cavityStrictUniformPath (base n) (depth n) s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s,
      |magneticBlockPath (hN n)
        (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n) s - p s|
        ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨D, hD, htied⟩ := cavity_magnetic_diagonal_asymptotic_ties
    rho lam hrho hsum hK hlam N depth hN mag base p hq
  apply cavity_self_consistency_asymptotic_l1_on p
    (fun n => magneticBlockPath (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n)) D hD htied
  intro Φ
  have hh := (cavity_rounding_test_difference p
    (fun n => cavityStrictUniformPath (base n) (depth n))
    (fun n => magneticBlockPath (hN n)
      (cavityStrictUniformField rho lam hrho hsum (base n) (depth n)) (mag n)) hq Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using hh

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

lemma cavityPrefixAffineFullGroup_eq {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (d r : ℕ) :
    cavityPrefixAffineFullGroup s c hsum d r=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r+n) := by
  symm
  apply cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+1+(d+n+3)) _
  dsimp only [cavityPrefixAffineSize]
  ring

lemma cavityPrefixAffineBase_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityPrefixAffineSize n (d+n+3) c r)) :
    Sum.elim (fun w => w.1) g ((cavityPrefixAffineBaseEquiv s c hs hsum g hg r).symm i)=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r) i := by
  rw [cavityPrefixAffineLabel_progression hm s c hsum hn]
  change Sum.elim _ g ((cavityOrderedBase _ g _).symm i)=_
  rw [cavityOrderedBase_label]
  have hcount : cavityBaseGroupDimension (cavityAffineRetained n d s c r) g=
      cavityAffineCount s c (d+n+3) r := by
    funext a
    exact cavityAffineBase_dimension s c hs hsum g hg r a
  simp only [hcount]

lemma cavityPrefixAffineBase_canonical_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityPrefixAffineSize n (d+n+3) c r)) :
    ((cavityBaseGroupEquiv (cavityAffineRetained n d s c r)
      (cavityPrefixAffineBaseEquiv s c hs hsum g hg r) g).symm i).1=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r) i :=
  (cavityBaseGroupEquiv_label _ _ _ i).trans (cavityPrefixAffineBase_label hm s c hs hsum hn g hg r i)

lemma cavityPrefixAffineBase_partition {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) :
    cavityBaseGroup (cavityAffineRetained n d s c r) (cavityPrefixAffineBaseEquiv s c hs hsum g hg r) g=
      cavitySpectralGroup (cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r)) := by
  funext a
  apply Finset.ext
  intro i
  simp only [cavityBaseGroup, cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
    cavityPrefixAffineBase_label hm s c hs hsum hn g hg r i]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetAffineSubsequenceTrial
attribute [-instance] _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational physical trial construction along any increasing selection of dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem offset_affine_subsequence_trial_witness
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0<n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (lam : Fin m → ℝ) (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (ι : ℕ → ℕ) (hι : StrictMono ι)
    (u : (r : ℕ) → Fin (cavityPrefixAffineSize n (m*n-n+n+3) c r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j∈Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      let M := cavityPrefixAffineSize n (m*n-n+n+3) c r
      let g := cavityAffineLabel (by omega : 0 < m) s c hsum M
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have hh := cavityRationalSize_ge_three n (m*n-n) r hn
        exact lt_of_lt_of_le (by norm_num : 0<3)
          (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
        (restrictedZeroTreePrior (offsetBlockConstraint (r+(m*n-n+n+3)) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) (u r) (v r) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (by
        have hh := cavityRationalSize_ge_three n (m*n-n) r hn
        exact lt_of_lt_of_le (by norm_num : 0<3)
          (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
        (restrictedZeroTreePrior (offsetBlockConstraint (r+(m*n-n+n+3)) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) u' v') :
    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
      Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
        (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r) t-cavityStrictUniformPath p r t) ∂pathMeasure)
        atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r)+
        fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r)/2+
        spectralFunctional (finiteR (fun a => (s a : ℝ)/n) lam
          (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))
          (cavityStrictUniformPath p r)-
        (n : ℝ)⁻¹*(affineRestrictedIncrement hm hn s c hsum R hR Cset hCset μ lam u v (ι (φ r))+
          (Real.log Cset.card-n*Real.log 2)) < ε := by
  let d := m*n-n
  let q := d+n+3
  let N := fun r => (∑ a, c a)+(ι r+q)*n
  let ρ := fun j => (s j : ℝ)/n
  have hm0 : 0 < m := by omega
  have hρ j : 0 < ρ j := cavityRationalMass_positive s hs hn j
  have hρsum : ∑ j, ρ j=1 := cavityRationalMass_sum s hsum hn
  obtain ⟨hd,es,a₀,B₀,hcounts,hB₀,hperp⟩ := cavity_rational_auxiliary_geometry hm hn s hs hsum
  let k := fun r => cavityAffineRetained n d s c (ι r)
  let e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r) :=
    fun r => cavityPrefixAffineBaseEquiv s c hs hsum a₀ hcounts (ι r)
  let gf := fun r => cavityPrefixAffineFullGroup s c hsum d (ι r)
  let l := fun r j => cavityOrderedStart (cavityAffineCount s c q (ι r+1)) j
  let w := fun r j => l r j+cavityAffineCount s c q (ι r+1) j
  have hN r : 3 ≤ N r := (cavityRationalSize_ge_three n d (ι r) hn).trans (Nat.le_add_left _ _)
  have hNl : Tendsto N atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_add_left _ _)
    ((cavityRationalDimension_tendsto n q hn).comp hι.tendsto_atTop)
  have hk r j : d ≤ k r j := cavityAffineRetained_ge s c hs (ι r) j
  have hdim r j : cavityBaseGroupDimension (k r) a₀ j=cavityAffineCount s c q (ι r) j :=
    cavityAffineBase_dimension s c hs hsum a₀ hcounts (ι r) j
  have hgroups r j : 0 < cavityBaseGroupDimension (k r) a₀ j := by
    rw [hdim]
    exact (cavityRationalCount_positive s hs (by omega) (ι r) j).trans_le (Nat.le_add_right _ _)
  have hdims j : Tendsto (fun r => cavityBaseGroupDimension (k r) a₀ j) atTop atTop := by
    simpa only [hdim, Function.comp_def] using (cavityAffineCount_tendsto s c hs q j).comp hι.tendsto_atTop
  have hmasslim : Tendsto (fun r j => (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have hh := (cavityAffineCount_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
    simpa only [hdim, N, cavityAffineSize, Nat.add_comm, Function.comp_def] using hh
  have hc : 0 < (1:ℝ)/(n+∑ a, c a : ℕ) := by
    apply div_pos zero_lt_one
    exact_mod_cast (show 0 < n+∑ a, c a by omega)
  have hfrac r j : (1:ℝ)/(n+∑ a, c a : ℕ) ≤ (cavityBaseGroupDimension (k r) a₀ j : ℝ)/N r := by
    rw [hdim]
    simpa only [N, cavityAffineSize, Nat.add_comm] using
      cavityAffineMass_lower s c hs hn (q := q) (by omega) (ι r) j
  have hwindow r j i : gf r i=j ↔ l r j ≤ i.val ∧ i.val < w r j :=
    cavityOrderedGroup_window _ _ j i
  have hln r j : l r j+n ≤ w r j :=
    cavityAffineFullWindow_size s c hs (by omega) (ι r) j
  have hw r j : w r j ≤ N r+n :=
    cavityOrderedStart_add_le (cavityAffineCount s c q (ι r+1))
      (cavityPrefixAffineFull_sum s c hsum q (ι r)) j ((cavityRationalCount_positive s hs (by omega) (ι r+1) j).trans_le (Nat.le_add_right _ _))
  have hl j : Tendsto (fun r => (l r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j : ℝ)/n)) := by
    simpa only [l, N, cavityAffineSize, Function.comp_def, Nat.add_comm] using
      (cavityAffineFullStart_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
  have hwlim j : Tendsto (fun r => (w r j : ℝ)/(N r+n)) atTop
      (𝓝 ((cavityOrderedStart s j+s j : ℝ)/n)) := by
    simpa only [w, l, N, cavityAffineSize, Function.comp_def, Nat.add_comm, Nat.cast_add, add_comm] using
      (cavityAffineFullEnd_ratio s c hn (q := q) (by omega) j).comp hι.tendsto_atTop
  have hK r : 2≤ι r+q := by dsimp only [q]; omega
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  let : ∀ r, IsProbabilityMeasure (μ (N r+n)) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : ∀ r, (μ (N r+n)).IsMulRightInvariant := fun _ => inferInstance
  let : ∀ r, IsProbabilityMeasure (μ (N r)) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : ∀ r, (μ (N r)).IsMulRightInvariant := fun _ => inferInstance
  have HH := offset_window_minimum_trial_witness hhaar hgauss hpub (fun r => ι r+q) hK
    ((tendsto_add_atTop_nat q).comp hι.tendsto_atTop) R hR Cset hCset
    (fun r => (show 0<(∑ a, c a)+(ι r+q)*n from by
      simpa only [N, cavityPrefixAffineSize, q, d] using
        (lt_of_lt_of_le (by norm_num : 0<3) (hN r)))) hNl hN gf k
    (fun r => cavityPrefixAffineRetainedEquiv s c hs hsum d (ι r)) e es B₀ a₀ hk
    (fun r a => μ (cavityBaseGroupDimension (k r) a₀ a)) l w hwindow hln hw
    (fun r => μ (N r+n)) (fun r => μ (N r)) (fun _ => θ) lam (fun r => v (ι r)) (fun r => hv (ι r))
    (fun r => u (ι r)) (fun r => hu (ι r)) (by
      intro r u' v' hu' hv'
      have hh := hmin (ι r) u' v' hu' hv'
      have heq (i : Fin (N r)) :
          ((cavityBaseGroupEquiv (k r) (e r) a₀).symm i).1=
            cavityAffineLabel hm0 s c hsum (N r) i :=
        cavityPrefixAffineBase_canonical_label hm0 s c hs hsum hn a₀ hcounts (ι r) i
      simp_rw [heq]
      exact hh)
    hd hn hB₀ ρ hρ hρsum (fun a => (cavityOrderedStart s a : ℝ)/n)
    (fun a => (cavityOrderedStart s a+s a : ℝ)/n)
    (funext fun a => (cavityRationalMass_difference s a).symm)
    (fun a => (cavityAffineEnd_tendsto s c hs q a).comp
      ((tendsto_add_atTop_nat 1).comp hι.tendsto_atTop))
    (fun a => (cavityAffineStart_alternative s c hs q a).imp
      (fun ha r => ha (ι r+1))
      (fun ha => ha.comp ((tendsto_add_atTop_nat 1).comp hι.tendsto_atTop)))
    (fun a => by simpa only [N, cavityPrefixAffineSize, Nat.cast_add, q, d] using hl a)
    (fun a => by simpa only [N, cavityPrefixAffineSize, Nat.cast_add, q, d] using hwlim a)
    hperp hgroups hdims hc hfrac hmasslim amax hmax s
    (cavityRationalCount_le_total s hsum) hcounts (fun a => by dsimp only [ρ]; field_simp)
  obtain ⟨p,φ,hφ,hself,htrial⟩ := HH
  refine ⟨p,φ,hφ,hself,?_⟩
  intro ε hε
  filter_upwards [htrial ε hε] with r hr
  have hf : gf (φ r)=cavityAffineLabel hm0 s c hsum (N (φ r)+n) :=
    cavityPrefixAffineFullGroup_eq hm0 s c hsum hn d (ι (φ r))
  have hb' (i : Fin (N (φ r))) :
      Sum.elim (fun w => w.1) a₀ ((e (φ r)).symm i)=cavityAffineLabel hm0 s c hsum (N (φ r)) i :=
    cavityPrefixAffineBase_label hm0 s c hs hsum hn a₀ hcounts (ι (φ r)) i
  have hp : cavityBaseGroup (k (φ r)) (e (φ r)) a₀=
      cavitySpectralGroup (cavityAffineLabel hm0 s c hsum (N (φ r))) :=
    cavityPrefixAffineBase_partition hm0 s c hs hsum hn a₀ hcounts (ι (φ r))
  have heig : (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e (φ r)).symm i))) =
      (fun i => lam (cavityAffineLabel hm0 s c hsum (N (φ r)) i)) :=
    funext fun i => congrArg lam (hb' i)
  rw [hf,hp,heig] at hr
  exact hr

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
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

lemma average_grouped_sites {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ f : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) :
    (N : ℝ)⁻¹ * (∑ j, f (group j)) = ∑ a, γ a * f a := by
  rw [sum_grouped_sites, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hcount a]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

lemma magneticGroupValue_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) (h : FieldStep) :
    (N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (mag (group j))) =
      magneticGroupValue γ mag h :=
  average_grouped_sites hN group γ (fun a => constrainedFieldValue h (mag a)) hcount

lemma magneticGroupLevel_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a)
    (h : FieldStep) (i : Fin (h.depth+1)) :
    magneticBlockLevel h (fun j => mag (group j)) i = magneticGroupLevel γ mag h i :=
  average_grouped_sites hN group γ (fun a => magneticFieldLevel h (mag a) i) hcount

lemma magneticGroupPath_eq_block {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ) = N * γ a) (h : FieldStep) :
    magneticBlockPath hN h (fun j => mag (group j)) = magneticGroupPath γ mag hγ hγsum h := by
  apply (show Function.Injective OverlapPath.val from by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl)
  funext t
  exact magneticGroupLevel_eq_block hN group γ mag hcount h (fieldLevelIndex h t)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupConsistency
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform block replacement turns constrained self-consistency into
the weighted magnetic self-consistency used by the entropy supremum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_group_l1_of_block_consistency {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ) = N r * γ a)
    {s H : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag a)/2))
    (h : ℕ → FieldStep) (hH : ∀ r, (h r).height (Fin.last (h r).depth) ≤ H)
    (p : OverlapPath)
    (hself : Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (h r) t-p t| ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ t, |magneticGroupPath γ mag hγ hγsum (h r) t-p t| ∂pathMeasure)
      atTop (𝓝 0) := by
  let a := fun r => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) (h r)
  let b := fun r => magneticGroupPath γ mag hγ hγsum (h r)
  have hab := magneticBlockPath_l1_tendsto N hN hNlim group k hk (fun _ => mag) hs
    (fun _ => hmag) hc h hH
  have he r : magneticBlockPath (hN r) (h r) (fun j => mag (group r j)) = b r :=
    magneticGroupPath_eq_block (hN r) (group r) γ mag hγ hγsum (hcount r) (h r)
  simp_rw [he] at hab
  have hz : Tendsto (fun r => (∫ t, |a r t-b r t| ∂pathMeasure)+
      ∫ t, |a r t-p t| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [add_zero] using hab.add hself
  apply squeeze_zero (fun r => integral_nonneg (fun t => abs_nonneg _)) (fun r => ?_) hz
  calc
    (∫ t, |b r t-p t| ∂pathMeasure) ≤
        ∫ t, (|a r t-b r t|+|a r t-p t|) ∂pathMeasure := by
      apply integral_mono ((b r).integrable.sub p.integrable).abs
        (((a r).integrable.sub (b r).integrable).abs.add (((a r).integrable.sub p.integrable).abs))
      intro t
      change |b r t-p t| ≤ |a r t-b r t|+|a r t-p t|
      simpa only [abs_sub_comm (b r t) (a r t)] using abs_sub_le (b r t) (a r t) (p t)
    _ = _ := integral_add ((a r).integrable.sub (b r).integrable).abs
      ((a r).integrable.sub p.integrable).abs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockTrialLower
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original constrained block trial attains the magnetic
variational lower bound once its physical overlap is self-consistent. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_block_trial_eventually_lower {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ) = N r * γ a)
    {s H : ℝ} (hs : s<1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a*((1+mag a)/2))
    (h : ℕ → FieldStep) (hH : ∀ r, (h r).height (Fin.last (h r).depth) ≤ H)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hself : Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (h r) t-p t| ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun r => ∫ t, |q r t-p t| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε>0, ∀ᶠ r in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal-ε ≤
        constrainedBlockValue (spinGroupSlice (group r) (k r)) (h r)+
          fieldPairing (q r) (h r)/2+spectralFunctional (finiteR ρ eig hρ hsum) (q r) := by
  have hgroup := magnetic_group_l1_of_block_consistency N hN hNlim group k hk γ mag
    hγ hγsum hcount hs hmag hc h hH p hself
  have hlower := magnetic_entropy_trial_eventually_lower ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).trans_lt hs) p q h hH hgroup hq
  have hgap := magneticBlockGap_tendsto N hN hNlim group k hk (fun _ => mag) hs
    (fun _ => hmag) hc h hH
  have he r : (N r : ℝ)⁻¹*(∑ j, constrainedFieldValue (h r) (mag (group r j))) =
      magneticGroupValue γ mag (h r) :=
    magneticGroupValue_eq_block (hN r) (group r) γ mag (hcount r) (h r)
  simp_rw [he] at hgap
  intro ε hε
  filter_upwards [hlower (ε/2) (half_pos hε),
    hgap.eventually (Iio_mem_nhds (half_pos hε))] with r hr hgapr
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticDiagonalL1Consistency
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained block overlap converges in L1 along a diagonal of growing blocks and varying base quantiles,
from its physical weak tests and almost-everywhere quantile convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_diagonal_l1_of_constrained_tests {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (mag : ℕ → A → ℝ)
    {s : ℝ} (hs : s < 1) (hmag : ∀ r a, |mag r a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag r a)/2))
    (base : ℕ → OverlapPath) (depth : ℕ → ℕ) (p : OverlapPath)
    (hq : ∀ᵐ t ∂pathMeasure, Tendsto
      (fun r => cavityStrictUniformPath (base r) (depth r) t) atTop (𝓝 (p t)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath (base r) (depth r) t) *
      (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
        (spinGroupSlice_nonempty (group r) (k r) (hk r))
        (cavityStrictUniformField rho lam hrho hsum (base r) (depth r)) t - cavityStrictUniformPath (base r) (depth r) t)
      ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (cavityStrictUniformField rho lam hrho hsum (base r) (depth r)) t-p t| ∂pathMeasure) atTop (𝓝 0) := by
  let h := fun r => cavityStrictUniformField rho lam hrho hsum (base r) (depth r)
  let a := fun r => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) (h r)
  let b := fun r => magneticBlockPath (hN r) (h r) (fun j => mag r (group r j))
  have hab := magneticBlockPath_l1_tendsto N hN hNlim group k hk mag hs hmag hc h
    (fun r => cavityStrictUniformField_height_le rho lam hrho hsum hK hlam (base r) (depth r) (Fin.last (depth r)))
  have hab' : Tendsto (fun r => ∫ t, |b r t-a r t| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using hab
  have hb : Tendsto (fun r => ∫ t, |b r t-p t| ∂pathMeasure) atTop (𝓝 0) := by
    apply cavity_magnetic_diagonal_self_consistency rho lam hrho hsum hK hlam N depth hN
      (fun r j => mag r (group r j)) base p hq
    intro Φ
    have hd := overlap_weighted_test_l1_transport (fun r => cavityStrictUniformPath (base r) (depth r)) b a hab' Φ
    have ht := hd.add (htest Φ)
    simpa only [a, b, h, sub_add_cancel, add_zero] using ht
  have hz : Tendsto (fun r => (∫ t, |a r t-b r t| ∂pathMeasure) +
      ∫ t, |b r t-p t| ∂pathMeasure) atTop (𝓝 0) := by simpa using hab.add hb
  apply squeeze_zero (fun r => integral_nonneg (fun t => abs_nonneg _)) (fun r => ?_) hz
  calc
    (∫ t, |a r t-p t| ∂pathMeasure) ≤ ∫ t, (|a r t-b r t|+|b r t-p t|) ∂pathMeasure :=
      integral_mono ((a r).integrable.sub p.integrable).abs
        (((a r).integrable.sub (b r).integrable).abs.add (((b r).integrable.sub p.integrable).abs))
        (fun t => abs_sub_le (a r t) (b r t) (p t))
    _ = _ := integral_add ((a r).integrable.sub (b r).integrable).abs
      ((b r).integrable.sub p.integrable).abs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticThresholdDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of one increasing finite-depth diagonal and one compact
quantile subsequence for growing attainable constrained blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem exists_magnetic_consistent_diagonal_above {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (mag : ℕ → A → ℝ)
    {s : ℝ} (hs : s < 1) (hmag : ∀ r a, |mag r a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag r a)/2))
    (threshold : ℕ → ℕ) (base : ℕ → OverlapPath)
    (htest : ∀ r (Φ : ℝ →ᵇ ℝ), Tendsto (fun j =>
      ∫ t, Φ (cavityStrictUniformPath (base r) j t) *
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField rho lam hrho hsum (base r) j) t -
          cavityStrictUniformPath (base r) j t) ∂pathMeasure) atTop (𝓝 0)) :
    ∃ (d φ : ℕ → ℕ) (p : OverlapPath), (∀ r, threshold r ≤ d r) ∧ StrictMono φ ∧
      Tendsto (fun r => ∫ t, |cavityStrictUniformPath (base (φ r)) (d (φ r)) t-p t|
        ∂pathMeasure) atTop (𝓝 0) ∧
      Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN (φ r))
        (spinGroupSlice (group (φ r)) (k (φ r)))
        (spinGroupSlice_nonempty (group (φ r)) (k (φ r)) (hk (φ r)))
        (cavityStrictUniformField rho lam hrho hsum (base (φ r)) (d (φ r))) t-p t|
        ∂pathMeasure) atTop (𝓝 0) := by
  let q := fun r j => cavityStrictUniformPath (base r) (threshold r+j)
  let B := fun r j => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r))
    (cavityStrictUniformField rho lam hrho hsum (base r) (threshold r+j))
  have ht r : Tendsto (fun j => threshold r+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat (threshold r)
  obtain ⟨d₀, _hd₀, hdiag⟩ := exists_diagonal_overlap_tests q B
    (fun r Φ => (htest r Φ).comp (ht r))
  let d := fun r => threshold r+d₀ r
  obtain ⟨p, φ, hφ, hpoint, hL1⟩ := overlapPath_ae_l1_subsequence (fun r => q r (d₀ r))
  refine ⟨d, φ, p, fun r => Nat.le_add_right _ _, hφ, hL1, ?_⟩
  apply magnetic_diagonal_l1_of_constrained_tests rho lam hrho hsum hK hlam
    (fun r => N (φ r)) (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop)
    (fun r => group (φ r)) (fun r => k (φ r)) (fun r => hk (φ r))
    (fun r => mag (φ r)) hs (fun r => hmag (φ r)) (fun r => hc (φ r))
    (fun r => base (φ r)) (fun r => d (φ r)) p hpoint
  intro Φ
  exact (hdiag Φ).comp hφ.tendsto_atTop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTrialBarrier
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak tests on growing physical blocks yield the magnetic variational trial lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_trial_barrier {m : ℕ}
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (base : ℕ → OverlapPath)
    (htest : ∀ r (Φ : ℝ →ᵇ ℝ), Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath (base r) j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum (base r) j) t-
          cavityStrictUniformPath (base r) j t) ∂pathMeasure) atTop (𝓝 0))
    (L : ℝ)
    (hupper : ∀ r, ∀ ε > 0, ∀ᶠ j in atTop,
      constrainedBlockValue (spinGroupSlice (group r) (k r))
          (cavityStrictUniformField ρ lam hρ hsum (base r) j)+
        fieldPairing (cavityStrictUniformPath (base r) j)
          (cavityStrictUniformField ρ lam hρ hsum (base r) j)/2+
        spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath (base r) j) ≤ L+ε) :
    (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal ≤ L := by
  let T := fun r j => constrainedBlockValue (spinGroupSlice (group r) (k r))
      (cavityStrictUniformField ρ lam hρ hsum (base r) j)+
    fieldPairing (cavityStrictUniformPath (base r) j)
      (cavityStrictUniformField ρ lam hρ hsum (base r) j)/2+
    spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath (base r) j)
  have hup r : ∃ b : ℕ, ∀ j ≥ b, T r j ≤ L+1/((r : ℝ)+1) := by
    exact eventually_atTop.mp (hupper r _ (by positivity))
  choose threshold hthreshold using hup
  obtain ⟨d,φ,p,hd,hφ,hq,hself⟩ := exists_magnetic_consistent_diagonal_above
    ρ lam hρ hsum hK hlam N hN hNlim group k hk (fun _ => mag) hs
      (fun _ => hmag) hc threshold base htest
  have hlower := magnetic_block_trial_eventually_lower ρ lam hρ hsum
    (fun r => N (φ r)) (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop)
    (fun r => group (φ r)) (fun r => k (φ r)) (fun r => hk (φ r)) γ mag hγ hγsum
    (fun r => hcount (φ r)) hs hmag (fun r => hc (φ r))
    (fun r => cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))
    (fun r => cavityStrictUniformField_height_le ρ lam hρ hsum hK hlam
      (base (φ r)) (d (φ r)) (Fin.last (d (φ r)))) p
    (fun r => cavityStrictUniformPath (base (φ r)) (d (φ r))) hself hq
  have herr : Tendsto (fun r => 1/((φ r : ℝ)+1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r,hr,he⟩ := ((hlower (ε/2) (half_pos hε)).and
    (herr.eventually (Iio_mem_nhds (half_pos hε)))).exists
  have hb := hthreshold (φ r) (d (φ r)) (hd (φ r))
  change (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal-ε/2 ≤
    T (φ r) (d (φ r)) at hr
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAffineIncrementLower
attribute [-instance] _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A physical constrained block has eventually large cavity increments whenever
the proposed pressure level is below the magnetic variational value. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_affine_increment_eventually_lower_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m) (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (spec : ℕ → Fin m → ℕ) (hsp : ∀ r a, 0 < spec r a) (hspec : ∀ r, ∑ a, spec r a=N r)
    (hρspec : ∀ r a, (spec r a : ℝ)=(N r : ℝ)*ρ a)
    (c : ℕ → Fin m → ℕ)
    (R : (r : ℕ) → Finset (Spin (∑ a, c r a))) (hR : ∀ r, (R r).Nonempty)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (u : (r j : ℕ) → Fin (cavityPrefixAffineSize (N r) (m*N r-N r+N r+3) (c r) j) → ℝ)
    (v : ℕ → ℕ → Fin m → ℝ)
    (hu : ∀ r j i, u r j i ∈ Set.Icc (1 : ℝ) 2)
    (hv : ∀ r j a, v r j a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      affineConstrainedObjective hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
        μ lam j (u r j) (v r j) ≤
      affineConstrainedObjective hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r)) μ lam j u' v')
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ r, ∀ᶠ j in atTop, L < (N r : ℝ)⁻¹*
      (affineRestrictedIncrement hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
        μ lam (u r) (v r) j +
        (Real.log (spinGroupSlice (group r) (k r)).card-N r*Real.log 2)) := by
  let Δ := fun r j => (N r : ℝ)⁻¹*
    (affineRestrictedIncrement hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      μ lam (u r) (v r) j + (Real.log (spinGroupSlice (group r) (k r)).card-N r*Real.log 2))
  change ∃ r, ∀ᶠ j in atTop, L < Δ r j
  by_contra hnone
  have hbad r : ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∀ j, Δ r (ι j) ≤ L := by
    have hn : ¬∀ᶠ j in atTop, L < Δ r j := fun h => hnone ⟨r,h⟩
    have hf : ∃ᶠ j in atTop, ¬L < Δ r j := by
      simpa only [Filter.Frequently, not_not] using hn
    obtain ⟨ι,hι,hb⟩ := extraction_of_frequently_atTop hf
    exact ⟨ι,hι,fun j => not_lt.mp (hb j)⟩
  choose ι hι hbad using hbad
  have hpaths r : ∃ p : OverlapPath,
      (∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath p j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum p j) t-cavityStrictUniformPath p j t)
          ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ j in atTop,
        constrainedBlockValue (spinGroupSlice (group r) (k r)) (cavityStrictUniformField ρ lam hρ hsum p j)+
        fieldPairing (cavityStrictUniformPath p j) (cavityStrictUniformField ρ lam hρ hsum p j)/2+
        spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath p j) ≤ L+ε := by
    have he : (fun a => (spec r a : ℝ)/(N r : ℝ))=ρ := by
      funext a
      rw [hρspec r a, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hN r).ne')]
    have hReq : finiteR (fun a => (spec r a : ℝ)/(N r : ℝ)) lam
        (cavityRationalMass_positive (spec r) (hsp r) (hN r))
        (cavityRationalMass_sum (spec r) (hspec r) (hN r)) = finiteR ρ lam hρ hsum := by
      subst ρ
      rfl
    obtain ⟨p,φ,hφ,hself,htrial⟩ := offset_affine_subsequence_trial_witness
      hhaar hgauss hpub hm (hN r) (spec r) (c r) (hsp r) (hspec r) (R r) (hR r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      μ lam amax hmax (ι r) (hι r) (u r) (v r) (hu r) (hv r) (hmin r)
    simp only [hReq, he] at hself htrial
    refine ⟨p,hself,?_⟩
    intro ε hε
    filter_upwards [htrial ε hε] with j hj
    have hb := hbad r (φ j)
    dsimp only [Δ] at hb
    linarith
  choose base htest hupper using hpaths
  exact (not_le_of_gt hL) (magnetic_trial_barrier ρ lam hρ hsum hK hlam N hN hNlim
    group k hk γ mag hγ hγsum hcount hs hmag hc base htest L hupper)

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.magnetic_affine_increment_eventually_lower_oai.{u_1} := @OAI.InvariantIsing.magnetic_affine_increment_eventually_lower_oai.{u_1}
