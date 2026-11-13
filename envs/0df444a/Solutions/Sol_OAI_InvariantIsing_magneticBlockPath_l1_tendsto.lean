-- Prove2me | solution 1 for OAI.InvariantIsing.magneticBlockPath_l1_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:59:49.119169+00:00
-- url     : https://prove2.me/submissions/a1fc5173-68e6-4ee7-9e9e-ac7265e238a1

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
import Theorems.Thm_OAI_InvariantIsing_magneticBias_uniform_bound
import Theorems.Thm_OAI_InvariantIsing_magneticCanonical_projection_distance

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open MeasureTheory ProbabilityTheory in
/-- Mathlib d13f23b's `ProbabilityTheory.rnDeriv_measure_compProd_right`: `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` is the kernel's
Radon-Nikodym derivative (InvariantIsing KernelRelativeEntropy, q251). -/
theorem _root_.ProbabilityTheory.rnDeriv_measure_compProd_right {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (κ η : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsFiniteKernel κ]
    [ProbabilityTheory.IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p => κ.rnDeriv η p.1 p.2 := by
  have h : κ = η.withDensity (κ.rnDeriv η) + κ.singularPart η :=
    (Kernel.rnDeriv_add_singularPart κ η).symm
  have hf : Measurable (Function.uncurry (κ.rnDeriv η)) := Kernel.measurable_rnDeriv κ η
  have hsum : μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η + (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    conv_lhs => rw [h]
    rw [Measure.compProd_add_right, Measure.compProd_withDensity hf, add_comm]
  refine Measure.eq_rnDeriv₀ hf.aemeasurable ?_ hsum |>.symm
  exact Measure.MutuallySingular.compProd_of_right μ μ (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_ConditionalRelativeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact relative entropy of conditioning on a nonnull event. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set

namespace InvariantIsing

theorem conditioned_measure_entropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    klDiv (cond μ S) μ ≠ ⊤ ∧ (klDiv (cond μ S) μ).toReal = -Real.log (μ.real S) := by
  let ν := cond μ S
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hpos
  have hν : ν ≪ μ := cond_absolutelyContinuous
  have hνr : ν ≪ μ.restrict S := Measure.smul_absolutelyContinuous
  have hs := hνr.ae_le (llr_smul_left (show μ.restrict S ≪ μ from Measure.restrict_le_self.absolutelyContinuous)
    (μ S)⁻¹ (ENNReal.inv_ne_zero.mpr (measure_ne_top μ S)) (ENNReal.inv_ne_top.mpr hpos))
  have hr := hν.ae_le (Measure.rnDeriv_restrict_self μ hS)
  have hl : llr ν μ =ᵐ[ν] fun _ => -Real.log (μ.real S) := by
    filter_upwards [hs, hr, ae_cond_mem hS (μ := μ)] with x hx hx' hxS
    change llr ((μ S)⁻¹ • μ.restrict S) μ x = _
    rw [hx]
    change Real.log ((μ.restrict S).rnDeriv μ x).toReal + Real.log ((μ S)⁻¹).toReal = _
    rw [hx', Set.indicator_of_mem hxS]
    simp only [Pi.one_apply, ENNReal.toReal_one, Real.log_one, zero_add,
      ENNReal.toReal_inv, Real.log_inv, measureReal_def]
  have hi : Integrable (llr ν μ) ν := (integrable_const _).congr hl.symm
  refine ⟨klDiv_ne_top hν hi, ?_⟩
  rw [toReal_klDiv hν hi, integral_congr_ae hl]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, add_sub_cancel_right]

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

private lemma integral_uniformBool (f : Bool → ℝ) :
    (∫ σ, f σ ∂(PMF.uniformOfFintype Bool).toMeasure) =
      (2 : ℝ)⁻¹ * (f false + f true) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, ENNReal.toReal_inv,
    smul_eq_mul, Fintype.sum_bool]
  norm_num
  ring

theorem scalarSpinKernel_mean (z : ℝ) :
    (∫ σ, spinValue σ ∂scalarSpinKernel z) = Real.tanh z := by
  change (∫ σ, spinValue σ ∂gibbsProbability
    (PMF.uniformOfFintype Bool).toMeasure (fun σ => z * spinValue σ)) = _
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite,
    integral_tilted_eq_div, integral_uniformBool, integral_uniformBool]
  simp only [spinValue, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, mul_neg_one, mul_one]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  ring

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

theorem fieldTailSpinKernel_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    (∫ σ, spinValue σ ∂fieldTailSpinKernel L hL z) =
      fieldScalarMean L (fun u => Real.log (Real.cosh u)) Real.tanh z := by
  induction L generalizing z with
  | nil => exact scalarSpinKernel_mean z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (∫ σ, spinValue σ ∂(fieldTailSpinKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun u => Real.log (Real.cosh u)))
        hreg.1) z) = _
    rw [Kernel.integral_comp (Integrable.of_finite)]
    simp_rw [ih ht]
    exact fieldTransitionKernel_integral av.1 av.2 _ hreg.1 hreg.2 _ z

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_KernelRelativeEntropy
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conditional entropy identity needed for the finite Gaussian
sampling path. Its nonnegative integral form also covers zero variances. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InvariantIsing

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]

lemma kernelRelativeEntropy_eq (κ η : Kernel X Y)
    [IsMarkovKernel κ] [IsMarkovKernel η] (x : X) (hac : κ x ≪ η x) :
    kernelRelativeEntropy κ η x = klDiv (κ x) (η x) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  apply lintegral_congr_ae
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
  rw [hy]

lemma klDiv_compProd_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  have hac' : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall hac)
  rw [klDiv_eq_lintegral_klFun_of_ac hac']
  calc
    _ = ∫⁻ p, ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
      rw [hp]
    _ = _ := Measure.lintegral_compProd (by
      exact ENNReal.measurable_ofReal.comp
        (continuous_klFun.measurable.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal))

lemma klDiv_compProd_integral (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_same_left μ κ η hac]

lemma klDiv_comp_le_integral (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv μ ν + ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  have he := klDiv_map_le (μ ⊗ₘ κ) (ν ⊗ₘ η) measurable_snd
  change klDiv (μ ⊗ₘ κ).snd (ν ⊗ₘ η).snd ≤ _ at he
  rw [Measure.snd_compProd, Measure.snd_compProd,
    klDiv_compProd_integral μ ν κ η hac] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_KernelProductEntropy
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy of two independent continuations from a common state. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InvariantIsing

lemma klDiv_prod_eq_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ ν : Measure X) (ρ σ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] (hac : ρ ≪ σ) :
    klDiv (μ.prod ρ) (ν.prod σ) = klDiv μ ν + klDiv ρ σ := by
  have he := klDiv_compProd_integral μ ν (Kernel.const X ρ) (Kernel.const X σ)
    (fun _ => hac)
  have hconst (x : X) : kernelRelativeEntropy (Kernel.const X ρ) (Kernel.const X σ) x =
      klDiv ρ σ := kernelRelativeEntropy_eq _ _ x hac
  simpa only [Measure.compProd_const, hconst, lintegral_const, measure_univ, mul_one] using he

lemma klDiv_prod_self {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountableOrCountablyGenerated X X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    klDiv (μ.prod μ) (ν.prod ν) = 2 * klDiv μ ν := by
  rw [klDiv_prod_eq_add μ ν μ ν hac, two_mul]

lemma entropy_budget_double {k d c : ℝ≥0∞} (h : k + d ≤ c) : k + 2 * d ≤ 2 * c := by
  calc
    k + 2 * d ≤ 2 * k + 2 * d := by
      exact add_le_add_left (show k ≤ 2 * k by simp only [two_mul]; exact le_self_add) _
    _ = 2 * (k + d) := (mul_add _ _ _).symm
    _ ≤ 2 * c := mul_le_mul_right h 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-prefix sampling of two scalar Ising spins. After the split
the two tails are independent; before the split they use the same actual
tilted Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldPairSpinKernel_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : ℝ) :
    (∫ σ, spinValue σ.1 * spinValue σ.2 ∂fieldPairSpinKernel L hL i z) =
      fieldScalarSquares L (fun u => Real.log (Real.cosh u)) Real.tanh i z := by
  induction L generalizing z with
  | nil =>
    simp only [fieldPairSpinKernel, Kernel.prod_apply, integral_prod_mul,
      scalarSpinKernel_mean, fieldScalarSquares, pow_two]
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∫ σ, spinValue σ.1 * spinValue σ.2
        ∂(fieldTailSpinKernel (av :: L) hL ×ₖ fieldTailSpinKernel (av :: L) hL) z) = _
      rw [Kernel.prod_apply, integral_prod_mul, fieldTailSpinKernel_mean]
      rw [fieldScalarSquares_zero, pow_two]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      change (∫ σ, spinValue σ.1 * spinValue σ.2
        ∂(fieldPairSpinKernel L ht j ∘ₖ
          fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun u => Real.log (Real.cosh u)))
            hreg.1) z) = _
      rw [Kernel.integral_comp (Integrable.of_finite)]
      simp_rw [ih ht]
      exact fieldTransitionKernel_integral av.1 av.2 _ hreg.1 hreg.2 _ z

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVectorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual vector spin sampling for independent scalar cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldVectorTransitionKernel_eq_tilted {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    fieldVectorTransitionKernel N ζ v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => ζ * ∑ i, F (y i)) :=
  (fieldGaussian_product_tilt ζ v F hF hG z).symm

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_ProductKernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise sampling commutes with a finite product of root laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma product_kernel_comp_general {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {N : ℕ} (κ : Kernel X Y) [IsMarkovKernel κ]
    (K : Kernel (Fin N → X) (Fin N → Y)) [IsMarkovKernel K]
    (hK : ∀ z, K z = Measure.pi (fun i => κ (z i)))
    (ν : Fin N → Measure X) [∀ i, IsProbabilityMeasure (ν i)] :
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
  have he (z : Fin N → X) : (K z).real (univ.pi s) = ∏ i, (κ (z i)).real (s i) := by
    rw [hK, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    rfl
  simp_rw [he]
  change (∫ z : Fin N → X, ∏ i,
    (fun y : X => (κ y).real (s i)) (z i) ∂Measure.pi ν) = _
  rw [integral_fintype_prod_eq_prod (fun i y => (κ y).real (s i)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernel_comp_real κ (ν i) (s i) (hs i)).symm

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TiltedRelativeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conditional relative entropy of two finite exponential tilts.
The resulting one-step budget retains the inverse exponent weight. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron InformationTheory

namespace InvariantIsing

lemma tilted_pair_log_likelihood {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) (b : ℝ)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ) :
    llr (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) =ᵐ[μ.tilted (fun x => b * G x)]
      (fun x => b * (G x - F x) +
        Real.log (∫ y, Real.exp (b * F y) ∂μ) - Real.log (∫ y, Real.exp (b * G y) ∂μ)) := by
  have hμG := tilted_absolutelyContinuous μ (fun x => b * G x)
  have hself := hμG.ae_le (log_rnDeriv_tilted_left_self hG)
  have hr := llr_tilted_right hμG hF
  filter_upwards [hself, hr] with x hx hx'
  change llr (μ.tilted (fun x => b * G x)) μ x = _ at hx
  rw [hx] at hx'
  rw [hx']
  ring

theorem tilted_pair_entropy_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) {b : ℝ} (hb : 0 < b)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x))) :
    klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) ≠ ⊤ ∧
      (klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x))).toReal +
        b * (∫ x, F x - G x ∂μ.tilted (fun x => b * G x)) =
        b * (logMean b μ F - logMean b μ G) := by
  let ν := μ.tilted (fun x => b * G x)
  let π := μ.tilted (fun x => b * F x)
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hG
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted hF
  let c := Real.log (∫ y, Real.exp (b * F y) ∂μ) - Real.log (∫ y, Real.exp (b * G y) ∂μ)
  have hac : ν ≪ π := (tilted_absolutelyContinuous μ _).trans (absolutelyContinuous_tilted hF)
  have hr : llr ν π =ᵐ[ν] (fun x => -b * (F x - G x) + c) := by
    filter_upwards [tilted_pair_log_likelihood μ F G b hF hG] with x hx
    rw [hx]
    dsimp only [c]
    ring
  have hI : Integrable (fun x => -b * (F x - G x) + c) ν :=
    (hFG.const_mul (-b)).add (integrable_const c)
  have hi : Integrable (llr ν π) ν := hI.congr hr.symm
  refine ⟨klDiv_ne_top hac hi, ?_⟩
  have he : (klDiv ν π).toReal = ∫ x, llr ν π x ∂ν := by
    rw [toReal_klDiv hac hi]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
  have hlin := integral_add (hFG.const_mul (-b)) (integrable_const c)
  have hK : (klDiv ν π).toReal = -b * (∫ x, F x - G x ∂ν) + c := by
    rw [he, integral_congr_ae hr, hlin, integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rfl
  change (klDiv ν π).toReal + b * (∫ x, F x - G x ∂ν) = _
  rw [hK]
  change _ = b * (Real.log (∫ x, Real.exp (b * F x) ∂μ) / b -
    Real.log (∫ x, Real.exp (b * G x) ∂μ) / b)
  dsimp only [c]
  field_simp
  ring

theorem tilted_pair_entropy_budget {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x))) :
    (klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x))).toReal +
      (∫ x, F x - G x ∂μ.tilted (fun x => b * G x)) ≤ logMean b μ F - logMean b μ G := by
  have he := (tilted_pair_entropy_identity μ F G hb hF hG hFG).2
  have hK := ENNReal.toReal_nonneg (a := klDiv
    (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)))
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hK]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinProductLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product law of the canonical terminal spins after all Gaussian
transitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldVectorTailSpinKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : Fin N → ℝ) :
    fieldVectorTailSpinKernel N L hL z = Measure.pi (fun i => fieldTailSpinKernel L hL (z i)) := by
  induction L generalizing z with
  | nil => exact fieldSpinGibbs_eq_product z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (fieldVectorTailSpinKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2 _ hreg.1) z = _
    rw [Kernel.comp_apply]
    change fieldVectorTailSpinKernel N L ht ∘ₘ
      Measure.pi (fun i => fieldTransitionKernel av.1 av.2 _ hreg.1 (z i)) = _
    rw [product_kernel_comp_general (fieldTailSpinKernel L ht)
      (fieldVectorTailSpinKernel N L ht) (ih ht)]
    rfl

lemma paired_product_reorder {X : Type*} [MeasurableSpace X] (N : ℕ)
    (ν : Fin N → Measure X) [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.pi ν).prod (Measure.pi ν)).map
      (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin N)).symm =
        Measure.pi (fun i => (ν i).prod (ν i)) :=
  (measurePreserving_arrowProdEquivProdArrow X X (Fin N) ν ν).symm.map_eq

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPairProductLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence across sites of the full common-prefix two-spin law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldVectorSitePairKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : Fin N → ℝ) :
    fieldVectorSitePairKernel N L hL i z = Measure.pi (fun j => fieldPairSpinKernel L hL i (z j)) := by
  induction L generalizing z with
  | nil =>
    rw [fieldVectorSitePairKernel, Kernel.map_apply _
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
    change ((fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N) z).map _ = _
    rw [Kernel.prod_apply]
    change ((gibbsProbability _ (fieldEnergy z)).prod (gibbsProbability _ (fieldEnergy z))).map _ = _
    rw [fieldSpinGibbs_eq_product, paired_product_reorder]
    simp only [fieldPairSpinKernel, Kernel.prod_apply]
  | cons av L ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [fieldVectorSitePairKernel, Kernel.map_apply _
        (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
      change ((fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL) z).map _ = _
      rw [Kernel.prod_apply, fieldVectorTailSpinKernel_product, paired_product_reorder]
      simp only [fieldPairSpinKernel, Fin.cases_zero, Kernel.prod_apply]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      change ((fieldVectorPairSpinKernel N L ht k ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2 _ hreg.1).map
        (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm) z = _
      rw [Kernel.map_comp, Kernel.comp_apply]
      change fieldVectorSitePairKernel N L ht k ∘ₘ
        Measure.pi (fun j => fieldTransitionKernel av.1 av.2 _ hreg.1 (z j)) = _
      rw [product_kernel_comp_general (fieldPairSpinKernel L ht k)
        (fieldVectorSitePairKernel N L ht k) (ih ht k)]
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_EntropyMeanComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative entropy controls the expectation of a canonical
sub-Gaussian observable. This avoids a loss from the ambient dimension. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal

namespace InvariantIsing

theorem entropy_variational_mean {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) (F : X → ℝ)
    (hF : Integrable F μ) (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (F x) ∂ν) := by
  let π := ν.tilted F
  let : IsProbabilityMeasure π := isProbabilityMeasure_tilted he
  have hac' : μ ≪ π := hac.trans (absolutelyContinuous_tilted he)
  have hi : Integrable (llr μ π) μ := integrable_llr_tilted_right hac hF hllr he
  have hn := integral_llr_add_sub_measure_univ_nonneg hac' hi
  have hE := integral_llr_tilted_right hac hF he hllr
  have hK := toReal_klDiv hac hllr
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right] at hn hK
  change 0 ≤ ∫ x, llr μ (ν.tilted F) x ∂μ at hn
  linarith

theorem entropy_subgaussian_mean {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) (Y : X → ℝ) {c : ℝ≥0}
    (hY : Integrable Y μ) (hG : HasSubgaussianMGF Y c ν) {t : ℝ} (ht : 0 < t) :
    |∫ x, Y x ∂μ| ≤ (klDiv μ ν).toReal / t + c * t / 2 := by
  have hp := entropy_variational_mean μ ν hac hllr (fun x => t * Y x)
    (hY.const_mul t) (hG.integrable_exp_mul t)
  have hn := entropy_variational_mean μ ν hac hllr (fun x => -t * Y x)
    (hY.const_mul (-t)) (hG.integrable_exp_mul (-t))
  have hgp := hG.cgf_le t
  have hgn := hG.cgf_le (-t)
  change Real.log (∫ x, Real.exp (t * Y x) ∂ν) ≤ _ at hgp
  change Real.log (∫ x, Real.exp (-t * Y x) ∂ν) ≤ _ at hgn
  rw [integral_const_mul] at hp hn
  have hbound : t * |∫ x, Y x ∂μ| ≤ (klDiv μ ν).toReal + c * t ^ 2 / 2 := by
    have h := (abs_le.mpr (show -( (klDiv μ ν).toReal + c * t ^ 2 / 2) ≤
      t * (∫ x, Y x ∂μ) ∧ t * (∫ x, Y x ∂μ) ≤
        (klDiv μ ν).toReal + c * t ^ 2 / 2 by constructor <;> nlinarith))
    simpa only [abs_mul, abs_of_pos ht] using h
  apply (mul_le_mul_iff_right₀ ht).mp
  calc
    _ = t * |∫ x, Y x ∂μ| := by ring
    _ ≤ _ := hbound
    _ = t * ((klDiv μ ν).toReal / t + c * t / 2) := by field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPairSubGaussian
attribute [-simp] _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The independent canonical site-pair law supplies the dimension-sharp
concentration bound needed in constrained magnetic replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma spinPairSiteValue_bounds (p : Bool × Bool) : spinPairSiteValue p ∈ Set.Icc (-1) 1 := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> norm_num [spinPairSiteValue, spinValue]

lemma spinPairSiteSum_subgaussian {N : ℕ} (ν : Fin N → Measure (Bool × Bool))
    [∀ i, IsProbabilityMeasure (ν i)] :
    HasSubgaussianMGF (fun u => spinPairSiteSum u - ∑ j, ∫ p, spinPairSiteValue p ∂ν j)
      (N : ℝ≥0) (Measure.pi ν) := by
  let X := fun j p => spinPairSiteValue p - ∫ q, spinPairSiteValue q ∂ν j
  have hi := iIndepFun_pi (μ := ν) (X := X)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have hg (j : Fin N) : HasSubgaussianMGF (fun u : Fin N → Bool × Bool => X j (u j)) 1
      (Measure.pi ν) := by
    apply HasSubgaussianMGF.of_map (X := X j) (μ := Measure.pi ν) (c := 1)
      (measurePreserving_eval ν j).measurable.aemeasurable
    rw [(measurePreserving_eval ν j).map_eq]
    have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν j) (X := spinPairSiteValue)
      (measurable_of_finite _).aemeasurable (Filter.Eventually.of_forall spinPairSiteValue_bounds)
    norm_num at hs
    exact hs
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (c := fun _ => 1)
    (fun j _ => hg j)
  simpa only [X, spinPairSiteSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_one] using hs

lemma spinPairSiteSum_entropy_bound {N : ℕ} (μ : Measure (Fin N → Bool × Bool))
    [IsProbabilityMeasure μ] (ν : Fin N → Measure (Bool × Bool))
    [∀ i, IsProbabilityMeasure (ν i)] (hK : klDiv μ (Measure.pi ν) ≠ ⊤)
    {t : ℝ} (ht : 0 < t) :
    |(∫ u, spinPairSiteSum u ∂μ) - ∑ j, ∫ p, spinPairSiteValue p ∂ν j| ≤
      (klDiv μ (Measure.pi ν)).toReal / t + N * t / 2 := by
  have hk := klDiv_ne_top_iff.mp hK
  have he := entropy_subgaussian_mean μ (Measure.pi ν) hk.1 hk.2
    (fun u => spinPairSiteSum u - ∑ j, ∫ p, spinPairSiteValue p ∂ν j)
    Integrable.of_finite (spinPairSiteSum_subgaussian ν) ht
  simpa only [integral_sub Integrable.of_finite (integrable_const _), integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, NNReal.coe_natCast] using he

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorGaussianTransition
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vector Gaussian transition for a nonseparable terminal,
including constrained spin blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma vectorShiftGaussianKernel_apply (N : ℕ) (v : ℝ≥0) (z : Fin N → ℝ) :
    vectorShiftGaussianKernel N v z = Measure.pi (fun i => gaussianReal (z i) v) := by
  have hg : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) :=
    ⟨0, 0, le_rfl, le_rfl, fun _ => by simp⟩
  rw [vectorShiftGaussianKernel, fieldVectorTransitionKernel_eq_tilted 0 v _ measurable_const hg]
  simp

lemma vectorGaussian_shift_exp_integrable {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    Integrable (fun y => Real.exp (a * F y)) (Measure.pi (fun i => gaussianReal (z i) v)) := by
  rw [← (vectorGaussian_shift v z).map_eq]
  apply (integrable_map_measure (hF.const_mul a).exp.aestronglyMeasurable
    (show AEMeasurable (fun w : Fin N → ℝ => z + w) (vectorGaussianLaw N v : Measure (Fin N → ℝ)) from
      (measurable_const.add measurable_id).aemeasurable)).mpr
  exact integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN v)
    (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) a

lemma vectorGaussianTransition_eq_tilted {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => a * F y) := by
  change normalizeMass ((vectorShiftGaussianKernel N v z).withDensity _) = _
  rw [vectorShiftGaussianKernel_apply]
  exact normalizeMass_exp _ _ (hF.const_mul a)
    (vectorGaussian_shift_exp_integrable hN a v F hF hG z)

lemma vectorGaussianTransition_eq_map {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      ((vectorGaussianLaw N v : Measure (Fin N → ℝ)).tilted
        (fun w => a * F (z + w))).map (fun w => z + w) := by
  rw [vectorGaussianTransition_eq_tilted hN a v F hF hG z]
  have he := cavity_tilt_map (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => z + w) (measurable_const.add measurable_id) (fun y => a * F y) (hF.const_mul a)
  rw [(vectorGaussian_shift v z).map_eq] at he
  exact he.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_EntropyBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative entropy budgets for successive finite sampling steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma entropy_budget_of_real {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (D : X → ℝ) (hD : Integrable D μ) (hD0 : ∀ x, 0 ≤ D x)
    {c : ℝ} (hK : klDiv μ ν ≠ ⊤) (h : (klDiv μ ν).toReal + (∫ x, D x ∂μ) ≤ c) :
    klDiv μ ν + (∫⁻ x, ENNReal.ofReal (D x) ∂μ) ≤ ENNReal.ofReal c := by
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Filter.Eventually.of_forall hD0),
    ← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
      (integral_nonneg hD0)]
  exact ENNReal.ofReal_le_ofReal h

lemma entropy_budget_drop {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) (D : X → ℝ≥0∞)
    (h : ∀ x, kernelRelativeEntropy κ η x ≤ D x) :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv μ ν + ∫⁻ x, D x ∂μ :=
  (klDiv_comp_le_integral μ ν κ η hac).trans (add_le_add_right (lintegral_mono h) _)

lemma entropy_budget_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) (D : Y → ℝ≥0∞) (hD : Measurable D) :
    klDiv (μ.map f) (ν.map f) + (∫⁻ y, D y ∂μ.map f) ≤
      klDiv μ ν + ∫⁻ x, D (f x) ∂μ := by
  rw [lintegral_map hD hf]
  exact add_le_add_left (klDiv_map_le μ ν hf) _

lemma tilted_pair_entropy_budget_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x)))
    (hGF : ∀ x, G x ≤ F x) :
    klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) +
      (∫⁻ x, ENNReal.ofReal (F x - G x) ∂μ.tilted (fun x => b * G x)) ≤
      ENNReal.ofReal (logMean b μ F - logMean b μ G) :=
  entropy_budget_of_real _ _ _ hFG (fun x => sub_nonneg.mpr (hGF x))
    (tilted_pair_entropy_identity μ F G hb hF hG hFG).1
    (tilted_pair_entropy_budget μ F G hb hb1 hF hG hFG)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTransitionEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and future loss at one actual vector Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

lemma vectorGaussianTransition_entropy_budget {N : ℕ} (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (v : ℝ≥0)
    (F G : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hLF : HasLinearGrowth F) (hLG : HasLinearGrowth G)
    (hGF : ∀ z, G z ≤ F z) (z : Fin N → ℝ) :
    klDiv (vectorGaussianTransition N a v G hG z) (vectorGaussianTransition N a v F hF z) +
      (∫⁻ y, ENNReal.ofReal (F y - G y) ∂vectorGaussianTransition N a v G hG z) ≤
      ENNReal.ofReal (logMean a (vectorGaussianLaw N v : Measure (Fin N → ℝ))
        (fun w => F (z + w)) -
          logMean a (vectorGaussianLaw N v : Measure (Fin N → ℝ)) (fun w => G (z + w))) := by
  let μ := (vectorGaussianLaw N v : Measure (Fin N → ℝ))
  let f := fun w : Fin N → ℝ => z + w
  have hf : Measurable f := measurable_const.add measurable_id
  have heF := integrable_exp_of_linearGrowth μ (vectorGaussianLaw_moments hN v)
    (hF.comp hf) (hLF.add_left z) a
  have heG := integrable_exp_of_linearGrowth μ (vectorGaussianLaw_moments hN v)
    (hG.comp hf) (hLG.add_left z) a
  have hiF := integrable_linearGrowth_tilted μ (vectorGaussianLaw_moments hN v)
    (fun w => G (f w)) (fun w => F (f w)) (hG.comp hf) (hLG.add_left z)
    (hF.comp hf) (hLF.add_left z) a
  have hiG := integrable_linearGrowth_tilted μ (vectorGaussianLaw_moments hN v)
    (fun w => G (f w)) (fun w => G (f w)) (hG.comp hf) (hLG.add_left z)
    (hG.comp hf) (hLG.add_left z) a
  let _ : IsProbabilityMeasure (μ.tilted (fun w => a * F (f w))) :=
    isProbabilityMeasure_tilted heF
  let _ : IsProbabilityMeasure (μ.tilted (fun w => a * G (f w))) :=
    isProbabilityMeasure_tilted heG
  rw [vectorGaussianTransition_eq_map hN a v G hG hLG z,
    vectorGaussianTransition_eq_map hN a v F hF hLF z]
  exact (entropy_budget_map (μ.tilted (fun w => a * G (f w)))
    (μ.tilted (fun w => a * F (f w))) f hf
    (fun y => ENNReal.ofReal (F y - G y)) (hF.sub hG).ennreal_ofReal).trans
      (tilted_pair_entropy_budget_ennreal μ (fun w => F (f w)) (fun w => G (f w))
        ha ha1 heF heG (hiF.sub hiG) (fun w => hGF (f w)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained terminal spin distribution is the physical Gibbs
law conditioned on the allowed spins. Its entropy cost is exactly the
loss in log partition functions, retaining the original cube mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem restrictedSpinLaw_entropy {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) :
    klDiv (restrictedSpinLaw S H) (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) ≠ ⊤ ∧
      (klDiv (restrictedSpinLaw S H)
        (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)).toReal =
      logPartition H - restrictedSpinLog S H := by
  have he := conditioned_measure_entropy
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) S S.measurableSet
    ((measureReal_ne_zero_iff).mp (spinGibbs_mass_pos H S hS).ne')
  refine ⟨he.1, he.2.trans ?_⟩
  rw [spinGibbs_mass_finset, Real.log_div
    (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne' (sum_exp_pos H).ne']
  rw [logPartition_eq, log_card_spin, restrictedSpinLog]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained terminal spin kernel, including measurability
and its exact conditional entropy cost. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set

namespace InvariantIsing

lemma restrictedSpinKernel_univ (N : ℕ) :
    restrictedSpinKernel (Finset.univ : Finset (Spin N)) = fieldVectorSpinKernel N := by
  ext z : 1
  change cond (fieldVectorSpinKernel N z) (Finset.univ : Finset (Spin N)) = _
  simpa only [Finset.coe_univ] using (cond_univ (μ := fieldVectorSpinKernel N z))

theorem restrictedSpinKernel_entropy {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z : Fin N → ℝ) :
    klDiv (restrictedSpinKernel S z) (fieldVectorSpinKernel N z) ≠ ⊤ ∧
      (klDiv (restrictedSpinKernel S z) (fieldVectorSpinKernel N z)).toReal =
        restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z := by
  have he := restrictedSpinLaw_entropy S hS (fieldEnergy z)
  rw [← restrictedSpinLog_univ] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedTailEntropy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entropy of the complete constrained sampling law is bounded by
its actual recursion loss, uniformly in the number of levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

theorem restrictedTailSpinKernel_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (hb1 : ∀ i < n, b i ≤ 1) (z : Fin N → ℝ) :
    klDiv (restrictedTailSpinKernel hN S hS n b v hb z)
      (restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb z) ≤
        ENNReal.ofReal (restrictedFieldRecursion Finset.univ n b v z -
          restrictedFieldRecursion S n b v z) := by
  induction n generalizing b v z with
  | zero =>
    change klDiv (restrictedSpinKernel S z) (restrictedSpinKernel Finset.univ z) ≤ _
    rw [restrictedSpinKernel_univ]
    have he := restrictedSpinKernel_entropy S hS z
    rw [← ENNReal.ofReal_toReal he.1, he.2]
    rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hbs1 : ∀ i < n, bs i ≤ 1 := fun i hi => hb1 (i + 1) (by omega)
    let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs
    let G := restrictedFieldRecursion S n bs vs
    have hF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hG := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    let κ := restrictedTailSpinKernel hN S hS n bs vs hbs
    let η := restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hac (y : Fin N → ℝ) : κ y ≪ η y :=
      (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (ih bs vs hbs hbs1 y))).1
    have hκ (y : Fin N → ℝ) : kernelRelativeEntropy κ η y ≤ ENNReal.ofReal (F y - G y) := by
      rw [kernelRelativeEntropy_eq κ η y (hac y)]
      exact ih bs vs hbs hbs1 y
    have hg := vectorGaussianTransition_entropy_budget hN (b 0) (hb 0 (by omega))
      (hb1 0 (by omega)) (v 0) F G hF.1 hG.1 hF.2 hG.2
      (fun y => restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
        (Finset.subset_univ S) n bs vs hbs y) z
    have he := entropy_budget_drop
      (vectorGaussianTransition N (b 0) (v 0) G hG.1 z)
      (vectorGaussianTransition N (b 0) (v 0) F hF.1 z) κ η hac
      (fun y => ENNReal.ofReal (F y - G y)) hκ
    rw [Measure.comp_eq_comp_const_apply, Measure.comp_eq_comp_const_apply] at he
    exact he.trans hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairEntropy
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entropy cost of a branching pair is at most twice the scalar
block loss, independently of the split level or number of levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

theorem restrictedPairSpinKernel_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (hb1 : ∀ j < n, b j ≤ 1)
    (i : Fin (n + 1)) (z : Fin N → ℝ) :
    klDiv (restrictedPairSpinKernel hN S hS n b v hb i z)
      (restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb i z) ≤
        2 * ENNReal.ofReal (restrictedFieldRecursion Finset.univ n b v z -
          restrictedFieldRecursion S n b v z) := by
  let _ := restrictedSpinKernel_markov S hS
  let _ := restrictedSpinKernel_markov (Finset.univ : Finset (Spin N)) Finset.univ_nonempty
  have htail (m : ℕ) (c : ℕ → ℝ) (w : ℕ → ℝ≥0) (hc : ∀ j < m, 0 < c j)
      (hc1 : ∀ j < m, c j ≤ 1) (y : Fin N → ℝ) :
      klDiv ((restrictedTailSpinKernel hN S hS m c w hc y).prod
          (restrictedTailSpinKernel hN S hS m c w hc y))
        ((restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty m c w hc y).prod
          (restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty m c w hc y)) ≤
      2 * ENNReal.ofReal (restrictedFieldRecursion Finset.univ m c w y -
          restrictedFieldRecursion S m c w y) := by
    have he := restrictedTailSpinKernel_entropy hN S hS m c w hc hc1 y
    have hac := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he)).1
    rw [klDiv_prod_self _ _ hac]
    exact mul_le_mul_right he 2
  induction n generalizing b v z with
  | zero =>
    change klDiv ((_ ×ₖ _) z) ((_ ×ₖ _) z) ≤ _
    simpa only [restrictedTailSpinKernel, Kernel.prod_apply] using htail 0 b v hb hb1 z
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change klDiv ((_ ×ₖ _) z) ((_ ×ₖ _) z) ≤ _
      simp only [Kernel.prod_apply]
      exact htail (n + 1) b v hb hb1 z
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      have hbs1 : ∀ j < n, bs j ≤ 1 := fun j hj => hb1 (j + 1) (by omega)
      let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs
      let G := restrictedFieldRecursion S n bs vs
      have hF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
      have hG := restrictedFieldRecursion_regular hN S hS n bs vs hbs
      let κ := restrictedPairSpinKernel hN S hS n bs vs hbs j
      let η := restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs j
      have hi (y : Fin N → ℝ) := ih bs vs hbs hbs1 j y
      have hac (y : Fin N → ℝ) : κ y ≪ η y :=
        (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (by finiteness) (hi y))).1
      have hκ (y : Fin N → ℝ) : kernelRelativeEntropy κ η y ≤
          2 * ENNReal.ofReal (F y - G y) := by
        rw [kernelRelativeEntropy_eq κ η y (hac y)]
        exact hi y
      have hg := vectorGaussianTransition_entropy_budget hN (b 0) (hb 0 (by omega))
        (hb1 0 (by omega)) (v 0) F G hF.1 hG.1 hF.2 hG.2
        (fun y => restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
          (Finset.subset_univ S) n bs vs hbs y) z
      have he := entropy_budget_drop
        (vectorGaussianTransition N (b 0) (v 0) G hG.1 z)
        (vectorGaussianTransition N (b 0) (v 0) F hF.1 z) κ η hac
        (fun y => 2 * ENNReal.ofReal (F y - G y)) hκ
      rw [lintegral_const_mul 2 (f := fun y => ENNReal.ofReal (F y - G y))
        (hF.1.sub hG.1).ennreal_ofReal] at he
      rw [Measure.comp_eq_comp_const_apply, Measure.comp_eq_comp_const_apply] at he
      exact he.trans (entropy_budget_double hg)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairRootEntropy
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared Gaussian root preserves the pair entropy estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

theorem restrictedLevelSpinPair_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) :
    klDiv (restrictedLevelSpinPair hN S hS h b i)
      (restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i) ≤
        2 * ENNReal.ofReal ((N : ℝ) *
          (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b)) := by
  let μ := Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))
  let B := chainExponent h.cut
  let V := fieldStepVariance h
  have hB : ∀ j < h.depth, 0 < B j :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1
  have hB1 : ∀ j < h.depth, B j ≤ 1 :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).2.le
  let κ := restrictedPairSpinKernel hN S hS h.depth B V hB i
  let η := restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty h.depth B V hB i
  let F := restrictedFieldRecursion (Finset.univ : Finset (Spin N)) h.depth B V
  let G := restrictedFieldRecursion S h.depth B V
  have hi (z : Fin N → ℝ) := restrictedPairSpinKernel_entropy hN S hS h.depth B V hB hB1 i z
  have hac (z : Fin N → ℝ) : κ z ≪ η z :=
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top (by finiteness) (hi z))).1
  have hκ (z : Fin N → ℝ) : kernelRelativeEntropy κ η z ≤ 2 * ENNReal.ofReal (F z - G z) := by
    rw [kernelRelativeEntropy_eq κ η z (hac z)]
    exact hi z
  have he := entropy_budget_drop μ μ κ η hac (fun z => 2 * ENNReal.ofReal (F z - G z)) hκ
  have hF := restrictedFieldRecursion_biased_root_integrable hN Finset.univ Finset.univ_nonempty h b
  have hG := restrictedFieldRecursion_biased_root_integrable hN S hS h b
  have hDm : Measurable (fun z => ENNReal.ofReal (F z - G z)) :=
    ((restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty h.depth B V hB).1.sub
      (restrictedFieldRecursion_regular hN S hS h.depth B V hB).1).ennreal_ofReal
  have hD0 (z : Fin N → ℝ) : 0 ≤ F z - G z := sub_nonneg.mpr
    (restrictedFieldRecursion_mono hN S Finset.univ hS Finset.univ_nonempty
      (Finset.subset_univ S) h.depth B V hB z)
  rw [klDiv_self, zero_add, lintegral_const_mul 2 hDm,
    ← ofReal_integral_eq_lintegral_ofReal (f := fun z => F z - G z) (μ := μ)
      (hF.sub hG) (Filter.Eventually.of_forall hD0)] at he
  have hval : (∫ z, F z - G z ∂μ) = (N : ℝ) *
      (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b) := by
    rw [integral_sub (f := F) (g := G) hF hG]
    unfold biasedConstrainedBlockValue
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp only [μ, F, G, B, V]
    field_simp
    ring
  rw [hval] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedKernelFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted member of the constrained sampling construction is
exactly the previously evaluated canonical scalar-field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal BigOperators

namespace InvariantIsing

lemma vectorGaussianTransition_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (a : ℝ) (r : ℝ≥0) :
    vectorGaussianTransition N a r (restrictedFieldRecursion Finset.univ n b v)
      (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n b v hb).1 =
    fieldVectorTransitionKernel N a r
      (fieldScalarValue (List.ofFn (fun i : Fin n => (b i, v i))) (fun y => Real.log (Real.cosh y)))
      (fieldScalarValue_regular _ (finiteFieldIncrements_positive n b v hb)
        measurable_logCosh logCosh_linearGrowth).1 := by
  ext z : 1
  rw [vectorGaussianTransition_eq_tilted hN a r _ _
    (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n b v hb).2,
    fieldVectorTransitionKernel_eq_tilted a r _ _
      (fieldScalarValue_regular _ (finiteFieldIncrements_positive n b v hb)
        measurable_logCosh logCosh_linearGrowth).2]
  congr 1
  funext y
  rw [restrictedFieldRecursion_univ n b v hb]

lemma restrictedTailSpinKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) :
    restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb =
      fieldVectorTailSpinKernel N (List.ofFn (fun i : Fin n => (b i, v i)))
        (finiteFieldIncrements_positive n b v hb) := by
  induction n generalizing b v with
  | zero => exact restrictedSpinKernel_univ N
  | succ n ih =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
    simp only [List.ofFn_succ, fieldVectorTailSpinKernel]
    change restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
        (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
    rw [ih bs vs hbs, vectorGaussianTransition_univ hN n bs vs hbs]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairFactorization
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the canonical member of the branching-pair family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldVectorPairSpinKernel_zero (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    fieldVectorPairSpinKernel N L hL 0 =
      fieldVectorTailSpinKernel N L hL ×ₖ fieldVectorTailSpinKernel N L hL := by
  cases L <;> rfl

lemma fieldVectorPairSpinKernel_transport (N : ℕ) {L L' : List (ℝ × ℝ≥0)}
    (he : L = L') (hL : ∀ av ∈ L, 0 < av.1) (hL' : ∀ av ∈ L', 0 < av.1)
    (i : Fin (L.length + 1)) (i' : Fin (L'.length + 1)) (hi : i.val = i'.val) :
    fieldVectorPairSpinKernel N L hL i = fieldVectorPairSpinKernel N L' hL' i' := by
  subst L'
  have hii : i = i' := Fin.ext hi
  subst i'
  rfl

theorem restrictedPairSpinKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) :
    restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb i =
      fieldVectorPairSpinKernel N (List.ofFn (fun j : Fin n => (b j, v j)))
        (finiteFieldIncrements_positive n b v hb) (Fin.cast (by simp) i) := by
  induction n generalizing b v with
  | zero =>
    change restrictedSpinKernel Finset.univ ×ₖ restrictedSpinKernel Finset.univ = _
    rw [restrictedSpinKernel_univ]
    rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairSpinKernel, Fin.cases_zero]
      rw [restrictedTailSpinKernel_univ, Fin.cast_zero, fieldVectorPairSpinKernel_zero]
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let L := List.ofFn (fun k : Fin n => (bs k, vs k))
      have hlist : List.ofFn (fun k : Fin (n + 1) => (b k, v k)) = (b 0, v 0) :: L := by
        rw [List.ofFn_succ]
        rfl
      have hL : ∀ av ∈ (b 0, v 0) :: L, 0 < av.1 := by
        rw [← hlist]
        exact finiteFieldIncrements_positive (n + 1) b v hb
      let j' : Fin (L.length + 1) := Fin.cast (by simp [L]) j
      have he := fieldVectorPairSpinKernel_transport N hlist
        (finiteFieldIncrements_positive (n + 1) b v hb) hL
        (Fin.cast (by simp) j.succ) j'.succ rfl
      rw [he]
      simp only [restrictedPairSpinKernel, Fin.cases_succ]
      change restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
          (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
      rw [ih bs vs hbs, vectorGaussianTransition_univ hN n bs vs hbs]
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalPairRootLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-site factorization at the biased shared root. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma biasedFieldLevelSpinPair_mean (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) :
    (∫ p, spinPairSiteValue p ∂biasedFieldLevelSpinPair h b i) = magneticLevelAtBias h b i := by
  unfold biasedFieldLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  simp only [Kernel.const_apply, spinPairSiteValue, fieldPairSpinKernel_mean]
  simp only [magneticLevelAtBias, fieldSpinTransition, zero_mul, tilted_const]

lemma restrictedLevelSpinPair_univ {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin (h.depth + 1)) :
    restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i =
      fieldVectorPairSpinKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
        (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
          Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0))) := by
  unfold restrictedLevelSpinPair
  rw [restrictedPairSpinKernel_univ]
  have hB : ∀ j < h.depth, 0 < chainExponent h.cut j :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1
  have he := fieldVectorPairSpinKernel_transport N (fieldStepIncrements h)
    (finiteFieldIncrements_positive h.depth (chainExponent h.cut) (fieldStepVariance h) hB)
    (scalarFieldIncrements_positive h) (Fin.cast (by simp) i)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) rfl
  rw [he]

lemma canonicalLevelSpinPair_product {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin (h.depth + 1)) :
    (restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i).map
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm =
        Measure.pi (fun j => biasedFieldLevelSpinPair h (b j) i) := by
  rw [restrictedLevelSpinPair_univ, Measure.map_comp _ _
    (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
  exact product_kernel_comp_general
    (fieldPairSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) _)
    (fieldVectorSitePairKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h) _)
    (fieldVectorSitePairKernel_product N _ _ _)
    (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTransitionShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation covariance of the actual Gaussian transition when the
backward potential changes by a constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma tilted_add_constant {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ)
    (c : ℝ) : μ.tilted (fun x => f x + c) = μ.tilted f := by
  let _ := isProbabilityMeasure_tilted hf
  exact (tilted_tilted hf (fun _ => c)).symm.trans (tilted_const _ c)

lemma vectorGaussianTransition_shift {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (d : Fin N → ℝ) (c : ℝ) (hshift : ∀ z, F (z + d) = F z + c) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF (z + d) =
      (vectorGaussianTransition N a v F hF z).map (fun y => y + d) := by
  rw [vectorGaussianTransition_eq_map hN a v F hF hG (z + d),
    vectorGaussianTransition_eq_map hN a v F hF hG z,
    Measure.map_map (f := fun w : Fin N → ℝ => z + w) (g := fun y => y + d)
      (measurable_id.add_const d) (measurable_const.add measurable_id)]
  have he : (fun w => a * F (z + d + w)) = fun w => a * F (z + w) + a * c := by
    funext w
    rw [show z + d + w = (z + w) + d by abel, hshift, mul_add]
  rw [he, tilted_add_constant (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => a * F (z + w))
    (integrable_exp_of_linearGrowth (vectorGaussianLaw N v : Measure (Fin N → ℝ))
      (vectorGaussianLaw_moments hN v) (hF.comp (measurable_const.add measurable_id))
      (hG.add_left z) a) (a * c)]
  congr 1
  funext w
  dsimp only [Function.comp_apply]
  abel

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPairComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-free comparison of the actual constrained two-spin mean
with the site-average magnetic field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

theorem restrictedBlockPairMean_comparison {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) {t : ℝ} (ht : 0 < t) :
    |restrictedBlockPairMean hN S hS h b i -
        (N : ℝ)⁻¹ * ∑ j, magneticLevelAtBias h (b j) i| ≤
      2 * (biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b) / t + t / 2 := by
  let P := restrictedLevelSpinPair hN S hS h b i
  let Q := restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i
  let e := (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm
  let μ := P.map e
  let ν := fun j => biasedFieldLevelSpinPair h (b j) i
  let D := biasedConstrainedBlockValue Finset.univ h b - biasedConstrainedBlockValue S h b
  have hD : 0 ≤ D := (biasedConstrainedBlockValue_gap hN S hS h b).1
  have hQ : Q.map e = Measure.pi ν := canonicalLevelSpinPair_product hN h b i
  have hK : klDiv μ (Measure.pi ν) ≤ 2 * ENNReal.ofReal (N * D) := by
    rw [← hQ]
    exact (klDiv_map_le P Q e.measurable).trans (restrictedLevelSpinPair_entropy hN S hS h b i)
  have hk : klDiv μ (Measure.pi ν) ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hK
  have hkr : (klDiv μ (Measure.pi ν)).toReal ≤ 2 * (N : ℝ) * D := by
    have he := ENNReal.toReal_mono (by finiteness) hK
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg N) hD), mul_assoc] using he
  have he := spinPairSiteSum_entropy_bound μ ν hk ht
  have hmean : (∫ u, spinPairSiteSum u ∂μ) =
      ∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j) ∂P := by
    rw [show μ = P.map e from rfl, integral_map e.measurable.aemeasurable
      (measurable_of_finite spinPairSiteSum).aestronglyMeasurable]
    rfl
  rw [hmean] at he
  simp_rw [show ∀ j, (∫ p, spinPairSiteValue p ∂ν j) = magneticLevelAtBias h (b j) i
    from fun j => biasedFieldLevelSpinPair_mean h (b j) i] at he
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ = (N : ℝ)⁻¹ * |(∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j) ∂P) -
        ∑ j, magneticLevelAtBias h (b j) i| := by
      rw [restrictedBlockPairMean, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ (N : ℝ)⁻¹ * ((2 * N * D) / t + N * t / 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      exact he.trans (add_le_add_left (div_le_div_of_nonneg_right hkr ht.le) _)
    _ = _ := by
      field_simp
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPairConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform two-spin replacement along arbitrary bounded-height field
partitions, including partitions of increasing depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma tendsto_zero_of_pair_entropy (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hg : Tendsto g atTop (𝓝 0))
    (hb : ∀ t : ℝ, 0 < t → ∀ n, f n ≤ 2 * g n / t + t / 2) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hf n))
  · intro a ha
    have ht : Tendsto (fun n => 2 * g n / a) atTop (𝓝 0) := by
      simpa using (hg.const_mul 2).div_const a
    filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2))] with n hn
    have he := hb a ha n
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinBias
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constant energy shift on the constraint set cancels from its
actual conditional Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinLaw_mass {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) (T : Finset (Spin N)) :
    (restrictedSpinLaw S H).real T =
      (∑ σ ∈ S ∩ T, Real.exp (H σ)) / ∑ σ ∈ S, Real.exp (H σ) := by
  classical
  rw [measureReal_def, restrictedSpinLaw, cond_apply S.measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S)⁻¹ *
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real
      ((S : Set (Spin N)) ∩ T) = _
  rw [← Finset.coe_inter, spinGibbs_mass_finset, spinGibbs_mass_finset]
  have hZ := (sum_exp_pos H).ne'
  have hZS := (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne'
  field_simp

lemma restrictedSpinLaw_eq_of_add_on_set {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H G : Spin N → ℝ) (c : ℝ) (hG : ∀ σ ∈ S, G σ = H σ + c) :
    restrictedSpinLaw S G = restrictedSpinLaw S H := by
  classical
  have hscale (T : Finset (Spin N)) (hT : T ⊆ S) :
      (∑ σ ∈ T, Real.exp (G σ)) = Real.exp c * ∑ σ ∈ T, Real.exp (H σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hG σ (hT hσ), Real.exp_add]
    ring
  let _ := restrictedSpinLaw_probability S hS G
  let _ := restrictedSpinLaw_probability S hS H
  apply Measure.ext_of_singleton
  intro σ
  have hreal : (restrictedSpinLaw S G).real ({σ} : Finset (Spin N)) =
      (restrictedSpinLaw S H).real ({σ} : Finset (Spin N)) := by
    rw [restrictedSpinLaw_mass S hS G, restrictedSpinLaw_mass S hS H,
      hscale (S ∩ {σ}) Finset.inter_subset_left, hscale S (fun _ hx => hx)]
    exact mul_div_mul_left _ _ (Real.exp_ne_zero c)
  have he := congrArg ENNReal.ofReal hreal
  rw [measureReal_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  simpa only [Finset.coe_singleton] using he

lemma restrictedSpinKernel_group_bias {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (bias : A → ℝ) (z : Fin N → ℝ) :
    restrictedSpinKernel (spinGroupSlice group k) (z + fun j => bias (group j)) =
      restrictedSpinKernel (spinGroupSlice group k) z := by
  apply restrictedSpinLaw_eq_of_add_on_set _ (spinGroupSlice_nonempty group k hk)
    (fieldEnergy z) (fieldEnergy (z + fun j => bias (group j)))
    (spinGroupFieldConstant group k bias)
  intro σ hσ
  have he : fieldEnergy (z + fun j => bias (group j)) σ =
      fieldEnergy z σ + fieldEnergy (fun j => bias (group j)) σ := by
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [he, fieldEnergy_on_group_slice group k bias hσ]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedKernelShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Group-constant bias leaves every constrained continuation unchanged
once the same translation is applied to its current field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedTailSpinKernel_group_shift {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedTailSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb (z + fun j => bias (group j)) =
    restrictedTailSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb z := by
  induction n generalizing b v z with
  | zero => exact restrictedSpinKernel_group_bias group k hk bias z
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let S := spinGroupSlice group k
    have hS := spinGroupSlice_nonempty group k hk
    let F := restrictedFieldRecursion S n bs vs
    have hF := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    let κ := restrictedTailSpinKernel hN S hS n bs vs hbs
    let K := vectorGaussianTransition N (b 0) (v 0) F hF.1
    change (κ ∘ₖ K) (z + fun j => bias (group j)) = (κ ∘ₖ K) z
    ext T hT : 1
    rw [Kernel.comp_apply' _ _ _ hT, Kernel.comp_apply' _ _ _ hT,
      vectorGaussianTransition_shift hN (b 0) (v 0) F hF.1 hF.2
        (fun j => bias (group j)) (spinGroupFieldConstant group k bias)
        (fun y => restrictedFieldRecursion_group_bias hN group k hk bias n bs vs hbs y) z,
      lintegral_map (g := fun y : Fin N → ℝ => y + fun j => bias (group j))
        (κ.measurable_coe hT) (measurable_id.add_const _)]
    exact lintegral_congr (fun y => congrArg (fun μ : Measure (Spin N) => μ T)
      (ih bs vs hbs y))

lemma restrictedPairSpinKernel_group_shift {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j)
    (i : Fin (n + 1)) (z : Fin N → ℝ) :
    restrictedPairSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb i (z + fun j => bias (group j)) =
    restrictedPairSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb i z := by
  let _ := restrictedSpinKernel_markov (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
  induction n generalizing b v z with
  | zero =>
    simp only [restrictedPairSpinKernel, Kernel.prod_apply, restrictedSpinKernel_group_bias group k hk bias]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairSpinKernel, Fin.cases_zero, Kernel.prod_apply,
        restrictedTailSpinKernel_group_shift hN group k hk bias]
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let S := spinGroupSlice group k
      have hS := spinGroupSlice_nonempty group k hk
      let F := restrictedFieldRecursion S n bs vs
      have hF := restrictedFieldRecursion_regular hN S hS n bs vs hbs
      let κ := restrictedPairSpinKernel hN S hS n bs vs hbs j
      let K := vectorGaussianTransition N (b 0) (v 0) F hF.1
      change (κ ∘ₖ K) (z + fun j => bias (group j)) = (κ ∘ₖ K) z
      ext T hT : 1
      rw [Kernel.comp_apply' _ _ _ hT, Kernel.comp_apply' _ _ _ hT,
        vectorGaussianTransition_shift hN (b 0) (v 0) F hF.1 hF.2
          (fun j => bias (group j)) (spinGroupFieldConstant group k bias)
          (fun y => restrictedFieldRecursion_group_bias hN group k hk bias n bs vs hbs y) z,
        lintegral_map (g := fun y : Fin N → ℝ => y + fun j => bias (group j))
        (κ.measurable_coe hT) (measurable_id.add_const _)]
      exact lintegral_congr (fun y => congrArg (fun μ : Measure (Spin N × Spin N) => μ T)
        (ih bs vs hbs j y))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRootShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the optimizing group biases from the actual shared-root
constrained spin-pair law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal BigOperators Topology

namespace InvariantIsing

lemma kernel_gaussian_root_shift {N : ℕ} {X : Type*} [MeasurableSpace X]
    (κ : Kernel (Fin N → ℝ) X) [IsMarkovKernel κ] (v : ℝ≥0) (d : Fin N → ℝ)
    (hκ : ∀ z, κ (z + d) = κ z) :
    κ ∘ₘ Measure.pi (fun j => gaussianReal (d j) v) =
      κ ∘ₘ (vectorGaussianLaw N v : Measure (Fin N → ℝ)) := by
  ext T hT
  rw [Measure.bind_apply hT κ.aemeasurable, Measure.bind_apply hT κ.aemeasurable,
    ← (vectorGaussian_shift v d).map_eq, lintegral_map (g := fun w : Fin N → ℝ => d + w) (κ.measurable_coe hT)
      (measurable_const.add measurable_id)]
  apply lintegral_congr
  intro z
  rw [add_comm d z, hκ]

lemma restrictedLevelSpinPair_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (h : FieldStep) (i : Fin (h.depth + 1)) :
    restrictedLevelSpinPair hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun j => bias (group j)) i =
    restrictedLevelSpinPair hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun _ => 0) i := by
  unfold restrictedLevelSpinPair
  exact kernel_gaussian_root_shift _ _ (fun j => bias (group j))
    (fun z => restrictedPairSpinKernel_group_shift hN group k hk bias _ _ _ _ i z)

lemma restrictedBlockPairMean_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (h : FieldStep) (i : Fin (h.depth + 1)) :
    restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun j => bias (group j)) i =
    restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun _ => 0) i := by
  unfold restrictedBlockPairMean
  rw [restrictedLevelSpinPair_group_bias hN group k hk bias]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical site-average overlap path and its uniform comparison
with the original constrained-block overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma magneticBlockPairMean_comparison {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) (i : Fin (h.depth + 1)) {t : ℝ} (ht : 0 < t) :
    |restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
        h (fun _ => 0) i - magneticBlockLevel h (fun j => m (group j)) i| ≤
      2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2 := by
  have he := restrictedBlockPairMean_comparison hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun j => magneticBias h (m (group j))) i ht
  rw [← magneticBlockGap_eq_biasedGap hN group k hk m hm hc h,
    restrictedBlockPairMean_group_bias hN group k hk (fun a => magneticBias h (m a)) h i] at he
  exact he

lemma magneticBlockPath_l1_comparison {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) {t : ℝ} (ht : 0 < t) :
    (∫ s, |restrictedBlockOverlapPath hN (spinGroupSlice group k)
        (spinGroupSlice_nonempty group k hk) h s - magneticBlockPath hN h (fun j => m (group j)) s|
      ∂pathMeasure) ≤
      2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2 := by
  let p := restrictedBlockOverlapPath hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h
  let q := magneticBlockPath hN h (fun j => m (group j))
  calc
    _ ≤ ∫ _s, (2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2) ∂pathMeasure := by
      apply integral_mono (p.integrable.sub q.integrable).abs (integrable_const _)
      intro s
      exact magneticBlockPairMean_comparison hN group k hk m hm hc h (fieldLevelIndex h s) ht
    _ = _ := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockPathConvergence
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform replacement of the entire original constrained overlap path,
with no bound on the number of covariance levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

theorem magneticBlockPath_l1_tendsto_oai {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H) :
    Tendsto (fun n => ∫ s, |restrictedBlockOverlapPath (hN n)
      (spinGroupSlice (group n) (k n)) (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n) s -
        magneticBlockPath (hN n) (h n) (fun j => m n (group n j)) s| ∂pathMeasure)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_pair_entropy _
    (fun n => (N n : ℝ)⁻¹ * (∑ j, constrainedFieldValue (h n) (m n (group n j))) -
      constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n))
    (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (magneticBlockGap_tendsto N hN hNlim group k hk m hr hm hc h hH)
  intro t ht n
  exact magneticBlockPath_l1_comparison (hN n) (group n) (k n) (hk n) (m n)
    (fun a => (hm n a).trans_lt hr) (hc n) (h n) ht

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.magneticBlockPath_l1_tendsto_oai.{u_1} := @OAI.InvariantIsing.magneticBlockPath_l1_tendsto_oai.{u_1}
