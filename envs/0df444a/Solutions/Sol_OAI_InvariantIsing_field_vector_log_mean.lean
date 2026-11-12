-- Prove2me | solution 1 for OAI.InvariantIsing.field_vector_log_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:58.664269+00:00
-- url     : https://prove2.me/submissions/3e6e378e-5b7e-4d01-bdcd-e6a52210c09d

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_field_vector_log_root_integral

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
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

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

end IsingPerceptron

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
namespace IsingPerceptron

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

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
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
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

lemma heightSequence_mono (h : FieldStep) : Monotone (heightSequence h) := by
  intro i j hij
  apply h.ordered_height
  exact min_le_min_right h.depth hij

lemma heightSequence_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ heightSequence h i :=
  h.nonneg _

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

/-- Equality with the scalar recursion, including its root Gaussian average
and diagonal covariance subtraction. -/
lemma fieldValue_eq_magneticFieldValue (h : FieldStep) :
    fieldValue h 0 = IsingPerceptron.magneticFieldValue h.depth
      (IsingPerceptron.chainExponent h.cut) (heightSequence h) := by
  let w := heightSequence h
  have hw : Monotone w := heightSequence_mono h
  have hw0 : 0 ≤ w 0 := heightSequence_nonneg h 0
  have htail : List.ofFn (fun i : Fin h.depth =>
      ((fieldIncrement h i.succ).2, (fieldIncrement h i.succ).1)) =
      List.ofFn (fun i : Fin h.depth =>
        ((IsingPerceptron.pathAmplitude w (i + 1)) ^ 2,
          IsingPerceptron.chainExponent h.cut i)) := by
    apply congrArg List.ofFn
    funext i
    rw [IsingPerceptron.pathAmplitude_sq hw hw0]
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, IsingPerceptron.pathIncrement,
      IsingPerceptron.chainExponent_apply h.cut i.isLt]
    congr 1
    change h.height i.succ - h.height ⟨i.val, by omega⟩ =
      heightSequence h (i.val + 1) - heightSequence h i.val
    rw [heightSequence_eq h _ (by omega), heightSequence_eq h _ (by omega)]
    rfl
  have hfold : (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) =
      IsingPerceptron.magneticRecursion h.depth
        (fun i => IsingPerceptron.pathAmplitude w (i + 1))
        (IsingPerceptron.chainExponent h.cut) := by
    simp_rw [gaussianOperator_eq_transform]
    rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
      (g := fun sd f => IsingPerceptron.gaussianTransform sd.1 sd.2 f)]
    rw [List.map_ofFn]
    simp only [Function.comp_def]
    rw [htail]
    exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
      (fun i => IsingPerceptron.pathAmplitude w (i + 1))
      (IsingPerceptron.chainExponent h.cut)).symm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    dsimp only [fieldIncrement]
    simp [h.first]
  have hzero : w 0 = h.height 0 := heightSequence_eq h 0 (Nat.zero_le _)
  have hlast : w h.depth = h.height (Fin.last h.depth) := heightSequence_eq h _ le_rfl
  have hamp : IsingPerceptron.pathAmplitude w 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, hzero]
  rw [fieldValue, List.ofFn_succ, List.foldr_cons, hfold, hroot]
  simp only [gaussianOperator, ite_true, if_true, zero_add, IsingPerceptron.magneticFieldValue]
  dsimp only [w] at hamp hlast ⊢
  rw [hamp, hlast]

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

lemma gaussianCascadeRecursion_eq_fold (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, b i ≠ 0) {F : ℝ → ℝ} (hF : Measurable F) :
    IsingPerceptron.cascadeRecursion n b
      (fun i => ⟨gaussianReal 0 (v i), inferInstance⟩)
      (fun _ p => p.1 + p.2) F =
      (List.ofFn (fun i : Fin n => (b i, (v i : ℝ)))).foldr
        (fun av U => gaussianOperator av.1 av.2 U) F := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have ht := IsingPerceptron.measurable_cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ => measurable_fst.add measurable_snd) hF
    have he := ih (fun i => b (i + 1)) (fun i => v (i + 1))
      (fun i hi => hb (i + 1) (by omega))
    change Measurable (IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
      (fun i => (⟨gaussianReal 0 (v (i + 1)), inferInstance⟩ : ProbabilityMeasure ℝ))
      (fun _ p => p.1 + p.2) F) at ht
    rw [he] at ht
    rw [List.ofFn_succ, List.foldr_cons]
    funext x
    change IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
      (fun g => IsingPerceptron.cascadeRecursion n (fun i => b (i + 1))
        (fun i => ⟨gaussianReal 0 (v (i + 1)), inferInstance⟩)
        (fun _ p => p.1 + p.2) F (x + g)) = _
    rw [he]
    exact (gaussianOperator_eq_gaussian_logMean (hb 0 (by omega)) (v 0) ht x).symm

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : Measurable (rotatedFieldTerminal eig U c) := by
  unfold rotatedFieldTerminal logPartition fieldEnergy
  fun_prop

lemma abs_rotatedFieldTerminal_sub_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c z w : Fin N → ℝ) :
    |rotatedFieldTerminal eig U c z - rotatedFieldTerminal eig U c w| ≤
      (N : ℝ) * ‖z - w‖ := by
  have he (σ : Spin N) :
      |(rotatedEnergy eig U σ + fieldEnergy (c + z) σ) -
        (rotatedEnergy eig U σ + fieldEnergy (c + w) σ)| ≤ (N : ℝ) * ‖z - w‖ := by
    rw [add_sub_add_left_eq_sub]
    calc
      _ ≤ ∑ i, |(c + z) i - (c + w) i| := abs_fieldEnergy_sub_le _ _ σ
      _ = ∑ i, |z i - w i| := by simp only [Pi.add_apply, add_sub_add_left_eq_sub]
      _ ≤ ∑ _ : Fin N, ‖z - w‖ := Finset.sum_le_sum fun i _ => by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - w) i
      _ = (N : ℝ) * ‖z - w‖ := by simp
  exact abs_logPartition_sub_le _ _ _ he

lemma rotatedFieldTerminal_linearGrowth {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : IsingPerceptron.HasLinearGrowth (rotatedFieldTerminal eig U c) := by
  refine ⟨|rotatedFieldTerminal eig U c 0|, N, abs_nonneg _, Nat.cast_nonneg _, fun z => ?_⟩
  have hl := abs_rotatedFieldTerminal_sub_le eig U c z 0
  rw [sub_zero] at hl
  have ht := abs_add_le (rotatedFieldTerminal eig U c z - rotatedFieldTerminal eig U c 0)
    (rotatedFieldTerminal eig U c 0)
  rw [sub_add_cancel] at ht
  linarith

lemma integrable_rotatedCascadeValue {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) (root : ℝ≥0) :
    Integrable (rotatedCascadeValue n b v eig U c)
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  have hm := IsingPerceptron.measurable_cascadeRecursion n b
    (fun i => vectorGaussianLaw N (v i))
    (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
  change Measurable (rotatedCascadeValue n b v eig U c) at hm
  have hg := IsingPerceptron.cascadeRecursion_linearGrowth n b
    (fun i => vectorGaussianLaw N (v i)) (fun i _ => vectorGaussianLaw_moments hN (v i))
    (measurable_rotatedFieldTerminal eig U c) (rotatedFieldTerminal_linearGrowth eig U c)
    (fun i hi => (hb.1 i hi).1)
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add ((vectorGaussianLaw_moments hN root 1).const_mul L)
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |rotatedCascadeValue n b v eig U c z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCascade
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite one-site functional as a Gaussian cascade expectation. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldCascadeFold_eq_magneticRecursion (h : FieldStep) :
    (List.ofFn (fun i : Fin h.depth =>
      (IsingPerceptron.chainExponent h.cut i, (fieldCascadeVariance h i : ℝ)))).foldr
      (fun av U => gaussianOperator av.1 av.2 U) (fun x => Real.log (Real.cosh x)) =
    IsingPerceptron.magneticRecursion h.depth
      (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
      (IsingPerceptron.chainExponent h.cut) := by
  simp_rw [gaussianOperator_eq_transform]
  rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
    (g := fun sd U => IsingPerceptron.gaussianTransform sd.1 sd.2 U), List.map_ofFn]
  simp only [Function.comp_def, fieldCascadeVariance, NNReal.coe_mk]
  exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
    (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
    (IsingPerceptron.chainExponent h.cut)).symm

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
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.mem_fieldCutSet _root_.OAI.InvariantIsing.rotationMatrix_one
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

theorem rotatedCascadeValue_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c z : Fin N → ℝ) :
    rotatedCascadeValue n b v (fun _ => 0) U c z =
      ∑ i, ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
        (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)))
        (c i + z i) := by
  have ht : rotatedFieldTerminal (fun _ : Fin N => 0) U c =
      (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) := by
    funext y
    simp only [rotatedFieldTerminal, rotatedEnergy_constant, zero_mul, zero_div, zero_add]
    simpa only [Pi.add_apply] using logPartition_fieldEnergy (c + y)
  unfold rotatedCascadeValue
  rw [ht, vectorCascade_logCosh_sum N n b v (fun i hi => (hb.1 i hi).1)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (gaussianCascadeRecursion_eq_fold n b v
    (fun j hj => (hb.1 j hj).1.ne') IsingPerceptron.measurable_logCosh) (c i + z i)

lemma integrable_gaussianReal_of_linearGrowth (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : IsingPerceptron.HasLinearGrowth F) :
    Integrable F (gaussianReal 0 v) := by
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add
    ((IsingPerceptron.gaussianReal_exponentialNormMoments 0 v 1).const_mul L)
  apply hi.mono' hF.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |F z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

theorem rotatedEnrichedPressure_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (root : ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b v root (fun _ => 0) U c =
      (N : ℝ)⁻¹ * ∑ i, gaussianOperator 0 root
        ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
          (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y))) (c i) := by
  let F := IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks v j)
    (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
  have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n b
    (fun j => gaussianCascadeMarks v j) (fun _ => measurable_fst.add measurable_snd)
    IsingPerceptron.measurable_logCosh
  have hg : IsingPerceptron.HasLinearGrowth F :=
    IsingPerceptron.cascadeRecursion_linearGrowth n b (fun j => gaussianCascadeMarks v j)
      (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v j))
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
      (fun j hj => (hb.1 j hj).1)
  have hfi (i : Fin N) : Integrable (fun g => F (c i + g)) (gaussianReal 0 root) :=
    integrable_gaussianReal_of_linearGrowth root (hm.comp (measurable_const.add measurable_id))
      (hg.add_left (c i))
  have hF : F = (List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)) :=
    gaussianCascadeRecursion_eq_fold n b v (fun j hj => (hb.1 j hj).1.ne')
      IsingPerceptron.measurable_logCosh
  unfold rotatedEnrichedPressure
  congr 1
  calc
    _ = ∫ z : Fin N → ℝ, (∑ i, F (c i + z i))
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        rw [rotatedCascadeValue_zero_interaction n b v hb U c z]
        simp only [hF]
    _ = ∑ i, ∫ z : Fin N → ℝ, F (c i + z i)
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) :=
      integral_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).integrable_comp
          (hfi i).aestronglyMeasurable |>.mpr (hfi i))
    _ = ∑ i, ∫ g, F (c i + g) ∂gaussianReal 0 root := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).hasLaw.integral_comp
        ((hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hs : Measurable (fun g : ℝ => F (c i + g)) :=
        hm.comp (measurable_const.add measurable_id)
      rw [integral_gaussianReal_zero_eq_standard root hs, hF]
      simp [gaussianOperator]

/-- The exact zero-time normalization in `up:zero-time`, before perturbations. -/
theorem rotatedEnrichedPressure_field_zero_time {N : ℕ} (hN : 0 < N)
    (h : FieldStep) (U : Rotation N) :
    rotatedEnrichedPressure h.depth (IsingPerceptron.chainExponent h.cut) (fieldCascadeVariance h)
      (NNReal.mk (h.height 0) (h.nonneg 0)) (fun _ => 0) U (fun _ => 0) -
      h.height (Fin.last h.depth) / 2 = fieldValue h 0 := by
  rw [rotatedEnrichedPressure_zero_interaction h.depth (IsingPerceptron.chainExponent h.cut)
    (fieldCascadeVariance h) _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last) U (fun _ => 0)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul, fieldCascadeFold_eq_magneticRecursion]
  simp only [gaussianOperator, zero_add, NNReal.coe_mk]
  rw [ite_true]
  rw [fieldValue_eq_magneticFieldValue]
  unfold IsingPerceptron.magneticFieldValue
  have hroot : IsingPerceptron.pathAmplitude (heightSequence h) 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, heightSequence]
  have hlast : heightSequence h h.depth = h.height (Fin.last h.depth) :=
    heightSequence_eq h _ le_rfl
  rw [hroot, hlast]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteFieldVariance
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar variances in the published field marking input coincide
with the finite spectral cavity covariance increments. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_height_sub (h : FieldStep) (i : Fin h.depth) :
    (fieldStepVariance h i : ℝ) = h.height i.succ - h.height i.castSucc := by
  rw [fieldStepVariance, dite_eq_left i.isLt]
  have hg : (scalarFieldIncrements h).get
      ⟨i, by simpa only [scalarFieldIncrements_length] using i.isLt⟩ =
      ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
    exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
      NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) _
  rw [hg]
  change (fieldIncrement h i.succ).2 = _
  simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero,
    dite_false, Nat.add_sub_cancel]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianIntegral
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar square completion for the quadratic cavity tilt.  The variance
may vanish; only positivity of the resulting precision is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_complete_square (b c d x : ℝ) (hb : b ≠ 0) :
    -b * x ^ 2 + c * x + d =
      -b * (x - c / (2 * b)) ^ 2 + (c ^ 2 / (4 * b) + d) := by
  field_simp [hb]
  ring

lemma cavity_integral_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2 + c * x + d)) =
      Real.sqrt (Real.pi / b) * Real.exp (c ^ 2 / (4 * b) + d) := by
  simp_rw [cavity_complete_square b c d _ hb.ne', Real.exp_add]
  rw [integral_mul_const, integral_sub_right_eq_self
    (fun x : ℝ => Real.exp (-b * x ^ 2)) (c / (2 * b)), integral_gaussian]

private lemma cavity_gaussian_weighted_integrand (v : ℝ≥0) (a u z : ℝ) :
    gaussianPDFReal 0 v z * Real.exp (a / 2 * (u + z) ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-( (1 - v * a) / (2 * v)) * z ^ 2 +
          (a * u) * z + a * u ^ 2 / 2) := by
  by_cases hv : (v : ℝ) = 0
  · simp [gaussianPDFReal, hv]
  simp only [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp [hv]
  ring

private lemma cavity_gaussian_normalizer (v : ℝ≥0) (a : ℝ)
    (hv : 0 < (v : ℝ)) (hq : 0 < 1 - v * a) :
    (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.sqrt (Real.pi / ((1 - v * a) / (2 * v))) =
      (Real.sqrt (1 - v * a))⁻¹ := by
  calc
    _ = Real.sqrt ((Real.pi / ((1 - v * a) / (2 * v))) /
        (2 * Real.pi * v)) := by
      conv_rhs => rw [Real.sqrt_div' _ (by positivity)]
      ring
    _ = Real.sqrt ((1 - v * a)⁻¹) := by
      congr 1
      field_simp [hv.ne', hq.ne', Real.pi_ne_zero]
    _ = _ := Real.sqrt_inv _

private lemma cavity_gaussian_constant (v a u : ℝ)
    (hq : 1 - v * a ≠ 0) :
    (a * u) ^ 2 / (4 * ((1 - v * a) / (2 * v))) + a * u ^ 2 / 2 =
      a * u ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [hq, hq']
  ring

/-- The one-dimensional form of `cav:q-gaussian-integral`, including
singular covariance `v = 0`. -/
theorem cavity_gaussian_quadratic_integral (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * (u + z) ^ 2) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ * Real.exp (a * u ^ 2 / (2 * (1 - v * a))) := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
    ring
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (1 - (v : ℝ) * a) / (2 * v) := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [cavity_gaussian_weighted_integrand]
  rw [integral_const_mul, cavity_integral_exp_quadratic _ _ _ hb]
  rw [← mul_assoc, cavity_gaussian_normalizer v a hvpos hq,
    cavity_gaussian_constant v a u hq.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianAffine
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine quadratic Gaussian integrals.  Independent linear terms are
needed after diagonalizing the precision of a noncommuting cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_affine_complete_square (a c d z : ℝ) (ha : a ≠ 0) :
    Real.exp (a / 2 * z ^ 2 + c * z + d) =
      Real.exp (a / 2 * (c / a + z) ^ 2) * Real.exp (d - c ^ 2 / (2 * a)) := by
  rw [← Real.exp_add]
  congr 1
  field_simp [ha]
  ring

private lemma cavity_affine_constant (v a c d : ℝ) (ha : a ≠ 0)
    (hq : 1 - v * a ≠ 0) :
    a * (c / a) ^ 2 / (2 * (1 - v * a)) + (d - c ^ 2 / (2 * a)) =
      d + v * c ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [ha, hq, hq']
  ring

private lemma cavity_gaussian_linear_integral (v : ℝ≥0) (c : ℝ) :
    (∫ z : ℝ, Real.exp (c * z) ∂gaussianReal 0 v) =
      Real.exp (v * c ^ 2 / 2) := by
  simpa only [mgf, zero_mul, zero_add] using
    congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) c

theorem cavity_gaussian_affine_integral (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * z ^ 2 + c * z + d) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ *
        Real.exp (d + v * c ^ 2 / (2 * (1 - v * a))) := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, zero_mul, zero_add, mul_zero, sub_zero,
      Real.sqrt_one, inv_one, one_mul, mul_one, Real.exp_add, integral_mul_const]
    rw [cavity_gaussian_linear_integral]
    ring
  simp_rw [cavity_affine_complete_square a c d _ ha]
  rw [integral_mul_const, cavity_gaussian_quadratic_integral v a (c / a) hq,
    mul_assoc, ← Real.exp_add, cavity_affine_constant v a c d ha hq.ne']

theorem cavity_diagonal_gaussian_affine_integral {d : ℕ}
    (v : Fin d → ℝ≥0) (a c : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    (∫ z : Fin d → ℝ, Real.exp (∑ i, (a i / 2 * z i ^ 2 + c i * z i))
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      (∏ i, (Real.sqrt (1 - v i * a i))⁻¹) *
        Real.exp (∑ i, v i * c i ^ 2 / (2 * (1 - v i * a i))) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i x => Real.exp (a i / 2 * x ^ 2 + c i * x))]
  have hi i := cavity_gaussian_affine_integral (v i) (a i) (c i) 0 (hq i)
  simp only [add_zero, zero_add] at hi
  simp_rw [hi]
  exact Finset.prod_mul_distrib

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary terminal residual in the cavity spin factor. Its
variance contributes a constant because every Ising spin has norm squared
equal to the number of cavity sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma cavity_spin_linear_gaussian_integral {n : ℕ}
    (v : ℝ≥0) (ε : Spin n) :
    (∫ w : Fin n → ℝ, Real.exp (fieldEnergy w ε)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ))) = Real.exp ((n : ℝ) * v / 2) := by
  have h := cavity_diagonal_gaussian_affine_integral (fun _ : Fin n => v)
    (fun _ => 0) (fun i => spinValue (ε i)) (fun _ => by simp)
  have he : (fun w : Fin n → ℝ => Real.exp (fieldEnergy w ε)) =
      (fun w : Fin n → ℝ => Real.exp (∑ i, (0 / 2 * w i ^ 2 + spinValue (ε i) * w i))) := by
    funext w
    simp only [fieldEnergy, zero_div, zero_mul, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change (∫ w : Fin n → ℝ, Real.exp (∑ i, (0 / 2 * w i ^ 2 + spinValue (ε i) * w i))
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 v)) = _
  rw [h]
  simp only [mul_zero, sub_zero, Real.sqrt_one, inv_one, Finset.prod_const_one,
    one_mul, spinValue_sq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  congr 1
  ring

/-- The ordinary Gaussian residual supplies `n*v/2` to the logarithm,
independently of the chosen cavity spin. -/
theorem cavity_residual_spin_integral {n : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin n → ℝ) (ε : Spin n) :
    (∫ w : Fin n → ℝ, Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ))) =
        Real.exp (fieldEnergy z ε + (n : ℝ) * (c + v) / 2) := by
  have he : (fun w : Fin n → ℝ => Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)) =
      (fun w => Real.exp (fieldEnergy z ε + (n : ℝ) * c / 2) * Real.exp (fieldEnergy w ε)) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he, integral_const_mul, cavity_spin_linear_gaussian_integral, ← Real.exp_add]
  congr 1
  ring

/-- The residual-integrated cavity terminal is a sum of one-site
`log cosh` terminals plus the deterministic scalar contribution. -/
theorem cavityResidualSpinLog_eq (n : ℕ) (v : ℝ≥0) (c : ℝ) (z : Fin n → ℝ) :
    cavityResidualSpinLog n v c z =
      (n : ℝ) * (c + v) / 2 + ∑ i, Real.log (Real.cosh (z i)) := by
  unfold cavityResidualSpinLog
  simp_rw [cavity_residual_spin_integral]
  change logPartition (fun ε : Spin n => fieldEnergy z ε + (n : ℝ) * (c + v) / 2) = _
  rw [logPartition_add_const, logPartition_fieldEnergy]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent-site backward recursion after the ordinary cavity
residual is integrated. The residual contributes an additive constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma cavity_sum_logCosh_linearGrowth (N : ℕ) :
    HasLinearGrowth (fun z : Fin N → ℝ => ∑ i, Real.log (Real.cosh (z i))) := by
  refine ⟨0, N, le_rfl, Nat.cast_nonneg _, ?_⟩
  intro z
  simp only [zero_add]
  calc
    _ ≤ ∑ i, |Real.log (Real.cosh (z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (abs_log_cosh_le (z i)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
    _ = _ := by simp

private lemma cavity_vector_recursion_const_add (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (a : ℝ) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (fun y => a + ∑ i, Real.log (Real.cosh (y i))) z =
      a + cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (y i))) z := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let F := cascadeRecursion n bs (fun i => vectorGaussianLaw N (vs i))
      (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i)))
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hm : Measurable F := measurable_cascadeRecursion n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun _ => measurable_fst.add measurable_snd)
      (by fun_prop)
    have hg : HasLinearGrowth F := cascadeRecursion_linearGrowth n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun i _ => vectorGaussianLaw_moments hN (vs i))
      (by fun_prop) (cavity_sum_logCosh_linearGrowth N) hbs
    have he : (fun g : Fin N → ℝ => cascadeRecursion n bs
        (fun i => vectorGaussianLaw N (vs i)) (fun _ p => p.1 + p.2)
        (fun y => a + ∑ i, Real.log (Real.cosh (y i))) (z + g)) =
        (fun g => a + F (z + g)) := by
      funext g
      exact ih bs vs hbs (z + g)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) _ =
      a + logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) _
    rw [he]
    exact logMean_const_add _ (hb 0 (by omega)).ne'
      (integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left z) (b 0)) a

/-- The transformed cavity spin recursion separates into one identical
scalar recursion per cavity site; the ordinary residual is not a new
Poisson level. -/
theorem cavityResidualSpinLog_recursion (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (r : ℝ≥0) (c : ℝ) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (cavityResidualSpinLog N r c) z =
      (N : ℝ) * (c + r) / 2 +
        ∑ i, cascadeRecursion n b (gaussianCascadeMarks v) (fun _ p => p.1 + p.2)
          (fun y => Real.log (Real.cosh y)) (z i) := by
  have ht : cavityResidualSpinLog N r c =
      (fun y => (N : ℝ) * (c + r) / 2 + ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    exact cavityResidualSpinLog_eq N r c y
  rw [ht, cavity_vector_recursion_const_add N hN n b v hb]
  congr 1
  simpa only [zero_add] using vectorCascade_logCosh_sum N n b v hb (fun _ => 0) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarRoot
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root-averaged scalar spin recursion occurring after the cavity
quadratic change of measure, in the manuscript's field normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem cavityScalarCascadeMean_normalized (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (root residual : ℝ≥0) (c : ℝ) (U : Rotation N) :
    (N : ℝ)⁻¹ * cavityScalarCascadeMean N n b v root residual c =
      rotatedEnrichedPressure n b v root (fun _ => 0) U (fun _ => 0) + (c + residual) / 2 := by
  have ht : rotatedFieldTerminal (fun _ : Fin N => 0) U (fun _ => 0) =
      (fun y => ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    simp only [rotatedFieldTerminal, rotatedEnergy_constant, zero_mul, zero_div, zero_add]
    change logPartition (fieldEnergy ((0 : Fin N → ℝ) + y)) = _
    simpa only [zero_add] using logPartition_fieldEnergy y
  have he (z : Fin N → ℝ) :
      cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
        (cavityResidualSpinLog N residual c) z =
        (N : ℝ) * (c + residual) / 2 +
          rotatedCascadeValue n b v (fun _ => 0) U (fun _ => 0) z := by
    rw [cavityResidualSpinLog_recursion N hN n b v (fun i hi => (hb.1 i hi).1),
      rotatedCascadeValue, ht]
    congr 1
    simpa only [zero_add] using
      (vectorCascade_logCosh_sum N n b v (fun i hi => (hb.1 i hi).1) (fun _ => 0) z).symm
  have hi := integrable_rotatedCascadeValue hN n b v hb (fun _ => 0) U (fun _ => 0) root
  unfold cavityScalarCascadeMean
  simp_rw [he]
  rw [integral_add (integrable_const _) hi, integral_const]
  simp only [probReal_univ, one_smul]
  unfold rotatedEnrichedPressure
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  ring

/-- The scalar part in `cav:before-parts`, with the root interval and
ordinary residual both included. -/
theorem cavityScalarCascadeMean_fieldStep (N : ℕ) (hN : 0 < N)
    (h : FieldStep) (residual : ℝ≥0) (c : ℝ) (U : Rotation N) :
    (N : ℝ)⁻¹ * cavityScalarCascadeMean N h.depth (chainExponent h.cut)
      (fieldCascadeVariance h) (NNReal.mk (h.height 0) (h.nonneg 0)) residual c =
      fieldValue h 0 + h.height (Fin.last h.depth) / 2 + (c + residual) / 2 := by
  rw [cavityScalarCascadeMean_normalized N hN h.depth (chainExponent h.cut)
    (fieldCascadeVariance h) (chainExponent_admissible h.ordered_cut h.first h.last)
    (NNReal.mk (h.height 0) (h.nonneg 0)) residual c U]
  have he := rotatedEnrichedPressure_field_zero_time hN h U
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLogMean
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The log normalizer has the manuscript's scalar field value, with
its terminal covariance subtraction restored before taking the mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_fieldCascadeVariance (h : FieldStep) :
    fieldStepVariance h = fieldCascadeVariance h := by
  funext i
  apply NNReal.eq
  change (fieldStepVariance h i : ℝ) = (pathAmplitude (heightSequence h) (i + 1))^2
  rw [pathAmplitude_sq (heightSequence_mono h) (heightSequence_nonneg h 0), pathIncrement]
  by_cases hi : i < h.depth
  · rw [fieldStepVariance_eq_height_sub h ⟨i, hi⟩,
      heightSequence_eq h (i + 1) (by omega), heightSequence_eq h i (by omega)]
    rfl
  · have hle : h.depth ≤ i := Nat.le_of_not_gt hi
    simp only [fieldStepVariance, dite_eq_right hi, NNReal.coe_zero, heightSequence,
      min_eq_right hle, min_eq_right (hle.trans (Nat.le_succ i)), sub_self]

theorem field_vector_log_mean_oai (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (U : Rotation N) :
    let μ := (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) :
      Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)
    Integrable (fun p => fieldVectorLogNormalizer N h p.1 p.2) μ ∧
      (N : ℝ)⁻¹ * (∫ p, fieldVectorLogNormalizer N h p.1 p.2 ∂μ) =
        fieldValue h 0 + h.height (Fin.last h.depth) / 2 := by
  intro μ
  have hc := field_vector_log_root_integral N hN h
    (NNReal.mk (h.height 0) (h.nonneg 0))
  refine ⟨hc.1, ?_⟩
  rw [hc.2, fieldStepVariance_eq_fieldCascadeVariance]
  have he := cavityScalarCascadeMean_fieldStep N hN h 0 0 U
  have hterm : cavityResidualSpinLog N 0 0 =
      (fun y => ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    simp only [cavityResidualSpinLog_eq, NNReal.coe_zero, add_zero, mul_zero,
      zero_div, zero_add]
  simpa only [cavityScalarCascadeMean, hterm, NNReal.coe_zero, add_zero, zero_div] using he

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.field_vector_log_mean_oai := @OAI.InvariantIsing.field_vector_log_mean_oai
