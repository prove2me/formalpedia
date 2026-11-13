-- Prove2me | solution 1 for OAI.InvariantIsing.magneticCanonical_projection_distance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:00:12.732383+00:00
-- url     : https://prove2.me/submissions/7afe0bcd-646c-403b-9a99-65820a99d616

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_fieldBiasMean_magneticBias

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

lemma finite_weighted_sum_abs_le_sqrt {X : Type*} [Fintype X]
    (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    |∑ x, p x * f x| ≤ Real.sqrt (∑ x, p x * f x ^ 2) := by
  have hn : 0 ≤ ∑ x, p x * f x ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hn]
  exact finite_weighted_sum_sq_le p f hp hpSum

lemma finite_integral_abs_le_sqrt_sq {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ) :
    (∫ x, |F x| ∂μ) ≤ Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
  let p := fun x : X => μ.real {x}
  have hp : ∀ x, 0 ≤ p x := fun x => measureReal_nonneg
  have hsum : ∑ x, p x = 1 := by
    have he := integral_fintype (μ := μ) (f := fun _ : X => (1 : ℝ)) Integrable.of_finite
    simpa [p, measureReal_def] using he.symm
  have he := finite_weighted_sum_abs_le_sqrt p (fun x => |F x|) hp hsum
  have hn : 0 ≤ ∑ x, p x * |F x| :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (abs_nonneg _))
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul, p,
    abs_of_nonneg hn, sq_abs] using he

end InvariantIsing

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupCountVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Count fluctuations under the independent canonical site law. The
result applies to the averaged Gaussian spin kernels as soon as their
bias equations give the prescribed group means. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace InvariantIsing

lemma sum_spinGroupCountSummand {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (σ : Spin N) :
    (∑ i, spinGroupCountSummand group a i (σ i)) = spinGroupCount group σ a := by
  simp [spinGroupCountSummand, spinGroupCount]

lemma spinGroupCountSummand_memLp {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (μ : Measure Bool) [IsFiniteMeasure μ] :
    MemLp (spinGroupCountSummand group a i) 2 μ := by
  apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
  apply ae_of_all
  intro b
  simp only [spinGroupCountSummand]
  split_ifs <;> norm_num

lemma variance_spinGroupCountSummand_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (μ : Measure Bool) [IsProbabilityMeasure μ] :
    Var[spinGroupCountSummand group a i; μ] ≤ if group i = a then (1 : ℝ) else 0 := by
  rw [variance_eq_sub (spinGroupCountSummand_memLp group a i μ)]
  have hi : (∫ b, (spinGroupCountSummand group a i b) ^ 2 ∂μ) ≤
      if group i = a then (1 : ℝ) else 0 := by
    calc
      _ ≤ ∫ _b, (if group i = a then (1 : ℝ) else 0) ∂μ :=
        integral_mono Integrable.of_finite (integrable_const _) (fun b => by
          by_cases hg : group i = a <;> cases b <;> simp [spinGroupCountSummand, hg])
      _ = _ := by
        have hu : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ]; norm_num
        simp only [integral_const, hu, one_smul]
  change (∫ b, (spinGroupCountSummand group a i b) ^ 2 ∂μ) - _ ≤ _
  linarith [sq_nonneg (∫ b, spinGroupCountSummand group a i b ∂μ)]

theorem spinGroupCount_variance_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] :
    Var[fun σ : Spin N => (spinGroupCount group σ a : ℝ); Measure.pi μ] ≤
      spinGroupSize group a := by
  have hf : (fun σ : Spin N => (spinGroupCount group σ a : ℝ)) =
      ∑ i, fun σ : Spin N => spinGroupCountSummand group a i (σ i) := by
    funext σ
    simp only [Finset.sum_apply, sum_spinGroupCountSummand]
  rw [hf, variance_sum_pi (fun i => spinGroupCountSummand_memLp group a i (μ i))]
  calc
    _ ≤ ∑ i, if group i = a then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => variance_spinGroupCountSummand_le group a i (μ i))
    _ = _ := by simp [spinGroupSize]

theorem spinGroupCount_centered_sq_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (k : ℕ)
    (hmean : (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) = k) :
    (∫ σ : Spin N, ((spinGroupCount group σ a : ℝ) - k) ^ 2 ∂Measure.pi μ) ≤
      spinGroupSize group a := by
  have hv := spinGroupCount_variance_le group a μ
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable, hmean] at hv
  exact hv

theorem spinGroupProjection_product_mean_distance {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hmean : ∀ a, (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) = k a) :
    (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ) ∂Measure.pi μ) ≤
      ∑ a, Real.sqrt (spinGroupSize group a) := by
  simp_rw [spinGroupProjection_distance_real]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_le_sum
  intro a _
  exact (finite_integral_abs_le_sqrt_sq (Measure.pi μ)
    (fun σ : Spin N => (spinGroupCount group σ a : ℝ) - k a)).trans
      (Real.sqrt_le_sqrt (spinGroupCount_centered_sq_le group a μ (k a) (hmean a)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCanonicalSpin
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical spin law, including the ordinary Gaussian root.
Its mean is the physical bias derivative, so optimizing the bias gives
the requested group magnetizations exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldCanonicalSpinLaw_mean (h : FieldStep) (b : ℝ) :
    (∫ σ, spinValue σ ∂fieldCanonicalSpinLaw h b) = fieldBiasMean h b := by
  unfold fieldCanonicalSpinLaw
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [fieldTailSpinKernel_mean]
  exact fieldTransitionKernel_integral 0 _ _
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).2 _ b

theorem fieldCanonicalSpinLaw_magnetic_mean (h : FieldStep) {m : ℝ} (hm : |m| < 1) :
    (∫ σ, spinValue σ ∂fieldCanonicalSpinLaw h (magneticBias h m)) = m := by
  rw [fieldCanonicalSpinLaw_mean, fieldBiasMean_magneticBias h hm]

lemma spin_true_mean_of_spin_mean (μ : Measure Bool) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : (∫ σ, spinValue σ ∂μ) = m) :
    (∫ σ, (if σ = true then (1 : ℝ) else 0) ∂μ) = (1 + m) / 2 := by
  have he (σ : Bool) : (if σ = true then (1 : ℝ) else 0) = (1 + spinValue σ) / 2 := by
    cases σ <;> norm_num [spinValue]
  simp_rw [he]
  have hu : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ]; norm_num
  rw [integral_div, integral_add (integrable_const _) Integrable.of_finite,
    integral_const, hu, one_smul, hm]

theorem spinGroupCount_mean_of_site_means {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (m : ℝ)
    (hm : ∀ i, group i = a → (∫ σ, spinValue σ ∂μ i) = m) :
    (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) =
      (spinGroupSize group a : ℝ) * ((1 + m) / 2) := by
  have hi (σ : Spin N) : (spinGroupCount group σ a : ℝ) =
      ∑ i, spinGroupCountSummand group a i (σ i) := (sum_spinGroupCountSummand group a σ).symm
  simp_rw [hi]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hj (i : Fin N) :
      (∫ σ : Spin N, spinGroupCountSummand group a i (σ i) ∂Measure.pi μ) =
        if group i = a then (1 + m) / 2 else 0 := by
    rw [integral_comp_eval (μ := μ) (i := i) (measurable_of_finite _).aestronglyMeasurable]
    by_cases hg : group i = a
    · simpa only [spinGroupCountSummand, hg, true_and, ite_true, if_true] using
        spin_true_mean_of_spin_mean (μ i) (hm i hg)
    · simp [spinGroupCountSummand, hg]
  simp_rw [hj]
  simp [Finset.sum_ite, spinGroupSize, mul_comm]

theorem magneticCanonical_projection_distance_oai {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) :
    (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)
      ∂Measure.pi (fun i => fieldCanonicalSpinLaw h (magneticBias h (m (group i))))) ≤
        ∑ a, Real.sqrt (spinGroupSize group a) := by
  apply spinGroupProjection_product_mean_distance
  intro a
  rw [spinGroupCount_mean_of_site_means group a _ (m a) (fun i hi => by
    rw [hi]
    exact fieldCanonicalSpinLaw_magnetic_mean h (hm a))]
  exact (hcount a).symm

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.magneticCanonical_projection_distance_oai.{u_1} := @OAI.InvariantIsing.magneticCanonical_projection_distance_oai.{u_1}
