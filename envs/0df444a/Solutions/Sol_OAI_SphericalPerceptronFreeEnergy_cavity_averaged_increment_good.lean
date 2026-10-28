-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:32:31.322629+00:00
-- url     : https://prove2.me/submissions/dfdc2cd8-3bf5-43f3-b396-0340bdebb000

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_cavity_data
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_original_increment_error
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_finiteSphericalFieldValue_depth_uniform
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_roundedCavity_uncap

section
-- module Solutions.OAIQ061_PF.Compat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma realTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    1 - B ≤ realTail μ x := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (realTail_integrable μ x) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hx hs) 1)

lemma cappedDensity_eq (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    cappedDensity μ B x = (realTail μ x)⁻¹ ^ 2 := by
  rw [cappedDensity, max_eq_right (realTail_lower μ hμ hx)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedCDF
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma cappedA_eq_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r = ∫ t in 0..r, (realTail μ t)⁻¹ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr] at hx
  exact cappedDensity_eq μ hμ (hx.2.trans hrB)

lemma boundedCDF_nonneg (μ : Measure Time) (r : Time) : 0 ≤ boundedCDF μ r :=
  measureReal_nonneg

lemma boundedCDF_le_one (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    boundedCDF μ r ≤ 1 := by
  rw [boundedCDF_eq]
  exact cdf_le_one _ _

theorem boundedQuantile_law (μ : Measure Time) [IsProbabilityMeasure μ] :
    (volume : Measure Time).map (boundedQuantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply (boundedQuantile_measurable μ) measurableSet_Iic]
  have hpre : boundedQuantile μ ⁻¹' Iic r =
      Iic (⟨boundedCDF μ r, boundedCDF_nonneg μ r, boundedCDF_le_one μ r⟩ : Time) := by
    ext u
    exact boundedQuantile_le_iff μ u r
  rw [hpre, unitInterval.volume_Iic]
  exact ENNReal.ofReal_toReal (measure_ne_top μ _)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

lemma tilt_law_integral {v F : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    ∫ x, F x ∂tiltLaw μ v t = tiltMean μ v F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (Real.exp (t * v x))) from (hv.const_mul t).exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos μ hv hC hvC t).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] in
lemma vectorEnergy_bound {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (x : E) (s : S) : |W s + V s x| ≤ K+C*‖x‖ := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hW s)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_integrable (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    Integrable (fun s => Real.exp (W s + V s x)) ρ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (K+C*‖x‖)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound hW hV x s))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_pos (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    0 < vectorPartition ρ W V x := by
  apply integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
    (vectorPartition_integrable ρ hWm hVm hW hV x) |>.mpr
  simp [Function.support,Real.exp_ne_zero]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

open TopologicalSpace

lemma compact_array_law_subsequence {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [CompactSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ℕ → ProbabilityMeasure (CompactArray K)) :
    ∃ ν : ProbabilityMeasure (CompactArray K), ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  obtain ⟨ν, -, s, hs, hμ⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  exact ⟨ν,s,hs,hμ⟩

open scoped Polynomial

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem controlValue_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : controlValue P f m ≤ ‖f‖ := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem zero_payoff_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    (∫ ω, f (brownianEval 1 ω) ∂P) ≤ controlValue P f m := by
  apply le_csSup (controlPayoffs_bddAbove P f m)
  exact ⟨fun _ _ => 0, progressive_zero P, by simp, by simp⟩

theorem neg_norm_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : -‖f‖ ≤ controlValue P f m := by
  exact (abs_le.mp (abs_integral_reward_le P f (brownianEval 1))).1.trans
    (zero_payoff_le_controlValue P f m)

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma terminalVariational_bounds (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((-α*‖f‖ : ℝ) : EReal) ≤ terminalVariational P α f ∧
      terminalVariational P α f ≤ ((α*‖f‖ : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro m
    have hcv : -α*‖f‖ ≤ α*controlValue P f m := by
      nlinarith [mul_le_mul_of_nonneg_left (neg_norm_le_controlValue P f m) hα]
    exact (EReal.coe_le_coe_iff.mpr hcv).trans
      (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
  · calc
      _ ≤ ((α*controlValue P f oneTrial : ℝ) : EReal) + (entropy oneTrial).toEReal :=
        iInf_le _ oneTrial
      _ ≤ ((α*‖f‖ : ℝ) : EReal) := by
        simp only [entropy_oneTrial, EReal.coe_ennreal_zero, add_zero]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (controlValue_le_norm P f _) hα)

lemma terminalVariational_coe_toReal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((terminalVariational P α f).toReal : EReal) = terminalVariational P α f := by
  obtain ⟨hlo,hhi⟩ := terminalVariational_bounds P α hα f
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma perturbationWeight_eq (j : ℕ) : (2:ℝ)^(-((j+1:ℕ):ℤ))=(1/2:ℝ)^(j+1) := by
  simp only [zpow_neg,zpow_natCast,one_div,inv_pow]

lemma half_power_sum_le_one (N : ℕ) : (∑ j : Fin N, (1/2:ℝ)^(j.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (1/2:ℝ)^(j+1)) N]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [sum_geometric_two_le N]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_VarianceProdMemLp
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_bound {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    |vectorLogPartition ρ W V x| ≤ K+C*‖x‖ := by
  have hh := abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (show Integrable (fun _ : S => Real.exp 0) ρ by simp)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (show 0 < ∫ _ : S, Real.exp 0 ∂ρ by simp)
    (c := K+C*‖x‖) (fun s => by simpa using vectorEnergy_bound hW hV x s)
  simpa [vectorLogPartition,vectorPartition] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_general {H F : S → ℝ} (hH : Measurable H) (hF : Measurable F)
    {t C : ℝ} (hC : 0 ≤ C) (hFC : ∀ x, |F x| ≤ C) :
    |tiltMean μ H F t| ≤ C := by
  by_cases hi : Integrable (fun x => Real.exp (t*H x)) μ
  · exact tiltMean_bound_of_integrable μ hH hF hi hFC
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,abs_zero]
    exact hC

lemma replica_exp_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    Integrable (fun x : Fin n → S => Real.exp (t*replicaPotential H n x))
      (Measure.pi fun _ : Fin n => μ) := by
  simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  exact Integrable.fintype_prod (fun _ => hi)

omit [IsProbabilityMeasure μ] in
lemma tilt_law_apply_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ H t s = (ENNReal.ofReal (tiltPartition μ H t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * H x) ∂μ) := by
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi_of_integrable {H : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ H t) := by
  let := tilt_law_probability_of_integrable μ hi
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply_of_integrable _ (replica_exp_integrable μ hi n) (MeasurableSet.univ_pi hs),
    replica_partition μ hH n,ENNReal.ofReal_pow (tilt_partition_pos_of_integrable μ hi).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential H n x) =
      ∏ i, Real.exp (t * H (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * H x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply_of_integrable μ hi (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma gibbsReplicaMean_integral_of_integrable {H : S → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (G : (Fin n → S) → ℝ) :
    gibbsReplicaMean μ H n G = ∫ x, G x ∂Measure.pi (fun _ : Fin n => tiltLaw μ H 1) := by
  rw [← tilt_law_pi_of_integrable μ hH (by simpa only [one_mul] using hi),
    tilt_law_integral_of_integrable _ (replicaPotential_measurable hH n)
      (replica_exp_integrable μ (by simpa only [one_mul] using hi) n)]
  rfl

lemma gibbsReplicaMean_coordinate_of_integrable {H F : S → ℝ}
    (hH : Measurable H) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (j : Fin n) :
    gibbsReplicaMean μ H n (fun x => F (x j)) = tiltMean μ H F 1 := by
  have heI : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ heI
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi,
    ← tilt_law_integral_of_integrable μ hH heI]
  have he := measurePreserving_eval (fun _ : Fin n => tiltLaw μ H 1) j
  conv_rhs => rw [← he.map_eq,integral_map he.measurable.aemeasurable hF.aestronglyMeasurable]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulkLogPartition_eq (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) :
    bulkLogPartition n M f v a g =
      Real.log (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1) := by
  simp only [bulkLogPartition, vectorLogPartition, vectorPartition, tiltPartition, one_mul, bulkHamiltonian,
    innerSL_apply_apply]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkConcentration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeatureBound_sq (N : ℕ) (v : ℕ→ℝ) :
    bulkFeatureBound N v^2 = ∑ p, bulkAmplitude N v p^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma bulkFeatureBound_sq_le (N : ℕ) (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ p, |v (p+1)|≤C) : bulkFeatureBound N v^2 ≤ C^2*bulkScale N^2 := by
  rw [bulkFeatureBound_sq]
  have hi (p : Fin N) : bulkAmplitude N v p^2 ≤ C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := by
    let w : ℝ := (1/2:ℝ)^(p.val+1)
    have hw0 : 0≤w := pow_nonneg (by norm_num) _
    have hw1 : w≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv2 : v (p.val+1)^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v (p.val+1))) hC).2 (hv p.val)
    unfold bulkAmplitude
    rw [perturbationWeight_eq]
    change (bulkScale N*w*v (p.val+1))^2 ≤ _
    calc
      _ ≤ bulkScale N^2*w^2*C^2 := by
        rw [mul_pow,mul_pow]; exact mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ ≤ C^2*bulkScale N^2*w := by
        nlinarith [mul_le_mul_of_nonneg_left (show w^2≤w by nlinarith) (mul_nonneg (sq_nonneg C) (sq_nonneg (bulkScale N)))]
  calc
    _ ≤ ∑ p : Fin N, C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := Finset.sum_le_sum fun p _ => hi p
    _ = C^2*bulkScale N^2*(∑ p : Fin N, (1/2:ℝ)^(p.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*bulkScale N^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (by positivity)
    _ = _ := mul_one _

lemma bulkLogPartition_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) := by
  simp_rw [bulkLogPartition_eq]
  change Measurable (fun a : BulkDisorder (n+1) M => Real.log (∫ x,
    Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x) ∂unitSphereLaw (n+1)))
  simp only [one_mul]
  exact (bulkHamiltonian_continuous (n+1) M f v).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma bulkLogPartition_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    |bulkLogPartition n M f v a.1 a.2| ≤ M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖ := by
  apply vectorLogPartition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (normalizedPatternEnergy_bound (n+1) M f a.1)
  intro x
  simp only [Function.comp_apply,innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl]

lemma bulkLogPartition_memLp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    MemLp (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) 2
      (bulkDisorderLaw (n+1) M) := by
  have hi : MemLp (id : BulkMark (n+1) → BulkMark (n+1)) 2 (stdGaussian (BulkMark (n+1))) :=
    IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)
  have hn : MemLp (fun g : BulkMark (n+1) => ‖g‖) 2 (stdGaussian (BulkMark (n+1))) := hi.norm
  have hc : MemLp (fun _ : BulkMark (n+1) => (M:ℝ)*‖f‖) 2 (stdGaussian (BulkMark (n+1))) := memLp_const _
  have hg : MemLp (fun g : BulkMark (n+1) => M*‖f‖+bulkFeatureBound (n+1) v*‖g‖) 2
      (stdGaussian (BulkMark (n+1))) := hc.add (hn.const_mul (bulkFeatureBound (n+1) v))
  apply (hg.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulkLogPartition_measurable n M f v).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkLogPartition_bound n M f v a

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkAnnealedTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

lemma bulkMarkNorm_integrable (N M : ℕ) :
    Integrable (fun a : BulkDisorder N M => ‖a.2‖) (bulkDisorderLaw N M) :=
  ((((IsGaussian.memLp_id (stdGaussian (BulkMark N)) 2 (by simp)).norm).integrable (by norm_num))).comp_snd _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ParameterResampling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bulkParameterLaw_ae : ∀ᵐ v ∂bulkParameterLaw, ∀ j, v j∈Icc (1:ℝ) 2 := by
  rw [ae_all_iff]
  intro j
  have he : ∀ᵐ x ∂bulkParameterUniform, x∈Icc (1:ℝ) 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => ⟨hx.1.le,hx.2⟩
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => bulkParameterUniform) j).quasiMeasurePreserving.ae he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkParameterDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeature_joint_continuous (N : ℕ) :
    Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N => bulkFeature N a.1 a.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => fun_prop
  | inr i =>
    change Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N =>
      bulkAmplitude N a.1 i.1*spinTensorFeature N (bulkDegree i.1) a.2 i.2)
    apply Continuous.mul
    · unfold bulkAmplitude; fun_prop
    · exact ((EuclideanSpace.proj i.2).continuous.comp (spinTensorFeature_continuous N (bulkDegree i.1))).comp continuous_snd

lemma bulkHamiltonian_parameter_continuous (N M : ℕ) (f : ℝ→ᵇℝ) :
    Continuous (fun a : ((ℕ→ℝ) × BulkDisorder N M) × NormalizedSpin N =>
      bulkHamiltonian N M f a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold bulkHamiltonian
  exact ((normalizedPatternEnergy_continuous N M f).comp
    (continuous_fst.snd.fst.prodMk continuous_snd)).add
    (((bulkFeature_joint_continuous N).comp (continuous_fst.fst.prodMk continuous_snd)).inner continuous_fst.snd.snd)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma timeTail_atom_integral (q t : Time) (w : ℝ) :
    (∫ s in Ici t, (if q ≤ s then w else 0) ∂timeLaw) = w*(1-max (q:ℝ) (t:ℝ)) := by
  change (∫ s in Ici t, (Ici q).indicator (fun _ => w) s ∂timeLaw) = _
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [Ici_inter_Ici]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,timeLaw_eq_volume,
    unitInterval.volume_Ici,ENNReal.toReal_ofReal (sub_nonneg.mpr (max q t).2.2),smul_eq_mul]
  rcases le_total q t with h | h
  · rw [max_eq_right h,max_eq_right (show (q:ℝ) ≤ (t:ℝ) from h)]
    ring
  · rw [max_eq_left h,max_eq_left (show (t:ℝ) ≤ (q:ℝ) from h)]
    ring

lemma tailIntegral_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : Time) :
    tailIntegral (weightedStepTrial w q hw hw1) t = ∑ i, w i*(1-max (q i:ℝ) (t:ℝ)) := by
  unfold tailIntegral
  change (∫ s in Ici t, ∑ i, if q i ≤ s then w i else 0 ∂timeLaw) = _
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => timeTail_atom_integral (q i) t (w i))
  · intro i _
    exact (integrable_const (w i)).indicator measurableSet_Ici

lemma weightedStepTail_continuous {I : Type*} [Fintype I] (w q : I → ℝ) :
    Continuous (weightedStepTail w q) := by
  unfold weightedStepTail
  fun_prop

lemma weightedStepTail_lower {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    1-B ≤ weightedStepTail w q t := by
  calc
    1-B = ∑ i, w i*(1-B) := by rw [← Finset.sum_mul,hw1,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (max_le (hq i) ht) 1) (hw i)

lemma weightedStepTail_upper {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    weightedStepTail w q t ≤ 1-t := by
  calc
    _ ≤ ∑ i, w i*(1-t) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_right (q i) t) 1) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_of_le {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw1 : ∑ i, w i = 1) {t : ℝ} (hq : ∀ i, q i ≤ t) :
    weightedStepTail w q t = 1-t := by
  simp only [weightedStepTail,max_eq_right (hq _)]
  rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_pos {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    0 < weightedStepTail w q t :=
  (sub_pos.mpr hB).trans_le (weightedStepTail_lower w q hw hw1 hq ht)

lemma weightedStepTail_inv_continuousOn {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) :
    ContinuousOn (fun t => (weightedStepTail w q t)⁻¹) (Icc 0 B) :=
  (weightedStepTail_continuous w q).continuousOn.inv₀
    (fun _ ht => (weightedStepTail_pos w q hw hw1 hB hq ht.2).ne')

lemma integral_one_sub_inv {B : ℝ} (hB : B < 1) :
    (∫ t in (0:ℝ)..B, (1-t)⁻¹) = -Real.log (1-B) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
  simp only [sub_zero]
  rw [integral_inv_of_pos (sub_pos.mpr hB) zero_lt_one,one_div,Real.log_inv]

theorem entropy_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    entropy (weightedStepTrial w q hw hw1) = ENNReal.ofReal
      (((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2) := by
  let D := weightedStepTail w (fun i => (q i:ℝ))
  let F : ℝ → ℝ := fun t => (D t)⁻¹-(1-t)⁻¹
  have hD (t : ℝ) (ht : t ≤ B) : 0 < D t := weightedStepTail_pos _ _ hw hw1 hB1 hq ht
  have hF : ContinuousOn F (Icc 0 B) :=
    (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).sub
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
        have : t < 1 := ht.2.trans_lt hB1
        exact (sub_pos.mpr this).ne'))
  have hF0 : ∀ t ∈ Icc 0 B, 0 ≤ F t := by
    intro t ht
    exact sub_nonneg.mpr (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1)) (hD t ht.2) |>.mpr
      (weightedStepTail_upper _ _ hw hw1 t))
  have he (t : Time) : (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ = (Iic B).indicator (fun t => ENNReal.ofReal (F t)) (t:ℝ) := by
    rw [tailIntegral_weightedStepTrial]
    change (ENNReal.ofReal (D (t:ℝ)))⁻¹-_ = _
    by_cases ht : (t:ℝ) ≤ B
    · rw [Set.indicator_of_mem (show (t:ℝ) ∈ Iic B from ht)]
      dsimp [F]
      rw [ENNReal.ofReal_sub _ (inv_nonneg.mpr (sub_nonneg.mpr t.2.2)),
        ENNReal.ofReal_inv_of_pos (hD t ht),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr (ht.trans_lt hB1))]
    · rw [Set.indicator_of_notMem (show (t:ℝ) ∉ Iic B from ht)]
      have hd : D (t:ℝ) = 1-(t:ℝ) := weightedStepTail_of_le _ _ hw1
        (fun i => (hq i).trans (le_of_not_ge ht))
      rw [hd,tsub_self]
  have hset : Iic B ∩ Icc (0:ℝ) 1 = Icc 0 B := by
    ext t
    constructor
    · rintro ⟨ht,h0,h1⟩
      exact ⟨h0,ht⟩
    · rintro ⟨h0,ht⟩
      exact ⟨ht,h0,ht.trans hB1.le⟩
  have hel : (∫⁻ t : Time, (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ ∂timeLaw) = ENNReal.ofReal (∫ t in Icc 0 B, F t) := by
    rw [lintegral_congr he]
    change (∫⁻ t : Icc (0:ℝ) 1, (Iic B).indicator (fun t => ENNReal.ofReal (F t)) t.val
      ∂Measure.comap Subtype.val volume) = _
    rw [lintegral_subtype_comap measurableSet_Icc,lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,hset]
    exact (ofReal_integral_eq_lintegral_ofReal hF.integrableOn_Icc
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hF0 t ht))).symm
  have hInt : (∫ t in Icc 0 B, F t) = (∫ t in (0:ℝ)..B, (D t)⁻¹)+Real.log (1-B) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hB0]
    have hiD : IntervalIntegrable (fun t => (D t)⁻¹) volume 0 B :=
      (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).intervalIntegrable_of_Icc hB0
    have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t (ht : t ∈ Icc (0:ℝ) B) =>
        (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
    rw [show F = (fun t => (D t)⁻¹-(1-t)⁻¹) from rfl,
      intervalIntegral.integral_sub hiD hiR,integral_one_sub_inv hB1,sub_neg_eq_add]
  rw [entropy,hel,hInt,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num
  rfl

lemma weightedStepTail_affine {k : ℕ} (w q : Fin (k+1) → ℝ) (hq : Monotone q)
    (i : Fin k) {t : ℝ} (ht : t ∈ Icc (q i.castSucc) (q i.succ)) :
    weightedStepTail w q t = weightedStepTail w q (q i.castSucc)-
      stepCumulative w i*(t-q i.castSucc) := by
  unfold weightedStepTail stepCumulative
  rw [Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ i.castSucc
  · rw [ite_eq_left hj,max_eq_right ((hq hj).trans ht.1),max_eq_right (hq hj)]
    ring
  · have hj' : i.succ ≤ j := by exact Fin.le_iff_val_le_val.mpr (by
      have hh := Fin.lt_def.mp (lt_of_not_ge hj)
      simp only [Fin.val_castSucc,Fin.val_succ] at *
      omega)
    rw [ite_eq_right hj,max_eq_left (ht.2.trans (hq hj')),max_eq_left
      ((hq (Fin.castSucc_le_succ i)).trans (hq hj'))]
    ring

lemma weightedStepTail_below_min {I : Type*} [Fintype I] (w q : I → ℝ)
    {a t : ℝ} (hq : ∀ i, a ≤ q i) (ht : t ≤ a) :
    weightedStepTail w q t = weightedStepTail w q a := by
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_left (ht.trans (hq i)),max_eq_left (hq i)]

lemma affine_pos_on {A B a b z : ℝ} (_hab : a ≤ b) (hB : 0 < B) (hz : 0 < z)
    (hrel : A-z*(b-a)=B) {x : ℝ} (hx : x ∈ Icc a b) : 0 < A-z*(x-a) := by
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hz.le
  linarith

lemma integral_positive_affine_inv_sq {A B a b z : ℝ} (hab : a ≤ b) (hA : 0 < A)
    (hB : 0 < B) (hz : 0 < z) (hrel : A-z*(b-a)=B) :
    (∫ x in a..b, 1/(A-z*(x-a))^2) = (b-a)/(A*B) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x => (A-z*(x-a))⁻¹/z) (1/(A-z*(x-a))^2) x := by
    have hd := (((hasDerivAt_id x).sub_const a).const_mul z).const_sub A
    have he := (hd.inv (affine_pos_on hab hB hz hrel hx).ne').div_const z
    have hv : (- -(z*1)/(A-z*(id x-a))^2)/z = 1/(A-z*(x-a))^2 := by
      dsimp only [id_eq]
      field_simp [hz.ne',(affine_pos_on hab hB hz hrel hx).ne']
    rw [hv] at he
    exact he
  have hi : IntervalIntegrable (fun x => 1/(A-z*(x-a))^2) volume a b := by
    have hc : ContinuousOn (fun x => (A-z*(x-a))⁻¹) (Icc a b) :=
      (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
        (fun x hx => (affine_pos_on hab hB hz hrel hx).ne')
    have hh := (hc.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
    change IntervalIntegrable (fun x => ((A-z*(x-a))⁻¹)^2) volume a b at hh
    simpa only [one_div,inv_pow] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) hi]
  rw [hrel]
  simp only [sub_self,mul_zero,sub_zero]
  have hAn := hA.ne'
  have hBn := hB.ne'
  have hzn := hz.ne'
  field_simp
  nlinarith

lemma weightedStepA_root {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) :
    weightedStepA w q (q 0) = q 0/(weightedStepTail w q (q 0))^2 := by
  unfold weightedStepA
  calc
    _ = ∫ _t in (0:ℝ)..q 0, 1/(weightedStepTail w q (q 0))^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hq0] at ht
      dsimp only
      rw [weightedStepTail_below_min w q (fun i => hq (Fin.zero_le i)) ht.2]
    _ = _ := by simp [div_eq_mul_inv]

lemma weightedStepA_increment {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last k) < 1) (i : Fin k) (hz : 0 < stepCumulative w i) :
    weightedStepA w q (q i.succ)-weightedStepA w q (q i.castSucc) =
      (q i.succ-q i.castSucc)/(weightedStepTail w q (q i.castSucc)*weightedStepTail w q (q i.succ)) := by
  let D := weightedStepTail w q
  have hqi (i : Fin (k+1)) : q i ≤ q (Fin.last k) := hq (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D (q i) := weightedStepTail_pos _ _ hw hw1 hq1 hqi (hqi i)
  have hc : ContinuousOn (fun t => 1/(D t)^2) (Icc 0 (q (Fin.last k))) := by
    have hh := (weightedStepTail_inv_continuousOn w q hw hw1 hq1 hqi).pow 2
    change ContinuousOn (fun t => ((D t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have h0i : 0 ≤ q i.castSucc := hq0.trans (hq (Fin.zero_le _))
  have hij : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
  have hi := (hc.mono (Icc_subset_Icc le_rfl (hqi i.castSucc))).intervalIntegrable_of_Icc (μ := volume) h0i
  have hj := (hc.mono (Icc_subset_Icc h0i (hqi i.succ))).intervalIntegrable_of_Icc (μ := volume) hij
  have ha := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hseg : (∫ t in q i.castSucc..q i.succ, 1/(D t)^2) =
      (q i.succ-q i.castSucc)/(D (q i.castSucc)*D (q i.succ)) := by
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hij,le_rfl⟩
    calc
      _ = ∫ t in q i.castSucc..q i.succ,
          1/(D (q i.castSucc)-stepCumulative w i*(t-q i.castSucc))^2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hij] at ht
        dsimp only
        rw [show D t = _ from weightedStepTail_affine w q hq i ht]
      _ = _ := integral_positive_affine_inv_sq hij (hD i.castSucc) (hD i.succ) hz he.symm
  change (∫ t in (0:ℝ)..q i.succ, 1/(D t)^2)-
    (∫ t in (0:ℝ)..q i.castSucc, 1/(D t)^2) = _
  rw [← ha,hseg]
  ring

lemma weightedStep_truncated_entropy_nonneg {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, q i ≤ B) :
    0 ≤ ((∫ t in (0:ℝ)..B, (weightedStepTail w q t)⁻¹)+Real.log (1-B))/2 := by
  have hiD := (weightedStepTail_inv_continuousOn w q hw hw1 hB1 hq).intervalIntegrable_of_Icc (μ := volume) hB0
  have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
    ((continuous_const.sub continuous_id).continuousOn.inv₀
      (fun t (ht : t ∈ Icc (0:ℝ) B) => (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
  have hle := intervalIntegral.integral_mono_on hB0 hiR hiD (fun t ht =>
    (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1))
      (weightedStepTail_pos w q hw hw1 hB1 hq ht.2)).mpr
        (weightedStepTail_upper w q hw hw1 t))
  rw [integral_one_sub_inv hB1] at hle
  linarith

lemma entropy_weightedStepTrial_toReal {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    (entropy (weightedStepTrial w q hw hw1)).toReal =
      ((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2 := by
  rw [entropy_weightedStepTrial w q hw hw1 B hB0 hB1 hq,ENNReal.toReal_ofReal
    (weightedStep_truncated_entropy_nonneg w (fun i => (q i:ℝ)) hw hw1 hB0 hB1 hq)]

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Entropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma reciprocal_supporting_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y-x)/y^2 ≤ x⁻¹-y⁻¹ := by
  have he : x⁻¹-y⁻¹-(y-x)/y^2=(x-y)^2/(x*y^2) := by
    field_simp [hx.ne',hy.ne']
    ring
  have hp := div_nonneg (sq_nonneg (x-y)) (mul_pos hx (sq_pos_of_pos hy)).le
  rw [← he] at hp
  linarith

lemma max_difference_support {p q t : ℝ} :
    (if t ≤ q then p-q else 0) ≤ max p t-max q t := by
  split_ifs with ht
  · rw [max_eq_left ht]
    exact sub_le_sub_right (le_max_left _ _) _
  · rw [max_eq_right (le_of_not_ge ht)]
    exact sub_nonneg.mpr (le_max_right _ _)

theorem entropy_weightedStep_support {I : Type*} [Fintype I]
    (w : I → ℝ) (p q : I → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ i, (p i:ℝ) ≤ B) (hq : ∀ i, (q i:ℝ) ≤ B) :
    (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-
        (entropy (weightedStepTrial w q hw hw1)).toReal := by
  classical
  let P : I → ℝ := fun i => p i
  let Q : I → ℝ := fun i => q i
  let Dp := weightedStepTail w P
  let Dq := weightedStepTail w Q
  have hcP := weightedStepTail_inv_continuousOn w P hw hw1 hB1 hp
  have hcQ := weightedStepTail_inv_continuousOn w Q hw hw1 hB1 hq
  have hiP := hcP.intervalIntegrable_of_Icc (μ := volume) hB0
  have hiQ := hcQ.intervalIntegrable_of_Icc (μ := volume) hB0
  have hcQ2 : ContinuousOn (fun t => 1/(Dq t)^2) (Icc 0 B) := by
    have hh := hcQ.pow 2
    change ContinuousOn (fun t => ((Dq t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have hiQ2 := hcQ2.intervalIntegrable_of_Icc (μ := volume) hB0
  let F : I → ℝ → ℝ := fun i => (Iic (Q i)).indicator (fun t => 1/(Dq t)^2)
  have hFi (i : I) : IntervalIntegrable (F i) volume 0 B :=
    ⟨hiQ2.1.indicator measurableSet_Iic,hiQ2.2.indicator measurableSet_Iic⟩
  have hl (t : ℝ) (ht : t ∈ Icc 0 B) :
      (∑ i, w i*(P i-Q i)*F i t) ≤ (Dp t)⁻¹-(Dq t)⁻¹ := by
    have hDtP : 0 < Dp t := weightedStepTail_pos w P hw hw1 hB1 hp ht.2
    have hDtQ : 0 < Dq t := weightedStepTail_pos w Q hw hw1 hB1 hq ht.2
    have hmax : (∑ i, w i*(if t ≤ Q i then P i-Q i else 0)) ≤ Dq t-Dp t := by
      change _ ≤ (∑ i, w i*(1-max (Q i) t))-(∑ i, w i*(1-max (P i) t))
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have hm := mul_le_mul_of_nonneg_left (@max_difference_support (P i) (Q i) t) (hw i)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ 1/(Dq t)^2)
    have he : (∑ i, w i*(P i-Q i)*F i t) =
        (∑ i, w i*(if t ≤ Q i then P i-Q i else 0))*(1/(Dq t)^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [F,Set.indicator_apply,mem_Iic]
      split_ifs <;> ring
    rw [he]
    calc
      _ ≤ (Dq t-Dp t)*(1/(Dq t)^2) := hmul
      _ = (Dq t-Dp t)/(Dq t)^2 := by ring
      _ ≤ _ := reciprocal_supporting_inequality hDtP hDtQ
  have hiF : IntervalIntegrable (fun t => ∑ i, w i*(P i-Q i)*F i t) volume 0 B := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => (hFi i).const_mul (w i*(P i-Q i)))
    have he : (∑ i, fun t => w i*(P i-Q i)*F i t) =
        (fun t => ∑ i, w i*(P i-Q i)*F i t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hInt := intervalIntegral.integral_mono_on hB0 hiF (hiP.sub hiQ) hl
  have hIntF (i : I) : (∫ t in (0:ℝ)..B, F i t) = weightedStepA w Q (Q i) := by
    exact intervalIntegral.integral_indicator ⟨(q i).2.1,hq i⟩
  rw [intervalIntegral.integral_sub hiP hiQ,
    intervalIntegral.integral_finsetSum (fun i _ => (hFi i).const_mul _)] at hInt
  simp only [intervalIntegral.integral_const_mul,hIntF] at hInt
  rw [entropy_weightedStepTrial_toReal w p hw hw1 B hB0 hB1 hp,
    entropy_weightedStepTrial_toReal w q hw hw1 B hB0 hB1 hq]
  change (∑ i, w i*(P i-Q i)*weightedStepA w Q (Q i))/2 ≤
    ((∫ t in (0:ℝ)..B, (Dp t)⁻¹)+Real.log (1-B))/2-
      ((∫ t in (0:ℝ)..B, (Dq t)⁻¹)+Real.log (1-B))/2
  linarith

theorem stationary_finite_entropy_minimizes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q p : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hp : Monotone p)
    (hq1 : (q (Fin.last k):ℝ) < 1) (hp1 : (p (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-∑ i, w i*h i*(p i:ℝ) := by
  let B := max (p (Fin.last k):ℝ) (q (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (p (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hp1 hq1
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_left _ _)
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_right _ _)
  have hs := entropy_weightedStep_support w p q hw hw1 B hB0 hB1 hP hQ
  have he : (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 =
      (∑ i, w i*h i*(p i:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hstat i]
    ring
  rw [he] at hs
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StationaryExistence
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma stepTailSum_zero {k : ℕ} (v : Fin k → ℝ) : stepTailSum v 0=∑ j, v j := by
  simp only [stepTailSum,Fin.zero_le,ite_true]

lemma stepTailSum_last {k : ℕ} (v : Fin k → ℝ) : stepTailSum v (Fin.last k)=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬Fin.last k ≤ j.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]; omega
  exact ite_eq_right hj

lemma stepTailSum_difference {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    stepTailSum v i.castSucc-stepTailSum v i.succ=v i := by
  classical
  unfold stepTailSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin k, if j=i then v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j=i
      · subst j
        have hi : ¬i.succ ≤ i.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]; omega
        simp only [ite_eq_left le_rfl,ite_eq_right hi,sub_zero,ite_true]
      · have he : (i.castSucc ≤ j.castSucc) ↔ (i.succ ≤ j.castSucc) := by
          simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]
          have hv : i.val ≠ j.val := by intro hij; exact hji (Fin.ext hij.symm)
          omega
        simp only [he,sub_self,ite_eq_right hji]
    _ = _ := by simp

lemma stepTailSum_le_zero {k : ℕ} (v : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (i : Fin (k+1)) :
    stepTailSum v i ≤ stepTailSum v 0 := by
  rw [stepTailSum_zero]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | rfl | exact hv j

lemma finitePrecisionShift_le_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) (i : Fin (k+1)) :
    finitePrecisionShift z h i ≤ finitePrecisionShift z h 0 :=
  stepTailSum_le_zero _ (fun j => mul_nonneg (mul_nonneg (by norm_num) (hz j))
    (sub_nonneg.mpr (hh (Fin.castSucc_le_succ j)))) i

lemma finitePrecisionTail_pos {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin (k+1)) : 0 < finitePrecisionTail z h b i :=
  inv_pos.mpr (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i).trans_lt hb))

lemma finitePrecisionTail_gap {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ =
      z i*finiteOverlapIncrement z h b i := by
  have h1 : b-finitePrecisionShift z h i.castSucc ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.castSucc).trans_lt hb)).ne'
  have h2 : b-finitePrecisionShift z h i.succ ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.succ).trans_lt hb)).ne'
  have he := stepTailSum_difference (fun j => 2*z j*(h j.succ-h j.castSucc)) i
  change finitePrecisionShift z h i.castSucc-finitePrecisionShift z h i.succ =
    2*z i*(h i.succ-h i.castSucc) at he
  unfold finiteOverlapIncrement finitePrecisionTail
  field_simp [h1,h2]
  linear_combination he

lemma finiteOverlapIncrement_nonneg {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : 0 ≤ finiteOverlapIncrement z h b i := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i))))
    (finitePrecisionTail_pos z h hz hh hb i.castSucc).le) (finitePrecisionTail_pos z h hz hh hb i.succ).le

lemma finiteStationarityMass_ge_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    {b : ℝ} (hb : finitePrecisionShift z h 0 < b) :
    finitePrecisionTail z h b 0 ≤ finiteStationarityMass z h b := by
  have hg (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ ≤
      finiteOverlapIncrement z h b i := by
    rw [finitePrecisionTail_gap z h hz0 hh hb i]
    exact mul_le_of_le_one_left (finiteOverlapIncrement_nonneg z h hz0 hh hb i) (hz1 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hg i)
  have ht := finite_sum_successive_differences k (finitePrecisionTail z h b)
  have he : (∑ i : Fin k, (finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ)) =
      finitePrecisionTail z h b 0-finitePrecisionTail z h b (Fin.last k) := by
    rw [Finset.sum_sub_distrib] at ht ⊢
    linarith
  rw [he] at hs
  have hn : 0 ≤ 2*h 0*(finitePrecisionTail z h b 0)^2 := by positivity
  unfold finiteStationarityMass
  linarith

lemma finiteStationarityMass_continuousOn {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) :
    ContinuousOn (finiteStationarityMass z h) (Ici (finitePrecisionShift z h 0+1)) := by
  have hc (i : Fin (k+1)) : ContinuousOn (fun b => finitePrecisionTail z h b i)
      (Ici (finitePrecisionShift z h 0+1)) := by
    apply (continuous_id.sub continuous_const).continuousOn.inv₀
    intro b hb
    have hi := finitePrecisionShift_le_root z h hz hh i
    change finitePrecisionShift z h 0+1 ≤ b at hb
    change b-finitePrecisionShift z h i ≠ 0
    exact (sub_pos.mpr (by linarith)).ne'
  exact ((continuousOn_const.mul (hc 0 |>.pow 2)).add
    (continuousOn_finsetSum Finset.univ (fun i _ =>
      (continuousOn_const.mul (hc i.castSucc)).mul (hc i.succ)))).add (hc (Fin.last k))

lemma finiteStationarityMass_tendsto {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) :
    Tendsto (finiteStationarityMass z h) atTop (𝓝 0) := by
  have ht (i : Fin (k+1)) : Tendsto (fun b => finitePrecisionTail z h b i) atTop (𝓝 0) := by
    simpa only [finitePrecisionTail,sub_eq_add_neg,Function.comp_def,id_eq] using
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-finitePrecisionShift z h i) tendsto_id))
  have hi (i : Fin k) : Tendsto (fun b => finiteOverlapIncrement z h b i) atTop (𝓝 0) := by
    simpa only [finiteOverlapIncrement,mul_zero] using ((ht i.castSucc).const_mul (2*(h i.succ-h i.castSucc))).mul (ht i.succ)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hf := (((ht 0).pow 2).const_mul (2*h 0)).add hs |>.add (ht (Fin.last k))
  change Tendsto (fun b => 2*h 0*(finitePrecisionTail z h b 0)^2+
    (∑ i, finiteOverlapIncrement z h b i)+finitePrecisionTail z h b (Fin.last k)) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,Finset.sum_const_zero,zero_add] using hf

theorem exists_finite_normalizing_precision {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ b : ℝ, finitePrecisionShift z h 0 < b ∧ finiteStationarityMass z h b=1 := by
  let a := finitePrecisionShift z h 0+1
  have ha : finitePrecisionShift z h 0 < a := by dsimp only [a]; linarith
  have hstart : 1 ≤ finiteStationarityMass z h a := by
    have hs := finiteStationarityMass_ge_root z h hz0 hz1 hh hh0 ha
    simpa only [finitePrecisionTail,a,add_sub_cancel_left,inv_one] using hs
  have hev := (finiteStationarityMass_tendsto z h).eventually_lt_const (by norm_num : (0:ℝ)<1)
  obtain ⟨b,hb,hend⟩ := ((eventually_ge_atTop a).and hev).exists
  have hc : ContinuousOn (finiteStationarityMass z h) (Icc a b) :=
    (finiteStationarityMass_continuousOn z h hz0 hh).mono Icc_subset_Ici_self
  obtain ⟨c,hc,he⟩ := intermediate_value_Icc' hb hc ⟨hend.le,hstart⟩
  exact ⟨c,ha.trans_le hc.1,he⟩

theorem exists_finite_stationary_quantile {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i) := by
  let z := stepCumulative w
  have hz0 : ∀ i, 0 < z i := stepCumulative_pos w hw
  have hz1 : ∀ i, z i < 1 := stepCumulative_lt_one w hw hw1
  obtain ⟨b,hb,hb1⟩ := exists_finite_normalizing_precision z h
    (fun i => (hz0 i).le) (fun i => (hz1 i).le) hh hh0
  let D := finitePrecisionTail z h b
  let v := finiteOverlapIncrement z h b
  let Q : Fin (k+1) → ℝ := fun i => 2*h 0*(D 0)^2+(∑ j, v j)-stepTailSum v i
  have hD (i : Fin (k+1)) : 0 < D i := finitePrecisionTail_pos z h (fun i => (hz0 i).le) hh hb i
  have hv (i : Fin k) : 0 ≤ v i := finiteOverlapIncrement_nonneg z h (fun i => (hz0 i).le) hh hb i
  have hQ0 : Q 0=2*h 0*(D 0)^2 := by simp only [Q,stepTailSum_zero]; ring
  have hQlast : Q (Fin.last k)=2*h 0*(D 0)^2+∑ j, v j := by simp only [Q,stepTailSum_last,sub_zero]
  have hQinc (i : Fin k) : Q i.succ-Q i.castSucc=v i := by
    have he := stepTailSum_difference v i
    dsimp only [Q]
    linarith
  have hQmono : Monotone Q := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have he := hQinc i
    linarith [hv i]
  have hQ0pos : 0 ≤ Q 0 := by rw [hQ0]; positivity
  have hnorm : Q (Fin.last k)+D (Fin.last k)=1 := by
    rw [hQlast]
    exact hb1
  have hQ1 : Q (Fin.last k) < 1 := by linarith [hD (Fin.last k)]
  have hgap (i : Fin k) : D i.castSucc-D i.succ=z i*(Q i.succ-Q i.castSucc) := by
    rw [hQinc]
    exact finitePrecisionTail_gap z h (fun i => (hz0 i).le) hh hb i
  let T : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hTgap (i : Fin k) : T i.castSucc-T i.succ=z i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hQmono i (t := Q i.succ) ⟨hQmono (Fin.castSucc_le_succ i),le_rfl⟩
    change T i.succ=T i.castSucc-z i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hTlast : T (Fin.last k)=D (Fin.last k) := by
    have he := weightedStepTail_of_le w Q hw1 (fun i => hQmono (Fin.le_last i))
    change T (Fin.last k)=1-Q (Fin.last k) at he
    linarith
  have hconst (i : Fin (k+1)) : T i-D i=T 0-D 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => linarith [hTgap i,hgap i]
  have hTD (i : Fin (k+1)) : T i=D i := by
    have he := hconst (Fin.last k)
    rw [hTlast] at he
    linarith [hconst i]
  have hroot : 2*h 0=Q 0/(T 0)^2 := by
    rw [hTD,hQ0]
    have hn : D 0 ≠ 0 := (hD 0).ne'
    field_simp [hn]
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=(Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) := by
    rw [hQinc,hTD,hTD]
    change 2*(h i.succ-h i.castSucc)=
      (2*(h i.succ-h i.castSucc)*D i.castSucc*D i.succ)/(D i.castSucc*D i.succ)
    have hn : D i.castSucc ≠ 0 := (hD i.castSucc).ne'
    have hn' : D i.succ ≠ 0 := (hD i.succ).ne'
    field_simp [hn,hn']
  have hstat (i : Fin (k+1)) : 2*h i=weightedStepA w Q (Q i) := by
    induction i using Fin.induction with
    | zero => rw [weightedStepA_root w Q hQmono hQ0pos]; exact hroot
    | succ i ih =>
      have he := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hQmono hQ0pos hQ1 i (hz0 i)
      change weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc)=
        (Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) at he
      linarith [hinc i]
  let q : Fin (k+1) → Time := fun i => ⟨Q i,⟨hQ0pos.trans (hQmono (Fin.zero_le i)),
    ((hQmono (Fin.le_last i)).trans_lt hQ1).le⟩⟩
  exact ⟨q,(fun i j hij => hQmono hij),hQ1,hstat⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CoupledDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma Trial.ext_fun {m n : Trial} (h : ∀ t, m t=n t) : m=n := by
  cases m
  cases n
  congr 1
  exact funext h

lemma weightedStepTrial_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w : I → ℝ) (q : I → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTrial c (fun a => q a.1) hc hc1=weightedStepTrial w q hw hw1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if q a.1 ≤ t then c a else 0)=∑ i, if q i ≤ t then w i else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i ≤ t <;> simp [hi,hrow]

lemma weightedStepTrial_coupling_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v : J → ℝ) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i=1)
    (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    weightedStepTrial c (fun a => p a.2) hc hc1=weightedStepTrial v p hv hv1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if p a.2 ≤ t then c a else 0)=∑ j, if p j ≤ t then v j else 0
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p j ≤ t <;> simp [hj,hcol]

lemma coupling_sum_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w f : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    (∑ a, c a*f a.1)=∑ i, w i*f i := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul,hrow]

lemma coupling_sum_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v f : J → ℝ) (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    (∑ a, c a*f a.2)=∑ j, v j*f j := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol]

lemma weightedStepTail_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTail c (fun a => q a.1)=weightedStepTail w q := by
  funext t
  exact coupling_sum_fst c w (fun i => 1-max (q i) t) hrow

lemma weightedStepA_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepA c (fun a => q a.1)=weightedStepA w q := by
  unfold weightedStepA
  rw [weightedStepTail_coupling_fst c w q hrow]

lemma entropy_coupled_stationary_comparison {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w h : I → ℝ) (v g : J → ℝ) (q : I → Time) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hv : ∀ j, 0 ≤ v j) (hv1 : ∑ j, v j=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) (hcol : ∀ j, ∑ i, c (i,j)=v j)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i:ℝ) ≤ B) (hp : ∀ j, (p j:ℝ) ≤ B)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun i => (q i:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial v p hv hv1)).toReal-∑ j, v j*g j*(p j:ℝ)+
        ∑ a, c a*|h a.1-g a.2| := by
  have hc1 : ∑ a, c a=1 := by rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hw1
  have hs := entropy_weightedStep_support c (fun a => p a.2) (fun a => q a.1)
    hc hc1 B hB0 hB1 (fun a => hp a.2) (fun a => hq a.1)
  rw [weightedStepTrial_coupling_fst c w q hc hc1 hw hw1 hrow,
    weightedStepTrial_coupling_snd c v p hc hc1 hv hv1 hcol,
    weightedStepA_coupling_fst c w (fun i => (q i:ℝ)) hrow] at hs
  have he : (∑ a, c a*((p a.2:ℝ)-(q a.1:ℝ))*weightedStepA w (fun i => (q i:ℝ)) (q a.1))/2 =
      (∑ a, c a*h a.1*(p a.2:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    simp only [mul_assoc]
    rw [← coupling_sum_fst c w (fun i => h i*(q i:ℝ)) hrow]
    simp only [← mul_assoc]
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hstat a.1]
    ring
  rw [he] at hs
  have hb : (∑ j, v j*g j*(p j:ℝ))-(∑ a, c a*h a.1*(p a.2:ℝ)) ≤
      ∑ a, c a*|h a.1-g a.2| := by
    simp only [mul_assoc]
    rw [← coupling_sum_snd c v (fun j => g j*(p j:ℝ)) hcol]
    simp only [← mul_assoc]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro a _
    have h₁ : (g a.2-h a.1)*(p a.2:ℝ) ≤ |h a.1-g a.2| := calc
      _ ≤ |g a.2-h a.1| *(p a.2:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) (p a.2).2.1
      _ ≤ |g a.2-h a.1| *1 := mul_le_mul_of_nonneg_left (p a.2).2.2 (abs_nonneg _)
      _ = _ := by rw [mul_one,abs_sub_comm]
    have H := mul_le_mul_of_nonneg_left h₁ (hc a)
    nlinarith [H]
  linarith

lemma finiteSphericalDual_eq_stationary {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hs : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    sInf (finiteSphericalDualValues w h hw hw1)=finiteSphericalDualObjective w h hw hw1 q := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
  rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
  exact stationary_finite_entropy_minimizes w h q p hw hw1 hq hp hq1 hp1 hs

theorem finiteSphericalDual_abs_sub_le {k : ℕ} (w h g : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (hg : Monotone g) (hg0 : 0 ≤ g 0) :
    |sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)-
      sInf (finiteSphericalDualValues w g (fun i => (hw i).le) hw1)| ≤
        ∑ i, w i*|h i-g i| := by
  classical
  obtain ⟨q,hq,hq1,hsq⟩ := exists_finite_stationary_quantile w h hw hw1 hh hh0
  obtain ⟨p,hp,hp1,hsp⟩ := exists_finite_stationary_quantile w g hw hw1 hg hg0
  rw [finiteSphericalDual_eq_stationary w h q (fun i => (hw i).le) hw1 hq hq1 hsq,
    finiteSphericalDual_eq_stationary w g p (fun i => (hw i).le) hw1 hp hp1 hsp]
  let c : Fin (k+1)×Fin (k+1) → ℝ := fun a => if a.1=a.2 then w a.1 else 0
  have hc : ∀ a, 0 ≤ c a := by intro a; dsimp [c]; split_ifs; exact (hw a.1).le; rfl
  have hr : ∀ i, ∑ j, c (i,j)=w i := by intro i; simp [c]
  have he : ∀ j, ∑ i, c (i,j)=w j := by intro j; simp [c]
  let B := max (q (Fin.last k):ℝ) (p (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (q (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hq1 hp1
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_left _ _)
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_right _ _)
  have H := entropy_coupled_stationary_comparison c w h w g q p hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hQ hP hsq
  have H' := entropy_coupled_stationary_comparison c w g w h p q hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hP hQ hsp
  have hsum : (∑ a, c a*|h a.1-g a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp
  have hsum' : (∑ a, c a*|g a.1-h a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp [abs_sub_comm]
  rw [hsum] at H
  rw [hsum'] at H'
  unfold finiteSphericalDualObjective
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma sphericalExp_gaussian_average (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    (∫ y, sphericalExp n (x+σ • y) R ∂stdGaussian (Spin (n+1)))=
      Real.exp (R^2*σ^2/2)*sphericalExp n x R := by
  let μ := stdGaussian (Spin (n+1))
  let ν := unitSphereLaw (n+1)
  have hI : Integrable (fun p : Spin (n+1)×Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))) (μ.prod ν) := by
    apply (((gaussian_integrable_exp_norm μ (|R| *|σ|)).const_mul (Real.exp (|R| *‖x‖))).comp_fst ν).mono' (by fun_prop)
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu : ‖(p.2:Spin (n+1))‖=1 := by simp
      have hh := abs_real_inner_le_norm (x+σ • p.1) (p.2:Spin (n+1))
      rw [hu,mul_one] at hh
      have ht := norm_add_le x (σ • p.1)
      rw [norm_smul,Real.norm_eq_abs] at ht
      have hb := mul_le_mul_of_nonneg_left (hh.trans ht) (abs_nonneg R)
      rw [← abs_mul] at hb
      have hl := (le_abs_self (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))).trans hb
      nlinarith
  have H := integral_integral_swap (f := fun (y : Spin (n+1)) (u : Metric.sphere (0:Spin (n+1)) 1) =>
    Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1)))) hI
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_ at H
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_
  rw [H]
  have he (u : Metric.sphere (0:Spin (n+1)) 1) :
      (∫ y : Spin (n+1), Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂μ)=
        Real.exp (R^2*σ^2/2)*Real.exp (R*inner ℝ x (u:Spin (n+1))) := by
    simp only [inner_add_left,real_inner_smul_left,mul_add,Real.exp_add]
    rw [integral_const_mul]
    have hh := integral_exp_inner_stdGaussian (u:Spin (n+1)) (R*σ)
    have hu : ‖(u:Spin (n+1))‖=1 := by simp
    rw [hu] at hh
    simp only [one_pow,mul_one] at hh
    have hinner : (fun y : Spin (n+1) => Real.exp (R*(σ*inner ℝ y (u:Spin (n+1)))))=
        (fun y => Real.exp ((R*σ)*inner ℝ (u:Spin (n+1)) y)) := by
      funext y
      rw [real_inner_comm y (u:Spin (n+1))]
      congr 1
      ring
    rw [hinner,hh,mul_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteFieldModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma FiniteFieldModel.integral {f : Time → ℝ} (M : FiniteFieldModel f) (F : ℝ → ℝ) :
    (∫ u, F (f u) ∂timeLaw)=∑ i, M.weight i*F (M.value i) := by
  unfold FiniteFieldModel.weight
  rw [← integral_finite_label M.label M.measurable_label (fun i => F (M.value i))]
  apply integral_congr_ae
  filter_upwards [M.agrees] with u hu
  rw [hu]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldRounding
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma sub_roundLower_lt (N : ℕ) {x : ℝ} (_hx : 0 ≤ x) : x-roundLower N x < 1/(N+1:ℕ) := by
  have h := Nat.lt_floor_add_one ((N+1:ℕ)*x)
  unfold roundLower
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm,add_comm] using h

lemma BoundedField.round_error {H : ℝ} (f : BoundedField H) (N : ℕ) (u : Time) :
    |f.round N u-f u| ≤ 1/(N+1:ℕ) := by
  change |roundLower N (f u)-f u| ≤ _
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (roundLower_le N (f.nonneg u)))]
  exact (sub_roundLower_lt N (f.nonneg u)).le

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedMarkedSelection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma roundTimeValue_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundTimeValue q n) :=
  (strictRoundModel q n).monotone_value

lemma BoundedField.round_tendsto {H : ℝ} (q : BoundedField H) (u : Time) :
    Tendsto (fun n => q.round n u) atTop (𝓝 (q u)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [Real.dist_eq,Nat.cast_add,Nat.cast_one] using q.round_error n u

lemma roundTime_tendsto (q : Time→Time) (hq : Monotone q) (u : Time) :
    Tendsto (fun n => roundTime (unitQuantileField q hq) n u) atTop (𝓝 (q u)) :=
  tendsto_subtype_rng.mpr ((unitQuantileField q hq).round_tendsto u)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_AnnealedMarkedReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SphericalPerceptronFreeEnergy
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_marked_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : A→(Fin r→S)→ℝ}
    (hG : Measurable (Function.uncurry G)) {B : ℝ} (hGB : ∀ a x,|G a x|≤B) :
    (∫ a,G a.1 (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH)=
      ∫ a,gibbsReplicaMean (κ a) (H a) r (G a) ∂P := by
  let := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (by fun_prop))
  have hi : Integrable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using hGB a.1 (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  rw [kernelInfiniteReplica_prefix_integral _ a r hG.of_uncurry_left]
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r (G a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma singleFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : |singleFieldMark w z|≤‖w‖ := w.norm_coe_le_norm _

lemma bulkSingleAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : |bulkSingleAverage n M w a x|≤M/(n+1:ℕ)*‖w‖ := by
  unfold bulkSingleAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,singleFieldMark w (bulkPatternFields i a x)|≤M*‖w‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => singleFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleEmpiricalLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

lemma bulkReplicaMean_annealed (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    bulkReplicaMean n M f v r G =
      ∫ p,G p.1 (fun i => p.2 i.val) ∂bulkAnnealedReplicaLaw n M f v := by
  symm
  exact annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f v) (bulkGibbsHamiltonian_measurable n M f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r hG hb

lemma bulkReplicaPrefix_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    Integrable (fun p => G p.1 (fun i => p.2 i.val)) (bulkAnnealedReplicaLaw n M f v) := by
  have hm : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => G p.1 (fun i => p.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable C
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p.1 (fun i => p.2 i.val)

lemma bulkReplicaMean_centered_square (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0≤C) (hb : ∀ a x,|G a x|≤C) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => (G a x-c)^2)=
      bulkReplicaMean n M f v r (fun a x => (G a x)^2)-2*c*bulkReplicaMean n M f v r G+c^2 := by
  have hsq : ∀ a x,|(G a x)^2|≤C^2 := fun a x => by
    rw [abs_pow]; exact (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb a x)
  have hcent : ∀ a x,|(G a x-c)^2|≤(C+|c|)^2 := fun a x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub (G a x) c).trans (add_le_add (hb a x) le_rfl)) 2
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ ((hG.sub_const c).pow_const 2) _ hcent,
    bulkReplicaMean_annealed _ _ _ _ _ _ (hG.pow_const 2) _ hsq,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG _ hb]
  have hg := bulkReplicaPrefix_integrable n M f v r G hG C hb
  have hg2 := bulkReplicaPrefix_integrable n M f v r (fun a x => (G a x)^2) (hG.pow_const 2) (C^2) hsq
  simp_rw [sub_sq]
  have h₁ : Integrable (fun p => (G p.1 (fun i => p.2 i.val))^2-2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := hg2.sub ((hg.const_mul 2).mul_const c)
  have h₂ : Integrable (fun p => 2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := (hg.const_mul 2).mul_const c
  rw [integral_add h₁ (integrable_const (μ:=bulkAnnealedReplicaLaw n M f v) (c^2)),
    integral_sub hg2 h₂,integral_mul_const,integral_const_mul]
  simp
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialIdentity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology

lemma bulkReplicaMean_mean_square_le (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (A : ℝ) (hA : 0≤A) (hb : ∀ a x,|F a x|≤A) (c : ℝ) :
    (bulkReplicaMean n M f v r F-c)^2≤
      bulkReplicaMean n M f v r (fun a x => (F a x-c)^2) := by
  rw [bulkReplicaMean_centered_square n M f v r F hF A hA hb c]
  have hme : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => F p.1 (fun i : Fin r=>p.2 i.val)) :=
    hF.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  have hp : MemLp (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) 2 (bulkAnnealedReplicaLaw n M f v) :=
    MemLp.of_bound hme.aestronglyMeasurable A (ae_of_all _ fun p=>by simpa only [Real.norm_eq_abs] using hb p.1 (fun i=>p.2 i.val))
  have hvv := variance_nonneg (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) (bulkAnnealedReplicaLaw n M f v)
  rw [variance_eq_sub hp] at hvv
  rw [bulkReplicaMean_annealed n M f v r F hF A hb,
    bulkReplicaMean_annealed n M f v r (fun a x => (F a x)^2) (hF.pow_const 2) (A^2)
      (fun a x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb a x) 2)]
  simp only [Pi.pow_apply] at hvv
  nlinarith

lemma bulkReplicaMean_L2_tendsto (N M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (r : ℕ)
    (F : (n : ℕ)→BulkDisorder (N n+1) (M n)→(Fin r→NormalizedSpin (N n+1))→ℝ)
    (hF : ∀ n,Measurable (Function.uncurry (F n))) (A : ℕ→ℝ) (hA : ∀ n,0≤A n)
    (hb : ∀ n a x,|F n a x|≤A n) (c : ℝ)
    (hl : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (F n)) atTop (𝓝 c) := by
  have hb' n : |bulkReplicaMean (N n) (M n) f (v n) r (F n)-c|≤
      Real.sqrt (bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) := by
    have he := bulkReplicaMean_mean_square_le (N n) (M n) r f (v n) (F n) (hF n) (A n) (hA n) (hb n) c
    exact Real.abs_le_sqrt he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun n=>abs_nonneg _) hb' (by simpa only [Real.sqrt_zero] using hl.sqrt)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulkFeature_inner (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x y : NormalizedSpin (m+1)) (j k : Fin (n+1)⊕Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x j) (cavityBulkFeature n d m M f a y k)=
      if j=k then Sum.elim (fun _=>bulkB (m+1) M f a.1 x y)
        (fun _=>inner ℝ x.val y.val) j else 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,cavityBulkFeature]
  rw [Fintype.sum_prod_type]
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    have he (p : Fin (n+1)⊕Fin d) :
        (∑ t : Fin M⊕Fin (m+1),
          (if p=j then cavityBulkBase n d m M f a y j t else 0)*
          (if p=j then cavityBulkBase n d m M f a x j t else 0))=
        if p=j then ∑ t : Fin M⊕Fin (m+1),
          cavityBulkBase n d m M f a y j t*cavityBulkBase n d m M f a x j t else 0 := by
      split_ifs <;> simp_all
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ,ite_true]
    cases j with
    | inl _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inl,mul_zero,Finset.sum_const_zero,add_zero]
      unfold bulkB
      rw [Finset.mul_sum]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
      apply Finset.sum_congr rfl
      intro i _hi
      have hn : (0:ℝ)<(m+1:ℕ) := by positivity
      have hs : Real.sqrt ((m+1:ℕ):ℝ)^2=(m+1:ℕ) := Real.sq_sqrt hn.le
      have hp : Real.sqrt ((m+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
      field_simp
      rw [hs]
      ring
    | inr _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl
  · rw [ite_eq_right hjk]
    apply Finset.sum_eq_zero
    intro p _hp
    apply Finset.sum_eq_zero
    intro t _ht
    by_cases hpj : p=j
    · subst p
      simp [hjk]
    · simp [hpj]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma log_sub_le_div_sub {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Real.log a-Real.log b≤(a-b)/b := by
  have h:=Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma cavity_cap_tail {x Λ : ℝ} (hx : 0≤x) (hΛ : 0<Λ) :
    0≤x-min x Λ ∧ x-min x Λ≤x^2/Λ := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  · apply (le_div_iff₀ hΛ).mpr
    by_cases h : x≤Λ
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith

lemma cavity_capped_log_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W F : S→ℝ} {C Λ : ℝ}
    (hW : Measurable W) (hWC : ∀ x,|W x|≤C) (hF : MemLp F 2 μ)
    (hF1 : ∀ x,1≤F x) (hΛ : 1≤Λ) :
    let A:=∫ x,Real.exp (W x)*F x ∂μ
    let B:=∫ x,Real.exp (W x)*min (F x) Λ ∂μ
    0≤Real.log A-Real.log B ∧
      Real.log A-Real.log B≤Real.exp (2*C)/Λ*(∫ x,(F x)^2 ∂μ) := by
  dsimp only
  let G : S→ℝ:=fun x=>min (F x) Λ
  have hFp x : 0≤F x := (by norm_num : (0:ℝ)≤1).trans (hF1 x)
  have hGp x : 1≤G x := le_min (hF1 x) hΛ
  have hGb x : ‖G x‖≤Λ := by
    rw [Real.norm_eq_abs,abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact min_le_right _ _
  have hGm : AEStronglyMeasurable G μ := (hF.aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hGi : Integrable G μ := Integrable.of_bound hGm Λ (ae_of_all _ hGb)
  have hFi := hF.integrable (by norm_num)
  have hF2 : Integrable (fun x=>(F x)^2) μ := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hWF : Integrable (fun x=>Real.exp (W x)*F x) μ := by
    apply (hFi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (hFp x)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) (hFp x)
  have hWG : Integrable (fun x=>Real.exp (W x)*G x) μ := by
    apply (hGi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hGm)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2)
      ((by norm_num : (0:ℝ)≤1).trans (hGp x))
  have hBlo : Real.exp (-C)≤∫ x,Real.exp (W x)*G x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-C) ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hWG fun x=>by
        calc
          Real.exp (-C)≤Real.exp (W x) := Real.exp_le_exp.mpr (abs_le.mp (hWC x)).1
          _≤Real.exp (W x)*G x := by nlinarith [Real.exp_pos (W x),hGp x]
  have hBA : (∫ x,Real.exp (W x)*G x ∂μ)≤∫ x,Real.exp (W x)*F x ∂μ :=
    integral_mono hWG hWF fun x=>mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
  have hBp: 0<∫ x,Real.exp (W x)*G x ∂μ := (Real.exp_pos _).trans_le hBlo
  have hAp:=hBp.trans_le hBA
  have htail : (∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ)≤
      Real.exp C/Λ*(∫ x,(F x)^2 ∂μ) := by
    rw [←integral_sub hWF hWG,←integral_const_mul]
    apply integral_mono (hWF.sub hWG) (hF2.const_mul _)
    intro x
    have ht:=cavity_cap_tail (hFp x) ((by norm_num : (0:ℝ)<1).trans_le hΛ)
    calc
      _=Real.exp (W x)*(F x-G x)  := by simp only [Pi.sub_apply]; ring
      _≤Real.exp C*(F x-G x) := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) ht.1
      _≤Real.exp C*((F x)^2/Λ) := mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le
      _=_ := by ring
  refine ⟨sub_nonneg.mpr (Real.log_le_log hBp hBA),?_⟩
  calc
    _≤((∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ))/
      (∫ x,Real.exp (W x)*G x ∂μ) := log_sub_le_div_sub hAp hBp
    _≤(Real.exp C/Λ*(∫ x,(F x)^2 ∂μ))/(Real.exp (-C)) :=
      (div_le_div_of_nonneg_right htail hBp.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg (div_nonneg (Real.exp_pos _).le (le_trans (by norm_num) hΛ))
          (integral_nonneg fun x=>sq_nonneg _)) (Real.exp_pos _) hBlo)
    _=_ := by rw [Real.exp_neg,div_inv_eq_mul,show 2*C=C+C by ring,Real.exp_add]; ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCompensator
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_exp_local_lipschitz {a b K : ℝ} (ha : a≤K) (hb : b≤K) :
    |Real.exp a-Real.exp b|≤Real.exp K*|a-b| := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (s:=Iic K) (C:=Real.exp K)
    (fun x _hx=>Real.differentiableAt_exp)
    (fun x hx=>by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx)
    (convex_Iic K) hb ha
  simpa only [Real.norm_eq_abs] using h

lemma cavity_log_local_lipschitz {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a-Real.log b|≤|a-b|/m := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.log) (s:=Ici m) (C:=m⁻¹)
    (fun x hx=>Real.differentiableAt_log (hm.trans_le hx).ne')
    (fun x hx=>by
      rw [Real.deriv_log,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hm.trans_le hx))]
      exact inv_anti₀ hm hx)
    (convex_Ici m) hb ha
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_comm] using h

lemma cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W C : S→ℝ} {a b K c t : ℝ}
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (∫ x,Real.exp (t*C x)*W x ∂μ)-
      (t*c+Real.log (∫ x,W x ∂μ))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(∫ x,|C x-c| ∂μ) := by
  have hb : 0≤b := by
    by_contra hh
    have hfalse : ∀ x : S, False := fun x=>not_le.mpr (ha.trans_le ((hw x).1.trans (hw x).2)) (le_of_not_ge hh)
    have he : (univ : Set S)=∅ := Set.ext (fun x=>⟨fun _=>(hfalse x).elim,fun h=>h.elim⟩)
    have hμ := measure_univ (μ:=μ)
    rw [he,measure_empty] at hμ
    exact zero_ne_one hμ
  have hK : 0≤K := (abs_nonneg c).trans hc
  have hWi : Integrable W μ := Integrable.of_bound hW.aestronglyMeasurable b
    (ae_of_all _ fun x=>by rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le (hw x).1)]; exact (hw x).2)
  have hEi : Integrable (fun x=>Real.exp (t*C x)*W x) μ :=
    Integrable.of_bound (hC.const_mul t |>.exp |>.aestronglyMeasurable |>.mul hW.aestronglyMeasurable)
      (Real.exp (t*K)*b) (ae_of_all _ fun x=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (ha.trans_le (hw x).1)]
        exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht))
          (hw x).2 (ha.trans_le (hw x).1).le (Real.exp_pos _).le)
  have hBi := hWi.const_mul (Real.exp (t*c))
  have hlo : Real.exp (-(t*K))*a≤∫ x,Real.exp (t*C x)*W x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-(t*K))*a ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hEi fun x=>by
        apply mul_le_mul _ (hw x).1 ha.le (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        nlinarith [(abs_le.mp (hcb x)).1]
  have hWlo : a≤∫ x,W x ∂μ := by
    simpa using integral_mono (integrable_const a) hWi fun x=>(hw x).1
  have hbLo : Real.exp (-(t*K))*a≤Real.exp (t*c)*(∫ x,W x ∂μ) := by
    apply mul_le_mul _ hWlo ha.le (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hc).1])
  have hCi : Integrable (fun x=>|C x-c|) μ :=
    Integrable.of_bound (hC.sub_const c).abs.aestronglyMeasurable (K+|c|)
      (ae_of_all _ fun x=>by simpa only [Real.norm_eq_abs,abs_abs] using
        (abs_sub (C x) c).trans (add_le_add (hcb x) (le_refl |c|)))
  have hdiff : |(∫ x,Real.exp (t*C x)*W x ∂μ)-Real.exp (t*c)*(∫ x,W x ∂μ)|≤
      Real.exp (t*K)*b*t*(∫ x,|C x-c| ∂μ) := by
    rw [←integral_const_mul,←integral_sub hEi hBi]
    apply (abs_integral_le_integral_abs).trans
    rw [←integral_const_mul]
    apply integral_mono (hEi.sub hBi).abs (hCi.const_mul _)
    intro x
    simp only [Pi.sub_apply]
    rw [←sub_mul,abs_mul,abs_of_pos (ha.trans_le (hw x).1)]
    have hex:=cavity_exp_local_lipschitz
      (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht)
      (mul_le_mul_of_nonneg_left (abs_le.mp hc).2 ht)
    rw [←mul_sub,abs_mul,abs_of_nonneg ht] at hex
    calc
      _≤(Real.exp (t*K)*(t*|C x-c|))*b := mul_le_mul hex (hw x).2 (ha.trans_le (hw x).1).le (by positivity)
      _=_ := by ring
  have hlog:=cavity_log_local_lipschitz (mul_pos (Real.exp_pos _) ha) hlo hbLo
  rw [Real.log_mul (Real.exp_pos _).ne' (ha.trans_le hWlo).ne',Real.log_exp] at hlog
  exact hlog.trans (by
    apply (div_le_div_of_nonneg_right hdiff (mul_pos (Real.exp_pos _) ha).le).trans
    apply le_of_eq
    ring)


lemma bulkC_measurable (m M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder (m+1) M×NormalizedSpin (m+1)=>bulkC (m+1) M f p.1.1 p.2) := by
  unfold bulkC
  fun_prop

lemma bulkC_bound (m M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (a : BulkDisorder (m+1) M) (x : NormalizedSpin (m+1)) :
    |bulkC (m+1) M f a.1 x|≤M/(m+1:ℕ)*‖f.dilationMark hf‖ := by
  exact bulkSingleAverage_bound m M (f.dilationMark hf) a (fun _=>x)

lemma cavity_comp_partition_joint_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H:=fun p x=>H p.1 x)
    (Y:=fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (Ψ.measurable.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityBulkCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkCompPartition n d m M f v Λ hΛ) := by
  exact cavity_comp_partition_joint_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) _ _

lemma cavityCompensatorConstant_nonneg (n d : ℕ) (f : ℝ→ᵇℝ) {Λ K : ℝ} (hΛ : 1≤Λ) :
    0 ≤ cavityCompensatorConstant n d f Λ K := by
  unfold cavityCompensatorConstant
  have : 0≤Λ := (by norm_num : (0:ℝ)≤1).trans hΛ
  positivity

lemma tilt_cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H W C : S→ℝ} {a b K c t : ℝ}
    (hH : Measurable H) (he : Integrable (fun x=>Real.exp (1*H x)) μ)
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (tiltMean μ H (fun x=>Real.exp (t*C x)*W x) 1)-
      (t*c+Real.log (tiltMean μ H W 1))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(tiltMean μ H (fun x=>|C x-c|) 1) := by
  have := tilt_law_probability_of_integrable μ he
  simp_rw [←tilt_law_integral_of_integrable μ hH he]
  exact cavity_compensator_bound _ hW hC ha ht hw hc hcb

lemma cavityBulkSingleWeight_measurable (n d m M : ℕ) (f : Jet3)
    (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    Measurable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) := by
  exact (cavitySingleTest n d f.f Λ hΛ).measurable.comp
    (cavity_rows_joint_measurable ((cavityBulkFeature_measurable n d m M f).of_uncurry_left) measurable_const)

lemma cavityBulkCompPartition_error (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    |Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)-
      ((n+1:ℕ)/2*c+Real.log (cavityBulkPartition n d m M f v Λ hΛ p))|≤
    cavityCompensatorConstant n d f.f Λ K*
      tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
        (fun x=>|bulkC (m+1) M f p.1.1 x-c|) 1 := by
  apply tilt_cavity_compensator_bound (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    (by simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v p.1)
    (cavityBulkSingleWeight_measurable n d m M f Λ hΛ p)
    ((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id))
    (Real.exp_pos _) (by positivity) (fun x=>cavitySingleTest_bounds n d f.f Λ hΛ _) hc (hC p.1)

lemma bulkC_L1_of_L2 (N M : ℕ→ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (v : ℕ→ℕ→ℝ) (c : ℝ)
    (hc : Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>(bulkC (N j+1) (M j) f a.1 (x 0)-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)) atTop (𝓝 0) := by
  apply bulkReplicaMean_L2_tendsto N M f.f v 1
    (fun j a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)
    (fun j=>?_) (fun j=>(M j:ℝ)/(N j+1:ℕ)*‖f.dilationMark hf‖+|c|)
    (fun j=>by positivity) (fun j a x=>?_) 0
  · simpa only [sub_zero,sq_abs] using hc
  · exact (((bulkC_measurable (N j) (M j) f).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).sub_const c).abs
  · rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add (bulkC_bound (N j) (M j) f hf a (x 0)) le_rfl)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySphericalMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma sphericalExp_square_le (n : ℕ) (R : ℝ) (x : Spin (n+1)) :
    sphericalExp n x R ^2 ≤ sphericalExp n x (2*R) := by
  let F : NormalizedSpin (n+1)→ℝ:=fun u=>Real.exp (R*inner ℝ x u.val)
  have hm : MemLp F 2 (unitSphereLaw (n+1)) := by
    apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable F _ from
      (show Continuous F from by unfold F; fun_prop).aestronglyMeasurable)).mpr
    exact unitSphere_continuous_integrable (by unfold F; fun_prop)
  have hv:=variance_nonneg F (unitSphereLaw (n+1))
  rw [variance_eq_sub hm] at hv
  have he : (∫ u,F u^2 ∂unitSphereLaw (n+1))=sphericalExp n x (2*R) := by
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [F]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  change 0≤(∫ u,F u^2 ∂unitSphereLaw (n+1))-(∫ u,F u ∂unitSphereLaw (n+1))^2 at hv
  rw [he] at hv
  exact sub_nonneg.mp hv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellExpansion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianRows_basis (n : ℕ) (σ : ℝ) (y : Spin (n+1)) :
    gaussianRows (fun i : Fin (n+1)=>σ • EuclideanSpace.single i (1:ℝ)) y=σ •y := by
  ext i
  simp [gaussianRows_apply,real_inner_smul_left,EuclideanSpace.inner_single_left]

lemma gaussianRows_isotropic_law (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) :
    (stdGaussian E).map (gaussianRows v)=
      (stdGaussian (Spin (n+1))).map (fun y=>Real.sqrt b •y) := by
  have hg : Matrix.gram ℝ v=Matrix.gram ℝ (fun i : Fin (n+1)=>Real.sqrt b • EuclideanSpace.single i (1:ℝ)) := by
    ext i j
    simp only [Matrix.gram_apply,hv,inner_smul_left,inner_smul_right,conj_trivial]
    by_cases h : i=j
    · subst j
      simp [Real.sq_sqrt hb,←pow_two]
    · simp [EuclideanSpace.inner_single_left,h]
  rw [gaussianRows_map_stdGaussian,hg,←gaussianRows_map_stdGaussian]
  congr 1
  funext y
  exact gaussianRows_basis n (Real.sqrt b) y

lemma gaussianRows_spherical_average (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R ∂stdGaussian E)=Real.exp (R^2*b/2) := by
  rw [←integral_map (gaussianRows v).measurable.aemeasurable
    (sphericalExp_continuous n R).aestronglyMeasurable,gaussianRows_isotropic_law n v hb hv,
    integral_map (by fun_prop) (sphericalExp_continuous n R).aestronglyMeasurable]
  have h:=sphericalExp_gaussian_average n R (Real.sqrt b) 0
  have hz : sphericalExp n 0 R=1 := by simp [sphericalExp]
  simpa only [zero_add,Real.sq_sqrt hb,hz,mul_one] using h

lemma gaussianRows_spherical_memLp (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    MemLp (fun g=>sphericalExp n (gaussianRows v g) R) 2 (stdGaussian E) := by
  have hm := (sphericalExp_continuous n R).comp (gaussianRows v).continuous
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi : Integrable (fun g=>sphericalExp n (gaussianRows v g) (2*R)) (stdGaussian E) := by
    by_contra hn
    have h:=gaussianRows_spherical_average n v hb hv (2*R)
    rw [integral_undef hn] at h
    exact (Real.exp_pos _).ne' h.symm
  apply hi.mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sphericalExp_square_le n R _

lemma gaussianRows_spherical_second (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R^2 ∂stdGaussian E)≤Real.exp (2*R^2*b) := by
  have hs := (memLp_two_iff_integrable_sq
    ((gaussianRows_spherical_memLp n v hb hv R).aestronglyMeasurable)).mp
    (gaussianRows_spherical_memLp n v hb hv R)
  have hi := (gaussianRows_spherical_memLp n v hb hv (2*R)).integrable (by norm_num)
  apply (integral_mono hs hi (fun g=>sphericalExp_square_le n R _)).trans_eq
  rw [gaussianRows_spherical_average n v hb hv]
  congr 1
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityMeanCap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_expected_cap {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (μ : Measure S) (P : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W F : G×S→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hFx : ∀ g,MemLp (fun x=>F (g,x)) 2 μ)
    (hFg : ∀ x,MemLp (fun g=>F (g,x)) 2 P)
    (h2 : ∀ x,(∫ g,F (g,x)^2 ∂P)≤K) :
    let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
    Integrable D P ∧ 0≤∫ g,D g ∂P ∧
      (∫ g,D g ∂P)≤Real.exp (2*C)/Λ*K := by
  let Q : S×G→ℝ := fun p=>F (p.2,p.1)^2
  have hQ : Measurable Q := (hF.comp measurable_swap).pow_const 2
  have hi : Integrable Q (μ.prod P) := by
    apply (integrable_prod_iff hQ.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x=>(memLp_two_iff_integrable_sq (hFg x).aestronglyMeasurable).mp (hFg x)
    · apply Integrable.of_bound (hQ.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable K
      filter_upwards [] with x
      have he : (∫ g,‖Q (x,g)‖ ∂P)=(∫ g,F (g,x)^2 ∂P) := by
        simp only [Q,Real.norm_eq_abs,abs_sq]
      rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun g=>sq_nonneg _)]
      exact h2 x
  have hS : Integrable (fun g=>∫ x,F (g,x)^2 ∂μ) P := hi.integral_prod_right
  have hB : (∫ g,∫ x,F (g,x)^2 ∂μ ∂P)≤K := by
    rw [←integral_integral_swap hi]
    calc
      _≤∫ _ : S,K ∂μ := integral_mono hi.integral_prod_left (integrable_const _) h2
      _=K := by simp
  let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
    Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
  have hD : Measurable D := by
    exact ((hW.exp.mul hF).stronglyMeasurable.integral_prod_right.measurable.log).sub
      ((hW.exp.mul (hF.min measurable_const)).stronglyMeasurable.integral_prod_right.measurable.log)
  have hp g : 0≤D g ∧ D g≤Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) :=
    cavity_capped_log_bound μ (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (g,x)) (hFx g) (fun x=>hF1 (g,x)) hΛ
  have hc : 0≤Real.exp (2*C)/Λ := div_nonneg (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)
  have hDi : Integrable D P := by
    apply (hS.const_mul (Real.exp (2*C)/Λ)).mono' hD.aestronglyMeasurable
    exact ae_of_all _ fun g=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (hp g).1] using (hp g).2
  refine ⟨hDi,integral_nonneg (fun g=>(hp g).1),?_⟩
  calc
    _≤∫ g,Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) ∂P :=
      integral_mono hDi (hS.const_mul _) (fun g=>(hp g).2)
    _=Real.exp (2*C)/Λ*(∫ g,∫ x,F (g,x)^2 ∂μ ∂P) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hB hc

lemma cavity_rows_joint_continuous {A J E : Type*} [TopologicalSpace A]
    [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : A→J→E} {y : A→E} (hv : Continuous v) (hy : Continuous y) :
    Continuous (fun a=>gaussianRows (v a) (y a)) := by
  change Continuous (fun a=>WithLp.toLp 2 (fun i=>inner ℝ (v a i) (y a)))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i=>((continuous_apply i).comp hv).inner hy

lemma cavityBulkFeature_continuous (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M) :
    Continuous (cavityBulkFeature n d m M f a) := by
  apply continuous_pi
  intro j
  unfold cavityBulkFeature
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  split_ifs
  · cases j <;> cases p.2 <;> dsimp [cavityBulkBase] <;> fun_prop
  · exact continuous_const

lemma cavityBulk_full_vector_second (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) :
    MemLp (fun y=>sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))) 2 (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
    (∫ y,sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))^2 ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
      Real.exp (2*(n+1:ℕ)*K) := by
  let w := fun i : Fin (n+1)=>cavityBulkFeature n d m M f a x (Sum.inl i)
  have hw i j : inner ℝ (w i) (w j)=if i=j then bulkB (m+1) M f a.1 x x else 0 := by
    simp only [w,cavityBulkFeature_inner,Sum.inl.injEq,Sum.elim_inl]
  have hb : 0≤bulkB (m+1) M f a.1 x x := by
    have hh : 0 ≤ inner ℝ (w 0) (w 0) := real_inner_self_nonneg
    rwa [hw,ite_eq_left rfl] at hh
  refine ⟨gaussianRows_spherical_memLp n w hb hw _,?_⟩
  apply (gaussianRows_spherical_second n w hb hw _).trans
  apply Real.exp_le_exp.mpr
  rw [Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ))]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans ((bulkB_bound _ _ _ _ _ _).trans hK)) (by positivity)

lemma cavityBulk_unclipped_cap (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC)
    (a : BulkDisorder (m+1) M) :
    let D:=fun y=>Real.log (cavityBulkFullCompPartition n d m M f v (a,y))-
      Real.log (cavityBulkCompPartition n d m M f v Λ hΛ (a,y))
    Integrable D (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
      (∀ y,0≤D y) ∧ 0≤∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∧
      (∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
        Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let μ:=tiltLaw (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a) 1
  have he : Integrable (fun x=>Real.exp (1*bulkGibbsHamiltonian m M f.f v a x)) (unitSphereLaw (m+1)) := by
    simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v a
  let : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _ he
  let w:=fun x i=>cavityBulkFeature n d m M f a x (Sum.inl i)
  let F : E×NormalizedSpin (m+1)→ℝ:=fun p=>sphericalExp n (gaussianRows (w p.2) p.1) (Real.sqrt (n+1:ℕ))
  let W : E×NormalizedSpin (m+1)→ℝ:=fun p=>(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2+
    ∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    exact (continuous_apply (Sum.inl i)).comp (cavityBulkFeature_continuous n d m M f a)
  have hFr : Continuous (fun p : E×NormalizedSpin (m+1)=>gaussianRows (w p.2) p.1) :=
    cavity_rows_joint_continuous (hw.comp continuous_snd) continuous_fst
  have hF : Continuous F := (sphericalExp_continuous n _).comp hFr
  have hW : Measurable W := by
    unfold W bulkC
    have hc:=cavityBulkFeature_continuous n d m M f a
    fun_prop
  have hWC p : |W p|≤(n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖ := by
    calc
      _≤|(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2|+
        |∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)| := abs_add_le _ _
      _≤(n+1:ℕ)/2*KC+∑ _ : Fin d,‖f.f‖ := by
        apply add_le_add
        · rw [abs_mul,abs_of_nonneg (by positivity : 0≤((n+1:ℕ):ℝ)/2)]
          exact mul_le_mul_of_nonneg_left (hC a p.2) (by positivity)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht=>f.f.norm_coe_le_norm _)
      _=_ := by simp
  have hFx y : MemLp (fun x=>F (y,x)) 2 μ :=
    (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg x:=cavityBulk_full_vector_second n d m M f a x K hK
  have hc:=cavity_expected_cap μ (stdGaussian E) W F hW hF.measurable hWC
    (fun p=>one_le_sphericalExp n _ _) hΛ hFx (fun x=>(hfg x).1) (fun x=>(hfg x).2)
  have hH:=(bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left (x:=a)
  have hfull y : (∫ x,Real.exp (W (y,x))*F (y,x) ∂μ)=cavityBulkFullCompPartition n d m M f v (a,y) :=
    tilt_law_integral_of_integrable _ hH he
  have hcap y : (∫ x,Real.exp (W (y,x))*min (F (y,x)) Λ ∂μ)=cavityBulkCompPartition n d m M f v Λ hΛ (a,y) := by
    rw [tilt_law_integral_of_integrable _ hH he]
    unfold cavityBulkCompPartition
    congr 1
    funext x
    simp only [W,F,w,cavitySingleTest_apply,gaussianRows_apply,Real.exp_add,Real.exp_sum]
    change Real.exp _ * (∏ t, _) * min (sphericalExp n (WithLp.toLp 2 _) _) Λ = _
    ring_nf
    rfl
  have hp y:=cavity_capped_log_bound μ
    (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (y,x))
    (hFx y) (fun x=>one_le_sphericalExp n _ _) hΛ
  dsimp only [Function.comp_apply,id_eq] at hc hp ⊢
  simp_rw [hfull,hcap] at hc hp
  refine ⟨hc.1,fun y=>(hp y).1,hc.2.1,hc.2.2.trans_eq ?_⟩
  rw [Real.exp_add]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityAnnealedUncap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_comp_partition_unbounded_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ℝ)
    (hΨ : Measurable Ψ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H := fun p x=>H p.1 x)
    (Y := fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (hΨ.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityFullSingleTest_measurable (n d : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
      Real.exp (∑ t,f (z (Sum.inr t)))*
        sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i))) (Real.sqrt (n+1:ℕ))) := by
  apply Measurable.mul (by fun_prop)
  apply (sphericalExp_continuous n _).measurable.comp
  fun_prop

lemma cavityBulkFullCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavityBulkFullCompPartition n d m M f v) := by
  have h:=cavity_comp_partition_unbounded_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) ((n+1:ℕ)/2)
    _ (cavityFullSingleTest_measurable n d f.f)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  simp only [Real.exp_add,gaussianRows_apply]
  rw [mul_assoc]
  rfl

lemma cavityBulkUncapError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkUncapError n d m M f v Λ hΛ) :=
  (cavityBulkFullCompPartition_measurable n d m M f v).log.sub
    (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log

theorem cavityBulk_uncap_annealed (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    let D:=cavityBulkUncapError n d m M f v Λ hΛ
    let P:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
    Integrable D P ∧ 0≤∫ p,D p ∂P ∧ (∫ p,D p ∂P)≤
      Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let D:=cavityBulkUncapError n d m M f v Λ hΛ
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let B:=Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ
  have hsec a:=cavityBulk_unclipped_cap n d m M f v Λ hΛ K KC hK hC a
  have hD : Measurable D:=cavityBulkUncapError_measurable n d m M f v Λ hΛ
  have hnorm a : (∫ y,‖D (a,y)‖ ∂stdGaussian E)=∫ y,D (a,y) ∂stdGaussian E := by
    apply integral_congr_ae
    exact ae_of_all _ fun y=>by
      change ‖D (a,y)‖=D (a,y)
      exact Real.norm_of_nonneg ((hsec a).2.1 y)
  have hi : Integrable D ((bulkDisorderLaw (m+1) M).prod (stdGaussian E)) := by
    apply (integrable_prod_iff hD.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun a=>(hsec a).1
    · apply Integrable.of_bound (hD.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable B
      filter_upwards [] with a
      rw [hnorm,Real.norm_eq_abs]
      have hp : 0≤∫ y,D (a,y) ∂stdGaussian E := (hsec a).2.2.1
      rw [abs_of_nonneg hp]
      exact (hsec a).2.2.2
  refine ⟨hi,integral_nonneg (fun p=>(hsec p.1).2.1 p.2),?_⟩
  rw [integral_prod _ hi]
  calc
    _≤∫ _ : BulkDisorder (m+1) M,B ∂bulkDisorderLaw (m+1) M :=
      integral_mono hi.integral_prod_left (integrable_const B) (fun a=>(hsec a).2.2.2)
    _=B := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityApproxStationary
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma finiteSphericalDual_approx_stationary {k : ℕ} (w h g : Fin (k+1)→ℝ)
    (q : Fin (k+1)→Time) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh : Monotone h) (hh0 : 0≤h 0) (hg : Monotone g) (hg0 : 0≤g 0)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ)<1)
    (hs : ∀ i,2*g i=weightedStepA w (fun j=>(q j:ℝ)) (q i))
    {δ : ℝ} (_hδ : 0≤δ) (hd : ∀ i,|h i-g i|≤δ) :
    (entropy (weightedStepTrial w q (fun i=>(hw i).le) hw1)).toReal-
      (∑ i,w i*h i*(q i:ℝ))-2*δ ≤
      sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1) := by
  have hsum : (∑ i,w i*|h i-g i|)≤δ := by
    calc
      _≤∑ i,w i*δ:=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hd i) (hw i).le
      _=δ:=by rw [←Finset.sum_mul,hw1,one_mul]
  have hD:=finiteSphericalDual_abs_sub_le w h g hw hw1 hh hh0 hg hg0
  rw [finiteSphericalDual_eq_stationary w g q (fun i=>(hw i).le) hw1 hq hq1 hs] at hD
  unfold finiteSphericalDualObjective at hD
  have hterm : (∑ i,w i*g i*(q i:ℝ))-(∑ i,w i*h i*(q i:ℝ))≤δ := by
    calc
      _=∑ i,w i*((g i-h i)*(q i:ℝ)):=by rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
      _≤∑ i,w i*|h i-g i|:=by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i).le
        calc
          (g i-h i)*(q i:ℝ)≤|g i-h i| *(q i:ℝ):=mul_le_mul_of_nonneg_right (le_abs_self _) (q i).prop.1
          _≤|g i-h i| *1:=mul_le_mul_of_nonneg_left (q i).prop.2 (abs_nonneg _)
          _=|h i-g i|:=by rw [mul_one,abs_sub_comm]
      _≤δ:=hsum
  linarith [(abs_le.mp (hD.trans hsum)).1]


lemma terminalVariational_le_trial (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (m : Trial) (hm : entropy m≠⊤) :
    (terminalVariational P α f).toReal ≤ α*controlValue P f m+(entropy m).toReal := by
  apply EReal.coe_le_coe_iff.mp
  rw [terminalVariational_coe_toReal P α hα f,EReal.coe_add,
    EReal.coe_ennreal_toReal hm]
  exact iInf_le _ m

lemma finiteCavity_trial_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (n d : ℕ) {k : ℕ}
    (w h g : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh : Monotone h) (hh0 : 0≤h 0) (hg : Monotone g) (hg0 : 0≤g 0)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ)<1)
    (hs : ∀ i,2*g i=weightedStepA w (fun j=>(q j:ℝ)) (q i))
    {δ ε a : ℝ} (hδ : 0≤δ) (hd : ∀ i,|h i-g i|≤δ)
    (hdim : |finiteSphericalFieldValue n k w h-
      sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε)
    (hdα : |(d:ℝ)-(n+1:ℕ)*α|≤1) :
    (n+1:ℕ)*(a/2+(terminalVariational P α f).toReal-
      (∑ i,w i*h i*(q i:ℝ))-2*δ-ε)-‖f‖ ≤
    (n+1:ℕ)*(a/2+finiteSphericalFieldValue n k w h)+
      d*controlValue P f (weightedStepTrial w q (fun i=>(hw i).le) hw1) := by
  let m:=weightedStepTrial w q (fun i=>(hw i).le) hw1
  have hm : entropy m≠⊤ := by
    rw [entropy_weightedStepTrial w q (fun i=>(hw i).le) hw1 (q (Fin.last k))
      (q (Fin.last k)).prop.1 hq1 (fun i=>hq (Fin.le_last i))]
    exact ENNReal.ofReal_ne_top
  have hv:=terminalVariational_le_trial P hα f m hm
  have hstat:=finiteSphericalDual_approx_stationary w h g q hw hw1 hh hh0 hg hg0 hq hq1 hs hδ hd
  have hcv : |controlValue P f m|≤‖f‖ :=
    abs_le.mpr ⟨neg_norm_le_controlValue P f m,controlValue_le_norm P f m⟩
  have he : |((d:ℝ)-(n+1:ℕ)*α)*controlValue P f m|≤‖f‖ := by
    rw [abs_mul]
    exact (mul_le_mul hdα hcv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hL : (0:ℝ)≤(n+1:ℕ):=by positivity
  have hlo := mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mp hdim).1) hL
  have hslo := mul_le_mul_of_nonneg_left hstat hL
  have hvlo := mul_le_mul_of_nonneg_left hv hL
  dsimp only [m] at hvlo he
  nlinarith [(abs_le.mp he).1]
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityExpectedCompensator
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCDefect_measurable (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ) :
    Measurable (bulkCDefect m M f v c) := by
  exact kernel_tiltMean_measurable (bulkSpinKernel m M)
    (bulkGibbsHamiltonian_measurable m M f.f v) ((bulkC_measurable m M f).sub_const c).abs

lemma bulkCDefect_bound (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (a : BulkDisorder (m+1) M) : |bulkCDefect m M f v c a|≤K+|c| := by
  apply tiltMean_bound_general (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    ((((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id)).sub_const c).abs)
    (by positivity)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (hC a x) le_rfl)

lemma bulkCDefect_integral (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ) :
    (∫ a,bulkCDefect m M f v c a ∂bulkDisorderLaw (m+1) M)=
      bulkReplicaMean m M f.f v 1 (fun a x=>|bulkC (m+1) M f a.1 (x 0)-c|) := by
  unfold bulkReplicaMean
  apply integral_congr_ae
  filter_upwards [] with a
  symm
  exact gibbsReplicaMean_coordinate_of_integrable (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    ((((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id)).sub_const c).abs)
    (bulkHamiltonian_exp_integrable m M f.f v a) 1 0

lemma cavityBulkCompError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c : ℝ) : Measurable (cavityBulkCompError n d m M f v Λ hΛ c) :=
  (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log.sub
    ((cavityBulkPartition_measurable n d m M f v Λ hΛ).log.const_add _)

lemma cavityBulkCompError_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (cavityBulkCompError n d m M f v Λ hΛ c)
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkCompError_measurable n d m M f v Λ hΛ c).aestronglyMeasurable
    (cavityCompensatorConstant n d f.f Λ K*(K+|c|))
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  refine (cavityBulkCompPartition_error n d m M f v Λ hΛ c K hc hC p).trans ?_
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bulkCDefect_bound m M f v c K ((abs_nonneg _).trans hc) hC p.1))
    (cavityCompensatorConstant_nonneg n d f.f hΛ)

lemma cavityBulkCompError_mean_bound (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    |∫ p,cavityBulkCompError n d m M f v Λ hΛ c p
      ∂((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))))|≤
      cavityCompensatorConstant n d f.f Λ K*
        bulkReplicaMean m M f.f v 1 (fun a x=>|bulkC (m+1) M f a.1 (x 0)-c|) := by
  have hE:=cavityBulkCompError_integrable n d m M f v Λ hΛ c K hc hC
  let P:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
  have hD : Integrable (fun p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)=>
      bulkCDefect m M f v c p.1) P := by
    apply Integrable.of_bound ((bulkCDefect_measurable m M f v c).comp measurable_fst).aestronglyMeasurable (K+|c|)
    exact ae_of_all _ fun p=>by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using bulkCDefect_bound m M f v c K ((abs_nonneg _).trans hc) hC p.1
  refine (abs_integral_le_integral_abs).trans ?_
  calc
    _≤∫ p,cavityCompensatorConstant n d f.f Λ K*bulkCDefect m M f v c p.1 ∂P :=
      integral_mono hE.abs (hD.const_mul _) (fun p=>cavityBulkCompPartition_error n d m M f v Λ hΛ c K hc hC p)
    _=_ := by rw [integral_const_mul,integral_fun_fst]; simp only [probReal_univ,one_smul,bulkCDefect_integral]

theorem cavityBulkCompError_tendsto_zero (n d : ℕ) (N M : ℕ→ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ j (a : BulkDisorder (N j+1) (M j)) x,|bulkC (N j+1) (M j) f a.1 x|≤K)
    (hL2 : Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>(bulkC (N j+1) (M j) f a.1 (x 0)-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun j=>∫ p,cavityBulkCompError n d (N j) (M j) f (v j) Λ hΛ c p
      ∂((bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j))))))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun j=> -(cavityCompensatorConstant n d f.f Λ K*
      bulkReplicaMean (N j) (M j) f.f (v j) 1 (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)))
    (h:=fun j=>cavityCompensatorConstant n d f.f Λ K*
      bulkReplicaMean (N j) (M j) f.f (v j) 1 (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|))
  · simpa using ((bulkC_L1_of_L2 N M f hf v c hL2).const_mul (cavityCompensatorConstant n d f.f Λ K)).neg
  · simpa using (bulkC_L1_of_L2 N M f hf v c hL2).const_mul (cavityCompensatorConstant n d f.f Λ K)
  · intro j; exact (abs_le.mp (cavityBulkCompError_mean_bound n d (N j) (M j) f (v j) Λ hΛ c K hc (hC j))).1
  · intro j; exact (abs_le.mp (cavityBulkCompError_mean_bound n d (N j) (M j) f (v j) Λ hΛ c K hc (hC j))).2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianCoordinateProjection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace SphericalPerceptronFreeEnergy

lemma finiteGaussian_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (e : J→I) (he : Function.Injective e) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I=>fun j=>x (e j))
      (stdGaussian (EuclideanSpace ℝ I)) (Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (PiLp.continuous_toLp 2 _).measurable]
  change (Measure.pi fun _ : I=>gaussianReal 0 1).map (fun x j=>x (e j))=_
  rw [←Measure.infinitePi_eq_pi,Measure.map_infinitePi_infinitePi_of_inj he,Measure.infinitePi_eq_pi]

lemma finiteGaussian_curry_preserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun x : I×J→ℝ=>fun i j=>x (i,j))
      (Measure.pi fun _ : I×J=>gaussianReal 0 1)
      (Measure.pi fun _ : I=>Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  have h:=Measure.infinitePi_map_curry (μ:=fun (_ : I) (_ : J)=>gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma cavityBulkNoiseSplit_preserving (n d m M : ℕ) :
    MeasurePreserving (cavityBulkNoiseSplit n d m M)
      (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
      ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d)) := by
  let e : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))→CavityBulkNoiseIndex n d m M :=
    Sum.elim (fun p=>(Sum.inl p.2,Sum.inl p.1)) (fun p=>(Sum.inr p.1,Sum.inr p.2))
  have he : Function.Injective e := by
    intro a b h
    cases a <;> cases b <;> simp only [e,Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq,Sum.inl.injEq,
      Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,false_and] at h
    · exact congrArg Sum.inl (Prod.ext h.2 h.1)
    · exact congrArg Sum.inr (Prod.ext h.1 h.2)
  have hp:=(measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))=>gaussianReal 0 1)).comp
    (finiteGaussian_coordinate_projection e he)
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin (n+1)→ℝ)→Spin (n+1))
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin (n+1))) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hleft:=(measurePreserving_pi (fun _ : Fin M=>Measure.pi fun _ : Fin (n+1)=>gaussianReal 0 1)
    (fun _=>stdGaussian (Spin (n+1))) (fun _=>ht)).comp (finiteGaussian_curry_preserving (Fin M) (Fin (n+1)))
  convert (hleft.prod (finiteGaussian_curry_preserving (Fin d) (Fin (m+1)))).comp hp using 1
  · rfl
  · rfl

lemma cavityBulkNoiseSplit_scalar (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) (t : Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x (Sum.inr t)) y=
      ∑ i,(cavityBulkNoiseSplit n d m M y).2 t i*x.val i := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,cavityBulkNoiseSplit]
  simp only [Sum.inl_ne_inr,Sum.inr.injEq,ite_false,ite_self,Finset.sum_const_zero,zero_add]
  rw [Finset.sum_comm]
  simp

lemma cavityBulkNoiseSplit_vector (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y=
      cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,a.1 t i*x.val i))
        (Real.sqrt (m+1:ℕ))⁻¹ (cavityBulkNoiseSplit n d m M y).1 := by
  classical
  ext i
  simp only [gaussianRows_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,
    cavityBulkNoiseSplit,cavityVectorField,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  simp only [Sum.inl.injEq,Sum.inr_ne_inl,ite_false,ite_self,Finset.sum_const_zero,add_zero]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']
  try simp only [cavityVectorField,PiLp.smul_apply,smul_eq_mul,PiLp.sum_apply,PiLp.toLp_apply]
  simp_rw [mul_comm (y.ofLp _) _]
  simp only [WithLp.ofLp_sum,PiLp.smul_apply,Finset.sum_apply,smul_eq_mul]
  simp only [mul_assoc,Finset.mul_sum]
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkUncappedLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulk_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    Integrable (fun p=>Real.log (cavityBulkPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkPartition_measurable n d m M f v Λ hΛ).log.aestronglyMeasurable
    ‖cavityPartitionLogTest d f.f Λ‖
  exact ae_of_all _ fun p=>(cavityPartitionLogTest d f.f Λ).norm_coe_le_norm
    ⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩

lemma cavityBulk_comp_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (fun p=>Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=cavityBulkCompError_integrable n d m M f v Λ hΛ 0 K (by simpa using hK) hC
  have hb:=cavityBulk_log_integrable n d m M f v Λ hΛ
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkCompError]; ring)

lemma cavityBulk_full_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (K KC : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) (hKC : 0≤KC)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    Integrable (fun p=>Real.log (cavityBulkFullCompPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=(cavityBulk_uncap_annealed n d m M f v 1 le_rfl K KC hK hC).1
  have hb:=cavityBulk_comp_log_integrable n d m M f v 1 le_rfl KC hKC hC
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkUncapError]; ring)

lemma cavityBulkFullLog_decomposition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K KC : ℝ) (hc : |c|≤KC)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    let Q:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
    cavityBulkFullLog n d m M f v=
      (∫ p,cavityBulkUncapError n d m M f v Λ hΛ p ∂Q)+
      (∫ p,cavityBulkCompError n d m M f v Λ hΛ c p ∂Q)+
      ((n+1:ℕ)/2*c+cavityBulkLog n d m M f v Λ hΛ) := by
  have hKC : 0≤KC:=(abs_nonneg c).trans hc
  have hi:=cavityBulk_full_log_integrable n d m M f v K KC hK hKC hC
  have hj:=cavityBulk_comp_log_integrable n d m M f v Λ hΛ KC hKC hC
  have hk:=cavityBulk_log_integrable n d m M f v Λ hΛ
  dsimp only
  unfold cavityBulkUncapError cavityBulkCompError
  have hs:=integral_sub hj ((integrable_const ((n+1:ℕ)/2*c)).add hk)
  have ha:=integral_add (integrable_const ((n+1:ℕ)/2*c)) hk
  simp only [Pi.add_apply] at hs ha
  rw [integral_sub hi hj,hs,ha,integral_const,probReal_univ,one_smul,integral_prod _ hk]
  unfold cavityBulkFullLog cavityBulkLog
  ring

lemma cavityBulkNoiseJoin_measurable (n d m M : ℕ) :
    Measurable (cavityBulkNoiseJoin n d m M) := by
  apply (MeasurableEquiv.toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  rcases j with ⟨i,t⟩
  cases i <;> cases t <;> dsimp [cavityBulkNoiseJoin] <;> fun_prop

lemma cavityBulkNoiseSplit_join (n d m M : ℕ)
    (p : (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ)) :
    cavityBulkNoiseSplit n d m M (cavityBulkNoiseJoin n d m M p)=p := by
  rfl

lemma cavitySplitPartition_identity (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    cavityBulkFullCompPartition n d m M f v (a,y)=
      cavitySplitPartition n d m M f v (a,cavityBulkNoiseSplit n d m M y) := by
  unfold cavitySplitPartition
  rw [tilt_law_integral _ (bulkHamiltonian_section_measurable (m+1) M f.f v a)
    (show 0≤M*‖f.f‖+bulkFeatureBound (m+1) v*‖a.2‖ from by
      unfold bulkFeatureBound; positivity) (bulkHamiltonian_bound (m+1) M f.f v a) 1]
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  rw [cavityBulkNoiseSplit_vector]
  simp_rw [cavityBulkNoiseSplit_scalar]
  congr 2
  unfold normalizedPatternEnergy
  ring

lemma cavitySplitPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavitySplitPartition n d m M f v) := by
  have hm:=(cavityBulkFullCompPartition_measurable n d m M f v).comp
    (measurable_fst.prodMk ((cavityBulkNoiseJoin_measurable n d m M).comp measurable_snd))
  simpa only [Function.comp_def,cavitySplitPartition_identity,cavityBulkNoiseSplit_join] using hm

lemma cavitySplitLog_integrable (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p=>Real.log (cavitySplitPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d))) := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  apply (hp.integrable_comp (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).mp
  have hi:=cavityBulk_full_log_integrable n d m M f v
    (M/(m+1:ℕ)*‖f.d1‖^2) (M/(m+1:ℕ)*‖f.dilationMark hf‖) le_rfl (by positivity)
    (bulkC_bound m M f hf)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2).symm

lemma cavityBulkFullLog_split (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    cavityBulkFullLog n d m M f v=
      ∫ a,∫ b,∫ y,Real.log (cavitySplitPartition n d m M f v (a,y,b))
        ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (n+1)))
        ∂finitePatternRowsLaw (m+1) d ∂bulkDisorderLaw (m+1) M := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  have h : (∫ p,Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))
      ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))))=
      ∫ p,Real.log (cavitySplitPartition n d m M f v p)
        ∂(bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
          (finitePatternRowsLaw (m+1) d)) := by
    rw [←hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).symm
  unfold cavityBulkFullLog
  have he : (fun p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)=>
      Real.log (cavityBulkFullCompPartition n d m M f v p))=
      (fun p=>Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))) := by
    funext p
    exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2)
  rw [he,h,integral_prod _ (cavitySplitLog_integrable n d m M f hf v)]
  apply integral_congr_ae
  filter_upwards [(cavitySplitLog_integrable n d m M f hf v).prod_right_ae] with a ha
  exact integral_prod_symm _ ha

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCounts
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_count_bounds {α : ℝ} (hα : 0≤α) (N : ℕ) :
    α*N-1≤(patternCount α N:ℝ) ∧ (patternCount α N:ℝ)≤α*N := by
  constructor
  · have h:=Nat.lt_floor_add_one (α*(N:ℝ))
    dsimp only [patternCount]
    linarith
  · exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg N))

lemma cavity_count_density {α : ℝ} (hα : 0≤α) :
    Tendsto (fun n=>(patternCount α (n+1):ℝ)/(n+1:ℕ)) atTop (𝓝 α) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi:=tendsto_inv_atTop_zero.comp hN
  have hl: Tendsto (fun n : ℕ=>α-((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 α) := by
    simpa only [sub_zero,Function.comp_def] using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    have h:=(cavity_count_bounds hα (n+1)).1
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
    calc
      _ = α*(n+1:ℕ)-1 := by field_simp
      _ ≤ _ := h
  · intro n
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2

lemma cavity_count_eventually_two {α : ℝ} (hα : 0<α) :
    ∀ᶠ n : ℕ in atTop,2≤patternCount α (n+1) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h:= (hN.const_mul_atTop hα).eventually_ge_atTop 3
  filter_upwards [h] with n hn
  have hb:=(cavity_count_bounds hα.le (n+1)).1
  have hc : (2:ℝ)≤patternCount α (n+1) := by linarith
  exact_mod_cast hc

lemma cavity_omitted_full {α : ℝ} (hα : 0<α) :
    ∀ᶠ n : ℕ in atTop,cavityOmittedCount α n+2=patternCount α (n+1) := by
  filter_upwards [cavity_count_eventually_two hα] with n hn
  exact Nat.sub_add_cancel hn

lemma cavity_omitted_density {α : ℝ} (hα : 0<α) :
    Tendsto (fun n=>((cavityOmittedCount α n+2:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 α) := by
  apply (cavity_count_density hα.le).congr'
  filter_upwards [cavity_omitted_full hα] with n hn
  rw [hn]

lemma cavity_omitted_bound {α : ℝ} (hα : 0≤α) (n : ℕ) :
    ((cavityOmittedCount α n+2:ℕ):ℝ)/(n+1:ℕ)≤α+2 := by
  have h: ((cavityOmittedCount α n+2:ℕ):ℝ)≤(patternCount α (n+1):ℝ)+2 := by
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ 2) 2
  have hb:=(cavity_count_bounds hα (n+1)).2
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
  have hN : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

lemma cavity_fresh_count {α : ℝ} (hα : 0≤α) (n L : ℕ) :
    patternCount α (n+1)+cavityFreshCount α n L=patternCount α (n+1+L) ∧
    |(cavityFreshCount α n L:ℝ)-(L:ℝ)*α|≤1 ∧
    cavityFreshCount α n L≤⌈(L:ℝ)*α+1⌉₊ := by
  have hm : patternCount α (n+1)≤patternCount α (n+1+L) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right (n+1) L) hα)
  have he : (cavityFreshCount α n L:ℝ)=(patternCount α (n+1+L):ℝ)-(patternCount α (n+1):ℝ) := by
    exact Nat.cast_sub hm
  refine ⟨Nat.add_sub_of_le hm,?_,?_⟩
  · rw [he,abs_le]
    have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    constructor <;> nlinarith [h0.1,h0.2,h1.1,h1.2]
  · have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    have hh : (cavityFreshCount α n L:ℝ)≤(L:ℝ)*α+1 := by rw [he]; nlinarith [h0.1,h1.2]
    exact_mod_cast hh.trans (Nat.le_ceil ((L:ℝ)*α+1))


lemma CavityGoodParameters.nonempty {α : ℝ} {f : ℝ→ᵇℝ} (G : CavityGoodParameters α f) :
    ∀ᶠ n in atTop,(bulkJointGoodSet α f G.J n).Nonempty := by
  filter_upwards [G.mass.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  by_contra h
  have he : bulkJointGoodSet α f G.J n=∅:=Set.not_nonempty_iff_eq_empty.mp h
  simp only [he,compl_empty,probReal_univ] at hn
  exact lt_irrefl _ hn

lemma cavity_eventually_uniform {X : Type*} (S : ℕ→Set X) (T : Set X) (x0 : X)
    (hx0 : x0∈T) (hST : ∀ n,S n⊆T) (hS : ∀ᶠ n in atTop,(S n).Nonempty)
    (R : ℕ→X→Prop)
    (hR : ∀ v : ℕ→X,(∀ n,v n∈T)→(∀ᶠ n in atTop,v n∈S n)→∀ᶠ n in atTop,R n (v n)) :
    ∀ᶠ n in atTop,∀ x∈S n,R n x := by
  classical
  let v : ℕ→X:=fun n=>if h : ∃ x∈S n,¬R n x then h.choose
    else if h' : (S n).Nonempty then h'.choose else x0
  have hvT : ∀ n,v n∈T := by
    intro n
    dsimp only [v]
    split_ifs with h h'
    · exact hST n h.choose_spec.1
    · exact hST n h'.choose_spec
    · exact hx0
  have hvS : ∀ᶠ n in atTop,v n∈S n := by
    filter_upwards [hS] with n hn
    by_cases h : ∃ x∈S n,¬R n x
    · simpa only [v,dite_eq_left h] using h.choose_spec.1
    · simpa only [v,dite_eq_right h,dite_eq_left hn] using hn.choose_spec
  filter_upwards [hR v hvT hvS] with n hn
  intro x hx
  by_contra hbad
  have he : ∃ x∈S n,¬R n x:=⟨x,hx,hbad⟩
  have hneg : ¬R n (v n) := by
    dsimp only [v]
    rw [dite_eq_left he]
    exact he.choose_spec.2
  exact hneg hn
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityOldExpectation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_three_integral {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] (F : A×B×C→ℝ)
    (hF : Integrable F (μ.prod (ν.prod ρ))) :
    (∫ p,F p ∂μ.prod (ν.prod ρ))=∫ a,∫ b,∫ c,F (a,b,c) ∂ρ ∂ν ∂μ := by
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with a ha
  exact integral_prod _ ha

lemma cavitySplitLog_proxy_integrable (n k M d : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p : CavityProxyRandom n (k+1) M d=>Real.log (cavitySplitPartition k d n M f v (p.1,p.2.2,p.2.1)))
      (cavityProxyLaw n (k+1) M d) := by
  have : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have : SFinite (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := inferInstance
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (n+1) M)).prod
    (Measure.measurePreserving_swap (μ:=finitePatternRowsLaw (n+1) d)
      (ν:=Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))))
  exact (hp.integrable_comp (cavitySplitPartition_measurable k d n M f v).log.aestronglyMeasurable).mpr
    (cavitySplitLog_integrable k d n M f hf v)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma cavitySplitPartition_lower (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : Fin M→Spin (n+1)) (b : Fin d→Fin (m+1)→ℝ)
    {KC : ℝ} (hC : ∀ x,|bulkC (m+1) M f a.1 x|≤KC) :
    Real.exp (-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2) ≤ cavitySplitPartition n d m M f v (a,y,b) := by
  let μ:=tiltLaw (unitSphereLaw (m+1)) (bulkHamiltonian (m+1) M f.f v a.1 a.2) 1
  have : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable m M f.f v a)
  let F:=fun x : NormalizedSpin (m+1)=>Real.exp (normalizedPatternEnergy (m+1) d f.f b x+
    (n+1:ℕ)*bulkC (m+1) M f a.1 x/2)*
    sphericalExp n (cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,a.1 t i*x.val i))
      (Real.sqrt (m+1:ℕ))⁻¹ y) (Real.sqrt (n+1:ℕ))
  have hw : Continuous (normalizedPatternEnergy (m+1) d f.f b) :=
    (normalizedPatternEnergy_continuous (m+1) d f.f).comp (continuous_const.prodMk continuous_id)
  have hc : Continuous (bulkC (m+1) M f a.1) := by unfold bulkC; fun_prop
  have hv : Continuous (fun x : NormalizedSpin (m+1)=>cavityVectorField M (n+1)
      (fun t=>f.d1 (∑ i,a.1 t i*x.val i)) (Real.sqrt (m+1:ℕ))⁻¹ y) := by
    unfold cavityVectorField
    fun_prop
  have hi : Integrable F μ := ((hw.add ((continuous_const.mul hc).div_const 2)).rexp.mul
    ((sphericalExp_continuous n _).comp hv)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change _≤∫ x,F x ∂μ
  calc
    _=(∫ _ : NormalizedSpin (m+1),Real.exp (-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2) ∂μ) := by simp
    _≤_ := integral_mono (integrable_const _) hi (fun x=>by
      have hb:=(abs_le.mp (normalizedPatternEnergy_bound (m+1) d f.f b x)).1
      have hc':=(abs_le.mp (hC x)).1
      have hs := mul_le_mul_of_nonneg_left hc' (show (0:ℝ)≤(n+1:ℕ) from by positivity)
      dsimp only [F]
      calc
        _≤Real.exp (normalizedPatternEnergy (m+1) d f.f b x+(n+1:ℕ)*bulkC (m+1) M f a.1 x/2) :=
          Real.exp_le_exp.mpr (by nlinarith)
        _≤_ := le_mul_of_one_le_right (Real.exp_pos _).le (one_le_sphericalExp n _ _))

lemma cavitySplitLog_lower (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : Fin M→Spin (n+1)) (b : Fin d→Fin (m+1)→ℝ)
    {KC : ℝ} (hC : ∀ x,|bulkC (m+1) M f a.1 x|≤KC) :
    -(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ≤ Real.log (cavitySplitPartition n d m M f v (a,y,b)) := by
  have h:=cavitySplitPartition_lower n d m M f v a y b hC
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h

lemma cavityBulkFullLog_lower (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ)
    {KC : ℝ} (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    -(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ≤ cavityBulkFullLog n d m M f v := by
  let G:=fun p : CavityProxyRandom m (n+1) M d=>Real.log (cavitySplitPartition n d m M f v (p.1,p.2.2,p.2.1))
  have hi : Integrable G (cavityProxyLaw m (n+1) M d):=cavitySplitLog_proxy_integrable m n M d f hf v
  have he: (∫ p,G p ∂cavityProxyLaw m (n+1) M d)=cavityBulkFullLog n d m M f v := by
    unfold cavityProxyLaw
    rw [cavity_three_integral _ _ _ G hi,cavityBulkFullLog_split n d m M f hf v]
  rw [←he]
  calc
    _=(∫ _ : CavityProxyRandom m (n+1) M d,-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ∂cavityProxyLaw m (n+1) M d) := by simp
    _≤_ := integral_mono (integrable_const _) hi (fun p=>cavitySplitLog_lower n d m M f v p.1 p.2.2 p.2.1 (hC p.1))
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_ContinuousCavityProfile
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cappedA_monotone (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ} (hB : B < 1) :
    Monotone (cappedA μ B) :=
  monotone_of_hasDerivAt_nonneg (cappedA_hasDerivAt μ hB) (fun _ => sq_nonneg _)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProbabilityMaps
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction BigOperators NNReal

lemma probabilityMap_tendsto_of_ae_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure Ω) (F : ℕ → Ω → X) (G : Ω → X)
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hlim : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun n => F n ω) atTop (𝓝 (G ω))) :
    Tendsto (fun n => μ.map (hF n).aemeasurable) atTop (𝓝 (μ.map hG.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have he n : (∫ x, f x ∂(μ.map (hF n).aemeasurable : Measure X)) =
      ∫ ω, f (F n ω) ∂(μ : Measure Ω) :=
    integral_map (hF n).aemeasurable f.measurable.aestronglyMeasurable
  have hg : (∫ x, f x ∂(μ.map hG.aemeasurable : Measure X)) =
      ∫ ω, f (G ω) ∂(μ : Measure Ω) :=
    integral_map hG.aemeasurable f.measurable.aestronglyMeasurable
  simp_rw [he,hg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.measurable.comp (hF n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
  exact hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω

lemma FiniteFieldModel.property_of_ae {f : Time→ℝ} (M : FiniteFieldModel f)
    (p : ℝ→Prop) (hf : ∀ᵐ u ∂timeLaw,p (f u)) (i : Fin (M.depth+1)) : p (M.value i) := by
  have hi : timeLaw (M.label ⁻¹' {i})≠0 := by
    intro hi
    have hp:=M.positive i
    change 0<(timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u,M.label u=i ∧ p (M.value (M.label u)) := by
    by_contra! hn
    have hz : ∀ᵐ u ∂timeLaw,u∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hz)
  obtain ⟨u,hu,hv⟩:=hne
  simpa [hu] using hv

lemma quantileRoundLaw_tendsto (η : Measure Time) [IsProbabilityMeasure η] :
    Tendsto (quantileRoundLaw η) atTop (𝓝 (⟨η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time)) := by
  have h:=probabilityMap_tendsto_of_ae_tendsto (⟨timeLaw,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time)
    (roundTime (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)))
    (boundedQuantile η) (fun j=>(roundTime_mono _ j).measurable) (boundedQuantile_measurable η)
    (ae_of_all _ fun u=>roundTime_tendsto _ (boundedQuantile_monotone η) u)
  have he : ProbabilityMeasure.map (⟨timeLaw,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time) (f := boundedQuantile η) (boundedQuantile_measurable η).aemeasurable=
      (⟨η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time) := by
    apply Subtype.ext
    exact boundedQuantile_law η
  rw [he] at h
  exact h

lemma realTail_quantileRoundLaw (η : Measure Time) [IsProbabilityMeasure η] (j : ℕ) (r : ℝ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    realTail (quantileRoundLaw η j) r=
      weightedStepTail (strictRoundModel F j).weight (fun i=>(roundTimeValue F j i:ℝ)) r := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  change (∫ x,1-max r (x:ℝ) ∂timeLaw.map (roundTime F j))=_
  rw [integral_map (roundTime_mono F j).measurable.aemeasurable (by fun_prop)]
  simpa only [F,roundTime,roundTimeValue,weightedStepTail,max_comm] using (strictRoundModel F j).integral (fun x=>1-max r x)

lemma quantileRoundLaw_support (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    ∀ᵐ r : Time ∂(quantileRoundLaw η j : Measure Time),(r:ℝ)≤B := by
  have hq : ∀ᵐ u ∂timeLaw,(boundedQuantile η u:ℝ)≤B := by
    have h:=hη
    rw [←boundedQuantile_law η] at h
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  apply (ae_map_iff (roundTime_mono _ _).measurable.aemeasurable (measurableSet_le measurable_subtype_coe measurable_const)).mpr
  exact hq.mono fun u hu=>(roundLower_le j (boundedQuantile η u).prop.1).trans hu

lemma roundTimeValue_support (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,(roundTimeValue F j i:ℝ)≤B := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  have hq : ∀ᵐ u ∂timeLaw,(boundedQuantile η u:ℝ)≤B := by
    have h:=hη
    rw [←boundedQuantile_law η] at h
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  exact (strictRoundModel F j).property_of_ae (fun r=>r≤B)
    (hq.mono fun u hu=>(roundLower_le j (boundedQuantile η u).prop.1).trans hu)

lemma cappedA_nonneg (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ cappedA η B r :=
  intervalIntegral.integral_nonneg hr (fun _ _=>sq_nonneg _)

lemma roundTimeValue_profile_exact (η : Measure Time) [IsProbabilityMeasure η]
    {B K a : ℝ} (hB : B<1) (ha0 : 0≤a) (haK : a≤K)
    (hA : ∀ᵐ r : Time ∂η,cappedA η B r≤a) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,(continuousCavityProfile η B ha0 haK (roundTimeValue F j i)).2.val=
      cappedA η B (roundTimeValue F j i) := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  have hq : ∀ᵐ u ∂timeLaw,cappedA η B (boundedQuantile η u)≤a := by
    have h : ∀ᵐ r : Time ∂timeLaw.map (boundedQuantile η),cappedA η B r≤a := by
      have hl : timeLaw.map (boundedQuantile η)=η := boundedQuantile_law η
      rw [hl]
      exact hA
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  have hv := (strictRoundModel F j).property_of_ae (fun r=>cappedA η B r≤a)
    (hq.mono fun u hu=>((cappedA_monotone η hB) (roundLower_le j (boundedQuantile η u).prop.1)).trans hu)
  dsimp only
  intro i
  change min a (max 0 (cappedA η B _))=_
  rw [max_eq_right (cappedA_nonneg η B (roundTimeValue F j i).prop.1)]
  exact min_eq_right (hv i)

lemma quantileRoundLaw_stationary (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,cappedA (quantileRoundLaw η j) B (roundTimeValue F j i)=
      weightedStepA (strictRoundModel F j).weight (fun l=>(roundTimeValue F j l:ℝ)) (roundTimeValue F j i) := by
  dsimp only
  intro i
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  rw [cappedA_eq_integral (quantileRoundLaw η j) (quantileRoundLaw_support η hη j)
    (roundTimeValue F j i).prop.1 (roundTimeValue_support η hη j i)]
  simp_rw [realTail_quantileRoundLaw]
  simp only [weightedStepA,one_div,inv_pow]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CappedAContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma realTail_weak_tendsto (μ : ℕ→ProbabilityMeasure Time) (ν : ProbabilityMeasure Time)
    (hμ : Tendsto μ atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun j=>realTail (μ j) t) atTop (𝓝 (realTail ν t)) := by
  let F : Time→ᵇℝ:=ContinuousMap.equivBoundedOfCompact Time ℝ ⟨fun s=>1-max t (s:ℝ),by fun_prop⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) F

lemma cappedDensity_bound (ν : Measure Time) {B : ℝ} (hB : B<1) (t : ℝ) :
    0 ≤ cappedDensity ν B t ∧ cappedDensity ν B t≤(1-B)⁻¹^2 := by
  have hb : 0<1-B:=sub_pos.mpr hB
  have hm : 0 < max (1-B) (realTail ν t):=hb.trans_le (le_max_left _ _)
  refine ⟨sq_nonneg _,?_⟩
  exact pow_le_pow_left₀ (inv_nonneg.mpr hm.le)
    ((inv_le_inv₀ hm hb).mpr (le_max_left _ _)) 2

lemma cappedAError_nonneg (μ ν : Measure Time) (B : ℝ) : 0 ≤ cappedAError μ ν B :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _=>abs_nonneg _)

lemma cappedA_sub_bound (μ ν : Measure Time) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : B<1) (r : Time) :
    |cappedA μ B r-cappedA ν B r| ≤ cappedAError μ ν B := by
  have hμ:=cappedDensity_continuous μ hB
  have hν:=cappedDensity_continuous ν hB
  rw [cappedA,cappedA,←intervalIntegral.integral_sub (hμ.intervalIntegrable _ _) (hν.intervalIntegrable _ _)]
  exact (intervalIntegral.abs_integral_le_integral_abs r.prop.1).trans
    (intervalIntegral.integral_mono_interval le_rfl r.prop.1 r.prop.2
      (ae_of_all _ fun _=>abs_nonneg _) ((hμ.sub hν).abs.intervalIntegrable _ _))

lemma cappedAError_tendsto (μ : ℕ→ProbabilityMeasure Time) (ν : ProbabilityMeasure Time)
    (hμ : Tendsto μ atTop (𝓝 ν)) {B : ℝ} (hB : B<1) :
    Tendsto (fun j=>cappedAError (μ j) ν B) atTop (𝓝 0) := by
  have hd (t : ℝ) : Tendsto (fun j=>cappedDensity (μ j) B t) atTop (𝓝 (cappedDensity ν B t)) := by
    exact ((tendsto_const_nhds.max (realTail_weak_tendsto μ ν hμ t)).inv₀
      (ne_of_gt ((sub_pos.mpr hB).trans_le (le_max_left _ _)))).pow 2
  have hh:=tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Ioc (0:ℝ) 1))
    (fun _ : ℝ=>2*(1-B)⁻¹^2)
    (F:=fun j t=>|cappedDensity (μ j) B t-cappedDensity ν B t|)
    (f:=fun _=>0)
    (fun j=>((cappedDensity_continuous (μ j) hB).sub (cappedDensity_continuous ν hB)).abs.measurable.aestronglyMeasurable)
    (integrable_const _) (fun j=>ae_of_all _ fun t=>by
      have h₁:=cappedDensity_bound (μ j) hB t
      have h₂:=cappedDensity_bound ν hB t
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_le.mpr ⟨by linarith,by linarith⟩)
    (ae_of_all _ fun t=>by simpa using ((hd t).sub (tendsto_const_nhds (x:=cappedDensity ν B t))).abs)
  simpa only [cappedAError,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_zero] using hh
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityRoundedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma roundedProfileMoment_tendsto (η : Measure Time) [IsProbabilityMeasure η]
    {B : ℝ} (hB : B<1) :
    Tendsto (roundedProfileMoment η B) atTop (𝓝 (cavityProfileMoment η B)) := by
  let G : Time→ᵇℝ:=ContinuousMap.equivBoundedOfCompact Time ℝ
    ⟨fun r=>(r:ℝ)*cappedA η B r/2,by exact
      (continuous_subtype_val.mul ((cappedA_continuous η hB).comp continuous_subtype_val)).div_const 2⟩
  have h:=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (quantileRoundLaw_tendsto η) G
  have he j : (∫ r,G r ∂(quantileRoundLaw η j : Measure Time))=roundedProfileMoment η B j := by
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    change (∫ r : Time,(r:ℝ)*cappedA η B r/2 ∂timeLaw.map (roundTime F j))=_
    rw [integral_map (roundTime_mono F j).measurable.aemeasurable (by
      exact ((continuous_subtype_val.mul ((cappedA_continuous η hB).comp continuous_subtype_val)).div_const 2).measurable.aestronglyMeasurable)]
    change (∫ u,(roundTime F j u:ℝ)*cappedA η B (roundTime F j u)/2 ∂timeLaw)=_
    have hv:=(strictRoundModel F j).integral (fun r=>r*cappedA η B r/2)
    change (∫ u,(roundTime F j u:ℝ)*cappedA η B (roundTime F j u)/2 ∂timeLaw)=_ at hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [roundedProfileMoment,roundTimeValue,F]
    ring
  simp_rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma roundedCavityValue_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (g : Jet3) (n d : ℕ)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a ε : ℝ}
    (hB : B<1) (ha0 : 0≤a) (haK : a≤K)
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (hA : ∀ᵐ r : Time ∂η,cappedA η B r≤a)
    (hdα : |(d:ℝ)-(n+1:ℕ)*α|≤1)
    (hdim : ∀ k (w h : Fin (k+1)→ℝ) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
      Monotone h → 0≤h 0 → h (Fin.last k)≤K/2 →
      |finiteSphericalFieldValue n k w h-sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε)
    (j : ℕ) :
    (n+1:ℕ)*(a/2+(terminalVariational P α g.f).toReal-roundedProfileMoment η B j-
      cappedAError (quantileRoundLaw η j) η B-ε)-‖g.f‖ ≤
      roundedCavityValue n d g P η B ha0 haK j := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  let q:=roundTimeValue F j
  let h:=fun i=>cappedA η B (q i)/2
  let h':=fun i=>cappedA (quantileRoundLaw η j) B (q i)/2
  have hh : Monotone h:=fun i l hil=>div_le_div_of_nonneg_right
    ((cappedA_monotone η hB) (roundTimeValue_mono F j hil)) (by norm_num)
  have hh' : Monotone h':=fun i l hil=>div_le_div_of_nonneg_right
    ((cappedA_monotone (quantileRoundLaw η j) hB) (roundTimeValue_mono F j hil)) (by norm_num)
  have hh0 : 0≤h 0:=div_nonneg (cappedA_nonneg η B (q 0).prop.1) (by norm_num)
  have hh'0 : 0≤h' 0:=div_nonneg (cappedA_nonneg (quantileRoundLaw η j) B (q 0).prop.1) (by norm_num)
  have hp i : (roundedCavityPair η B ha0 haK j i).2.val=cappedA η B (q i) :=
    roundTimeValue_profile_exact η hB ha0 haK hA j i
  have htop : h (Fin.last M.depth)≤K/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [←hp]
    exact ((roundedCavityPair η B ha0 haK j _).2.prop.2)
  have hq1 : (q (Fin.last M.depth):ℝ)<1:=
    (roundTimeValue_support η hη j _).trans_lt hB
  have hs i : 2*h' i=weightedStepA M.weight (fun l=>(q l:ℝ)) (q i) := by
    dsimp [h']; rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
    exact quantileRoundLaw_stationary η hη j i
  have hd i : |h i-h' i| ≤ cappedAError (quantileRoundLaw η j) η B/2 := by
    dsimp [h,h']
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sub_comm]
    exact div_le_div_of_nonneg_right (cappedA_sub_bound (quantileRoundLaw η j) η hB (q i)) (by norm_num)
  have hlow:=finiteCavity_trial_lower P hα g.f n d M.weight h h' q M.weight_pos M.weight_sum hh hh0 hh' hh'0
    (roundTimeValue_mono F j) hq1 hs
    (div_nonneg (cappedAError_nonneg _ _ _) (by norm_num)) hd
    (hdim _ _ _ M.weight_pos M.weight_sum hh hh0 htop) hdα (a:=a)
  have herr : 2*(cappedAError (quantileRoundLaw η j) η B/2)=cappedAError (quantileRoundLaw η j) η B:=by ring
  rw [herr] at hlow
  unfold roundedCavityValue
  simp_rw [hp]
  exact hlow


end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformUncapLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SphericalPerceptronFreeEnergy

lemma tendsto_zero_of_uniform_inverse_cap (f : ℕ→ℝ) (g : ℝ→ℕ→ℝ) {C : ℝ}
    (hC : 0≤C) (hbound : ∀ Λ,1≤Λ→∀ j,|f j-g Λ j|≤C/Λ)
    (hlim : ∀ Λ,1≤Λ→Tendsto (g Λ) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let Λ:=1+2*C/ε
  have hΛ : 1≤Λ:=by dsimp [Λ]; linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hC) hε.le]
  have hΛp : 0<Λ:=lt_of_lt_of_le zero_lt_one hΛ
  have hsmall : C/Λ<ε/2 := by
    apply (div_lt_iff₀ hΛp).mpr
    dsimp [Λ]
    field_simp
    nlinarith
  obtain ⟨N,hN⟩:=Metric.tendsto_atTop.mp (hlim Λ hΛ) (ε/2) (half_pos hε)
  refine ⟨N,fun j hj=>?_⟩
  have he:=hN j hj
  rw [Real.dist_eq,sub_zero] at he ⊢
  calc
    |f j|≤|f j-g Λ j|+|g Λ j|:=by simpa using abs_add_le (f j-g Λ j) (g Λ j)
    _≤C/Λ+|g Λ j|:=add_le_add (hbound Λ hΛ j) le_rfl
    _<ε:=by linarith
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityUncappedLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityBulkFullLog_rounded_tendsto (n d : ℕ) (N M : ℕ→ℕ) (g : Jet3)
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hBrow : IsBrownianReal brownianEval P)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a c KC : ℝ} (hB : B<1)
    (ha0 : 0≤a) (haK : a≤K) (hc : |c|≤KC)
    (hK : ∀ j,M j/(N j+1:ℕ)*‖g.d1‖^2≤K)
    (hC : ∀ j (b : BulkDisorder (N j+1) (M j)) x,|bulkC (N j+1) (M j) g b.1 x|≤KC)
    (hL2 : Tendsto (fun j=>bulkReplicaMean (N j) (M j) g.f (v j) 1
      (fun b x=>(bulkC (N j+1) (M j) g b.1 (x 0)-c)^2)) atTop (𝓝 0))
    (hcap : ∀ (Λ : ℝ) (hΛ : 1≤Λ),Tendsto (fun j=>cavityBulkLog n d (N j) (M j) g (v j) Λ hΛ-
      roundedCavityLog n d g.f Λ hΛ η B ha0 haK j) atTop (𝓝 0)) :
    Tendsto (fun j=>cavityBulkFullLog n d (N j) (M j) g (v j)-
      ((n+1:ℕ)/2*c+roundedCavityValue n d g P η B ha0 haK j)) atTop (𝓝 0) := by
  let U:=Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖g.f‖)+2*(n+1:ℕ)*K)
  let V:=Real.exp (2*((d:ℝ)*‖g.f‖))*Real.exp (2*(n+1:ℕ)*a)
  let F:=fun j=>cavityBulkFullLog n d (N j) (M j) g (v j)-
    ((n+1:ℕ)/2*c+roundedCavityValue n d g P η B ha0 haK j)
  let G:=fun Λ j=>if hΛ : 1≤Λ then
      (∫ b,cavityBulkCompError n d (N j) (M j) g (v j) Λ hΛ c b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))+
      (cavityBulkLog n d (N j) (M j) g (v j) Λ hΛ-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j)
    else 0
  apply tendsto_zero_of_uniform_inverse_cap F G (C:=U+V) (by dsimp [U,V]; positivity)
  · intro Λ hΛ j
    have hb:=cavityBulk_uncap_annealed n d (N j) (M j) g (v j) Λ hΛ K KC (hK j) (hC j)
    have hr:=roundedCavity_uncap n d g P hBrow η hB ha0 haK j hΛ
    have he:=cavityBulkFullLog_decomposition n d (N j) (M j) g (v j) Λ hΛ c K KC hc (hK j) (hC j)
    dsimp only at he hb
    have hid : F j-G Λ j=
      (∫ b,cavityBulkUncapError n d (N j) (M j) g (v j) Λ hΛ b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))-
      (roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j) := by
      dsimp [F,G]; rw [dite_eq_left hΛ,he]; ring
    rw [hid]
    have hV : roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j≤V/Λ := by
      exact hr.2.trans_eq (by dsimp [V]; ring)
    have hU : (∫ b,cavityBulkUncapError n d (N j) (M j) g (v j) Λ hΛ b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))≤U/Λ := hb.2.2
    have hU0 : 0≤U/Λ:=by dsimp [U]; positivity
    have hV0 : 0≤V/Λ:=by dsimp [V]; positivity
    rw [add_div]
    exact abs_le.mpr ⟨by linarith [hb.2.1,hr.1],by linarith [hb.2.1,hr.1]⟩
  · intro Λ hΛ
    have hcomp:=cavityBulkCompError_tendsto_zero n d N M g hg v Λ hΛ c KC hc hC hL2
    simpa only [G,dite_eq_left hΛ,zero_add] using hcomp.add (hcap Λ hΛ)

theorem bulk_cavity_uniform_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hBrow : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0≤α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) {K : ℝ} (hK0 : 0≤K)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ→ℕ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
      (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
      (D : BulkCavityData M g v s α K μ hg)
      (KC : ℝ) (_hDc : |D.c|≤KC)
      (_hK : ∀ j,((M (s j)+2:ℕ):ℝ)/(s j+1:ℕ)*‖g.d1‖^2≤K)
      (_hC : ∀ j (b : BulkDisorder (s j+1) (M (s j)+2)) x,
        |bulkC (s j+1) (M (s j)+2) g b.1 x|≤KC)
      (d : ℕ), |(d:ℝ)-(n+1:ℕ)*α|≤1 →
      ∀ δ : ℝ,0<δ → ∀ᶠ j : ℕ in atTop,
      (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ ≤
        cavityBulkFullLog n d (s j) (M (s j)+2) g (v (s j)) := by
  filter_upwards [finiteSphericalFieldValue_depth_uniform (K/2) (by positivity) ε hε] with n hn
  intro M v s μ D KC hDc hK hC d hd δ hδ
  let η:=markedTimePair K μ
  let B:=(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA0 : 0≤α*‖g.d1‖^2:=mul_nonneg hα (sq_nonneg _)
  have hB : B<1:=(div_lt_one (by linarith : 0<1+α*‖g.d1‖^2)).mpr (by linarith)
  let V:=roundedCavityValue n d g P η B D.a_nonneg D.a_le_K
  let U:=fun j=>cavityBulkFullLog n d (s j) (M (s j)+2) g (v (s j))
  have hfull : Tendsto (fun j=>U j-((n+1:ℕ)/2*D.c+V j)) atTop (𝓝 0) :=
    cavityBulkFullLog_rounded_tendsto n d s (fun j=>M (s j)+2) g hg (fun j=>v (s j)) P hBrow
      η hB D.a_nonneg D.a_le_K hDc hK hC D.c_L2 (D.capped n d)
  have hm:=roundedProfileMoment_tendsto η hB
  have he:=cappedAError_tendsto (quantileRoundLaw η) (⟨η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time)
    (quantileRoundLaw_tendsto η) hB
  let R:=fun j=>(n+1:ℕ)*((D.c+D.a)/2+(terminalVariational P α g.f).toReal-roundedProfileMoment η B j-
    cappedAError (quantileRoundLaw η j) η B-ε)-‖g.f‖
  have hR : Tendsto R atTop (𝓝 ((n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖)) := by
    have h:=((((tendsto_const_nhds (x:=(D.c+D.a)/2+(terminalVariational P α g.f).toReal)).sub hm).sub he).sub_const ε).const_mul ((n+1:ℕ):ℝ)
    have h':=h.sub_const ‖g.f‖
    have heq : (n+1:ℕ)*((D.c+D.a)/2+(terminalVariational P α g.f).toReal-
        cavityProfileMoment η B-0-ε)-‖g.f‖ =
        (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖ := by
      rw [show (D.c+D.a)/2=cavityProfileMoment η B from D.radial]
      ring
    rw [heq] at h'
    exact h'
  have ht:=hR.add hfull
  simp only [add_zero] at ht
  have hev:=ht.eventually (Ioi_mem_nhds (show
    (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ <
    (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖ from by linarith))
  filter_upwards [hev] with j hj
  have hlo:=roundedCavityValue_lower P hα g n d η hB D.a_nonneg D.a_le_K D.support D.field_bound hd hn j
  change _<R j+(U j-((n+1:ℕ)/2*D.c+V j)) at hj
  dsimp [R] at hj
  dsimp [V,U] at hj
  linarith

theorem cavity_good_fullLog_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (G : CavityGoodParameters α g.f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ d : ℕ,|(d:ℝ)-(k+1:ℕ)*α|≤1→∀ δ : ℝ,0<δ→
      ∀ᶠ n : ℕ in atTop,∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k d n (patternCount α (n+1)) g v := by
  let M:=cavityOmittedCount α
  let K:=(α+2)*‖g.d1‖^2
  let KC:=(α+2)*‖g.dilationMark hg‖
  have hK0 : 0≤K:=by dsimp [K]; positivity
  have hK : ∀ n,((M n+2:ℕ):ℝ)/(n+1:ℕ)*‖g.d1‖^2≤K := fun n=>
    mul_le_mul_of_nonneg_right (cavity_omitted_bound hα.le n) (sq_nonneg _)
  have hC : ∀ n (b : BulkDisorder (n+1) (M n+2)) x,|bulkC (n+1) (M n+2) g b.1 x|≤KC := by
    intro n b x
    exact (bulkC_bound n (M n+2) g hg b x).trans
      (mul_le_mul_of_nonneg_right (cavity_omitted_bound hα.le n) (norm_nonneg _))
  filter_upwards [bulk_cavity_uniform_lower P hB hα.le g hg hK0 ε hε] with k hk
  intro d hd δ hδ
  apply cavity_eventually_uniform (bulkJointGoodSet α g.f G.J)
    {v : ℕ→ℝ | ∀ p,v p∈Icc (1:ℝ) 2} (fun _=>1) (by intro p; constructor <;> norm_num)
    (fun _ _ h=>h.2) G.nonempty
  intro v hv hvG
  have hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0) :=
    fun p=>(G.deviation v hvG p).2
  have hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0) := by
    intro p
    apply (G.deviation v hvG p).1.congr'
    filter_upwards [cavity_omitted_full hα] with n hn
    rw [show M n+2=patternCount α (n+1) from hn]
  have hv1 : ∀ n p,1≤v n p:=fun n p=>(hv n p).1
  have hv2 : ∀ n p,|v n (p+1)|≤(2:ℝ) := by
    intro n p
    rw [abs_of_nonneg (by linarith [(hv n (p+1)).1])]
    exact (hv n (p+1)).2
  by_contra hnot
  have hbad : ∃ᶠ n : ℕ in atTop,cavityBulkFullLog k d n (patternCount α (n+1)) g (v n)<
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ := by
    simpa only [not_eventually,not_le] using hnot
  obtain ⟨q,hq,hqbad⟩:=extraction_of_frequently_atTop hbad
  obtain ⟨ν,t,ht,ho⟩:=compact_array_law_subsequence (fun j=>bulkGibbsArrayLaw (q j) (M (q j)) g.f (v (q j)))
  let b:=q∘t
  have hb : StrictMono b:=hq.comp ht
  obtain ⟨μ,u,hu,hf⟩:=compact_array_law_subsequence (fun j=>bulkMarkedArrayLaw (b j) (M (b j)+2) g (v (b j)) K (hK (b j)))
  let s:=b∘u
  have hs : StrictMono s:=hb.comp hu
  have ho' : Tendsto (fun j=>bulkGibbsArrayLaw (s j) (M (s j)) g.f (v (s j))) atTop (𝓝 ν):=
    ho.comp hu.tendsto_atTop
  have hf' : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)+2) g (v (s j)) K (hK (s j))) atTop (𝓝 μ):=hf
  obtain ⟨D⟩:=bulk_cavity_data M g hg v hv1 (by norm_num : (0:ℝ)≤2) hv2 hdO hdF s hs α hα.le
    ((cavity_omitted_density hα).comp hs.tendsto_atTop) ν ho' K hK0 hK μ hf'
  have hDc : |D.c|≤KC := D.c_bound.trans (by dsimp [KC]; nlinarith [norm_nonneg (g.dilationMark hg)])
  have hlow:=hk M v s μ D KC hDc (fun j=>hK (s j)) (fun j=>hC (s j)) d hd δ hδ
  obtain ⟨j,hj,hje⟩:=(hlow.and (hs.tendsto_atTop.eventually (cavity_omitted_full hα))).exists
  rw [show M (s j)+2=patternCount α (s j+1) from hje] at hj
  exact (not_lt_of_ge hj) (hqbad (t (u j)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGoodFreshLower
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_good_fresh_fullLog_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (G : CavityGoodParameters α g.f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,
      ∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v := by
  filter_upwards [cavity_good_fullLog_lower P hB hα g hg G ε hε] with k hk
  intro δ hδ
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  have h : ∀ᶠ n : ℕ in atTop,∀ d∈Finset.range (D+1),
      |(d:ℝ)-(k+1:ℕ)*α|≤1→∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k d n (patternCount α (n+1)) g v := by
    apply (eventually_all_finset _).mpr
    intro d _
    by_cases hd : |(d:ℝ)-(k+1:ℕ)*α|≤1
    · exact (hk d hd δ hδ).mono (fun _n hn _=>hn)
    · exact Eventually.of_forall (fun _ h=>False.elim (hd h))
  filter_upwards [h] with n hn
  exact hn _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (cavity_fresh_count hα.le n (k+1)).2.2))
    (cavity_fresh_count hα.le n (k+1)).2.1


lemma cavity_original_increment_background {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) :
    ∃ A : ℝ,∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
      A ≤ cavityOriginalIncrement α g.f n k v := by
  let KC:=α*‖g.dilationMark h1‖
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  refine ⟨Real.log (cavityShellMass k)-KC/2-1-D*‖g.f‖-(k+1:ℕ)*KC/2,?_⟩
  filter_upwards [cavity_original_increment_error hα k g h1 h2 h3 (by norm_num : (0:ℝ)<1)] with n hn
  intro v hv
  have hC : ∀ (a : BulkDisorder (n+1) (patternCount α (n+1))) x,
      |bulkC (n+1) (patternCount α (n+1)) g a.1 x|≤KC := by
    intro a x
    apply (bulkC_bound n _ g h1 a x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2
  have hlow:=cavityBulkFullLog_lower k (cavityFreshCount α n (k+1)) n _ g h1 v hC
  have hd : (cavityFreshCount α n (k+1):ℝ)≤D := by exact_mod_cast (cavity_fresh_count hα n (k+1)).2.2
  have hdn:=mul_le_mul_of_nonneg_right hd (norm_nonneg g.f)
  have hi:=hn v hv
  dsimp only [KC] at *
  linarith

lemma cavity_original_increment_good (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (G : CavityGoodParameters α g.f)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,∀ v∈bulkJointGoodSet α g.f G.J n,
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
        (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
      cavityOriginalIncrement α g.f n k v := by
  filter_upwards [cavity_good_fresh_fullLog_lower P hB hα g h1 G ε hε] with k hk
  intro δ hδ
  filter_upwards [hk (δ/2) (by positivity),cavity_original_increment_error hα.le k g h1 h2 h3
    (show 0<δ/2 by positivity)] with n hn he
  intro v hv
  have hv2 : ∀ p,|v (p+1)|≤(2:ℝ) := by
    intro p
    exact abs_le.mpr ⟨by linarith [(hv.2 (p+1)).1],(hv.2 (p+1)).2⟩
  have hlo:=hn v hv
  have hi:=he v hv2
  linarith


lemma bulkExpectedLog_parameter_measurable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (bulkExpectedLog n M f) := by
  have hm : Measurable (fun p : (ℕ→ℝ)×BulkDisorder (n+1) M=>
      bulkLogPartition n M f p.1 p.2.1 p.2.2) := by
    simp_rw [bulkLogPartition_eq]
    simpa only [tiltPartition,one_mul] using
      (bulkHamiltonian_parameter_continuous (n+1) M f).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma bulkExpectedLog_box_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hv : ∀ p,|v (p+1)|≤2) :
    |bulkExpectedLog n M f v|≤M*‖f‖+2*|bulkScale (n+1)| *
      ∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M := by
  have hb : bulkFeatureBound (n+1) v≤2*|bulkScale (n+1)| := by
    have hh:=bulkFeatureBound_sq_le (n+1) v (by norm_num : (0:ℝ)≤2) hv
    have hs:=sq_abs (bulkScale (n+1))
    nlinarith [Real.sqrt_nonneg (∑ p,bulkAmplitude (n+1) v p^2),abs_nonneg (bulkScale (n+1))]
  let Q:=bulkDisorderLaw (n+1) M
  have hi : Integrable (fun a : BulkDisorder (n+1) M=>
      M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖) Q :=
    (integrable_const _).add ((bulkMarkNorm_integrable (n+1) M).const_mul _)
  calc
    _≤∫ a : BulkDisorder (n+1) M,|bulkLogPartition n M f v a.1 a.2| ∂Q := abs_integral_le_integral_abs
    _≤∫ a : BulkDisorder (n+1) M,M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖ ∂Q := by
      apply integral_mono ((bulkLogPartition_memLp n M f v).integrable (by norm_num)).abs hi
      intro a
      exact (bulkLogPartition_bound n M f v a).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (norm_nonneg a.2)))
    _=_ := by rw [integral_add (integrable_const _) ((bulkMarkNorm_integrable (n+1) M).const_mul _),integral_const_mul]; simp [integral_const_mul]

lemma bulkExpectedLog_parameter_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (bulkExpectedLog n M f) bulkParameterLaw := by
  apply Integrable.of_bound (bulkExpectedLog_parameter_measurable n M f).aestronglyMeasurable
    (M*‖f‖+2*|bulkScale (n+1)| *∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M)
  filter_upwards [bulkParameterLaw_ae] with v hv
  rw [Real.norm_eq_abs]
  exact bulkExpectedLog_box_bound n M f v (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)

lemma cavityAveragedLog_sub (α : ℝ) (f : ℝ→ᵇℝ) (n k : ℕ) :
    cavityAveragedLog α f (n+(k+1))-cavityAveragedLog α f n=
      ∫ v,cavityOriginalIncrement α f n k v ∂bulkParameterLaw :=
  (integral_sub (bulkExpectedLog_parameter_integrable _ _ f)
    (bulkExpectedLog_parameter_integrable _ _ f)).symm

lemma integral_good_bad_lower {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X→ℝ} (hF : Integrable F μ)
    {s : Set X} (hs : MeasurableSet s) {A B : ℝ}
    (hA : ∀ᵐ x ∂μ,A≤F x) (hB : ∀ x∈s,B≤F x) :
    B+(A-B)*μ.real sᶜ≤∫ x,F x ∂μ := by
  have hi : Integrable (fun x=>B+sᶜ.indicator (fun _=>A-B) x) μ :=
    (integrable_const _).add ((integrable_const _).indicator hs.compl)
  have he : (∫ x,B+sᶜ.indicator (fun _=>A-B) x ∂μ)=B+(A-B)*μ.real sᶜ := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hs.compl)]
    simp [integral_indicator_const,hs.compl,smul_eq_mul,mul_comm]
  rw [←he]
  apply integral_mono_ae hi hF
  filter_upwards [hA] with x hx
  by_cases hxs : x∈s
  · simpa [hxs] using hB x hxs
  · simpa [hxs] using hx

lemma cavity_averaged_increment_good_oai (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (G : CavityGoodParameters α g.f)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
        (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
      cavityAveragedLog α g.f (n+(k+1))-cavityAveragedLog α g.f n := by
  filter_upwards [cavity_original_increment_good P hB hα g h1 h2 h3 G hε] with k hk
  intro δ hδ
  obtain ⟨A,hA⟩:=cavity_original_increment_background hα.le k g h1 h2 h3
  let B:=Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
    (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ/2
  have ht : Tendsto (fun n=>(A-B)*bulkParameterLaw.real (bulkJointGoodSet α g.f G.J n)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using G.mass.const_mul (A-B)
  have he:=ht.eventually (Ioi_mem_nhds (show -δ/2<0 by linarith))
  filter_upwards [hk (δ/2) (by positivity),hA,he] with n hn ha he
  have hl:=integral_good_bad_lower bulkParameterLaw
    ((bulkExpectedLog_parameter_integrable _ _ g.f).sub (bulkExpectedLog_parameter_integrable _ _ g.f))
    (G.measurable n) (A:=A) (B:=B) (F:=cavityOriginalIncrement α g.f n k)
    (by
      filter_upwards [bulkParameterLaw_ae] with v hv
      exact ha v (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)) hn
  rw [←cavityAveragedLog_sub] at hl
  dsimp only [B] at hl he
  linarith


end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good_oai := @OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good_oai
