-- Prove2me | solution 1 for OAI.LogConcaveSampling.eventually_subpolynomial_sampler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:41:05.523586+00:00
-- url     : https://prove2.me/submissions/1c109ab0-4228-4d0f-b00e-28d1f1855cdb

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_exists_source_numerical_ready
import Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_uniform_routine_accuracy

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ContinuousFirstOrderReply
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

theorem Admissible.continuous_firstOrderReply {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Continuous (firstOrderReply V) := by
  have hg : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.smooth.continuous_fderiv (by norm_num))
  exact hV.smooth.continuous.prodMk hg

theorem OracleAlgorithm.measurable_history {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) (n : ℕ) :
    Measurable (fun ω => A.history V ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      by_cases hn : n < q
      · have hr : Measurable (fun ω =>
            firstOrderReply V (A.query ⟨n, hn⟩ (ω, A.history V ω n))) :=
          hV.continuous_firstOrderReply.measurable.comp
            ((A.query_measurable ⟨n, hn⟩).comp (measurable_id.prodMk ih))
        apply Measurable.of_eval
        intro i
        by_cases hi : i = ⟨n, hn⟩
        · simpa [history, hn, Function.update_apply, hi] using hr
        · simpa [history, hn, Function.update_apply, hi, Function.comp_def] using
            (measurable_pi_apply i).comp ih
      · simpa [history, hn] using ih

theorem OracleAlgorithm.measurable_run {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) :
    Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history hV q))

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.contDiff_gradient {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : ContDiff ℝ 1 (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hV.smooth.fderiv_right (by norm_num))

theorem Admissible.quadratic_bounds {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) :
    ‖x‖ ^ 2 / 2 ≤ V x ∧ V x ≤ ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hV.smooth.differentiable (by norm_num) (t • x)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    change inner ℝ x (gradient V (t • x)) = fderiv ℝ V (t • x) x
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using
      (hasDerivAt_const t x).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg
    (fun t => hV.hessian_bounds (t • x) x)
  dsimp only [f, g] at ht
  rw [zero_smul, one_smul, hV.value_zero, hV.gradient_zero, inner_zero_right, zero_add] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem Admissible.integrable_exp_neg {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Integrable (fun x => Real.exp (-V x)) := by
  apply (integrable_gaussian_envelope d (b := 1 / 2) (by norm_num)).mono'
    ((Real.continuous_exp.comp hV.smooth.continuous.neg).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (hV.quadratic_bounds x).1
    linarith

theorem Admissible.partition_ne_top {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : partition V ≠ ⊤ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    hV.integrable_exp_neg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-V x)).le)).2
      hV.integrable_exp_neg

theorem Admissible.partition_pos {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : 0 < partition V := by
  have hm : Measurable (gibbsDensity V) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hV.smooth.continuous.neg)).measurable
  rw [partition, lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity V) = Set.univ := by
    ext x
    simp [Function.mem_support, gibbsDensity, not_le_of_gt (Real.exp_pos (-V x))]
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem Admissible.isProbabilityMeasure_gibbs {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : IsProbabilityMeasure (gibbs V) := by
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hV.partition_pos.ne' hV.partition_ne_top

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_SymmetricGradientDerivative
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.gradient_lipschitz {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : LipschitzWith 2 (gradient V) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hV.contDiff_gradient.differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (gradient V) x‖ ≤ (2 : ℝ)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient
    (fderiv ℝ (gradient V) x) (ContDiff.isSymmetric_gradient_derivative hV.smooth x)]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]
  simp only [RCLike.re_to_real]
  rw [abs_of_nonneg (div_nonneg ((sq_nonneg ‖v‖).trans (hV.hessian_bounds x v).1)
    (sq_nonneg ‖v‖)), div_le_iff₀ hn]
  exact (hV.hessian_bounds x v).2

theorem Admissible.gradient_norm_le {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) : ‖gradient V x‖ ≤ 2 * ‖x‖ := by
  simpa [dist_eq_norm, hV.gradient_zero] using hV.gradient_lipschitz.dist_le_mul x 0

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PrimitivePotentialModeBounds
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma integrable_sq_norm_gaussian (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^2 * Real.exp (-b * ‖x‖^2)) := by
  apply ((integrable_gaussian_envelope d (b := b/2) (by positivity)).const_mul (2/b)).mono'
    ((continuous_norm.pow 2).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  filter_upwards [] with x
  change |‖x‖^2 * Real.exp (-b * ‖x‖^2)| ≤ _
  rw [abs_of_nonneg (by positivity)]
  exact polynomial_gaussian_absorb hb (sq_nonneg _)

theorem radial_integration_by_parts {d : ℕ} {H : Point d → ℝ} {m K : ℝ}
    (hH : ContDiff ℝ 1 H) (hm : 0 < m) (hK : 0 ≤ K)
    (htail : ∀ x, m * ‖x‖^2 / 2 ≤ H x)
    (hgrad : ∀ x, ‖gradient H x‖ ≤ K * ‖x‖) :
    Integrable (fun x => inner ℝ (gradient H x) x * Real.exp (-H x)) ∧
      (∫ x, inner ℝ (gradient H x) x * Real.exp (-H x)) =
        (d : ℝ) * ∫ x, Real.exp (-H x) := by
  let F : ℝ → Point d → ℝ := fun a x => Real.exp (-H (a • x))
  let F' : ℝ → Point d → ℝ := fun a x =>
    -(inner ℝ (gradient H (a • x)) x) * Real.exp (-H (a • x))
  have hgc : Continuous (gradient H) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hH.continuous_fderiv (by norm_num))
  have hdiff : ∀ (x : Point d) (a : ℝ), HasDerivAt (fun a => F a x) (F' a x) a := by
    intro x a
    have hh := ((hH.differentiable (by norm_num) (a • x)).hasFDerivAt).comp_hasDerivAt a
      ((hasDerivAt_id a).smul_const x)
    have hh' : HasDerivAt (fun a => H (a • x)) (inner ℝ (gradient H (a • x)) x) a := by
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      change inner ℝ (gradient H (a • x)) x = fderiv ℝ H (a • x) ((1 : ℝ) • x)
      rw [one_smul,inner_gradient_left]
    convert! hh'.neg.exp using 1; simp only [F',mul_comm,Pi.neg_apply]
  have hbase : Integrable (F 1) := by
    simp only [F,one_smul]
    apply (integrable_gaussian_envelope d (b := m/2) (by positivity)).mono'
      ((Real.continuous_exp.comp hH.continuous.neg).aestronglyMeasurable)
    filter_upwards [] with x
    change |Real.exp (-H x)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    linarith [htail x]
  have hbnd : ∀ (x : Point d) (a : ℝ), a ∈ Set.Ioo (1/2 : ℝ) 2 →
      ‖F' a x‖ ≤ (2*K) * (‖x‖^2 * Real.exp (-(m/8) * ‖x‖^2)) := by
    intro x a ha
    have hap : 0 ≤ a := by linarith [ha.1]
    have hga : ‖gradient H (a • x)‖ ≤ 2*K*‖x‖ := by
      calc
        _ ≤ K * ‖a • x‖ := hgrad _
        _ = K * (a*‖x‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hap]
        _ ≤ 2*K*‖x‖ := by
          calc
            _ ≤ K * (2*‖x‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.2.le (norm_nonneg x)) hK
            _ = _ := by ring
    have hinner : |inner ℝ (gradient H (a • x)) x| ≤ 2*K*‖x‖^2 := by
      calc
        _ ≤ ‖gradient H (a • x)‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ (2*K*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right hga (norm_nonneg x)
        _ = _ := by ring
    have htail' : (m/8)*‖x‖^2 ≤ H (a • x) := by
      have ht := htail (a • x)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hap,mul_pow] at ht
      have ha2 : (1/4 : ℝ) ≤ a^2 := by nlinarith [ha.1]
      have hh := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ m*‖x‖^2 by positivity)
      nlinarith
    dsimp [F']
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (2*K*‖x‖^2) * Real.exp (-H (a • x)) := mul_le_mul_of_nonneg_right hinner (by positivity)
      _ ≤ (2*K*‖x‖^2) * Real.exp (-(m/8)*‖x‖^2) := by
        gcongr
        linarith
      _ = _ := by ring
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Point d))) (F := F) (F' := F')
    (bound := fun x => (2*K) * (‖x‖^2 * Real.exp (-(m/8)*‖x‖^2)))
    (x₀ := (1 : ℝ)) (s := Set.Ioo (1/2 : ℝ) 2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun a =>
      ((Real.continuous_exp.comp (hH.continuous.comp (continuous_id.const_smul a)).neg)).aestronglyMeasurable)
    hbase
    (by
      have hh : Continuous (fun x => -(inner ℝ (gradient H x) x) * Real.exp (-H x)) :=
        (hgc.inner continuous_id).neg.mul (Real.continuous_exp.comp hH.continuous.neg)
      convert! hh.aestronglyMeasurable using 1
      all_goals try with_reducible_and_instances rfl
      simp only [F',one_smul])
    (Filter.Eventually.of_forall hbnd)
    ((integrable_sq_norm_gaussian d (b := m/8) (by positivity)).const_mul (2*K))
    (Filter.Eventually.of_forall fun x a _ => hdiff x a)
  have hidentity : (fun a : ℝ => ∫ x, F a x) =ᶠ[𝓝 1]
      (fun a => (a^d)⁻¹ * ∫ x, Real.exp (-H x)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    simpa [F,finrank_euclideanSpace_fin] using
      (Measure.integral_comp_smul_of_nonneg (volume : Measure (Point d))
        (fun x => Real.exp (-H x)) a (hR := ha.le))
  have halgebra : HasDerivAt (fun a : ℝ => (a^d)⁻¹ * ∫ x, Real.exp (-H x))
      (-(d : ℝ) * ∫ x, Real.exp (-H x)) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).pow d).inv (by simp)).mul_const (∫ x, Real.exp (-H x)) using 1; simp
  have heq := hparam.2.unique (halgebra.congr_of_eventuallyEq hidentity)
  have hi : Integrable (fun x => inner ℝ (gradient H x) x * Real.exp (-H x)) := by
    simpa [F',neg_mul] using hparam.1.neg
  refine ⟨hi, ?_⟩
  have heq' : -(∫ x, inner ℝ (gradient H x) x * Real.exp (-H x)) =
      -((d : ℝ) * ∫ x, Real.exp (-H x)) := by
    simpa only [F',one_smul,neg_mul,integral_neg] using heq
  exact neg_inj.mp heq'

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.radial_gradient_lower {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) : ‖x‖^2 ≤ inner ℝ (gradient V x) x := by
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    simpa [g,h,Function.comp_def] using (hasDerivAt_const t x).inner ℝ hh
  have hderiv : ∀ t, HasDerivAt (fun t => g t - ‖x‖^2*t) (h t-‖x‖^2) t := by
    intro t
    convert! (hg t).sub ((hasDerivAt_id t).const_mul (‖x‖^2)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hmono : Monotone (fun t => g t-‖x‖^2*t) :=
    monotone_of_hasDerivAt_nonneg hderiv (fun t => sub_nonneg.mpr (hV.hessian_bounds (t • x) x).1)
  have hh := hmono (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [g,zero_smul,one_smul,hV.gradient_zero,inner_zero_right,mul_zero,sub_zero,mul_one] at hh
  rw [real_inner_comm] at hh
  linarith only [hh]

theorem Admissible.second_moment_bound {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) :
    Integrable (fun x => ‖x‖^2) (gibbs V) ∧ (∫ x, ‖x‖^2 ∂gibbs V) ≤ d := by
  have hi := radial_integration_by_parts (hV.smooth.of_le (by norm_num))
    (m := 1) (K := 2) (by norm_num) (by norm_num)
    (fun x => by simpa using (hV.quadratic_bounds x).1) hV.gradient_norm_le
  have hisq : Integrable (fun x => Real.exp (-V x) * ‖x‖^2) := by
    apply (integrable_sq_norm_gaussian d (b := 1/2) (by norm_num)).mono'
      ((Real.continuous_exp.comp hV.smooth.continuous.neg).mul (continuous_norm.pow 2)).aestronglyMeasurable
    filter_upwards [] with x
    change |Real.exp (-V x) * ‖x‖^2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ Real.exp (-(1/2)*‖x‖^2) * ‖x‖^2 := by
        gcongr
        linarith [(hV.quadratic_bounds x).1]
      _ = _ := by ring
  have hnum : (∫ x, Real.exp (-V x) * ‖x‖^2) ≤ (d : ℝ) * ∫ x, Real.exp (-V x) := by
    rw [← hi.2]
    apply integral_mono hisq hi.1
    intro x
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (hV.radial_gradient_lower x) (Real.exp_pos (-V x)).le
  have hZ : 0 < ∫ x, Real.exp (-V x) := by
    rw [← partition_toReal hV.integrable_exp_neg]
    exact ENNReal.toReal_pos hV.partition_pos.ne' hV.partition_ne_top
  refine ⟨integrable_gibbs_of_weighted hV.smooth.continuous hV.integrable_exp_neg hisq, ?_⟩
  rw [integral_gibbs hV.smooth.continuous hV.integrable_exp_neg]
  exact (div_le_iff₀ hZ).mpr hnum

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling.OracleCompiler

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

lemma algorithm_history (A : Program Ω d q (Point d)) (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    A.algorithm.history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OracleAlgorithm.history, history, ih]
    rfl

lemma algorithm_run (A : Program Ω d q (Point d)) (V : Point d → ℝ) (ω : Ω) :
    A.algorithm.run V ω = A.run V ω := by
  unfold OracleAlgorithm.run run
  rw [algorithm_history]
  rfl

lemma history_tail (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (n : ℕ) (i : Fin q) (hi : n ≤ i.val) : A.history V ω n i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih (by omega)
    · exact ih (by omega)

lemma history_stable (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin q) (hi : i.val < m) :
    A.history V ω n i = A.history V ω m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih
    · exact ih

lemma prefix_zero (h : Transcript d q) : mask 0 h = 0 := by
  funext i
  simp [mask]

lemma prefix_full (h : Transcript d q) : mask q h = h := by
  funext i
  simp [mask, i.isLt]

lemma prefix_succ (n : ℕ) (hn : n < q) (h : Transcript d q) :
    mask (n+1) h = Function.update (mask n h) ⟨n,hn⟩ (h ⟨n,hn⟩) := by
  funext i
  by_cases hi : i = ⟨n,hn⟩
  · subst i
    simp [mask]
  · rw [Function.update_of_ne hi]
    simp only [mask]
    have hne : i.val ≠ n := by intro he; exact hi (Fin.ext he)
    have he : (i.val < n+1) ↔ (i.val < n) := by omega
    simp only [he]

lemma history_eq_prefix (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {n : ℕ} (hn : n ≤ q) : A.history V ω n = mask n (A.history V ω q) := by
  funext i
  simp only [mask]
  split_ifs with hi
  · exact (A.history_stable V ω hn i hi).symm
  · exact A.history_tail V ω n i (by omega)

lemma history_spec (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) (i : Fin q) :
    A.history V ω q i =
      firstOrderReply V (A.query i (ω, mask i.val (A.history V ω q))) := by
  rw [A.history_stable V ω (m := i.val+1) (by omega) i (by omega)]
  rw [history, dite_eq_left i.isLt]
  simp only [Function.update_self]
  rw [A.history_eq_prefix V ω (by omega)]

lemma history_unique (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (h : Transcript d q)
    (hh : ∀ i, h i = firstOrderReply V (A.query i (ω, mask i.val h))) :
    A.history V ω q = h := by
  have hp : ∀ n ≤ q, A.history V ω n = mask n h := by
    intro n hn
    induction n with
    | zero => simp [history, prefix_zero]
    | succ n ih =>
      have hnq : n < q := by omega
      rw [history, dite_eq_left hnq, ih (by omega), prefix_succ n hnq h, hh ⟨n,hnq⟩]
  simpa only [prefix_full] using hp q le_rfl

lemma measurable_history (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) (n : ℕ) :
    Measurable (A.history V · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · apply Measurable.of_eval
      intro i
      by_cases hi : i = ⟨n,hn⟩
      · subst i
        simp only [Function.update_self]
        exact hV.comp ((A.query_measurable _).comp (measurable_id.prodMk ih))
      · simp only [Function.update_of_ne hi]
        exact (measurable_pi_apply i).comp ih
    · exact ih

lemma measurable_run (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) : Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history V hV q))

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

lemma leftTrace_prefix_left (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask n (Fin.append h k)) = mask n h := by
  funext i
  simp [leftTrace, mask]

lemma leftTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask (q+n) (Fin.append h k)) = h := by
  funext i
  have hi : i.val < q+n := by omega
  simp [leftTrace, mask, hi]

lemma rightTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    rightTrace (mask (q+n) (Fin.append h k)) = mask n k := by
  funext i
  simp [rightTrace, mask]

lemma seq_history (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).history V ω (q+r) =
      Fin.append (A.history V ω q) (B.history V (ω,A.run V ω) r) := by
  apply history_unique
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, seq, Fin.addCases_left, Fin.val_castAdd,
      leftTrace_prefix_left]
    exact A.history_spec V ω j
  · simp only [Fin.append_right, seq, Fin.addCases_right, Fin.val_natAdd,
      leftTrace_prefix_right, rightTrace_prefix_right]
    exact B.history_spec V (ω,A.run V ω) j

lemma seq_run (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).run V ω = B.run V (ω,A.run V ω) := by
  unfold run
  rw [seq_history]
  simp only [seq, leftTrace_append, rightTrace_append]
  rfl

lemma map_history (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    (A.map f hf).history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma map_run (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) : (A.map f hf).run V ω = f (ω,A.run V ω) := by
  unfold run
  rw [map_history]
  rfl

lemma seedMap_history {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) (n : ℕ) :
    (A.seedMap f hf).history V ω n = A.history V (f ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma seedMap_run {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) :
    (A.seedMap f hf).run V ω = A.run V (f ω) := by
  unfold run
  rw [seedMap_history]
  rfl

end LogConcaveSampling.OracleCompiler.Program

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma slot_energy (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) (g : ι → E) :
    (∑ i, ‖slotTransform c a g i‖ ^ 2) + ‖slotSum a g‖ ^ 2 =
      ∑ i, ‖g i‖ ^ 2 := by
  let S := slotSum a g
  have hi : ∑ i, a i * inner ℝ (g i) S = ‖S‖ ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq S
  have hsum : (∑ i, ‖slotTransform c a g i‖ ^ 2) =
      (∑ i, ‖g i‖ ^ 2) - (2 * c) * (∑ i, a i * inner ℝ (g i) S) +
        c ^ 2 * (∑ i, a i ^ 2) * ‖S‖ ^ 2 := by
    simp only [slotTransform, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right]
    dsimp only [S]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsum, hi]
  change _ + ‖S‖ ^ 2 = _
  nlinarith [mul_eq_zero_of_left hc (‖S‖ ^ 2)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in
lemma sqrtCoefficient_equation (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (sqrtCoefficient a) ^ 2 * (∑ i, a i ^ 2) - 2 * sqrtCoefficient a + 1 = 0 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hpos : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E O : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma normalized_shift_bound {D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) :
    (∑ i, (v i / (2 * D)) ^ 2) ≤ 1 / 4 := by
  simp only [div_pow, ← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))).mpr
  nlinarith

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slotSum_transform (c : ℝ) (a : ι → ℝ) (g : ι → E) :
    slotSum a (slotTransform c a g) = (1 - c * ∑ i, a i ^ 2) • slotSum a g := by
  simp only [slotSum, slotTransform, smul_sub, smul_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sub_smul, one_smul]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma slotTransform_comp (c t : ℝ) (a : ι → ℝ) (g : ι → E) :
    slotTransform t a (slotTransform c a g) =
      slotTransform (c + t - t * c * ∑ i, a i ^ 2) a g := by
  funext i
  simp only [slotTransform, slotSum_transform, smul_smul]
  rw [sub_sub, ← add_smul]
  congr 2
  ring

lemma slotSum_energy_bound (a : ι → ℝ) (g : ι → E) :
    ‖slotSum a g‖ ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, ‖g i‖ ^ 2) := by
  calc
    ‖slotSum a g‖ ^ 2 ≤ (∑ i, |a i| * ‖g i‖) ^ 2 := by
      apply sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => by positivity) |>.mpr
      simpa [slotSum, norm_smul] using norm_sum_le Finset.univ (fun i => a i • g i)
    _ ≤ (∑ i, |a i| ^ 2) * (∑ i, ‖g i‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i|) (fun i => ‖g i‖)
    _ = _ := by simp only [sq_abs]

lemma sqrtCoefficient_eigenvalue (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    1 - sqrtCoefficient a * ∑ i, a i ^ 2 = Real.sqrt (1 - ∑ i, a i ^ 2) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hp : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

lemma inverseCoefficient_cancel (a : ι → ℝ) (ha : (∑ i, a i ^ 2) < 1) :
    sqrtCoefficient a + inverseCoefficient a -
      inverseCoefficient a * sqrtCoefficient a * ∑ i, a i ^ 2 = 0 := by
  have he := sqrtCoefficient_eigenvalue a ha.le
  have hp : 0 < Real.sqrt (1 - ∑ i, a i ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr ha)
  unfold inverseCoefficient
  field_simp
  rw [← he]
  ring

lemma slotTransform_inverse (a : ι → ℝ) (ha : (∑ i, a i ^ 2) < 1) (g : ι → E) :
    slotTransform (sqrtCoefficient a) a (slotTransform (inverseCoefficient a) a g) = g := by
  rw [slotTransform_comp]
  have he := inverseCoefficient_cancel a ha
  have : inverseCoefficient a + sqrtCoefficient a -
      sqrtCoefficient a * inverseCoefficient a * ∑ i, a i ^ 2 = 0 := by nlinarith
  rw [this]
  funext i
  simp [slotTransform]

lemma inverse_slot_energy (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1 / 4) (g : ι → E) :
    (∑ i, ‖slotTransform (inverseCoefficient a) a g i‖ ^ 2) ≤
      4 * ∑ i, ‖g i‖ ^ 2 := by
  let h := slotTransform (inverseCoefficient a) a g
  have hA : (∑ i, a i ^ 2) < 1 := ha.trans_lt (by norm_num)
  have he := slot_energy (sqrtCoefficient a) a (sqrtCoefficient_equation a hA.le) h
  rw [slotTransform_inverse a hA g] at he
  have hb := slotSum_energy_bound a h
  have hs : 0 ≤ ∑ i, ‖h i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (∑ i, a i ^ 2) * (∑ i, ‖h i‖ ^ 2) ≤ (1 / 4) * (∑ i, ‖h i‖ ^ 2) :=
    mul_le_mul_of_nonneg_right ha hs
  change (∑ i, ‖h i‖ ^ 2) ≤ _
  nlinarith

end LogConcaveSampling.SeedCompiler

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling

theorem TVAtMost.map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ ν : Measure E} {ε : ℝ} (h : TVAtMost μ ν ε)
    {f : E → F} (hf : Measurable f) : TVAtMost (μ.map f) (ν.map f) ε := by
  intro s hs
  simpa only [Measure.real, Measure.map_apply hf hs] using h (f ⁻¹' s) (hs.preimage hf)

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_AffinePotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped Classical NNReal RealInnerProductSpace

variable {d : ℕ}

lemma gradient_affinePotential {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
    (a : Point d) (s : ℝ) (z : Point d) :
    gradient (affinePotential V a s) z=s • gradient V (a+s • z) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha : HasFDerivAt (fun w : Point d => a+s • w)
      (0+s • ContinuousLinearMap.id ℝ (Point d)) z :=
    (hasFDerivAt_const a z).add ((hasFDerivAt_id z).const_smul s)
  have hb := (hV.differentiable (by norm_num) (a+s • z)).hasFDerivAt.comp z ha
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,zero_add,ContinuousLinearMap.map_smul,smul_eq_mul]
  change inner ℝ (s • gradient V (a+s • z)) v=s*(fderiv ℝ V (a+s • z)) v
  rw [real_inner_smul_left,←toDual_gradient]
  rfl

lemma Admissible.affinePrimitive {V : Point d → ℝ} (hV : Admissible V)
    (a : Point d) (s : ℝ) : Primitive (affinePotential V a s) ⟨2*s^2,by positivity⟩ := by
  constructor
  · exact hV.smooth.comp (contDiff_const.add (contDiff_id.const_smul s))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [gradient_affinePotential hV.smooth,gradient_affinePotential hV.smooth,dist_smul₀]
    have hh := hV.gradient_lipschitz.dist_le_mul (a+s • x) (a+s • y)
    rw [dist_add_left,dist_smul₀] at hh
    have hb := mul_le_mul_of_nonneg_left hh (norm_nonneg s)
    change ‖s‖ * dist (gradient V (a+s • x)) (gradient V (a+s • y)) ≤ (2*s^2)*dist x y
    calc
      _ ≤ ‖s‖*(2*(‖s‖*dist x y)) := hb
      _ = _ := by rw [Real.norm_eq_abs]; calc
        _ = 2*|s|^2*dist x y := by ring
        _ = _ := by rw [sq_abs]

namespace OracleCompiler.Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {q : ℕ}

lemma affineReplies_update (s : ℝ) (H : Transcript d q) (i : Fin q) (u : Reply d) :
    affineReplies s (Function.update H i u)=
      Function.update (affineReplies s H) i (u.1,s • u.2) := by
  funext j
  by_cases hj : j=i
  · subst j; simp [affineReplies]
  · simp [affineReplies,Function.update_of_ne hj]

lemma affineOracle_history (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a)
    (s : ℝ) {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) (ω : Ω) (n : ℕ) :
    affineReplies s ((A.affineOracle a ha s).history V ω n)=
      A.history (affinePotential V (a ω) s) ω n := by
  induction n with
  | zero => exact affineReplies_zero s
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [affineReplies_update,ih]
      congr 1
      change (V (a ω+s • A.query ⟨n,hn⟩ (ω,affineReplies s ((A.affineOracle a ha s).history V ω n))),
        s • gradient V (a ω+s • A.query ⟨n,hn⟩ (ω,affineReplies s ((A.affineOracle a ha s).history V ω n))))=_
      rw [ih]
      simp only [firstOrderReply,affinePotential,gradient_affinePotential hV]
    · exact ih

lemma affineOracle_run (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a)
    (s : ℝ) {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) (ω : Ω) :
    (A.affineOracle a ha s).run V ω=A.run (affinePotential V (a ω) s) ω := by
  unfold run
  change A.output (ω,affineReplies s ((A.affineOracle a ha s).history V ω q))=_
  rw [affineOracle_history A a ha s hV]

end OracleCompiler.Program
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ}

lemma gaussian_inner_law (a : Point d) :
    (stdGaussian (Point d)).map (fun z => inner ℝ a z)=
      gaussianReal 0 (‖a‖₊^2) := by
  simp only [←innerSL_apply_apply ℝ]
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Point d)) (innerSL ℝ a)
  simpa only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,Real.toNNReal_pow (norm_nonneg a),norm_toNNReal] using h

lemma gaussian_exp_inner_integrable (a : Point d) (t : ℝ) :
    Integrable (fun z => Real.exp (t*inner ℝ a z)) (stdGaussian (Point d)) := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := ‖a‖₊^2) t
  rw [←gaussian_inner_law a] at h
  exact h.comp_measurable (by fun_prop)

lemma gaussian_exp_inner_integral (a : Point d) (t : ℝ) :
    (∫z,Real.exp (t*inner ℝ a z) ∂stdGaussian (Point d))=
      Real.exp (‖a‖^2*t^2/2) := by
  have hlaw : HasLaw (fun z => inner ℝ a z) (gaussianReal 0 (‖a‖₊^2))
      (stdGaussian (Point d)) := ⟨by fun_prop,gaussian_inner_law a⟩
  simpa only [mgf,zero_mul,zero_add,NNReal.coe_pow,coe_nnnorm] using
    mgf_gaussianReal hlaw.map_eq t

lemma gaussianShiftRatio_integrable (a : Point d) :
    Integrable (gaussianShiftRatio a) (stdGaussian (Point d)) := by
  change Integrable (fun z => Real.exp (inner ℝ a z-‖a‖^2/2)) _
  have h := (gaussian_exp_inner_integrable a 1).mul_const (Real.exp (-‖a‖^2/2))
  simpa only [one_mul,←Real.exp_add,sub_eq_add_neg,neg_div] using h

lemma gaussianShiftRatio_integral (a : Point d) :
    (∫z,gaussianShiftRatio a z ∂stdGaussian (Point d))=1 := by
  simp only [gaussianShiftRatio,sub_eq_add_neg,Real.exp_add]
  rw [integral_mul_const]
  have h := gaussian_exp_inner_integral a 1
  simp only [one_mul,one_pow,mul_one] at h
  rw [h,←Real.exp_add]
  simp

lemma gaussianShiftRatio_density (a : Point d) :
    (stdGaussian (Point d)).map (fun z => a+z)=
      (stdGaussian (Point d)).withDensity (fun z => ENNReal.ofReal (gaussianShiftRatio a z)) := by
  let e := (Homeomorph.addLeft a).toMeasurableEquiv
  have hpres : MeasurePreserving e (volume : Measure (Point d)) volume :=
    measurePreserving_add_left volume a
  rw [EulerDensity.standard_density,Measure.map_smul,withDensity_smul_measure]
  change _ • Measure.map e _ = _
  rw [map_withDensity_of_measurePreserving e hpres (by fun_prop)]
  rw [←withDensity_mul _ (by fun_prop) (by unfold gaussianShiftRatio; fun_prop)]
  congr 2
  funext z
  change ENNReal.ofReal (Real.exp (-‖(-a)+z‖^2/2)) = _
  simp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,gaussianShiftRatio,←Real.exp_add]
  congr 2
  rw [show -a+z=z-a by abel,norm_sub_sq_real,real_inner_comm z a]
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma TVAtMost_of_density {f : E → ℝ} (hf : Integrable f μ) (hpos : ∀x,0≤f x) :
    TVAtMost (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ (∫x,|f x-1| ∂μ) := by
  intro s hs
  have hmeasure : (μ.withDensity (fun x => ENNReal.ofReal (f x))).real s=∫x in s,f x ∂μ := by
    rw [measureReal_def,withDensity_apply _ hs]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
      hf.aestronglyMeasurable.restrict).symm
  rw [hmeasure,←show (∫x in s,(1:ℝ) ∂μ)=μ.real s by simp,←integral_sub hf.restrict (integrable_const _)]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (hf.sub (integrable_const _)).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

lemma density_root_L1_sq {h : E → ℝ} (hh : MemLp h 2 μ)
    (hpos : ∀x,0≤h x) (hunit : (∫x,(h x)^2 ∂μ)=1) :
    (∫x,|(h x)^2-1| ∂μ)^2 ≤ 4*(1-(∫x,h x ∂μ)^2) := by
  have hi := hh.integrable (by norm_num : (1:ENNReal)≤2)
  have hsq := (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mp hh
  have hc := integral_mul_sq_le (hh.sub (memLp_const (1:ℝ))).norm
    (hh.add (memLp_const (1:ℝ)))
  have hmul : (fun x => |h x-1| *(h x+1))=(fun x => |(h x)^2-1|) := by
    funext x
    rw [←abs_of_nonneg (add_nonneg (hpos x) zero_le_one),←abs_mul]
    congr 1
    ring
  have hmi : Integrable (fun x => (h x)^2-2*h x) μ := hsq.sub (hi.const_mul 2)
  have hpi : Integrable (fun x => (h x)^2+2*h x) μ := hsq.add (hi.const_mul 2)
  have hminus : (∫x,(h x-1)^2 ∂μ)=2-2*(∫x,h x ∂μ) := by
    simp_rw [show ∀x,(h x-1)^2=(h x)^2-2*h x+1 by intro x; ring]
    rw [integral_add hmi (integrable_const _),
      integral_sub hsq (hi.const_mul 2),integral_const_mul,hunit]
    simp
    ring
  have hplus : (∫x,(h x+1)^2 ∂μ)=2+2*(∫x,h x ∂μ) := by
    simp_rw [show ∀x,(h x+1)^2=(h x)^2+2*h x+1 by intro x; ring]
    rw [integral_add hpi (integrable_const _),
      integral_add hsq (hi.const_mul 2),integral_const_mul,hunit]
    simp
    ring
  simp only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,sq_abs] at hc
  rw [hmul,hminus,hplus] at hc
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ}

lemma gaussian_shift_L1 (a : Point d) :
    (∫z,|gaussianShiftRatio a z-1| ∂stdGaussian (Point d))≤‖a‖ := by
  let h : Point d → ℝ := fun z => Real.exp ((inner ℝ a z-‖a‖^2/2)/2)
  have hs (z : Point d) : (h z)^2=gaussianShiftRatio a z := by
    dsimp [h,gaussianShiftRatio]
    rw [sq,←Real.exp_add]
    congr 1
    ring
  have hM : MemLp h 2 (stdGaussian (Point d)) := by
    apply (memLp_two_iff_integrable_sq (by dsimp [h]; fun_prop)).mpr
    simpa only [hs] using gaussianShiftRatio_integrable a
  have hi : (∫z,h z ∂stdGaussian (Point d))=Real.exp (-‖a‖^2/8) := by
    have he : h=fun z => Real.exp ((1/2)*inner ℝ a z)*Real.exp (-‖a‖^2/4) := by
      funext z
      dsimp [h]
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he,integral_mul_const,gaussian_exp_inner_integral,←Real.exp_add]
    congr 1
    ring
  have hb := density_root_L1_sq hM (fun z => (Real.exp_pos _).le)
    (by simpa only [hs] using gaussianShiftRatio_integral a)
  simp only [hs,hi] at hb
  have he : (Real.exp (-‖a‖^2/8))^2=Real.exp (-‖a‖^2/4) := by
    rw [sq,←Real.exp_add]
    congr 1
    ring
  rw [he] at hb
  have ht := Real.add_one_le_exp (-‖a‖^2/4)
  have hn : 0≤(∫z,|gaussianShiftRatio a z-1| ∂stdGaussian (Point d)) :=
    integral_nonneg (fun z => abs_nonneg (gaussianShiftRatio a z-1))
  nlinarith [norm_nonneg a]

theorem TVAtMost_gaussian_shift (a : Point d) :
    TVAtMost ((stdGaussian (Point d)).map (fun z => a+z))
      (stdGaussian (Point d)) ‖a‖ := by
  rw [gaussianShiftRatio_density]
  intro s hs
  exact (TVAtMost_of_density (gaussianShiftRatio_integrable a)
    (fun z => (Real.exp_pos _).le) s hs).trans (gaussian_shift_L1 a)

lemma TVAtMost.mono {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    {a b : ℝ} (h : TVAtMost μ ν a) (hab : a≤b) : TVAtMost μ ν b :=
  fun s hs => (h s hs).trans hab

lemma TVAtMost.trans {E : Type*} [MeasurableSpace E] {μ ν θ : Measure E}
    {a b : ℝ} (h : TVAtMost μ ν a) (h' : TVAtMost ν θ b) : TVAtMost μ θ (a+b) := by
  intro s hs
  exact (abs_sub_le (μ.real s) (ν.real s) (θ.real s)).trans (add_le_add (h s hs) (h' s hs))

theorem TVAtMost_gaussian_affine (x y : Point d) {s : ℝ} (hs : 0 < s) :
    TVAtMost ((stdGaussian (Point d)).map (fun z => x+s • z))
      ((stdGaussian (Point d)).map (fun z => y+s • z)) (‖x-y‖/s) := by
  have h := (TVAtMost_gaussian_shift (s⁻¹ • (x-y))).map
    (show Measurable (fun z : Point d => y+s • z) by fun_prop)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have he : (fun z : Point d => y+s • (s⁻¹ • (x-y)+z))=(fun z => x+s • z) := by
    funext z
    rw [smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    abel
  simpa only [Function.comp_def,he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,div_eq_inv_mul] using h
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_UnitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

lemma pi_snoc_law {X : Type*} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => ν)).prod ν).map (fun p => Fin.snoc (α := fun _ : Fin (n+1) => X) p.1 p.2) =
      Measure.pi (fun _ : Fin (n+1) => ν) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm.map_eq
  have hs := Measure.prod_swap (μ := Measure.pi (fun _ : Fin n => ν)) (ν := ν)
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  exact (Fin.insertNth_last' p.2 p.1).symm

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolyC1
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integrable_polynomial_gibbs {d : ℕ} {H f : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : Continuous f)
    (hg : HasPolynomialGrowth f) : Integrable f (gibbs H) := by
  apply integrable_gibbs_of_weighted hH (ht.integrable_exp hH)
  simpa using integrable_tilted H hH hf ht hg 0

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointInterpolationLaw
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma weighted_integral_zero_of_gibbs {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Point d → ℝ}
    (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    {u : Point d → E} (hu : (∫ z,u z ∂gibbs H)=0) :
    (∫ z,Real.exp (-H z) • u z)=0 := by
  rw [integral_gibbs_vector hc hi] at hu
  exact (smul_eq_zero.mp hu).resolve_left (inv_ne_zero (integral_exp_pos hi).ne')

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMean
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open OracleCompiler.Program

lemma terminalQuery_invariant {d n : ℕ} (x Δ : Point d) (r : ℝ)
    (g : Fin (n+1) → Point d) :
    (x + r • Δ) + r • (g 0 + terminalShift n 0 • Δ) = x+r • g 0 := by
  simp only [terminalShift, ite_true, neg_smul, one_smul]
  module

end LogConcaveSampling.SeedCompiler

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Expression
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory

variable {Ω O R Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSpace R] [MeasurableSpace Ξ] {d q r : ℕ}

namespace Equivariant
variable {A : Program Ω d q O} {f : Ω → Ω} {τ : O → O}

theorem seq (hA : A.Equivariant f τ) {B : Program (Ω × O) d r R} {σ : R → R}
    (hB : B.Equivariant (fun z => (f z.1,τ z.2)) σ) : (A.seq B).Equivariant f σ := by
  constructor
  · intro i ω h
    refine Fin.addCases (fun _ => ?_) (fun j => ?_) i
    · simp only [Program.seq,Fin.addCases_left]
      exact hA.query _ _ _
    · simp only [Program.seq,Fin.addCases_right,hA.output]
      exact hB.query j (ω,A.output (ω,leftTrace h)) (rightTrace h)
  · intro ω h
    simp only [Program.seq,hA.output]
    exact hB.output (ω,A.output (ω,leftTrace h)) (rightTrace h)

theorem seedMap (hA : A.Equivariant f τ) (g : Ξ → Ω) (hg : Measurable g)
    (f' : Ξ → Ξ) (hf : ∀ξ,g (f' ξ)=f (g ξ)) : (A.seedMap g hg).Equivariant f' τ := by
  constructor
  · intro i ξ h
    simpa only [Program.seedMap,hf] using hA.query i (g ξ) h
  · intro ξ h
    simpa only [Program.seedMap,hf] using hA.output (g ξ) h

theorem map (hA : A.Equivariant f τ) (g : Ω × O → R) (hg : Measurable g)
    (σ : R → R) (he : ∀ω x,g (f ω,τ x)=σ (g (ω,x))) :
    (A.map g hg).Equivariant f σ := by
  constructor
  · exact hA.query
  · intro ω h
    simp only [Program.map,hA.output,he]

end Equivariant

lemma pure_equivariant (g : Ω → O) (hg : Measurable g) (f : Ω → Ω) (τ : O → O)
    (he : ∀ω,g (f ω)=τ (g ω)) : (Program.pure (d:=d) g hg).Equivariant f τ := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro ω h
    exact he ω

lemma oneQuery_equivariant (x : Ω → Point d) (hx : Measurable x)
    (g : Ω × Reply d → O) (hg : Measurable g) (f : Ω → Ω) (τ : O → O)
    (he : ∀ω,x (f ω)=x ω) (hout : ∀ω a,g (f ω,a)=τ (g (ω,a))) :
    (Program.oneQuery x hx g hg).Equivariant f τ := by
  constructor
  · intro i ω h
    exact he ω
  · intro ω h
    exact hout ω (h 0)

end LogConcaveSampling.OracleCompiler.Program

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma leftBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    leftBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots u Δ (leftBlock g) := by
  ext i
  simp [leftBlock,shiftSlots]
lemma middleBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    middleBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots v Δ (middleBlock g) := by
  ext i
  simp [middleBlock,shiftSlots]
lemma rightBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    rightBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots w Δ (rightBlock g) := by
  ext i
  simp [rightBlock,shiftSlots]

lemma noise_equivariant (b : X → Point d) (hb : Measurable b) (n c : ℝ)
    (f : X → X) (Δ : Point d) (he : ∀x,b (f x)=b x+c • Δ) :
    (noise b hb n).compile.Equivariant (moveSeed f (fun _ => 0) Δ) (fun y => y+c • Δ) := by
  apply Program.pure_equivariant
  intro z
  simp [moveSeed,shiftSlots,he]
  abel

lemma add_equivariant (a : ℝ) (C T : Expression X d) {k q : ℕ}
    (M : Program (Point d × (Fin k → Point d)) d q (Point d))
    (P : (Fin k → Point d) → (Fin k → Point d)) (hP : Measurable P)
    (f : X → X) (Δ : Point d) (u : Fin C.slots → ℝ) (v : Fin k → ℝ)
    (w : Fin T.slots → ℝ) (c t : ℝ)
    (hC : C.compile.Equivariant (moveSeed f u Δ) (fun y => y+c • Δ))
    (hM : (M.seedMap (fun z : Point d × (Fin k → Point d) => (z.1,P z.2))
      (measurable_fst.prodMk (hP.comp measurable_snd))).Equivariant
        (moveSeed (fun y => y+c • Δ) v Δ) id)
    (hT : T.compile.Equivariant (moveSeed f w Δ) (fun y => y+t • Δ)) :
    (add a C k q M P hP T).compile.Equivariant
      (moveSeed f (Fin.append u (Fin.append v w)) Δ) (fun y => y+t • Δ) := by
  let Ω := X × (Fin (C.slots+(k+T.slots)) → Point d)
  let F : Ω → Ω := moveSeed f (Fin.append u (Fin.append v w)) Δ
  let A : Program Ω d C.calls (Point d) := C.compile.seedMap
    (fun z => (z.1,leftBlock z.2))
    (measurable_fst.prodMk ((measurable_leftBlock _ _ _).comp measurable_snd))
  have hA : A.Equivariant F (fun y => y+c • Δ) := by
    apply hC.seedMap
    intro z
    simp only [F,moveSeed,leftBlock_shift]
  let B : Program (Ω × Point d) d q (Point d) := M.seedMap
    (fun z => (z.2,P (middleBlock z.1.2)))
    (measurable_snd.prodMk (hP.comp ((measurable_middleBlock _ _ _).comp
      (measurable_snd.comp measurable_fst))))
  let G : (Ω × Point d) → (Ω × Point d) := fun z => (F z.1,z.2+c • Δ)
  have hB : B.Equivariant G id := by
    constructor
    · intro i z h
      have H := hM.query i (z.2,middleBlock z.1.2) h
      simpa only [B,Program.seedMap,G,F,moveSeed,middleBlock_shift] using H
    · intro z h
      have H := hM.output (z.2,middleBlock z.1.2) h
      simpa only [B,Program.seedMap,G,F,moveSeed,middleBlock_shift] using H
  let D : Program ((Ω × Point d) × Point d) d T.calls (Point d) :=
    (T.compile.seedMap (fun z => (z.1.1.1,rightBlock z.1.1.2))
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_rightBlock _ _ _).comp (measurable_snd.comp
          (measurable_fst.comp measurable_fst))))).map
      (fun z => a • z.1.2+z.2) (by fun_prop)
  have hD : D.Equivariant (fun z => (G z.1,id z.2)) (fun y => y+t • Δ) := by
    apply Program.Equivariant.map
    · apply hT.seedMap
      intro z
      simp only [G,F,moveSeed,rightBlock_shift]
    · intro z y
      dsimp
      abel
  exact hA.seq (hB.seq hD)

end LogConcaveSampling.OracleCompiler.Expression

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

lemma split_slots_preserving (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving
      (fun g : Fin (c+k) → E =>
        ((fun i : Fin c => g (Fin.castAdd k i)),fun i : Fin k => g (Fin.natAdd c i)))
      (Measure.pi fun _ => μ) ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ)) := by
  have H := (measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ Fin k => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (c+k) => μ) finSumFinEquiv).symm
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end LogConcaveSampling.OracleCompiler.Expression

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChildNoise
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma calls_compileTerms (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    (compileTerms D k a C M E).calls=E.calls+∑i,((C i).calls+(M i).calls) := by
  induction k with
  | zero => simp [compileTerms]
  | succ k ih =>
    simp only [compileTerms,Expression.calls,ih,Fin.sum_univ_succ]
    omega

lemma slots_compileTerms (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    (compileTerms D k a C M E).slots=E.slots+∑i,((C i).slots+(M i).slots) := by
  induction k with
  | zero => simp [compileTerms]
  | succ k ih =>
    simp only [compileTerms,Expression.slots,ih,Fin.sum_univ_succ]
    omega

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem weighted_gaussian_law (a : ι → ℝ) (n : ℝ) (ha : (∑i,a i^2)=n^2) :
    (Measure.pi fun _ : ι => stdGaussian E).map (fun g => ∑i,a i • g i)=
      (stdGaussian E).map (fun z => n • z) := by
  let S : (ι → E) →L[ℝ] E := ∑i,a i • ContinuousLinearMap.proj i
  let T : E →L[ℝ] E := n • ContinuousLinearMap.id ℝ E
  have hS (g : ι → E) : S g=∑i,a i • g i := by simp [S]
  have hT0 (z : E) : T z=n • z := by simp [T]
  simp_rw [←hS,←hT0]
  change (Measure.pi fun _ : ι => stdGaussian E).map S=(stdGaussian E).map T
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_map,charFunDual_pi]
  have hL (i : ι) : (L.comp S).comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)=a i • L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, hS, map_sum, map_smul, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  have hT : L.comp T=n • L := by ext z; simp [T]
  simp_rw [hL,hT,charFunDual_stdGaussian]
  rw [←Complex.exp_sum]
  simp only [norm_smul,Real.norm_eq_abs]
  congr 1
  norm_cast
  simp only [mul_pow,sq_abs,←Finset.sum_div,Finset.sum_neg_distrib,←Finset.sum_mul,ha]

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma calls_compileDeclared (D A : ℝ) (M : ℝ → ℝ → SeedProgram d)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) :
    (compileDeclared D A M (.node k b hb a r C) n).calls=
      ∑i,((compileDeclared D A M (C i) (r i/(2*D))).calls+(M (r i) (declaredNoise n A)).calls) := by
  simp only [compileDeclared,calls_compileTerms,Expression.calls,zero_add]

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianPairSumLaw
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {d : ℕ}

lemma gaussian_pair_sum_law (a b s : ℝ) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => a • z.1+b • z.2)=
      (stdGaussian (Point d)).map (fun z => s • z) := by
  have h := MeanTree.weighted_gaussian_law (E:=Point d) ![a,b] s (by simpa using hs)
  rw [←(measurePreserving_finTwoArrow (stdGaussian (Point d))).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin 2 => stdGaussian (Point d))).map
    (fun z => a • z 0+b • z 1)=_
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

lemma smoothing_add_gaussian {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (μ : Measure X) [IsProbabilityMeasure μ] (θ : Measure W) [IsProbabilityMeasure θ]
    (u : X → Point d) (f : W → Point d) (hu : Measurable u) (hf : Measurable f)
    (a b s : ℝ) (hs : a^2+b^2=s^2)
    (hlaw : μ.map u=(θ.prod (stdGaussian (Point d))).map (fun z => f z.1+a • z.2)) :
    (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+b • z.2)=
      (θ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2) := by
  let γ := stdGaussian (Point d)
  have h := congrArg (fun η : Measure (Point d) => (η.prod γ).map (fun z => z.1+b • z.2)) hlaw
  have hl : (μ.map u).prod γ=(μ.prod γ).map (Prod.map u id) := by
    rw [←Measure.map_prod_map _ _ hu measurable_id,Measure.map_id]
  have hr : ((θ.prod γ).map (fun z => f z.1+a • z.2)).prod γ=
      ((θ.prod γ).prod γ).map (Prod.map (fun z => f z.1+a • z.2) id) := by
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  rw [hl,hr,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  apply h.trans
  have hassoc := (measurePreserving_prodAssoc θ γ γ).map_eq
  have hsum : (θ.prod (γ.prod γ)).map
      (fun z => (z.1,a • z.2.1+b • z.2.2))=
      θ.prod (γ.map (fun z => s • z)) := by
    rw [show (fun z : W × (Point d × Point d) => (z.1,a • z.2.1+b • z.2.2))=
      Prod.map id (fun z => a • z.1+b • z.2) from rfl]
    rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]
    rw [gaussian_pair_sum_law a b s hs]
  have hsum' := congrArg (Measure.map (fun z : W × Point d => f z.1+z.2)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hsum'
  have he := congrArg (Measure.map (fun z : W × (Point d × Point d) =>
    f z.1+(a • z.2.1+b • z.2.2))) hassoc
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  have hfinal : (θ.prod (γ.map (fun z => s • z))).map (fun z => f z.1+z.2)=
      (θ.prod γ).map (fun z => f z.1+s • z.2) := by
    rw [show θ.prod (γ.map (fun z => s • z))=(θ.prod γ).map
      (Prod.map id (fun z => s • z)) by
        rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hh := he.trans (hsum'.trans hfinal)
  change ((θ.prod γ).prod γ).map (fun z => f z.1.1+(a • z.1.2+b • z.2))=_ at hh
  change ((θ.prod γ).prod γ).map (fun z => (f z.1.1+a • z.1.2)+b • z.2)=_
  simpa only [add_assoc] using hh
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_LogMeshLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

lemma logMeshCount_bound {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (logMeshCount T h:ℝ)<logMeshLength T/h+1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (logMeshLength_pos hT0 hT1) hh))

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

lemma probabilityNode_card (T h : ℝ) (n : ℕ) :
    Fintype.card (ProbabilityNode T h n)=logMeshCount T h*(n+1) := by
  simp [ProbabilityNode]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PoincareVectorVariance
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

lemma stdGaussian_sq_norm (d : ℕ) :
    (∫z : Point d,‖z‖^2 ∂stdGaussian (Point d))=d := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hei (j : Fin d) : Integrable (fun z : Point d => (inner ℝ (b j) z)^2) (stdGaussian (Point d)) :=
    ((IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).continuousLinearMap_comp (innerSL ℝ (b j))).integrable_sq
  calc
    _ = ∫z,∑j : Fin d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs,sq_abs] using (b.sum_sq_norm_inner_right z).symm
    _ = ∑j : Fin d,∫z,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := integral_finsetSum _ (fun j _ => hei j)
    _ = _ := by
      have hj (j : Fin d) : (∫z : Point d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d))=1 := by
        change (∫z : Point d,((innerSL ℝ (b j)) z)^2 ∂stdGaussian (Point d))=1
        rw [GaussianPoincare.integral_dual_sq,innerSL_apply_norm,b.norm_eq_one,one_pow]
      simp_rw [hj]
      simp
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitD
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma circuitD_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) : 0 ≤ circuitD F x := by
  unfold circuitD; positivity
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticNormalizedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

lemma dimensionLog_nonneg (d : ℕ) : 0≤dimensionLog d := by
  have hh : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  unfold dimensionLog
  linarith

lemma dimensionLog_isBigO_log : dimensionLog =O[atTop] (fun d : ℕ => Real.log (d:ℝ)) := by
  have ht : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ d : ℕ in atTop,1≤Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog] with d hd hl
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (2:ℝ)≤d := by exact_mod_cast hd
  have ht : Real.log ((d:ℝ)+1)≤2*Real.log (d:ℝ) := by
    calc
      _ ≤ Real.log ((d:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.norm_of_nonneg (dimensionLog_nonneg d),Real.norm_of_nonneg (by linarith : 0≤Real.log (d:ℝ))]
  unfold dimensionLog
  linarith

lemma dimensionLog_pow_isLittleO (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun d : ℕ => dimensionLog d^k) =o[atTop] (fun d : ℕ => (d:ℝ)^s) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hs).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simp only [Real.rpow_natCast,Function.comp_def] at hh
  exact (dimensionLog_isBigO_log.pow k).trans_isLittleO hh

theorem polylog_power_absorb (C : ℝ) (k : ℕ) {a b : ℝ} (hab : b<a) :
    ∀ᶠ d : ℕ in atTop, |C| *dimensionLog d^k*(d:ℝ)^(-a)≤(d:ℝ)^(-b) := by
  have hh := ((dimensionLog_pow_isLittleO k (sub_pos.mpr hab)).const_mul_left |C|).mul_isBigO
    (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)
  have he : (fun d : ℕ => (d:ℝ)^(a-b)*(d:ℝ)^(-a)) =ᶠ[atTop]
      (fun d : ℕ => (d:ℝ)^(-b)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    rw [←Real.rpow_add hd0]
    congr 1
    ring
  have hbnd := (hh.congr' Filter.EventuallyEq.rfl he).def (by norm_num : (0:ℝ)<1)
  filter_upwards [hbnd] with d hd
  simpa only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] : 0≤|C| *dimensionLog d^k*(d:ℝ)^(-a)),
    Real.norm_of_nonneg (by positivity : 0≤(d:ℝ)^(-b))] using hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

lemma dimensionLog_one_le (d : ℕ) : 1≤dimensionLog d := by
  unfold dimensionLog
  have h := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d] : 1≤(d:ℝ)+1)
  linarith

namespace LogPowerRate

lemma congr {f g : ℕ → ℝ} {a : ℝ} (h : LogPowerRate f a) (he : f=ᶠ[atTop] g) : LogPowerRate g a := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,hk.congr' he Filter.EventuallyEq.rfl⟩

lemma mono {f : ℕ → ℝ} {a b : ℝ} (h : LogPowerRate f a) (hba : b≤a) : LogPowerRate f b := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,hk.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := lt_of_lt_of_le zero_lt_one hd1
  simp only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-a)), Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-b))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)) (by positivity [dimensionLog_nonneg d])

lemma const (C : ℝ) : LogPowerRate (fun _ => C) 0 := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,neg_zero,Real.rpow_zero,mul_one] using
    (isBigO_const_const C (by norm_num : (1:ℝ)≠0) atTop : (fun _ : ℕ => C)=O[atTop] (fun _ => (1:ℝ)))

lemma power (a : ℝ) : LogPowerRate (fun d => (d:ℝ)^(-a)) a := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,one_mul] using (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)

lemma log : LogPowerRate dimensionLog 0 := by
  refine ⟨1,?_⟩
  simpa only [pow_one,neg_zero,Real.rpow_zero,mul_one] using (isBigO_refl dimensionLog atTop)

lemma mul {f g : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g b) :
    LogPowerRate (fun d => f d*g d) (a+b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  refine ⟨k+l,(hk.mul hl).congr' Filter.EventuallyEq.rfl ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  rw [pow_add,neg_add,Real.rpow_add hd0]
  ring

lemma pow {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (n : ℕ) :
    LogPowerRate (fun d => f d^n) (n*a) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih =>
    have h := ih.mul hf
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

lemma const_mul {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => C*f d) a := by
  simpa only [zero_add] using (const C).mul hf

lemma mul_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d*C) a := by
  simpa only [add_zero] using hf.mul (const C)

lemma add {f g : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g a) :
    LogPowerRate (fun d => f d+g d) a := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  have bound (i j : ℕ) : (fun d : ℕ => dimensionLog d^i*(d:ℝ)^(-a)) =O[atTop]
      (fun d => dimensionLog d^(i+j)*(d:ℝ)^(-a)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with d
    rw [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d]),
      Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d])]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (dimensionLog_one_le d) (by omega)) (by positivity)
  exact ⟨k+l,(hk.trans (bound k l)).add (hl.trans (by simpa only [Nat.add_comm] using bound l k))⟩

lemma of_le_abs {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hfg : ∀ᶠ d in atTop, |f d|≤|g d|) : LogPowerRate f a := by
  obtain ⟨k,hk⟩ := hg
  exact ⟨k,(IsBigO.of_bound 1 (by simpa only [one_mul,Real.norm_eq_abs] using hfg)).trans hk⟩

lemma eventually_small {f : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hba : b<a) :
    ∀ᶠ d in atTop, |f d|≤(d:ℝ)^(-b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨C,hC⟩ := hk.bound
  have hp := polylog_power_absorb C k hba
  filter_upwards [hC,hp] with d hd hp
  have hdn : 0≤dimensionLog d^k*(d:ℝ)^(-a) := by positivity [dimensionLog_nonneg d]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hdn] at hd
  calc
    _ ≤ C*(dimensionLog d^k*(d:ℝ)^(-a)) := hd
    _ ≤ |C| *(dimensionLog d^k*(d:ℝ)^(-a)) := mul_le_mul_of_nonneg_right (le_abs_self C) hdn
    _ ≤ _ := by simpa only [mul_assoc] using hp

end LogPowerRate
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators

namespace LogPowerRate

lemma div_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d/C) a := by
  simpa only [div_eq_mul_inv] using hf.mul_const C⁻¹

lemma of_le {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hf : ∀ᶠ d : ℕ in atTop,0≤f d) (hfg : ∀ᶠ d : ℕ in atTop,f d≤g d) : LogPowerRate f a := by
  apply of_le_abs hg
  filter_upwards [hf,hfg] with d hd he
  rw [abs_of_nonneg hd,abs_of_nonneg (hd.trans he)]
  exact he

lemma inv_power (a : ℝ) : LogPowerRate (fun d => ((d:ℝ)^(-a))⁻¹) (-a) := by
  apply (power (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg d
  rw [Real.rpow_neg hd0]

lemma log_nat : LogPowerRate (fun d : ℕ => Real.log (d:ℝ)) 0 := by
  apply of_le log
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.log_nonneg (by exact_mod_cast hd)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    have he := Real.log_le_log hp (by linarith : (d:ℝ)≤(d:ℝ)+1)
    unfold dimensionLog
    linarith

lemma log_power (a : ℝ) : LogPowerRate (fun d : ℕ => Real.log ((d:ℝ)^(-a))) 0 := by
  apply (log_nat.const_mul (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  rw [Real.log_rpow (by exact_mod_cast hd : (0:ℝ)<d)]
end LogPowerRate

lemma logMeshLength_le_scale {T R : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hR : 0<R) (hRT : R^2≤1-T^2) :
    logMeshLength T≤Real.log 2-2*Real.log R := by
  have hden : 0<1-T := by linarith
  have hRR : R^2/2≤1-T := by nlinarith
  have he := Real.log_le_log (by positivity : 0<R^2/2) hRR
  rw [Real.log_div (by positivity : R^2≠0) (by norm_num),Real.log_pow] at he
  unfold logMeshLength
  norm_num at he
  linarith

lemma logMeshLength_rate {T : ℕ → ℝ} (a : ℝ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-a))^2≤1-(T d)^2) :
    LogPowerRate (fun d => logMeshLength (T d)) 0 := by
  apply LogPowerRate.of_le ((LogPowerRate.const (Real.log 2)).add
    ((LogPowerRate.log_power a).const_mul (-2)))
  · filter_upwards [hT0,hT1] with d hd0 hd1
    exact (logMeshLength_pos hd0 hd1).le
  · filter_upwards [hT0,hT1,hRT,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hRT hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [sub_eq_add_neg,neg_mul] using
      logMeshLength_le_scale hd0 hd1 (Real.rpow_pos_of_pos hp (-a)) hRT

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_DistanceCoupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

variable {E : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

lemma tight_range_of_tendsto {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) : IsTightMeasureSet (range (fun n => (μs n : Measure E))) := by
  have hc : IsCompact (closure (range μs)) := h.isCompact_insert_range.of_isClosed_subset
    isClosed_closure (closure_minimal (subset_insert _ _) h.isCompact_insert_range.isClosed)
  have hh := isTightMeasureSet_of_isCompact_closure hc
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext ν
  simp only [mem_range,mem_ofPred_eq]
  aesop

theorem distanceCoupled_of_tendsto {μ ν : ProbabilityMeasure E}
    {μs νs : ℕ → ProbabilityMeasure E} (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) (R : ℝ)
    (hc : ∀n,DistanceCoupled (μs n : Measure E) (νs n : Measure E) R) : DistanceCoupled (μ : Measure E) (ν : Measure E) R := by
  choose κ hκ hfst hsnd hdist using hc
  let Ks : ℕ → ProbabilityMeasure (E×E) := fun n => ⟨κ n,hκ n⟩
  have hj : IsTightMeasureSet (range κ) := by
    apply IsTightMeasureSet.prodMk
    · have he : Measure.fst '' range κ=range (fun n => (μs n : Measure E)) := by
        ext ρ
        simp only [mem_image,mem_range,exists_exists_eq_and]
        simp only [hfst]
      rw [he]
      exact tight_range_of_tendsto hμ
    · have he : Measure.snd '' range κ=range (fun n => (νs n : Measure E)) := by
        ext ρ
        simp only [mem_image,mem_range,exists_exists_eq_and]
        simp only [hsnd]
      rw [he]
      exact tight_range_of_tendsto hν
  have hj' : IsTightMeasureSet {((ρ : ProbabilityMeasure (E×E)) : Measure (E×E)) | ρ∈range Ks} := by
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    ext ρ
    simp only [mem_ofPred_eq,mem_range,exists_exists_eq_and]
    rfl
  obtain ⟨K,_,φ,hφ,hK⟩ := (isCompact_closure_of_isTightMeasureSet hj').tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (Ks ∘ φ) K hK continuous_fst
  have hg := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (Ks ∘ φ) K hK continuous_snd
  have hfm : (fun n => (Ks (φ n)).map measurable_fst.aemeasurable)=μs ∘ φ := by
    funext n; apply Subtype.ext; exact hfst (φ n)
  have hgm : (fun n => (Ks (φ n)).map measurable_snd.aemeasurable)=νs ∘ φ := by
    funext n; apply Subtype.ext; exact hsnd (φ n)
  simp only [Function.comp_apply] at hf hg
  rw [hfm] at hf
  rw [hgm] at hg
  have hef := tendsto_nhds_unique hf (hμ.comp hφ.tendsto_atTop)
  have heg := tendsto_nhds_unique hg (hν.comp hφ.tendsto_atTop)
  refine ⟨K,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hef,
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) heg,?_⟩
  let S : Set (E×E) := {z | dist z.1 z.2≤R}
  have hS : IsClosed S := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  have hprob (n : ℕ) : (Ks n : Measure (E×E)) S=1 := by
    calc (Ks n : Measure (E×E)) S = (Ks n : Measure (E×E)) univ := by
          apply measure_congr
          filter_upwards [hdist n] with z hz
          apply propext
          change (dist z.1 z.2≤R) ↔ True
          exact iff_true_intro hz
      _ = 1 := measure_univ
  have hl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hK hS
  simp only [Function.comp_apply,hprob,limsup_const] at hl
  have he : (K : Measure (E×E)) S=1 := le_antisymm (by simpa only [measure_univ] using (measure_mono (subset_univ S) : (K : Measure (E×E)) S≤(K : Measure (E×E)) univ)) hl
  rw [←show (∀ᵐ z : E×E ∂(K : Measure (E×E)),z∈S) ↔ (∀ᵐ z ∂(K : Measure (E×E)),dist z.1 z.2≤R) from Iff.rfl]
  exact (ae_iff).mpr (by
    change (K : Measure (E×E)) Sᶜ=0
    rw [measure_compl hS.measurableSet (measure_ne_top _ _),measure_univ,he,tsub_self])

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_Law
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal

variable {d : ℕ}

theorem laws_tendsto (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → Point d → Point d} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {D : ℕ → ℝ} (hD : Tendsto (fun k => (N k:ℝ)*D k) atTop (𝓝 0))
    (hstep : ∀ k (f : Point d → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator (T k) (σ k) f x ∂μ)-∫ x, f x ∂μ| ≤ B*D k)
    (x : Point d) :
    Tendsto (fun k => (⟨law (T k) (σ k) (N k) x,law_probability (hT k).continuous.measurable _ _ _⟩ : ProbabilityMeasure (Point d)))
      atTop (nhds (X := ProbabilityMeasure (Point d)) ⟨μ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))⟩) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hf hl
  obtain ⟨C,hC⟩ := hf
  obtain ⟨L,hL⟩ := hl
  have hb (z : Point d) : |f z|≤C+|f 0| := by
    have h := hC z 0
    rw [Real.dist_eq] at h
    have ha := abs_add_le (f z-f 0) (f 0)
    rw [sub_add_cancel] at ha
    linarith
  have hB : 0≤C+|f 0| := (abs_nonneg (f 0)).trans (hb 0)
  have ht := expectations_tendsto μ hT σ N hq hD hstep hL.uniformContinuous hB hb x
  convert ht using 1
  · funext k
    change (∫z,f z ∂law (T k) (σ k) (N k) x)=_
    rw [law,integral_map (measurable_iterate_map (hT k).continuous.measurable _ _ _).aemeasurable hL.continuous.aestronglyMeasurable]
    exact integral_iterate_gaussian (hT k).continuous.measurable (σ k) hL.continuous.measurable hb (N k) x
  · rfl

lemma comparison_iterate {T U : Point d → Point d} {R : ℝ} (hr : 0≤R)
    (hstep : ∀x y,dist x y≤R → dist (T x) (U y)≤R)
    (σ : ℝ) (n : ℕ) (x : Point d) (g : Fin n → Point d) :
    dist (iterate T σ n x g) (iterate U σ n x g)≤R := by
  induction n with
  | zero => simpa only [iterate,dist_self] using hr
  | succ n ih =>
    simp only [iterate,dist_add_right]
    exact hstep _ _ (ih _)

lemma laws_distanceCoupled {T U : Point d → Point d} (hT : Measurable T) (hU : Measurable U)
    {R : ℝ} (hr : 0≤R) (hstep : ∀x y,dist x y≤R → dist (T x) (U y)≤R)
    (σ : ℝ) (n : ℕ) (x : Point d) : Coupling.DistanceCoupled (law T σ n x) (law U σ n x) R := by
  let J := fun g : PiLp 2 (fun _ : Fin n => Point d) =>
    (iterate T σ n x g.ofLp,iterate U σ n x g.ofLp)
  have hm : Measurable J := (measurable_iterate_map hT _ _ _).prodMk (measurable_iterate_map hU _ _ _)
  refine ⟨(stdGaussian _).map J,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_,?_⟩
  · change ((stdGaussian _).map J).map Prod.fst=_
    rw [Measure.map_map measurable_fst hm]
    rfl
  · change ((stdGaussian _).map J).map Prod.snd=_
    rw [Measure.map_map measurable_snd hm]
    rfl
  · apply ae_map_iff hm.aemeasurable (measurableSet_le (by fun_prop) measurable_const) |>.mpr
    exact Filter.Eventually.of_forall (fun g => comparison_iterate hr hstep σ n x g.ofLp)
end LogConcaveSampling.EulerGeometry

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter EulerGeometry
open scoped Topology Classical NNReal

variable {d : ℕ}

theorem gibbs_distanceCoupled_of_euler
    {H U : Point d → ℝ} (hH : ContDiff ℝ 2 H) (hU : ContDiff ℝ 2 U)
    {MH MU : ℝ≥0} (hMH : LipschitzWith MH (gradient H)) (hMU : LipschitzWith MU (gradient U))
    (hH0 : partition H ≠ 0) (hHt : partition H ≠ ⊤)
    (hU0 : partition U ≠ 0) (hUt : partition U ≠ ⊤)
    (hHi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    (hUi : Integrable (fun x => ‖gradient U x‖^2) (gibbs U))
    {m a B : ℝ} (hm : 0 < m) (ha : 0 < a) (hma : m*a≤1) (hB : 0 ≤ B)
    (hTH : ∀h,0 ≤ h → h ≤ a → ∀x y,dist (eulerDrift H h x) (eulerDrift H h y)≤(1-m*h)*dist x y)
    (hTU : ∀h,0 ≤ h → h ≤ a → ∀x y,dist (eulerDrift U h x) (eulerDrift U h y)≤(1-m*h)*dist x y)
    (hpert : ∀x,‖gradient H x-gradient U x‖≤B) :
    Coupling.DistanceCoupled (gibbs H) (gibbs U) (B/m) := by
  let := probability_gibbs_of_partition hH0 hHt
  let := probability_gibbs_of_partition hU0 hUt
  have hrate : Tendsto (fun s => EulerDefect.rate H s+EulerDefect.rate U s) (𝓝 0) (𝓝 0) := by
    simpa only [zero_add] using (EulerDefect.rate_tendsto hH hMH hHi).add (EulerDefect.rate_tendsto hU hMU hUi)
  obtain ⟨N,s,hs,hD⟩ := exists_consistent_schedule hrate
    (fun s => add_nonneg (EulerDefect.rate_nonneg H s) (EulerDefect.rate_nonneg U s)) ha
  have hq0 (k) : 0 ≤ 1-m*(s k)^2 := by
    have h := mul_le_mul_of_nonneg_left (hs k).2.2.1 hm.le
    linarith
  let q : ℕ → ℝ≥0 := fun k => ⟨1-m*(s k)^2,hq0 k⟩
  have hTL (k) : LipschitzWith (q k) (eulerDrift H ((s k)^2)) :=
    LipschitzWith.of_dist_le_mul (hTH _ (sq_nonneg _) (hs k).2.2.1)
  have hUL (k) : LipschitzWith (q k) (eulerDrift U ((s k)^2)) :=
    LipschitzWith.of_dist_le_mul (hTU _ (sq_nonneg _) (hs k).2.2.1)
  have hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0) :=
    schedule_contraction_tendsto hm N s hq0 (fun k => (hs k).2.2.2)
  have hDH : Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*EulerDefect.rate H (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity [EulerDefect.rate_nonneg H (s k)]) _ hD
    intro k
    gcongr
    exact le_add_of_nonneg_right (EulerDefect.rate_nonneg U _)
  have hDU : Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*EulerDefect.rate U (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity [EulerDefect.rate_nonneg U (s k)]) _ hD
    intro k
    gcongr
    exact le_add_of_nonneg_left (EulerDefect.rate_nonneg H _)
  have hcH := laws_tendsto (gibbs H) hTL (fun k => Real.sqrt 2*s k) N hq hDH
    (fun k f hf B hB hb => euler_operator_gibbs_defect hH hMH hH0 hHt hHi
      (hs k).1.ne' (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hf hB hb) 0
  have hcU := laws_tendsto (gibbs U) hUL (fun k => Real.sqrt 2*s k) N hq hDU
    (fun k f hf B hB hb => euler_operator_gibbs_defect hU hMU hU0 hUt hUi
      (hs k).1.ne' (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hf hB hb) 0
  apply Coupling.distanceCoupled_of_tendsto hcH hcU
  intro k
  apply laws_distanceCoupled (hTL k).continuous.measurable (hUL k).continuous.measurable
    (div_nonneg hB hm.le)
  intro x y hxy
  have he : dist (eulerDrift H ((s k)^2) y) (eulerDrift U ((s k)^2) y)≤(s k)^2*B := by
    rw [eulerDrift,eulerDrift,dist_eq_norm,show y-(s k)^2 • gradient H y-(y-(s k)^2 • gradient U y) =
      -(s k)^2 • (gradient H y-gradient U y) by module,norm_smul,Real.norm_eq_abs,abs_neg,abs_sq]
    exact mul_le_mul_of_nonneg_left (hpert y) (sq_nonneg _)
  have ht := dist_triangle (eulerDrift H ((s k)^2) x) (eulerDrift H ((s k)^2) y)
    (eulerDrift U ((s k)^2) y)
  have hb := (hTL k).dist_le_mul x y
  have hmul := mul_le_mul_of_nonneg_left hxy (hq0 k)
  have hid : (1-m*(s k)^2)*(B/m)+(s k)^2*B=B/m := by field_simp; ring
  change _≤B/m
  change dist _ _≤(1-m*(s k)^2)*dist x y at hb
  linarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal RealInnerProductSpace

variable {d : ℕ}

lemma gradient_contDiff_one {H : Point d → ℝ} (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (gradient H) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp (hH.fderiv_right (by norm_num))

lemma hessian_euler_contraction {H : Point d → ℝ} (hH : ContDiff ℝ 2 H)
    {m M s : ℝ} (_ : 0 < m) (hs : 0 ≤ s) (hsM : s*M ≤ 1)
    (hess : ∀x v : Point d,m*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (gradient H) x v) ∧
      inner ℝ v (fderiv ℝ (gradient H) x v) ≤ M*‖v‖^2)
    (hsm : s*m ≤ 1) :
    LipschitzWith ⟨1-s*m,sub_nonneg.mpr hsm⟩ (eulerDrift H s) := by
  have hg := (gradient_contDiff_one hH).differentiable (by norm_num)
  have hd (x : Point d) : fderiv ℝ (eulerDrift H s) x=
      ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x :=
    ((hasFDerivAt_id x).sub ((hg x).hasFDerivAt.const_smul s)).fderiv
  apply lipschitzWith_of_nnnorm_fderiv_le (differentiable_id.sub (hg.const_smul s))
  intro x
  change ‖fderiv ℝ (eulerDrift H s) x‖ ≤ 1-s*m
  rw [hd]
  change ‖ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x‖ ≤ 1-s*m
  have hsym : (ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x).IsSymmetric := by
    intro v w
    change inner ℝ (v-s • fderiv ℝ (gradient H) x v) w=inner ℝ v (w-s • fderiv ℝ (gradient H) x w)
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    have he : inner ℝ (fderiv ℝ (gradient H) x v) w=inner ℝ v (fderiv ℝ (gradient H) x w) :=
      (ContDiff.isSymmetric_gradient_derivative hH x) v w
    rw [he]
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
  apply ciSup_le
  intro v
  by_cases hv : v=0
  · simp [hv,sub_nonneg.mpr hsm]
  have hp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,real_inner_comm]
  simp only [RCLike.re_to_real,sub_apply,ContinuousLinearMap.id_apply,
    smul_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hn : 0 ≤ ‖v‖^2-s*inner ℝ v (fderiv ℝ (gradient H) x v) := by
    have hh := mul_le_mul_of_nonneg_left (hess x v).2 hs
    have hb := mul_le_mul_of_nonneg_right hsM hp.le
    nlinarith
  rw [abs_of_nonneg (div_nonneg hn hp.le),div_le_iff₀ hp]
  have hh := mul_le_mul_of_nonneg_left (hess x v).1 hs
  nlinarith

lemma posterior_smooth {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y : Point d) :
    ContDiff ℝ 2 (posteriorPotential V h y) :=
  hV.smooth.add (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)

lemma posterior_gradient {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y z : Point d) :
    gradient (posteriorPotential V h y) z=gradient V z+h⁻¹ • (z-y) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha := (hasStrictFDerivAt_norm_sq (z-y)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hd := (hV.smooth.differentiable (by norm_num) z).hasFDerivAt.add (ha.const_smul (2*h)⁻¹)
  convert! hd using 1
  · funext w
    simp only [posteriorPotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,Pi.sub_apply,id_eq,smul_eq_mul]
    ring
  ext v
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearMap.id_apply,
    map_sub,sub_zero,smul_eq_mul,innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply,inner_add_left,real_inner_smul_left,inner_sub_left,←toDual_gradient]
  ring

lemma posterior_hessian {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y z v : Point d) :
    fderiv ℝ (gradient (posteriorPotential V h y)) z v=fderiv ℝ (gradient V) z v+h⁻¹ • v := by
  have he : gradient (posteriorPotential V h y)=(fun z => gradient V z+h⁻¹ • (z-y)) :=
    funext (posterior_gradient hV h y)
  rw [he]
  have hd := (hV.contDiff_gradient.differentiable (by norm_num) z).hasFDerivAt.add
    (((hasFDerivAt_id z).sub (hasFDerivAt_const y z)).const_smul h⁻¹)
  change (fderiv ℝ (gradient V+h⁻¹ • (id-fun _ => y)) z) v=_
  rw [hd.fderiv]
  simp

lemma posterior_tail {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0 < h) (y : Point d) :
    HasGaussianLowerTail (posteriorPotential V h y) := by
  refine ⟨1/2,by norm_num,0,fun z => ?_⟩
  dsimp [posteriorPotential]
  have hq := (hV.quadratic_bounds z).1
  have hn : 0 ≤ ‖z-y‖^2/(2*h) := by positivity
  linarith

lemma posterior_gradient_lipschitz {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0 < h) (y : Point d) :
    LipschitzWith ⟨2+h⁻¹,by positivity⟩ (gradient (posteriorPotential V h y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [posterior_gradient hV h y]
  have hb := dist_add_add_le (gradient V x) (h⁻¹ • (x-y)) (gradient V z) (h⁻¹ • (z-y))
  simp only [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),dist_sub_right] at hb
  have hg := hV.gradient_lipschitz.dist_le_mul x z
  change _ ≤ (2+h⁻¹)*dist x z
  norm_num at hg
  nlinarith

lemma norm_sq_growth_of_lipschitz {g : Point d → Point d} {L : ℝ≥0} (hg : LipschitzWith L g) :
    HasPolynomialGrowth (fun x => ‖g x‖^2) := by
  obtain ⟨C,hC,n,hb⟩ := growth_of_lipschitz hg
  refine ⟨2*C^2,by positivity,2*n,fun x => ?_⟩
  rw [Real.norm_eq_abs,abs_sq]
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  have hr := sq_nonneg (1-‖x‖^n)
  rw [mul_comm 2 n,pow_mul]
  nlinarith [mul_nonneg (sq_nonneg C) hr]

lemma posterior_gradient_integrable {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0 < h) (y : Point d) :
    Integrable (fun z => ‖gradient (posteriorPotential V h y) z‖^2) (gibbs (posteriorPotential V h y)) :=
  integrable_polynomial_gibbs (posterior_smooth hV h y).continuous (posterior_tail hV hh y)
    ((posterior_gradient_lipschitz hV hh y).continuous.norm.pow 2)
    (norm_sq_growth_of_lipschitz (posterior_gradient_lipschitz hV hh y))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal RealInnerProductSpace

variable {d : ℕ}

lemma posterior_euler_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0 < h) (y : Point d) {s : ℝ} (hs : 0 ≤ s) (hsM : s*(2+h⁻¹) ≤ 1) :
    ∀ x z, dist (eulerDrift (posteriorPotential V h y) s x)
      (eulerDrift (posteriorPotential V h y) s z) ≤ (1-(1+h⁻¹)*s)*dist x z := by
  have hsm : s*(1+h⁻¹) ≤ 1 := by nlinarith
  have he := hessian_euler_contraction (posterior_smooth hV h y)
    (by positivity : 0 < 1+h⁻¹) hs hsM (fun x v => ?_) hsm
  · intro x z
    have hb := he.dist_le_mul x z
    change dist _ _ ≤ (1-s*(1+h⁻¹))*dist x z at hb
    convert! hb using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [posterior_hessian hV h y,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    obtain ⟨hl,hu⟩ := hV.hessian_bounds x v
    constructor <;> nlinarith

theorem posterior_distanceCoupled {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0 < h) (y z : Point d) :
    Coupling.DistanceCoupled (gibbs (posteriorPotential V h y))
      (gibbs (posteriorPotential V h z)) (dist y z/(1+h)) := by
  have hM : 0 < 2+h⁻¹ := by positivity
  have hm : 0 < 1+h⁻¹ := by positivity
  have hma : (1+h⁻¹)*(2+h⁻¹)⁻¹ ≤ 1 := by
    rw [←div_eq_mul_inv,div_le_one hM]
    linarith
  have hstep (u : Point d) (s : ℝ) (hs : 0 ≤ s) (hsa : s ≤ (2+h⁻¹)⁻¹) :=
    posterior_euler_lipschitz hV hh u hs (by
      have hsc := mul_le_mul_of_nonneg_right hsa hM.le
      rw [inv_mul_cancel₀ hM.ne'] at hsc
      exact hsc)
  have hpert (x : Point d) :
      ‖gradient (posteriorPotential V h y) x-gradient (posteriorPotential V h z) x‖ ≤ h⁻¹*dist y z := by
    rw [posterior_gradient hV h y,posterior_gradient hV h z,
      show gradient V x+h⁻¹ • (x-y)-(gradient V x+h⁻¹ • (x-z))=h⁻¹ • (z-y) by module,
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),←dist_eq_norm,dist_comm z y]
  have he := gibbs_distanceCoupled_of_euler (posterior_smooth hV h y) (posterior_smooth hV h z)
    (posterior_gradient_lipschitz hV hh y) (posterior_gradient_lipschitz hV hh z)
    (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))
    (partition_pos_of_continuous (posterior_smooth hV h z).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh z).integrable_exp (posterior_smooth hV h z).continuous))
    (posterior_gradient_integrable hV hh y) (posterior_gradient_integrable hV hh z)
    hm (inv_pos.mpr hM) hma (mul_nonneg (inv_pos.mpr hh).le dist_nonneg)
    (hstep y) (hstep z) hpert
  have hid : h⁻¹*dist y z/(1+h⁻¹)=dist y z/(1+h) := by
    field_simp
    ring
  rwa [hid] at he

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma bounded_integrable {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀x,|f x|≤C) :
    Integrable f μ := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma bounded_integral {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsProbabilityMeasure μ] {f : E → ℝ} {C : ℝ} (_ : 0≤C) (hb : ∀x,|f x|≤C) :
    |∫x,f x ∂μ|≤C := by
  rw [←Real.norm_eq_abs]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
    (fun x => by simpa only [Real.norm_eq_abs] using hb x))).trans (by simp)

lemma posteriorKernel_probability {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0<h) : IsMarkovKernel (posteriorKernel V hV h) := by
  constructor
  intro y
  exact probability_gibbs_of_partition (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))

lemma noisedLaw_probability {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    IsProbabilityMeasure (noisedLaw V h) := by
  let := hV.isProbabilityMeasure_gibbs
  unfold noisedLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma jointPosteriorLaw_probability {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    IsProbabilityMeasure (jointPosteriorLaw V h) := by
  let := hV.isProbabilityMeasure_gibbs
  unfold jointPosteriorLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma jointPosterior_fst {V : Point d → ℝ} (h : ℝ) :
    (jointPosteriorLaw V h).map Prod.fst=gibbs V := by
  rw [jointPosteriorLaw,Measure.map_map measurable_fst (by fun_prop)]
  simpa only [Function.comp_def,measure_univ,one_smul] using
    (Measure.map_fst_prod (μ:=gibbs V) (ν:=stdGaussian (Point d)))

lemma jointPosterior_snd {V : Point d → ℝ} (h : ℝ) :
    (jointPosteriorLaw V h).map Prod.snd=noisedLaw V h := by
  rw [jointPosteriorLaw,Measure.map_map measurable_snd (by fun_prop)]
  rfl

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma appendSlots_preserving {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2)
      ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (c+k) => μ) := by
  have hm : Measurable (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right] <;> fun_prop
  refine ⟨hm,?_⟩
  rw [←(Expression.split_slots_preserving μ c k).map_eq,Measure.map_map hm
    (Expression.split_slots_preserving μ c k).measurable]
  have he : (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) ∘
      (fun g : Fin (c+k) → E => ((fun i => g (Fin.castAdd k i)),fun i => g (Fin.natAdd c i)))=id := by
    funext g; exact Fin.append_castAdd_natAdd
  rw [he,Measure.map_id]

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SlotTransformAddShift
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open OracleCompiler OracleCompiler.Expression

namespace SeedCompiler

variable {k d : ℕ}

lemma slotTransform_add_shift (c : ℝ) (a v : Fin k → ℝ) (g : Fin k → Point d) (Δ : Point d) :
    slotTransform c a (shiftSlots v Δ g)=
      shiftSlots (slotTransform c a v) Δ (slotTransform c a g) := by
  have hs : slotSum a (shiftSlots v Δ g)=slotSum a g+(slotSum a v) • Δ := by
    simp only [slotSum,shiftSlots,smul_add,Finset.sum_add_distrib,smul_smul,smul_eq_mul]
    rw [Finset.sum_smul]
  ext i
  simp only [slotTransform,shiftSlots,hs,smul_add,sub_smul,smul_smul,smul_eq_mul]
  abel_nf

lemma slotTransform_scalar_mul (c s : ℝ) (a v : Fin k → ℝ) :
    slotTransform c a (fun i => s*v i)=fun i => s*slotTransform c a v i := by
  ext i
  simp only [slotTransform,slotSum,smul_eq_mul]
  have he : (∑i,a i*(s*v i))=s*∑i,a i*v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

lemma inverse_shift_identity (a v : Fin k → ℝ) (ha : (∑i,a i^2)<1)
    (s : ℝ) (g : Fin k → Point d) (Δ : Point d) :
    slotTransform (sqrtCoefficient a) a
      (shiftSlots (fun i => s*slotTransform (inverseCoefficient a) a v i) Δ g)=
      shiftSlots v (s • Δ) (slotTransform (sqrtCoefficient a) a g) := by
  rw [slotTransform_add_shift,slotTransform_scalar_mul,slotTransform_inverse a ha]
  funext i
  simp only [shiftSlots,smul_smul]
  rw [mul_comm s (v i)]

lemma inverse_shift_energy (a v : Fin k → ℝ) (ha : (∑i,a i^2)≤1/4) (s : ℝ) :
    (∑i,(s*slotTransform (inverseCoefficient a) a v i)^2) ≤
      4*s^2*(∑i,v i^2) := by
  have h := inverse_slot_energy (E:=ℝ) a ha v
  simp only [Real.norm_eq_abs,sq_abs] at h
  simp_rw [mul_pow]
  rw [←Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg s)]

theorem transformed_mean_equivariant {queryCount : ℕ}
    (M : Program (Point d × (Fin k → Point d)) d queryCount (Point d))
    {r : ℝ} (hr : r≠0) (v a : Fin k → ℝ) (ha : (∑i,a i^2)<1)
    (hM : ∀Δ,M.Equivariant (moveSeed (fun x => x+r • Δ) v Δ) id)
    (c : ℝ) (Δ : Point d) :
    (M.seedMap (fun z => (z.1,slotTransform (sqrtCoefficient a) a z.2))
      (measurable_fst.prodMk ((measurable_slotTransform _ _).comp measurable_snd))).Equivariant
      (moveSeed (fun x => x+c • Δ)
        (fun i => (c/r)*slotTransform (inverseCoefficient a) a v i) Δ) id := by
  apply (hM ((c/r) • Δ)).seedMap
  intro z
  apply Prod.ext
  · dsimp [moveSeed]
    rw [smul_smul]
    congr 2
    field_simp
  · dsimp [moveSeed]
    exact inverse_shift_identity a v ha (c/r) z.2 Δ

end SeedCompiler
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowGaussian
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

omit [MeasurableSpace X] in
lemma DirectCenter.radius {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (_hT0 : 0≤T) (_hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) :
    r*Real.sqrt (1-T^2) ≤ r' ∧ r' ≤ r := by
  obtain ⟨ρ,hρ,θ,hθ,rfl,hb⟩ := hb
  have hρsq : ρ^2≤T^2 := pow_le_pow_left₀ hρ.1 hρ.2 2
  have hlo := Real.sqrt_le_sqrt (show 1-T^2≤1-ρ^2 by linarith)
  have hhi : Real.sqrt (1-ρ^2)≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
  exact ⟨mul_le_mul_of_nonneg_left hlo hr,(mul_le_mul_of_nonneg_left hhi hr).trans_eq (mul_one r)⟩

omit [MeasurableSpace X] in
lemma DirectCenter.radius_pos {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 < r) (hT0 : 0≤T) (hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) : 0 < r' := by
  have ht : 0<1-T^2 := by nlinarith
  exact lt_of_lt_of_le (mul_pos hr (Real.sqrt_pos.mpr ht)) (hb.radius hr.le hT0 hT1).1

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma compileTerms_equivariant (D : ℝ) (k : ℕ) (a c : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (u : (i : Fin k) → Fin (C i).slots → ℝ) (v : (i : Fin k) → Fin (M i).slots → ℝ)
    (w : Fin E.slots → ℝ) (t : ℝ) (f : X → X) (Δ : Point d)
    (hC : ∀i,(C i).compile.Equivariant (moveSeed f (u i) Δ) (fun y => y+c i • Δ))
    (hM : ∀i,((M i).program.seedMap (fun z => (z.1,(M i).damping D z.2))
      (measurable_fst.prodMk (((M i).measurable_damping D).comp measurable_snd))).Equivariant
      (moveSeed (fun y => y+c i • Δ) (v i) Δ) id)
    (hE : E.compile.Equivariant (moveSeed f w Δ) (fun y => y+t • Δ)) :
    (compileTerms D k a C M E).compile.Equivariant
      (moveSeed f (compileTermsShift D k a C M E u v w) Δ) (fun y => y+t • Δ) := by
  induction k with
  | zero => exact hE
  | succ k ih =>
    exact add_equivariant (a 0) (C 0) _ (M 0).program _ _ f Δ (u 0) (v 0) _ (c 0) t
      (hC 0) (hM 0) (ih _ _ _ _ _ _ (fun i => hC i.succ) (fun i => hM i.succ))

lemma compileTermsShift_energy (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (u : (i : Fin k) → Fin (C i).slots → ℝ) (v : (i : Fin k) → Fin (M i).slots → ℝ)
    (w : Fin E.slots → ℝ) :
    (∑j,compileTermsShift D k a C M E u v w j^2)=
      (∑j,w j^2)+∑i,((∑j,u i j^2)+(∑j,v i j^2)) := by
  induction k with
  | zero =>
    change (∑j,w j^2)=(∑j,w j^2)+∑i : Fin 0,_
    simp
  | succ k ih =>
    change (∑j : Fin ((C 0).slots+((M 0).slots+(compileTerms D k (fun i => a i.succ)
      (fun i => C i.succ) (fun i => M i.succ) E).slots)),
      (Fin.append (u 0) (Fin.append (v 0) (compileTermsShift D k (fun i => a i.succ)
        (fun i => C i.succ) (fun i => M i.succ) E (fun i => u i.succ) (fun i => v i.succ) w)) j)^2)=_
    simp only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,ih,Fin.sum_univ_succ]
    ring

theorem compileDeclared_equivariant (D A : ℝ) (hD : 0<D)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hM : ∀r τ,P r τ → ∀Δ,(M r τ).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (M r τ).shift Δ) id)
    (f : Point d → X → X) (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hp : DriftValid f E p)
    (hready : ShiftReady D A P E n) :
    ∀Δ,(compileDeclared D A M E n).compile.Equivariant
      (moveSeed (f Δ) (compileDeclaredShift D A M E n p) Δ) (fun y => y+p.root E • Δ) := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro Δ
    apply compileTerms_equivariant
    · intro i
      exact ih i (r i/(2*D)) (p.2 i) (hp.2 i) (hready i).2.2 Δ
    · intro i
      exact transformed_mean_equivariant (M (r i) (declaredNoise n A)).program
        (hready i).1 _ _
        ((normalized_shift_bound hD _ (hv _ _ (hready i).2.1)).trans_lt (by norm_num))
        (hM _ _ (hready i).2.1) ((p.2 i).root (C i)) Δ
    · exact noise_equivariant b hb _ p.1 (f Δ) Δ (hp.1 Δ)
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Cost
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclared_size (D A : ℝ) (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (S Q : ℕ) (hM : ∀r τ,P r τ → (M r τ).slots≤S ∧ (M r τ).calls≤Q)
    (E : MeanTree X d) (n : ℝ) (hready : ShiftReady D A P E n) :
    (compileDeclared D A M E n).slots≤1+cost E*(S+1) ∧
      (compileDeclared D A M E n).calls ≤ cost E*Q := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hc (i) := ih i (r i/(2*D)) (hready i).2.2
    have hm (i) := hM (r i) (declaredNoise n A) (hready i).2.1
    constructor
    · simp only [compileDeclared,slots_compileTerms,Expression.slots,cost]
      apply Nat.add_le_add_left
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).1
      have h₂ := (hm i).1
      nlinarith
    · simp only [calls_compileDeclared,cost,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).2
      have h₂ := (hm i).2
      nlinarith

theorem compileDeclaredShift_energy_bound {D A R B : ℝ} (hD : 0<D) (_hR : 0≤R) (hB : 0≤B)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hBv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤B)
    (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hready : ShiftReady D A P E n) (hg : DriftBound R E p) :
    (∑j,compileDeclaredShift D A M E n p j^2)≤(cost E:ℝ)*(4*R^2*B) := by
  induction E generalizing n with | node k b hb a r C ih =>
    change (∑j,compileTermsShift D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun i => compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)))
      (fun _ => 0) j^2)≤_
    rw [compileTermsShift_energy]
    simp only [zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,zero_add,cost,Nat.cast_sum,Nat.cast_add,Nat.cast_one,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hc := ih i (r i/(2*D)) (p.2 i) (hready i).2.2 (hg i).2
    have hi := inverse_shift_energy (fun j => (M (r i) (declaredNoise n A)).shift j/(2*D))
      (M (r i) (declaredNoise n A)).shift (normalized_shift_bound hD _ (hv _ _ (hready i).2.1))
      (((p.2 i).root (C i))/(r i))
    have hs := hBv _ _ (hready i).2.1
    have hh : (((p.2 i).root (C i))/(r i))^2≤R^2 := by
      have hb := pow_le_pow_left₀ (abs_nonneg _) (hg i).1 2
      simpa only [sq_abs] using hb
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4)) hB
    have hv' := mul_le_mul_of_nonneg_left hs (show 0≤4*(((p.2 i).root (C i))/(r i))^2 by positivity)
    change (∑j,compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i) j^2)+
      (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)) j^2)≤_
    change (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)) j^2)≤_ at hi
    nlinarith
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompileDeclaredRootShift
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_equivariant (D A Af : ℝ) (hD : 0<D)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ D^2)
    (hM : ∀s r τ,P s r τ → ∀Δ,(M s r τ).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (M s r τ).shift Δ) id)
    (f : Point d → X → X) (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hp : DriftValid f E p) (hr : RootShiftReady D A Af (P true) (P false) E n) :
    ∀Δ,(compileDeclaredRoot D A Af (M true) (M false) E n).compile.Equivariant
      (moveSeed (f Δ) (compileDeclaredRootShift D A Af (M true) (M false) E n p) Δ)
      (fun y => y+p.root E • Δ) := by
  cases E with | node k b hb a r C =>
    intro Δ
    apply compileTerms_equivariant
    · intro i
      exact compileDeclared_equivariant D A hD (P false) (M false) (hv false) (hM false)
        f (C i) (r i/(2*D)) (p.2 i) (hp.2 i) (hr i).2.2 Δ
    · intro i
      exact transformed_mean_equivariant (M true (r i) (declaredNoise n Af)).program
        (hr i).1 _ _ ((normalized_shift_bound hD _ (hv _ _ _ (hr i).2.1)).trans_lt (by norm_num))
        (hM _ _ _ (hr i).2.1) ((p.2 i).root (C i)) Δ
    · exact noise_equivariant b hb _ p.1 (f Δ) Δ (hp.1 Δ)

theorem compileDeclaredRoot_size (D A Af : ℝ)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (S Q : ℕ) (hM : ∀s r τ,P s r τ → (M s r τ).slots ≤ S ∧ (M s r τ).calls ≤ Q)
    (E : MeanTree X d) (n : ℝ) (hr : RootShiftReady D A Af (P true) (P false) E n) :
    (compileDeclaredRoot D A Af (M true) (M false) E n).slots ≤ 1+cost E*(S+1) ∧
      (compileDeclaredRoot D A Af (M true) (M false) E n).calls ≤ cost E*Q := by
  cases E with | node k b hb a r C =>
    have hc (i) := compileDeclared_size D A (P false) (M false) S Q (hM false) (C i) (r i/(2*D)) (hr i).2.2
    have hm (i) := hM true (r i) (declaredNoise n Af) (hr i).2.1
    constructor
    · simp only [compileDeclaredRoot,slots_compileTerms,Expression.slots,cost]
      apply Nat.add_le_add_left
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).1
      have h₂ := (hm i).1
      nlinarith
    · simp only [compileDeclaredRoot,calls_compileTerms,Expression.calls,zero_add,cost,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).2
      have h₂ := (hm i).2
      nlinarith

theorem compileDeclaredRootShift_energy_bound {D A Af R B : ℝ} (hD : 0<D) (hR : 0≤R) (hB : 0≤B)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ D^2)
    (hBv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ B)
    (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hr : RootShiftReady D A Af (P true) (P false) E n) (hg : DriftBound R E p) :
    (∑j,compileDeclaredRootShift D A Af (M true) (M false) E n p j^2) ≤ (cost E:ℝ)*(4*R^2*B) := by
  cases E with | node k b hb a r C =>
    change (∑j,compileTermsShift D k a (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun i => compileDeclaredShift D A (M false) (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)))
      (fun _ => 0) j^2) ≤ _
    rw [compileTermsShift_energy]
    simp only [zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,zero_add,cost,Nat.cast_sum,Nat.cast_add,Nat.cast_one,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hc := compileDeclaredShift_energy_bound hD hR hB (P false) (M false) (hv false) (hBv false)
      (C i) (r i/(2*D)) (p.2 i) (hr i).2.2 (hg i).2
    have hi := inverse_shift_energy (fun j => (M true (r i) (declaredNoise n Af)).shift j/(2*D))
      (M true (r i) (declaredNoise n Af)).shift (normalized_shift_bound hD _ (hv _ _ _ (hr i).2.1))
      (((p.2 i).root (C i))/(r i))
    have hs := hBv _ _ _ (hr i).2.1
    have hh : (((p.2 i).root (C i))/(r i))^2 ≤ R^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hg i).1 2
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4)) hB
    have hv' := mul_le_mul_of_nonneg_left hs (show 0≤4*(((p.2 i).root (C i))/(r i))^2 by positivity)
    change (∑j,compileDeclaredShift D A (M false) (C i) (r i/(2*D)) (p.2 i) j^2)+
      (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)) j^2) ≤ _
    change (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)) j^2) ≤ _ at hi
    nlinarith
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_RoutineKind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

theorem routine_induction {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (P : RoutineLabel → Prop) (hbase : ∀L,L.terminal → P L)
    (hstep : ∀L,¬L.terminal → (∀C,RoutineStep t L C → P C) → P L) : ∀L,P L := by
  intro L
  induction hn : L.rank t using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hL : L.terminal
    · exact hbase L hL
    · apply hstep L hL
      intro C hc
      exact ih _ (hn ▸ hc.rank_lt ht hs hL) C rfl
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_ReservedProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

namespace ReservedProgram

lemma full_run (S : ReservedProgram d) (V : Point d → ℝ)
    (x : Point d) (g : Fin (S.slots+1) → Point d) :
    S.full.program.run V (x,g)=
      S.pre.run V (x,fun i => g (Fin.castAdd 1 i))+S.reserve • g (Fin.natAdd S.slots 0) := by
  change ((S.pre.seedMap (fun z : Point d × (Fin (S.slots+1) → Point d) =>
    (z.1,fun i => z.2 (Fin.castAdd 1 i))) (by fun_prop)).map
    (fun z => z.2+S.reserve • z.1.2 (Fin.natAdd S.slots 0)) (by fun_prop)).run V (x,g)=_
  rw [Program.map_run,Program.seedMap_run]

lemma full_equivariant (S : ReservedProgram d) (r c : ℝ) (Δ : Point d)
    (hS : S.pre.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) (fun y => y-Δ)) :
    S.full.program.Equivariant
      (moveSeed (fun x => x+r • Δ) (S.extraShift c) Δ)
      (fun y => y-Δ+(S.reserve*c) • Δ) := by
  dsimp only [full]
  apply Program.Equivariant.map
    (hS.seedMap _ (by fun_prop) _ ?_) _ (by fun_prop) _
  · intro z y
    simp only [moveSeed,extraShift,shiftSlots,Fin.append_right]
    simp only [smul_add,smul_smul]
    abel
  · intro z
    apply Prod.ext
    · rfl
    · funext i
      simp [moveSeed,extraShift,shiftSlots]

lemma extraShift_energy (S : ReservedProgram d) (c : ℝ) :
    (∑i,S.extraShift c i^2)=(∑i,S.shift i^2)+c^2 := by
  simp [extraShift,Fin.sum_univ_add]
end ReservedProgram

lemma meanParent_shift_energy (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) :
    (∑i,(meanParent S E u v T).shift i^2)=(∑i,u i^2)+(∑i,v i^2) := by
  change (∑i : Fin (S.slots+(1+E.slots)), (Fin.append u (Fin.append (fun _ => 0) v)) i^2)=_
  simp [Fin.sum_univ_add]

lemma sampleParent_shift_energy (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η : ℝ) :
    (∑i,(sampleParent E v T η).shift i^2)=T^2+(∑i,v i^2) := by
  change (∑i : Fin (1+E.slots), (Fin.append (fun _ => -T) v) i^2)=_
  simp [Fin.sum_univ_add]

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

lemma sourceCorrelation_eventually {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,0 < sourceCorrelation a d ∧ sourceCorrelation a d<1 ∧
      ((d:ℝ)^(-a))^2=1-(sourceCorrelation a d)^2 := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with d hd hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  change (d:ℝ)^(-a)<1 at hd
  have hp := Real.rpow_pos_of_pos hd0 (-a)
  have hs : 0<1-((d:ℝ)^(-a))^2 := by nlinarith
  have hsq := Real.sq_sqrt hs.le
  refine ⟨Real.sqrt_pos.mpr hs,?_,?_⟩
  · change Real.sqrt _<1
    nlinarith [Real.sqrt_nonneg (1-((d:ℝ)^(-a))^2)]
  · change ((d:ℝ)^(-a))^2=1-Real.sqrt (1-((d:ℝ)^(-a))^2)^2
    linarith

lemma sourceCorrelation_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (sourceCorrelation a) atTop (nhds 1) := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  change Tendsto (fun d : ℕ => Real.sqrt (1-((d:ℝ)^(-a))^2)) atTop (nhds 1)
  simpa only [Function.comp_def,zero_pow (by omega : (2:ℕ)≠0),sub_zero,Real.sqrt_one] using
    ((tendsto_const_nhds (x:=(1:ℝ))).sub (ht.pow 2)).sqrt

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitParameters
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature
open scoped Classical

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

lemma meanDrift_spec (r σ : ℝ) (hr : 0 < r) :
    DriftValid (meanInputMove r C.T) (C.meanTree (d:=d) r σ) (C.meanDrift r σ hr) ∧
      (C.meanDrift (d:=d) r σ hr).root _=0 ∧ DriftBound 3 _ (C.meanDrift (d:=d) r σ hr) :=
  (literalMean_drift hr C.T_lower C.T_upper C.h_pos C.v_nonneg C.angle_small C.angle_bound C.meanEndpoint).choose_spec

end CircuitParameters

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SampleParentEquivariant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

lemma sampleParent_equivariant (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (r T η : ℝ) (Δ : Point d)
    (hE : E.compile.Equivariant
      (moveSeed (fun z => (z.1+r • Δ,z.2-T • Δ)) v Δ) (fun y => y-Δ)) :
    (sampleParent E v T η).pre.Equivariant
      (moveSeed (fun x => x+r • Δ) (sampleParent E v T η).shift Δ) (fun y => y-Δ) := by
  dsimp only [sampleParent]
  apply hE.seedMap _ (by fun_prop) _
  intro z
  apply Prod.ext
  · simp [moveSeed,shiftSlots,Fin.append_left,sub_eq_add_neg]
  · funext i
    simp [moveSeed,shiftSlots,Fin.append_right]

lemma meanParent_equivariant (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) {r T : ℝ} (hT : T≠0) (Δ : Point d)
    (hS : S.program.Equivariant (moveSeed (fun x => x+r • Δ) u Δ)
      (fun y => y-(T⁻¹)^2 • Δ))
    (hE : E.compile.Equivariant
      (moveSeed (fun z => (z.1+r • Δ,(z.2.1-T⁻¹ • Δ,z.2.2))) v Δ) id) :
    (meanParent S E u v T).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (meanParent S E u v T).shift Δ) id := by
  dsimp only [meanParent]
  apply Program.Equivariant.seq (hS.seedMap _ (by unfold leftBlock; fun_prop) _ ?_)
  · apply hE.seedMap _ (by unfold middleBlock rightBlock; fun_prop) _
    intro z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · simp only [moveSeed,smul_sub,smul_smul]
          congr 1
          congr 1
          field_simp
        · simp [moveSeed,shiftSlots,middleBlock]
    · funext i
      simp [moveSeed,shiftSlots,rightBlock]
  · intro z
    apply Prod.ext
    · rfl
    · funext i
      simp [moveSeed,shiftSlots,leftBlock]

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling Expression
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma terminalReservedProgram_equivariant (r η : ℝ) (Δ : Point d) :
    (terminalReservedProgram d r η).pre.Equivariant
      (moveSeed (fun x => x+r • Δ) (terminalReservedProgram d r η).shift Δ) (fun y => y-Δ) := by
  change (oneQuery (fun p : Point d × (Fin 2 → Point d) => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop)).Equivariant _ _
  apply Program.oneQuery_equivariant
  · intro p
    simp [moveSeed,shiftSlots,terminalReservedProgram,SeedCompiler.terminalShift]
    module
  · intro p z
    simp [moveSeed,shiftSlots,terminalReservedProgram,SeedCompiler.terminalShift]
    module

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMeanEquivariant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.SeedCompiler
open OracleCompiler OracleCompiler.Expression

lemma terminalMean_equivariant {d : ℕ} (r σ : ℝ) (Δ : Point d) :
    (terminalMean d r σ).Equivariant
      (moveSeed (fun x => x+r • Δ) (terminalShift 1) Δ) id := by
  apply Program.oneQuery_equivariant
  · intro z
    exact terminalQuery_invariant _ _ _ _
  · intro z a
    simp [moveSeed,shiftSlots,terminalShift]

end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ScalarPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma cost_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    (f : ℕ → ℕ) (a₀ : ℕ) (hφ : ∀i E,cost (φ i E)=f (cost E))
    (ha : ∀i,cost (a i)=a₀) (N : ℕ) (i : I) :
    cost (picard w φ a N i)=scalarPicard (Fintype.card I) f a₀ N := by
  induction N generalizing i with
  | zero => exact ha i
  | succ N ih => simp only [picard,cost_add,cost_sumFamily,cost_scale,hφ,ih,ha,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,scalarPicard]

lemma cost_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) (f : ℕ × ℕ → ℕ × ℕ)
    (hφ : ∀p,(cost (φ p).1,cost (φ p).2)=f (cost p.1,cost p.2)) (N : ℕ) (i : I) :
    (cost (pairPicard w φ a N i).1,cost (pairPicard w φ a N i).2)=
      vectorPicard (Fintype.card I) f (cost a.1,cost a.2) N := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    have hp (j : I) := hφ (pairPicard w φ a N j)
    simp_rw [ih] at hp
    have hp₁ j := congrArg Prod.fst (hp j)
    have hp₂ j := congrArg Prod.snd (hp j)
    dsimp only at hp₁ hp₂
    apply Prod.ext <;> simp only [pairPicard,cost_add,cost_sumFamily,cost_scale,
      hp₁,hp₂,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,vectorPicard]

lemma cost_probability (r T h : ℝ) (n N : ℕ) (s i : ProbabilityNode T h n) (x y : MeanTree X d) :
    cost (probability r T h n N s x y i)=flowWork (Fintype.card (ProbabilityNode T h n)) N (cost x) (cost y) := by
  exact cost_picard _ _ _ _ _ (fun _ _ => by simp) (fun _ => rfl) N i

lemma cost_forward (r T h : ℝ) (n N : ℕ) (i : ProbabilityNode T h n) (x y : MeanTree X d) :
    cost (forward r T h n N x y i)=flowWork (Fintype.card (ProbabilityNode T h n)) N (cost x) (cost y) := by
  exact cost_picard _ _ _ _ _ (fun _ _ => by simp) (fun _ => rfl) N i

lemma cost_harmonic (r ρ θ : ℝ) (n N : ℕ) (i : Fin (n+1)) (x y g : MeanTree X d) :
    cost (harmonic r ρ θ n N x y g i)=flowWork (n+1) N (cost x) (cost y+cost g) := by
  simpa only [Fintype.card_fin,harmonic,flowWork] using cost_picard (harmonicWeight n θ) _ _ (fun z => 1+cost x+z)
    (cost y+cost g) (fun _ _ => by simp) (fun _ => by simp) N i

lemma cost_kernelCorrection (r T h θ : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) :
    cost (kernelCorrection r T h θ n N s e x y g)=
      kernelWork (Fintype.card (ProbabilityNode T h n)) (n+1) N (cost x) (cost y) (cost g) := by
  simp only [kernelCorrection,cost_sumFamily,cost_scale,cost_conditional,cost_probability,
    cost_harmonic,Finset.sum_const,Finset.card_univ,smul_eq_mul,kernelWork]

lemma cost_kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) :
    cost (kernelQuadrature r T h ψ n m N e w x y g)=
      Fintype.card (ProbabilityNode T h n)*(m+1)*
        kernelWork (Fintype.card (ProbabilityNode T h n)) (n+1) N (cost x) (cost y) (cost g) := by
  simp only [kernelQuadrature,kernelAction,cost_sumFamily,cost_scale,cost_kernelCorrection,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_assoc]

lemma cost_velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) :
    (cost (velocity r T h ψ s n m N e x p).1,cost (velocity r T h ψ s n m N e x p).2)=
      velocityWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N (cost x) (cost p.1,cost p.2) := by
  simp only [velocity,cost_scale,cost_add,cost_conditional,cost_mean,cost_kernelQuadrature,velocityWork]
  congr 1
  omega

lemma cost_meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (x y g : MeanTree X d) :
    cost (meanCircuit r T h ψ s n m N nc Nc e x y g)=
      meanWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N nc Nc (cost x) (cost y) (cost g) := by
  have hp (i : Fin (nc+1)) := cost_pairPicard (centeringWeight nc) _ (y,g)
    _ (fun p => cost_velocity r T h ψ s n m N e x p) Nc i
  have hy (i : Fin (nc+1)) := congrArg Prod.fst (hp i)
  simp only [Fintype.card_fin] at hy
  simp only [meanCircuit,cost_add,cost_scale,cost_sumFamily,cost_conditional,centeringStates,hy,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,meanWork]

lemma cost_literalMean (r T h ψ σ : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) :
    cost (literalMean (d:=d) r T h ψ σ n m N nc Nc e)=
      meanWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N nc Nc 0 0 0 := by
  simp only [literalMean,cost_meanCircuit,cost_anchor]

lemma cost_literalSample (r T h : ℝ) (n N : ℕ) (e : ProbabilityNode T h n) :
    cost (literalSample (d:=d) r T h n N e)=flowWork (Fintype.card (ProbabilityNode T h n)) N 0 0 := by
  simp only [literalSample,cost_scale,cost_forward,cost_anchor]
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeanTree OracleCompiler MeasureTheory OracleCompiler.Expression OracleCompiler.Program
open scoped Classical BigOperators

variable {d : ℕ}

namespace MeanTree
lemma shiftReady_of_positive {X : Type*} [MeasurableSpace X] (D A : ℝ)
    (E : MeanTree X d) (hE : centers (fun r _ => 0 < r) E) (n : ℝ) :
    ShiftReady D A (fun r _ => 0 < r) E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro i
    exact ⟨(hE i).1.ne',(hE i).1,ih i (hE i).2 _⟩
lemma rootShiftReady_of_positive {X : Type*} [MeasurableSpace X] (D A Af : ℝ)
    (E : MeanTree X d) (hE : centers (fun r _ => 0 < r) E) (n : ℝ) :
    RootShiftReady D A Af (fun r _ => 0 < r) (fun r _ => 0 < r) E n := by
  cases E with | node k b hb a r C =>
    intro i
    exact ⟨(hE i).1.ne',(hE i).1,shiftReady_of_positive D A _ (hE i).2 _⟩
end MeanTree

namespace OracleCompiler

lemma MeanBudget.mono {B C : ℕ} {r : ℝ} {S : SeedProgram d} (h : MeanBudget B r S) (hBC : B≤C) : MeanBudget C r S :=
  ⟨h.slots.trans hBC,h.calls.trans hBC,h.energy.trans (by exact_mod_cast hBC),h.equiv⟩
lemma SampleBudget.mono {B C : ℕ} {r η : ℝ} {S : ReservedProgram d} (h : SampleBudget B r η S) (hBC : B≤C) : SampleBudget C r η S :=
  ⟨h.slots.trans hBC,h.calls.trans hBC,h.energy.trans (by exact_mod_cast hBC),h.equiv,h.reserve⟩

lemma terminalMeanProgram_budget (r σ : ℝ) : MeanBudget 2 r (terminalMeanProgram d r σ) := by
  refine ⟨le_rfl,by norm_num [terminalMeanProgram],?_,fun Δ => SeedCompiler.terminalMean_equivariant r σ Δ⟩
  change (∑j : Fin 2,(if j=0 then (-1:ℝ) else 0)^2)≤2
  norm_num [Fin.sum_univ_two]
lemma terminalReservedProgram_budget (r η : ℝ) : SampleBudget 2 r η (terminalReservedProgram d r η) := by
  refine ⟨le_rfl,by norm_num [terminalReservedProgram],?_,fun Δ => terminalReservedProgram_equivariant r η Δ,rfl⟩
  change (∑j : Fin 2,(if j=0 then (-1:ℝ) else 0)^2)≤2
  norm_num [Fin.sum_univ_two]

namespace CircuitParameters
variable (C : CircuitParameters)
lemma mean_positive {r σ : ℝ} (hr : 0 < r) : centers (fun r _ => 0 < r) (C.meanTree (d:=d) r σ) := by
  exact centers_mono _ (fun _ _ h => DirectCenter.radius_pos hr (by linarith [C.T_lower]) C.T_upper h)
    (literalMean_geometry (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
lemma sample_positive {r η : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1) :
    centers (fun r _ => 0 < r) (C.sampleTree (d:=d) r η hη hη1) := by
  have ht := sampleCorrelation_properties hη hη1
  exact centers_mono _ (fun _ _ h => DirectCenter.radius_pos hr (by linarith [ht.1]) ht.2.1 h)
    (literalSample_geometry (Nat.succ_pos C.n) (by linarith [ht.1]) ht.2.1 C.h_pos (C.sampleEndpoint η hη hη1)).2
lemma sampleDrift_spec (r η : ℝ) (hr : 0 < r) (hη : 0<η) (hη1 : η≤1) :
    DriftValid (sampleInputMove r (sampleCorrelation η)) (C.sampleTree (d:=d) r η hη hη1) (C.sampleDrift r η hr hη hη1) ∧
      (C.sampleDrift (d:=d) r η hr hη hη1).root _ = -1 ∧ DriftBound 2 _ (C.sampleDrift (d:=d) r η hr hη hη1) := by
  exact (literalSample_drift hr (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.sampleEndpoint η hη hη1)).choose_spec

lemma sampleFrom_budget {B c : ℕ} (hB : 1≤B) (hD : 0<C.D) (hBD : (B:ℝ)≤C.D^2)
    (Mf Mi : ℝ → ℝ → SeedProgram d)
    (hM : ∀(s : Bool) r σ,0 < r → MeanBudget B r ((if s then Mf else Mi) r σ))
    (r η : ℝ)
    (hc : 0 < r → ∀hη : 0<η, ∀hη1 : η≤1,cost (C.sampleTree (d:=d) r η hη hη1) ≤ c) :
    SampleBudget ((40*c+40)*B) r η (C.sampleFrom Mf Mi r η) := by
  by_cases hv : 0 < r ∧ 0<η ∧ η≤1
  · rw [sampleFrom,dite_eq_left hv]
    let E := C.sampleTree (d:=d) r η hv.2.1 hv.2.2
    let p := C.sampleDrift (d:=d) r η hv.1 hv.2.1 hv.2.2
    let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
    have hready := rootShiftReady_of_positive C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) E (C.sample_positive hv.1 hv.2.1 hv.2.2) (η/Real.sqrt 2)
    have hvD : ∀s r σ,0 < r → (∑j,(M s r σ).shift j^2)≤C.D^2 := fun s r σ hr => (hM s r σ hr).energy.trans hBD
    have hsize := compileDeclaredRoot_size C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) (fun _ r _ => 0 < r) M B B
      (fun s r σ hr => ⟨(hM s r σ hr).slots,(hM s r σ hr).calls⟩) E _ hready
    have he := compileDeclaredRootShift_energy_bound hD (by norm_num : (0:ℝ)≤2)
      (by positivity : (0:ℝ)≤B) (fun _ r _ => 0 < r) M hvD (fun s r σ hr => (hM s r σ hr).energy)
      E _ p hready (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).2.2
    simp only [M,ite_true,ite_false,Bool.false_eq_true] at hsize he
    have hproot : p.root E = -1 := (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).2.1
    have hcost := hc hv.1 hv.2.1 hv.2.2
    have hc' : (cost E:ℝ) ≤ c := by exact_mod_cast hcost
    have hB' : (1:ℝ)≤B := by exact_mod_cast hB
    have ht := sampleCorrelation_properties hv.2.1 hv.2.2
    refine ⟨?_,?_,?_,?_,rfl⟩
    · change 1+(compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E _).slots≤_
      nlinarith [hsize.1]
    · change (compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E _).calls≤_
      nlinarith [hsize.2]
    · rw [sampleParent_shift_energy]
      have htsq : (sampleCorrelation η)^2≤1 := by nlinarith [ht.1,ht.2.1]
      push_cast
      change (∑j,compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E (η/Real.sqrt 2) p j^2)≤_ at he
      nlinarith
    · intro Δ
      apply sampleParent_equivariant
      have hh := compileDeclaredRoot_equivariant C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) hD (fun _ r _ => 0 < r) M hvD
        (fun s r σ hr => (hM s r σ hr).equiv) (sampleInputMove r (sampleCorrelation η)) E _ p
        (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).1 hready Δ
      rw [hproot] at hh
      have hout : (fun y : Point d => y+(-1:ℝ) • Δ)=(fun y=>y-Δ) := by
        funext y; simp [sub_eq_add_neg]
      rw [hout] at hh
      exact hh
  · rw [sampleFrom,dite_eq_right hv]
    exact (terminalReservedProgram_budget r η).mono (by nlinarith)
lemma meanFrom_budget {B c : ℕ} (hB : 1≤B) (hD : 0<C.D) (hBD : (B:ℝ)≤C.D^2)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (hM : ∀(s : Bool) r σ,0 < r → MeanBudget B r ((if s then Mf else Mi) r σ))
    (hS : ∀r,0 < r → SampleBudget B r (Real.sqrt (1-C.T^2)/C.T) (S r (Real.sqrt (1-C.T^2)/C.T)))
    (r σ : ℝ) (hc : cost (C.meanTree (d:=d) r σ) ≤ c) :
    MeanBudget ((40*c+40)*B) r (C.meanFrom Mf Mi S r σ) := by
  by_cases hr : 0 < r
  · rw [meanFrom,dite_eq_left hr]
    let E := C.meanTree (d:=d) r σ
    let p := C.meanDrift (d:=d) r σ hr
    let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
    let R := Real.sqrt (1-C.T^2)
    let anc := S r (R/C.T)
    have hs : SampleBudget B r (R/C.T) anc := hS r hr
    have hT : 0<C.T := by linarith [C.T_lower]
    have hT2 : 0≤1-C.T^2 := by nlinarith [C.T_upper]
    have hR : 0≤R := Real.sqrt_nonneg _
    have hR2 : R^2=1-C.T^2 := Real.sq_sqrt hT2
    have hR1 : R≤1 := by nlinarith [sq_nonneg C.T]
    have hRT : R/C.T≤2 := (div_le_iff₀ hT).mpr (by linarith [C.T_lower])
    have hsquare : (-2*R/C.T)^2≤16 := by
      have hn : 0≤R/C.T := div_nonneg hR hT.le
      rw [mul_div_assoc]
      nlinarith
    have hready := rootShiftReady_of_positive C.D (C.meanCenterBudget r σ) C.Af E (C.mean_positive hr) (Real.sqrt 3*σ/2)
    have hvD : ∀s r σ,0 < r → (∑j,(M s r σ).shift j^2)≤C.D^2 := fun s r σ hr => (hM s r σ hr).energy.trans hBD
    have hsize := compileDeclaredRoot_size C.D (C.meanCenterBudget r σ) C.Af (fun _ r _ => 0 < r) M B B
      (fun s r σ hr => ⟨(hM s r σ hr).slots,(hM s r σ hr).calls⟩) E _ hready
    have he := compileDeclaredRootShift_energy_bound hD (by norm_num : (0:ℝ)≤3)
      (by positivity : (0:ℝ)≤B) (fun _ r _ => 0 < r) M hvD (fun s r σ hr => (hM s r σ hr).energy)
      E _ p hready (C.meanDrift_spec r σ hr).2.2
    simp only [M,ite_true,ite_false,Bool.false_eq_true] at hsize he
    have hproot : p.root E = 0 := (C.meanDrift_spec r σ hr).2.1
    have hc' : (cost E:ℝ) ≤ c := by exact_mod_cast hc
    have hB' : (1:ℝ)≤B := by exact_mod_cast hB
    refine ⟨?_,?_,?_,?_⟩
    · change anc.slots+1+(1+(compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E _).slots)≤_
      nlinarith [hsize.1,hs.slots]
    · change anc.calls+(compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E _).calls≤_
      nlinarith [hsize.2,hs.calls]
    · change (∑j,(meanParent anc.full (compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2))
        (anc.extraShift (-2*R/C.T)) (compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p) C.T).shift j^2)≤_
      have henergy := meanParent_shift_energy anc.full (compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2))
        (anc.extraShift (-2*R/C.T)) (compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p) C.T
      change _ = _ at henergy
      rw [henergy]
      change (∑i : Fin (anc.slots+1),anc.extraShift (-2*R/C.T) i^2)+_≤_
      rw [ReservedProgram.extraShift_energy]
      push_cast
      change (∑j,compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p j^2)≤_ at he
      have ha := hs.energy
      change (∑j,anc.shift j^2)+(-2*R/C.T)^2+_≤_
      nlinarith
    · intro Δ
      apply meanParent_equivariant _ _ _ _ hT.ne'
      · have hx := anc.full_equivariant r (-2*R/C.T) Δ (hs.equiv Δ)
        have hid : (fun y : Point d => y-Δ+(anc.reserve*(-2*R/C.T)) • Δ)=
            (fun y => y-(C.T⁻¹)^2 • Δ) := by
          rw [hs.reserve]
          funext y
          have heq : 1-(R/C.T/2)*(-2*R/C.T)=(C.T⁻¹)^2 := by
            field_simp
            nlinarith [hR2]
          calc
            _ = y-(1-(R/C.T/2)*(-2*R/C.T)) • Δ := by module
            _ = _ := by rw [heq]
        rw [hid] at hx
        exact hx
      · have hh := compileDeclaredRoot_equivariant C.D (C.meanCenterBudget r σ) C.Af hD (fun _ r _ => 0 < r) M hvD
          (fun s r σ hr => (hM s r σ hr).equiv) (meanInputMove r C.T) E _ p
          (C.meanDrift_spec r σ hr).1 hready Δ
        rw [hproot] at hh
        have hout : (fun y : Point d => y+(0:ℝ) • Δ)=id := by
          funext y; simp
        rw [hout] at hh
        exact hh
  · rw [meanFrom,dite_eq_right hr]
    exact (terminalMeanProgram_budget r σ).mono (by nlinarith)
end CircuitParameters
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_VelocityWorkCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open scoped BigOperators

lemma flowWork_bound (p N y : ℕ) : flowWork p N 0 y+1≤(y+1)*(p+1)^N := by
  induction N with
  | zero => simp [flowWork,scalarPicard]
  | succ N ih =>
    have hp : 1≤(p+1)^N := Nat.one_le_pow N _ (by omega)
    have hy : y+1≤(y+1)*(p+1)^N := by nlinarith
    have he := Nat.mul_le_mul_left p ih
    change y+p*(1+0+flowWork p N 0 y)+1≤_
    rw [pow_succ]
    nlinarith

lemma kernelWork_bound (p q N y g : ℕ) :
    kernelWork p q N 0 y g+1≤(q+1)^N*(p+1)^(2*N+1)*(y+g+1) := by
  let U := flowWork p N 0 y
  let V := flowWork q N 0 (U+g)
  let W := flowWork p N 0 V
  have hP : 1≤(p+1)^N := Nat.one_le_pow N _ (by omega)
  have hQ : 1≤(q+1)^N := Nat.one_le_pow N _ (by omega)
  have hU : U+g+1≤(y+g+1)*(p+1)^N := by
    have he := flowWork_bound p N y
    change U+1≤_ at he
    nlinarith
  have hV : V+1≤(y+g+1)*(p+1)^N*(q+1)^N :=
    (flowWork_bound q N (U+g)).trans (Nat.mul_le_mul_right _ hU)
  have hW : W+1≤(y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N :=
    (flowWork_bound p N V).trans (Nat.mul_le_mul_right _ hV)
  have hone : 1≤(y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_left p hW
  change p*(1+0+W)+1≤_
  have he : (q+1)^N*(p+1)^(2*N+1)*(y+g+1)=
      (p+1)*((y+g+1)*(p+1)^N*(q+1)^N*(p+1)^N) := by
    rw [pow_add,pow_one,show 2*N=N+N by omega,pow_add]
    ring
  rw [he]
  nlinarith

lemma velocityWork_bound (p q m N : ℕ) (z : ℕ × ℕ) :
    (velocityWork p q m N 0 z).1+(velocityWork p q m N 0 z).2+1≤
      velocityWorkCoefficient q m N*(p+1)^(2*N+2)*(z.1+z.2+1) := by
  have hk := kernelWork_bound p q N z.1 z.2
  have hp : 1≤(p+1)^(2*N+1) := Nat.one_le_pow _ _ (by omega)
  have hh : kernelWork p q N 0 z.1 z.2≤(q+1)^N*(p+1)^(2*N+1)*(z.1+z.2+1) := by omega
  have hmul := Nat.mul_le_mul_left (p*(m+1)) hh
  have hg : (z.1+z.2+1)≤(p+1)^(2*N+1)*(z.1+z.2+1) := by nlinarith
  have hc : p*(m+1)*(q+1)^N+3≤(4+(m+1)*(q+1)^N)*(p+1) := by nlinarith
  have hh' := Nat.mul_le_mul_right ((p+1)^(2*N+1)*(z.1+z.2+1)) hc
  have hz : z.1+3≤3*(p+1)^(2*N+1)*(z.1+z.2+1) := by nlinarith
  change p*(m+1)*kernelWork p q N 0 z.1 z.2+(2+2*0+z.1)+1≤_
  unfold velocityWorkCoefficient
  rw [show 2*N+2=(2*N+1)+1 by omega,pow_add,pow_one]
  nlinarith

lemma vectorPicard_zero_bound (p q m N k : ℕ) (hk : 1≤k) (Nc : ℕ) :
    (vectorPicard k (velocityWork p q m N 0) (0,0) Nc).1+
      (vectorPicard k (velocityWork p q m N 0) (0,0) Nc).2+1≤
      (k*velocityWorkCoefficient q m N)^Nc*(p+1)^(Nc*(2*N+2)) := by
  induction Nc with
  | zero => simp [vectorPicard]
  | succ Nc ih =>
    let z := vectorPicard k (velocityWork p q m N 0) (0,0) Nc
    have hv := velocityWork_bound p q m N z
    have hm := Nat.mul_le_mul_left (k*velocityWorkCoefficient q m N*(p+1)^(2*N+2)) ih
    have hx := Nat.mul_le_mul_left k hv
    change 0+k*(velocityWork p q m N 0 z).1+(0+k*(velocityWork p q m N 0 z).2)+1≤_
    rw [pow_succ,Nat.succ_mul,pow_add]
    change z.1+z.2+1≤_ at ih
    nlinarith

lemma meanWork_polynomial (p q m N nc Nc : ℕ) :
    meanWork p q m N nc Nc 0 0 0≤
      (nc+1)*((nc+1)*velocityWorkCoefficient q m N)^Nc*(p+1)^(Nc*(2*N+2)) := by
  have he := vectorPicard_zero_bound p q m N (nc+1) (by omega) Nc
  have hm := Nat.mul_le_mul_left (nc+1) he
  unfold meanWork
  nlinarith

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_LogMeshCountRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology

lemma logMeshCount_rate {T : ℕ → ℝ} {b : ℝ} (hb : 0≤b)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hL : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => (logMeshCount (T d) ((d:ℝ)^(-b)):ℝ)) (-b) := by
  have hr := hL.mul (LogPowerRate.inv_power b)
  simp only [zero_add] at hr
  apply LogPowerRate.of_le (hr.add ((LogPowerRate.const 1).mono (by linarith)))
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [hT0,hT1,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [div_eq_mul_inv] using (logMeshCount_bound hd0 hd1 (Real.rpow_pos_of_pos hp (-b))).le

lemma probabilityNode_card_rate {T : ℕ → ℝ} {b : ℝ} (hb : 0≤b) (n : ℕ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hL : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => (Fintype.card (ProbabilityNode (T d) ((d:ℝ)^(-b)) n):ℝ)) (-b) := by
  simpa only [probabilityNode_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    (logMeshCount_rate hb hT0 hT1 hL).mul_const ((n:ℝ)+1)

theorem meanWork_rate {p : ℕ → ℕ} {b : ℝ} (hb : 0≤b)
    (hp : LogPowerRate (fun d => (p d:ℝ)) (-b)) (q m N nc Nc : ℕ) :
    LogPowerRate (fun d => (meanWork (p d) q m N nc Nc 0 0 0:ℝ)) (-((Nc*(2*N+2):ℕ):ℝ)*b) := by
  have hr := (hp.add ((LogPowerRate.const 1).mono (by linarith))).pow (Nc*(2*N+2))
  have he := hr.const_mul (((nc+1)*((nc+1)*velocityWorkCoefficient q m N)^Nc:ℕ):ℝ)
  simp only [mul_neg,neg_mul] at he ⊢
  apply LogPowerRate.of_le he
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro d
    exact_mod_cast meanWork_polynomial (p d) q m N nc Nc

lemma routineBudget_rate {c : ℕ → ℕ} {a : ℝ} (ha : 0≤a)
    (hc : LogPowerRate (fun d => (c d:ℝ)) (-a)) (rank : ℕ) :
    LogPowerRate (fun d => ((2*(40*c d+40)^rank:ℕ):ℝ)) (-(rank:ℝ)*a) := by
  have he := (((hc.const_mul 40).add ((LogPowerRate.const 40).mono (by linarith))).pow rank).const_mul 2
  simp only [mul_neg,neg_mul] at he ⊢
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using he
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

lemma sampleCorrelation_antitone {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    sampleCorrelation b≤ sampleCorrelation a := by
  unfold sampleCorrelation
  apply (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))).mpr
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma logMeshCount_mono {T U h : ℝ} (hT : T≤U) (hU : U<1) (hh : 0<h) :
    logMeshCount T h≤logMeshCount U h := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ hh.le
  unfold logMeshLength
  have he := Real.log_le_log (by linarith : 0<1-U) (by linarith : 1-U≤1-T)
  linarith

lemma sampleCorrelation_radius_lower {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    η/4≤Real.sqrt (1-(sampleCorrelation η)^2) := by
  have hp := sampleCorrelation_properties hη hη1
  have ht : 0 < sampleCorrelation η := by linarith
  have he : Real.sqrt (1-(sampleCorrelation η)^2)=sampleCorrelation η*(η/2) := by
    have h := congrArg (fun z : ℝ => sampleCorrelation η*z) hp.2.2
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using h
  rw [he]
  nlinarith

lemma logMeshLength_sample_rate {η : ℕ → ℝ} {a : ℝ}
    (hη : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)≤η d ∧ η d≤1) :
    LogPowerRate (fun d => logMeshLength (sampleCorrelation (η d))) 0 := by
  have hr := ((LogPowerRate.const (Real.log 2)).add
    (((LogPowerRate.log_power a).add (LogPowerRate.const (-Real.log 4))).const_mul (-2)))
  apply LogPowerRate.of_le hr
  · filter_upwards [hη,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hp : (0:ℝ)<d := by exact_mod_cast hd1
    have hpη := sampleCorrelation_properties (lt_of_lt_of_le (Real.rpow_pos_of_pos hp _) hd.1) hd.2
    exact (logMeshLength_pos (by linarith [hpη.1]) hpη.2.1).le
  · filter_upwards [hη,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hp : (0:ℝ)<d := by exact_mod_cast hd1
    have hR : 0<(d:ℝ)^(-a) := Real.rpow_pos_of_pos hp _
    have hηpos := lt_of_lt_of_le hR hd.1
    have hpη := sampleCorrelation_properties hηpos hd.2
    have hh := sampleCorrelation_radius_lower hηpos hd.2
    have hu : (d:ℝ)^(-a)/4≤Real.sqrt (1-(sampleCorrelation (η d))^2) := by linarith
    have hs : 0≤1-(sampleCorrelation (η d))^2 := by nlinarith [hpη.1,hpη.2.1]
    have hdR : ((d:ℝ)^(-a)/4)^2≤1-(sampleCorrelation (η d))^2 := by
      have he := pow_le_pow_left₀ (by positivity : 0≤(d:ℝ)^(-a)/4) hu 2
      rwa [Real.sq_sqrt hs] at he
    have he := logMeshLength_le_scale (by linarith [hpη.1]) hpη.2.1
      (by positivity : 0<(d:ℝ)^(-a)/4) hdR
    rw [Real.log_div hR.ne' (by norm_num)] at he
    linarith
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_OccurrenceBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology Classical

lemma sourceOccurrenceBudget_rate {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (n m N nc Nc : ℕ) :
    LogPowerRate (fun d => (sourceOccurrenceBudget a b n m N nc Nc d:ℝ))
      (-((occurrenceDegree N Nc:ℕ):ℝ)*b) := by
  have he := sourceCorrelation_eventually ha
  have hp := probabilityNode_card_rate hb.le (n+1)
    (he.mono (fun _ h => h.1)) (he.mono (fun _ h => h.2.1))
    (logMeshLength_rate a (he.mono (fun _ h => h.1))
      (he.mono (fun _ h => h.2.1)) (he.mono (fun _ h => h.2.2.le)))
  have hR : ∀ᶠ d : ℕ in atTop,0<(d:ℝ)^(-a) ∧ (d:ℝ)^(-a)≤1 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)⟩
  have hs := hR.mono (fun d hd => sampleCorrelation_properties hd.1 hd.2)
  have hsp := probabilityNode_card_rate hb.le (n+1)
    (hs.mono (fun _ h => by linarith [h.1])) (hs.mono (fun _ h => h.2.1))
    (logMeshLength_sample_rate (hR.mono (fun _ h => ⟨le_rfl,h.2⟩)))
  have hsample := (hsp.add ((LogPowerRate.const 1).mono (by linarith))).pow N
  have hmean := meanWork_rate hb.le hp (n+2) m N nc Nc
  have hB₁ : ((Nc*(2*N+2):ℕ):ℝ)≤(occurrenceDegree N Nc:ℝ) := by
    exact_mod_cast le_max_left (Nc*(2*N+2)) N
  have hB₂ : (N:ℝ)≤(occurrenceDegree N Nc:ℝ) := by exact_mod_cast le_max_right (Nc*(2*N+2)) N
  have hm := hmean.mono (show -(occurrenceDegree N Nc:ℝ)*b≤-((Nc*(2*N+2):ℕ):ℝ)*b by nlinarith)
  have hp' := hsample.mono (show -(occurrenceDegree N Nc:ℝ)*b≤(N:ℝ)*(-b) by nlinarith)
  simpa only [sourceOccurrenceBudget,Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hm.add hp'

namespace OracleCompiler

lemma literalSample_cost_le_source {a b : ℝ} {d : ℕ} (hd : 0<d)
    (n m N nc Nc : ℕ) {η : ℝ} (hηR : (d:ℝ)^(-a)≤η) (hη1 : η≤1)
    (r : ℝ) (e : ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1)) :
    cost (literalSample (d:=d) r (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1) N e)≤
      sourceOccurrenceBudget a b n m N nc Nc d := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hR := Real.rpow_pos_of_pos hd0 (-a)
  have hη := lt_of_lt_of_le hR hηR
  have hR1 : (d:ℝ)^(-a)≤1 := hηR.trans hη1
  have hmono := logMeshCount_mono (sampleCorrelation_antitone hR.le hηR)
    (sampleCorrelation_properties hR hR1).2.1 (Real.rpow_pos_of_pos hd0 (-b))
  have hcard : Fintype.card (ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1))≤
      Fintype.card (ProbabilityNode (sampleCorrelation ((d:ℝ)^(-a))) ((d:ℝ)^(-b)) (n+1)) := by
    simp only [probabilityNode_card]
    exact Nat.mul_le_mul_right _ hmono
  rw [cost_literalSample]
  have he := flowWork_bound (Fintype.card (ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-b)) (n+1))) N 0
  simp only [zero_add,one_mul] at he
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hcard 1) N
  unfold sourceOccurrenceBudget
  omega

theorem exists_cost_mesh_exponent {t κ : ℝ} (ht : 0<t) (hκ : 0<κ)
    (N Nc rank : ℕ) : ∃w : ℝ,0<w ∧ w<t ∧
      ∀n m nc,∀ᶠ d : ℕ in atTop,
        ((2*(40*sourceOccurrenceBudget (κ*t) (κ*w) n m N nc Nc d+40)^rank:ℕ):ℝ)≤
          (d:ℝ)^(κ*t) := by
  let H : ℝ := (rank:ℝ)*(occurrenceDegree N Nc:ℝ)+1
  have hH : 0<H := by dsimp [H]; positivity
  let w := t/(2*H)
  have hw : 0<w := div_pos ht (mul_pos (by norm_num) hH)
  have hHt : 1≤H := by
    dsimp [H]
    have : 0≤(rank:ℝ)*(occurrenceDegree N Nc:ℝ) := by positivity
    linarith
  have hwid : w*(2*H)=t := div_mul_cancel₀ t (ne_of_gt (mul_pos (by norm_num) hH))
  have hwt : w<t := by nlinarith
  refine ⟨w,hw,hwt,?_⟩
  intro n m nc
  have hc := sourceOccurrenceBudget_rate (mul_pos hκ ht) (mul_pos hκ hw) n m N nc Nc
  have hr := routineBudget_rate (show 0≤(occurrenceDegree N Nc:ℝ)*(κ*w) by positivity) (by simpa only [neg_mul] using hc) rank
  have hexp : -(κ*t)< -(rank:ℝ)*((occurrenceDegree N Nc:ℝ)*(κ*w)) := by
    have he : (rank:ℝ)*(occurrenceDegree N Nc:ℝ)*w<t := by dsimp [H] at hwid hH hHt; nlinarith
    nlinarith
  have he := hr.eventually_small hexp
  filter_upwards [he] with d hd
  exact (le_abs_self _).trans (by simpa only [neg_neg] using hd)

end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_IntegralLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

lemma Coupling.DistanceCoupled.integral_lipschitz {E : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} {R L C : ℝ}
    (h : Coupling.DistanceCoupled μ ν R) (hL : 0≤L) {f : E → ℝ}
    (hf : Measurable f) (hb : ∀x,|f x|≤C)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)|≤L*R := by
  obtain ⟨κ,hκ,hx,hy,hd⟩ := h
  let := hκ
  have hix := bounded_integrable (hf.comp measurable_fst) (fun p : E×E => hb p.1) (μ:=κ)
  have hiy := bounded_integrable (hf.comp measurable_snd) (fun p : E×E => hb p.2) (μ:=κ)
  simp only [Function.comp_def] at hix hiy
  rw [←hx,←hy]
  change |(∫x,f x ∂κ.map Prod.fst)-(∫x,f x ∂κ.map Prod.snd)|≤_
  rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,←integral_sub hix hiy,
    ←Real.norm_eq_abs]
  exact (norm_integral_le_of_norm_le_const (hd.mono (fun p hp =>
    (show ‖f p.1-f p.2‖≤L*dist p.1 p.2 by simpa only [Real.norm_eq_abs] using hl p.1 p.2).trans
      (mul_le_mul_of_nonneg_left hp hL)))).trans (by simp)

lemma TVAtMost.integral_unit {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : TVAtMost μ ν ε) {f : E → ℝ} (hf : Measurable f)
    (hb : ∀x,0≤f x ∧ f x≤1) : |(∫x,f x ∂μ)-(∫x,f x ∂ν)|≤ε := by
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hiμ := bounded_integrable hf hbf (μ:=μ)
  have hiν := bounded_integrable hf hbf (μ:=ν)
  have hlayer (ρ : Measure E) [IsProbabilityMeasure ρ] :
      Integrable (fun t : ℝ => ρ.real {x | t≤f x}) (volume.restrict (Set.Ioc 0 1)) := by
    apply bounded_integrable (C:=1)
    · exact (Antitone.measurable (show Antitone (fun t : ℝ => ρ {x | t≤f x}) from
        fun a b hab => measure_mono (fun x hx => hab.trans hx))).ennreal_toReal
    · intro t
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  rw [hiμ.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall (fun x => (hb x).1))
    (Filter.Eventually.of_forall (fun x => (hb x).2)),
    hiν.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall (fun x => (hb x).1))
    (Filter.Eventually.of_forall (fun x => (hb x).2)),←integral_sub (hlayer μ) (hlayer ν),←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (Set.Ioc (0:ℝ) 1))
    (f:=fun t : ℝ => μ.real {x | t≤f x}-ν.real {x | t≤f x}) (C:=ε)
    (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using h {x | t≤f x} (measurableSet_le measurable_const hf)))
  simpa using hh

lemma kernel_integral_comp {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {f : F → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀x,|f x|≤C) :
    (∫z,f z ∂κ ∘ₘ μ)=∫x,(∫z,f z ∂κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp (bounded_integrable hf hb)

lemma kernel_event_real {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {s : Set F} (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s=∫x,(κ x).real s ∂μ := by
  rw [measureReal_def,Measure.bind_apply hs κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hs).aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top _ _))).symm

lemma kernel_event_integrable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {s : Set F} (hs : MeasurableSet s) : Integrable (fun x => (κ x).real s) μ :=
  bounded_integrable ((κ.measurable_coe hs).ennreal_toReal)
    (fun x => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)

lemma TVAtMost.kernel {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : TVAtMost μ ν ε) (κ : Kernel E F) [IsMarkovKernel κ] :
    TVAtMost (κ ∘ₘ μ) (κ ∘ₘ ν) ε := by
  intro s hs
  rw [kernel_event_real μ κ hs,kernel_event_real ν κ hs]
  exact h.integral_unit ((κ.measurable_coe hs).ennreal_toReal)
    (fun x => ⟨measureReal_nonneg,measureReal_le_one⟩)

lemma TVAtMost.kernel_mixture {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ η : Kernel E F)
    [IsMarkovKernel κ] [IsMarkovKernel η] {e : E → ℝ}
    (hi : Integrable e μ) (h : ∀x,TVAtMost (κ x) (η x) (e x)) :
    TVAtMost (κ ∘ₘ μ) (η ∘ₘ μ) (∫x,e x ∂μ) := by
  intro s hs
  rw [kernel_event_real μ κ hs,kernel_event_real μ η hs,
    ←integral_sub (kernel_event_integrable μ κ hs) (kernel_event_integrable μ η hs),←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ((kernel_event_integrable μ κ hs).sub (kernel_event_integrable μ η hs)).norm hi
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using h x s hs

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TapeSnocEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

lemma seedTapeSnoc_law {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (μ : Measure Ω) (γ : Measure R) [SFinite μ] [SigmaFinite γ] (n : ℕ) :
    (((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map (seedTapeSnoc n)) =
      μ.prod (Measure.pi (fun _ : Fin (n+1) => γ)) := by
  change ((μ.prod (Measure.pi (fun _ : Fin n => γ))).prod γ).map
    (((MeasurableEquiv.refl Ω).prodCongr (tapeSnocEquiv n)) ∘ MeasurableEquiv.prodAssoc) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.prodAssoc_prod]
  have h := Measure.map_prod_map μ ((Measure.pi (fun _ : Fin n => γ)).prod γ)
    measurable_id (tapeSnocEquiv n).measurable
  rw [Measure.map_id] at h
  change (μ.prod ((Measure.pi (fun _ : Fin n => γ)).prod γ)).map (Prod.map id (tapeSnocEquiv n)) = _
  rw [← h]
  have ht : (tapeSnocEquiv (R := R) n : (Fin n → R) × R → _) =
    fun p => Fin.snoc (α := fun _ : Fin (n+1) => R) p.1 p.2 := by funext p; exact tapeSnocEquiv_apply n p
  rw [ht, pi_snoc_law]

section Run
variable {S : ℕ → Type*} {Ω R : Type*}
  [∀ n, MeasurableSpace (S n)] [MeasurableSpace Ω] [MeasurableSpace R]

lemma measurable_stateRun (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    Measurable (stateRun init step n) := by
  induction n with
  | zero => exact hi.comp measurable_fst
  | succ n ih =>
    apply (hs n).comp
    exact (ih.comp (measurable_fst.prodMk (Measurable.of_eval
      (fun index => (measurable_pi_apply index.castSucc).comp measurable_snd)))).prodMk
        (by fun_prop)

lemma stateRun_law (μ : Measure Ω) (γ : Measure R) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (init : Ω → S 0) (hi : Measurable init)
    (step : (n : ℕ) → S n × R → S (n+1)) (hs : ∀ n, Measurable (step n)) (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => γ))).map (stateRun init step n) =
      stateLaw (μ.map init) γ step n := by
  induction n with
  | zero =>
    change (μ.prod (Measure.pi (fun _ : Fin 0 => γ))).map (init ∘ Prod.fst) = μ.map init
    rw [← Measure.map_map hi measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    rw [← seedTapeSnoc_law μ γ n, Measure.map_map (measurable_stateRun init hi step hs (n+1))
      (seedTapeSnoc n).measurable]
    change _ = (((stateLaw (μ.map init) γ step n).prod γ).map (step n))
    rw [← ih]
    have h := Measure.map_prod_map (μ.prod (Measure.pi (fun _ : Fin n => γ))) γ
      (measurable_stateRun init hi step hs n) measurable_id
    rw [Measure.map_id] at h
    rw [h, Measure.map_map (hs n) ((measurable_stateRun init hi step hs n).prodMap measurable_id)]
    congr 1
    funext p
    exact stateRun_snoc init step n p

end Run
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Fresh
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] {d q : ℕ}

lemma fresh_run (A : ℕ → Program (E × R) d q E) (V : Point d → ℝ) (n : ℕ)
    (p : E × (Fin n → R)) :
    (fresh A n).run V p=stateRun id (fun j => (A j).run V) n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fresh,seq_run,seedMap_run,stateRun]
    rw [ih]

lemma fresh_law (A : ℕ → Program (E × R) d q E) {V : Point d → ℝ}
    (hV : Measurable (firstOrderReply V)) (μ : Measure E) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => γ))).map ((fresh A n).run V)=
      stateLaw μ γ (fun j => (A j).run V) n := by
  have h := stateRun_law μ γ id measurable_id (fun j => (A j).run V)
    (fun j => (A j).measurable_run V hV) n
  simpa only [←funext (fresh_run A V n),Measure.map_id] using h

end LogConcaveSampling.OracleCompiler.Program

end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrependTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Function
open scoped Classical

variable {d : ℕ}

lemma oneSlot_preserving {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (fun z : Ω => fun _ : Fin 1 => z) μ (Measure.pi fun _ : Fin 1 => μ) := by
  convert (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω)) using 1
  all_goals try with_reducible_and_instances rfl
  funext z i
  have hi : i=default := Subsingleton.elim _ _
  subst i
  rfl

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_FullTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.ReservedProgram
open MeasureTheory ProbabilityTheory Function Coupling
open scoped Classical NNReal

variable {d : ℕ}

lemma fullTape_preserving (k : ℕ) :
    MeasurePreserving (fullTape (d:=d) k) ((gaussianTape d k).prod (stdGaussian (Point d)))
      (gaussianTape d (k+1)) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) k 1).comp
    ((MeasurePreserving.id _).prod (oneSlot_preserving (stdGaussian (Point d))))

end LogConcaveSampling.OracleCompiler.ReservedProgram

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_IndependentSeq
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω E R : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace R] {d q r : ℕ}

lemma independentSeq_run (A : Program Ω d q E) (B : Program (E × R) d r E)
    (V : Point d → ℝ) (p : Ω × R) :
    (A.independentSeq B).run V p=B.run V (A.run V p.1,p.2) := by
  rw [independentSeq,seq_run,seedMap_run,seedMap_run]

lemma independentSeq_law (A : Program Ω d q E) (B : Program (E × R) d r E)
    {V : Point d → ℝ} (hV : Measurable (firstOrderReply V)) (μ : Measure Ω) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] :
    (μ.prod γ).map ((A.independentSeq B).run V)=((μ.map (A.run V)).prod γ).map (B.run V) := by
  have hm := Measure.map_prod_map μ γ (A.measurable_run V hV) measurable_id
  rw [Measure.map_id] at hm
  rw [hm,Measure.map_map (B.measurable_run V hV) ((A.measurable_run V hV).prodMap measurable_id)]
  congr 1
  funext p
  exact independentSeq_run A B V p

end LogConcaveSampling.OracleCompiler.Program

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_RoutineBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree
open scoped Classical

variable {d : ℕ}

lemma RoutineBudget.mono {B C : ℕ} {η₀ η₁ : ℝ} {k : RoutineKind} {R : RoutineValue d k}
    (h : RoutineBudget B η₀ η₁ R) (hBC : B≤C) : RoutineBudget C η₀ η₁ R := by
  cases k with
  | mean => exact fun r σ => (h r σ).mono hBC
  | sample => exact fun r η hη => (h r η hη).mono hBC

theorem constructRoutine_budget (C : CircuitParameters) {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (c : ℕ) (η₁ : ℝ) (hD : 0<C.D)
    (hcm : ∀r σ,cost (C.meanTree (d:=d) r σ) ≤ c)
    (hcs : ∀r η,η=Real.sqrt (1-C.T^2)/C.T ∨ η=η₁ →
      ∀hη : 0<η, ∀hη1 : η≤1,cost (C.sampleTree (d:=d) r η hη hη1) ≤ c) :
    ∀L,((2*(40*c+40)^L.rank t : ℕ):ℝ)≤C.D^2 →
      RoutineBudget (2*(40*c+40)^L.rank t) (Real.sqrt (1-C.T^2)/C.T) η₁
        (constructRoutine d C ht hs L) := by
  let K := 40*c+40
  have hK : 0<K := by dsimp [K]; omega
  have hp (n : ℕ) : 2≤2*K^n := by have := Nat.one_le_pow n _ hK; omega
  apply routine_induction ht hs
  · intro L hL hcap
    rw [constructRoutine,dite_eq_left hL]
    cases L with | mk k b p =>
      cases k with
      | mean => exact fun r σ => (terminalMeanProgram_budget r σ).mono (hp _)
      | sample => exact fun r η _ => (terminalReservedProgram_budget r η).mono (hp _)
  · intro L hL ih hcap
    let n := L.rank t-1
    let B := 2*K^n
    have hi : (RoutineLabel.mk .mean (L.b-10*t) (L.p-1/4)).rank t<L.rank t :=
      RoutineStep.rank_lt ht hs hL (by cases L; exact RoutineStep.internal _ .mean _ _)
    have hpos : 0<L.rank t := by omega
    have hn : n+1=L.rank t := by dsimp [n]; omega
    have hB : 1≤B := (by have := hp n; exact le_trans (by omega) this)
    have hBparent : B≤2*K^L.rank t := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hK (by dsimp [n]; omega))
    have hBD : (B:ℝ)≤C.D^2 := le_trans (by exact_mod_cast hBparent) hcap
    have hbfinal : K*B=2*K^L.rank t := by rw [←hn]; dsimp [B]; rw [pow_succ]; ring
    have child (L' : RoutineLabel) (hh : RoutineStep t L L') :
        RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hs L') := by
      have hr := hh.rank_lt ht hs hL
      have hb : 2*K^L'.rank t≤B := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hK (by dsimp [n]; omega))
      exact (ih L' hh (le_trans (by exact_mod_cast hb.trans hBparent) hcap)).mono hb
    rw [constructRoutine,dite_eq_right hL]
    cases L with | mk k b p =>
      cases k with
      | mean =>
        have hf := child ⟨.mean,b+t,p⟩ (RoutineStep.meanFinal b p)
        have hi := child ⟨.mean,b-10*t,p-1/4⟩ (RoutineStep.internal .mean .mean b p)
        have hs' := child ⟨.sample,b-10*t,p-1/4⟩ (RoutineStep.internal .mean .sample b p)
        intro r σ
        have hh := C.meanFrom_budget hB hD hBD
          (constructRoutine d C ht hs ⟨.mean,b+t,p⟩)
          (constructRoutine d C ht hs ⟨.mean,b-10*t,p-1/4⟩)
          (constructRoutine d C ht hs ⟨.sample,b-10*t,p-1/4⟩)
          (fun s r σ _ => by cases s; exact hi r σ; exact hf r σ)
          (fun r _ => hs' r _ (Or.inl rfl)) r σ (hcm r σ)
        rw [show (40*c+40)*B=2*(40*c+40)^({kind:=RoutineKind.mean,b:=b,p:=p}:RoutineLabel).rank t from hbfinal] at hh
        exact hh
      | sample =>
        have hf := child ⟨.mean,b,p⟩ (RoutineStep.sampleFinal b p)
        have hi := child ⟨.mean,b-10*t,p-1/4⟩ (RoutineStep.internal .sample .mean b p)
        intro r η hη
        have hh := C.sampleFrom_budget hB hD hBD
          (constructRoutine d C ht hs ⟨.mean,b,p⟩)
          (constructRoutine d C ht hs ⟨.mean,b-10*t,p-1/4⟩)
          (fun s r σ _ => by cases s; exact hi r σ; exact hf r σ) r η
          (fun _ hηpos hη1 => hcs r η hη hηpos hη1)
        rw [show (40*c+40)*B=2*(40*c+40)^({kind:=RoutineKind.sample,b:=b,p:=p}:RoutineLabel).rank t from hbfinal] at hh
        exact hh
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Shape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Topology Classical

lemma source_anchor_radius {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)≤Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d) ∧
      Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d)≤1 := by
  have he := sourceCorrelation_eventually ha
  have ht := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (3/4:ℝ)<1))
  filter_upwards [he,ht,eventually_ge_atTop (1:ℕ)] with d hd hT hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hR := Real.rpow_pos_of_pos hd0 (-a)
  have hr : Real.sqrt (1-(sourceCorrelation a d)^2)=(d:ℝ)^(-a) := by
    rw [←hd.2.2,Real.sqrt_sq hR.le]
  rw [hr]
  constructor
  · exact (le_div_iff₀ hd.1).mpr (by nlinarith [mul_le_mul_of_nonneg_left hd.2.1.le hR.le])
  · apply (div_le_one hd.1).mpr
    nlinarith [hd.2.2]

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Classical Topology

lemma source_angle_square {a : ℝ} (ha : 0<a) (m : ℕ) :
    ∀ᶠ d : ℕ in atTop,(((d:ℝ)^(-(4*a)))*(m:ℝ))^2≤(d:ℝ)^(-a) := by
  have he := (((LogPowerRate.power (4*a)).mul_const (m:ℝ)).pow 2).eventually_small
    (show a<(2:ℝ)*(4*a) by linarith)
  exact he.mono (fun d hd => (le_abs_self _).trans hd)

theorem exists_source_configuration {a b : ℝ} (ha : 0<a) (_ : 0<b)
    (n m N nc Nc : ℕ) : ∀ᶠ d : ℕ in atTop,∃C : CircuitParameters,
      C.n=n ∧ C.m=m ∧ C.N=N ∧ C.nc=nc ∧ C.Nc=Nc ∧
      C.T=sourceCorrelation a d ∧ C.h=(d:ℝ)^(-b) ∧ C.ψ=(d:ℝ)^(-(4*a)) ∧
      C.D=(d:ℝ)^a ∧ C.A=C.actualA ∧ C.Af=C.actualAf := by
  have ht := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [sourceCorrelation_eventually ha,source_angle_square ha m,ht,eventually_ge_atTop (1:ℕ)] with d hd hangle hT hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hψ : 0<(d:ℝ)^(-(4*a)) := Real.rpow_pos_of_pos hd0 _
  have hroot : Real.sqrt (1-(sourceCorrelation a d)^2)=(d:ℝ)^(-a) := by
    rw [←hd.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 (-a)).le]
  let C₀ : CircuitParameters := {
    n:=n, m:=m, N:=N, nc:=nc, Nc:=Nc,
    T:=sourceCorrelation a d, h:=(d:ℝ)^(-b), ψ:=(d:ℝ)^(-(4*a)),
    v:=(d:ℝ)^(-(4*a))*m, D:=(d:ℝ)^a, A:=1, Af:=1,
    T_lower:=hT.le, T_upper:=hd.2.1, h_pos:=Real.rpow_pos_of_pos hd0 _,
    v_nonneg:=by positivity,
    angle_bound:=by
      intro j
      have hj : 0≤angleNodes m j := by simp [angleNodes]
      have hjm : angleNodes m j ≤ (m : ℝ) := by
        dsimp [angleNodes]
        exact_mod_cast (Nat.le_of_lt_succ j.isLt)
      rw [abs_of_nonneg (mul_nonneg hψ.le hj)]
      exact mul_le_mul_of_nonneg_left hjm hψ.le,
    angle_small:=by rw [hroot]; exact hangle }
  let C := {C₀ with A:=C₀.actualA,Af:=C₀.actualAf}
  exact ⟨C,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature
open scoped Classical Topology

lemma exists_source_shape {κ t w : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (n N : ℕ) :
    ∀ᶠ d : ℕ in atTop,∃C : CircuitParameters,SourceShape κ t w n N d C := by
  filter_upwards [exists_source_configuration (mul_pos hκ ht) (mul_pos hκ hw) n n N n N] with d hd
  obtain ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf⟩ := hd
  exact ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf⟩
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

lemma RoutineLabel.Admissible.b_lower {t K : ℝ} {L : RoutineLabel}
    (h : L.Admissible t K) (ht : 0≤t) : 1/2≤L.b := by
  have he : 0≤40*t*L.p := by positivity [h.1]
  linarith [h.2.2]

lemma RoutineLabel.Admissible.rank_bound {t K : ℝ} {L : RoutineLabel}
    (h : L.Admissible t K) (ht : 0<t) : L.rank t≤2*⌈K/t⌉₊+1 := by
  have hb := h.b_lower ht.le
  have hn : ⌈(L.p-L.b)/t⌉₊≤⌈K/t⌉₊ := Nat.ceil_mono
    (div_le_div_of_nonneg_right (by linarith [h.2.1]) ht.le)
  unfold RoutineLabel.rank
  cases L.kind <;> dsimp only <;> omega

lemma topLabel_admissible {t K : ℝ} (hK : 0≤K) (ht : 0≤t)
    (hsmall : 40*(K+2)*t<1/4) : (⟨.sample,1,K⟩:RoutineLabel).Admissible t K := by
  refine ⟨hK,le_rfl,?_⟩
  dsimp
  nlinarith
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Classical Topology

theorem exists_uniform_routine_mesh {κ t K : ℝ} (hκ : 0<κ) (ht : 0<t) (hts : t≤1/44)
    (N : ℕ) : ∃w : ℝ,0<w ∧ w<t ∧ ∀n : ℕ,
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧
      ∀L : RoutineLabel,L.Admissible t K → ∀η₁ : ℝ,(d:ℝ)^(-(κ*t))≤η₁ → η₁≤1 →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hts L) := by
  let rank := 2*⌈K/t⌉₊+1
  obtain ⟨w,hw,hwt,hcost⟩ := exists_cost_mesh_exponent ht hκ N N rank
  refine ⟨w,hw,hwt,?_⟩
  intro n
  filter_upwards [hcost n n n,source_anchor_radius (mul_pos hκ ht),eventually_ge_atTop (1:ℕ)] with d hd hanchor hd1
  intro C hC
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hdge : (1:ℝ)≤d := by exact_mod_cast hd1
  have hDpos : 0<C.D := by rw [hC.D_eq]; exact Real.rpow_pos_of_pos hd0 _
  have hDone : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow hdge (mul_pos hκ ht).le
  let c := sourceOccurrenceBudget (κ*t) (κ*w) n n N n N d
  let B := 2*(40*c+40)^rank
  have hcap : (B:ℝ)≤C.D := by simpa only [B,c,hC.D_eq] using hd
  refine ⟨B,hcap,?_⟩
  intro L hL η₁ hηR hη1
  have hmono : 2*(40*c+40)^L.rank t≤B := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega : 1≤40*c+40) (hL.rank_bound ht)
  apply RoutineBudget.mono (hBC:=hmono)
  apply constructRoutine_budget C ht hts c η₁ hDpos
  · intro r σ
    unfold CircuitParameters.meanTree
    rw [cost_literalMean]
    simp only [hC.n_eq,hC.m_eq,hC.N_eq,hC.nc_eq,hC.Nc_eq,hC.T_eq,hC.h_eq]
    unfold c sourceOccurrenceBudget
    omega
  · intro r η hη hηpos hηle
    unfold CircuitParameters.sampleTree
    have hradius : (d:ℝ)^(-(κ*t))≤η := by
      rcases hη with hη|hη
      · rw [hη,hC.T_eq]; exact hanchor.1
      · rw [hη]; exact hηR
    let e : ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-(κ*w))) (n+1) := by
      simpa only [←hC.h_eq,←hC.n_eq] using C.sampleEndpoint η hηpos hηle
    have he := literalSample_cost_le_source (b:=κ*w) (by omega : 0<d) n n N n N hradius hηle r e
    simpa only [cost_literalSample,hC.n_eq,hC.N_eq,hC.h_eq,c] using he
  · have hmreal : ((2*(40*c+40)^L.rank t:ℕ):ℝ)≤B := by exact_mod_cast hmono
    have hreal : ((2*(40*c+40)^L.rank t:ℕ):ℝ)≤C.D := hmreal.trans hcap
    exact hreal.trans (by nlinarith)
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_PrimitiveProducer
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

theorem exists_primitive_producer {κ P : ℝ} (hκ : 0<κ) (hP : 1≤P) :
    ∃t : ℝ,0<t ∧ t<1/100 ∧ 40*(P+2)*t<1/4 ∧
    ∃K : ℝ,0≤K ∧ ∃e : ℕ → ℝ,LogPowerRate e (κ*P) ∧
      (∀ᶠ d : ℕ in atTop,0<e d) ∧
      ∀ᶠ d : ℕ in atTop,∃S : ℝ → ℝ → ReservedProgram d,∃B : ℕ,
        (B:ℝ)≤(d:ℝ)^(κ*t) ∧
        (∀r : ℝ,SampleBudget B r 1 (S r 1)) ∧
        ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
          SampleCorrect F lam ((d:ℝ)^(-κ)) K (e d) ((d:ℝ)^(-(κ*t))) S := by
  let t : ℝ := 1/(1000*(P+2))
  have ht : 0<t := by dsimp [t]; positivity
  have heq : t*(1000*(P+2))=1 := by dsimp [t]; exact one_div_mul_cancel (by positivity)
  have hsmall : 40*(P+2)*t<1/4 := by nlinarith only [heq]
  have hts : t<1/100 := by nlinarith [mul_nonneg ht.le (by linarith : 0≤P)]
  let J := P+1
  have hJ : 1≤J := by dsimp [J]; linarith
  let N := numericalLayerCount J
  obtain ⟨w,hw,hwt,hbudget⟩ := exists_uniform_routine_mesh (K:=P) hκ ht (by linarith) N
  obtain ⟨n,hnw,hnt,hnn,hnum⟩ := exists_source_numerical_ready hκ hJ ht hts hw hwt
  have hR : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*t))≤1 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by nlinarith)
  have hb : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t P →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L) := by
    filter_upwards [hbudget n,hR] with d hd hRd
    intro C hC
    obtain ⟨B,hB,hbud⟩ := hd C hC
    exact ⟨B,hB,fun L hL => hbud L hL 1 hRd le_rfl⟩
  have ha := uniform_routine_accuracy hκ ht hts hw hwt (show P≤J by dsimp [J]; linarith)
    (show N=numericalLayerCount J from rfl) hb hnum
    ⟨.sample,1,P⟩ (topLabel_admissible (by linarith) ht.le hsmall)
  have hq : LogPowerRate (fun d : ℕ => (d:ℝ)^(-κ)) (κ*1) := by
    simpa only [mul_one] using LogPowerRate.power κ
  have hqp : ∀ᶠ d : ℕ in atTop,0<(d:ℝ)^(-κ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  obtain ⟨K,hK,e,her,hep,he⟩ := ha _ hq hqp
  refine ⟨t,ht,hts,hsmall,K,hK,e,her,hep,?_⟩
  filter_upwards [he,hb,exists_source_shape hκ ht hw n N] with d hd hbd hshape
  obtain ⟨C,hC⟩ := hshape
  obtain ⟨B,hB,hbud⟩ := hbd C hC
  refine ⟨constructRoutine d C ht (by linarith) ⟨.sample,1,P⟩,B,?_,?_,?_⟩
  · simpa only [hC.D_eq] using hB
  · intro r
    exact hbud _ (topLabel_admissible (by linarith) ht.le hsmall) r 1 (Or.inr rfl)
  · intro F lam hF hlam hlam1
    exact hd C hC hF hlam hlam1

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProdMapEventReal
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma prod_map_event_real {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] (μ : Measure Ω) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × G → E) (hf : Measurable f) {A : Set E} (hA : MeasurableSet A) :
    ((μ.prod ν).map f).real A = ∫x,ν.real ((fun z => f (x,z)) ⁻¹' A) ∂μ := by
  rw [measureReal_def,Measure.map_apply hf hA,Measure.prod_apply (hA.preimage hf)]
  exact (integral_toReal (measurable_measure_prodMk_left (hA.preimage hf)).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _))).symm

lemma prod_event_integrable {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] (μ : Measure Ω) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × G → E) (hf : Measurable f) {A : Set E} (hA : MeasurableSet A) :
    Integrable (fun x => ν.real ((fun z => f (x,z)) ⁻¹' A)) μ := by
  have hm : Measurable (fun x => ν.real ((fun z => f (x,z)) ⁻¹' A)) :=
    (measurable_measure_prodMk_left (hA.preimage hf)).ennreal_toReal
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one)

theorem TVAtMost_gaussian_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (f g : Ω → Point d) (hf : Measurable f) (hg : Measurable g)
    {s : ℝ} (hs : 0 < s) (hi : Integrable (fun z => ‖f z-g z‖) μ) :
    TVAtMost ((μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2))
      ((μ.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2))
      ((∫z,‖f z-g z‖ ∂μ)/s) := by
  intro A hA
  have hf' : Measurable (fun z : Ω × Point d => f z.1+s • z.2) := by fun_prop
  have hg' : Measurable (fun z : Ω × Point d => g z.1+s • z.2) := by fun_prop
  rw [prod_map_event_real μ _ _ hf' hA,prod_map_event_real μ _ _ hg' hA,
    ←integral_sub (prod_event_integrable μ _ _ hf' hA) (prod_event_integrable μ _ _ hg' hA)]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [←integral_div]
  apply integral_mono ((prod_event_integrable μ _ _ hf' hA).sub
    (prod_event_integrable μ _ _ hg' hA)).norm (hi.div_const s)
  intro z
  have hh := TVAtMost_gaussian_affine (f z) (g z) hs A hA
  rw [measureReal_def,measureReal_def,
    Measure.map_apply (show Measurable (fun u : Point d => f z+s • u) by fun_prop) hA,
    Measure.map_apply (show Measurable (fun u : Point d => g z+s • u) by fun_prop) hA] at hh
  simpa only [Real.norm_eq_abs,Pi.sub_apply,measureReal_def] using hh

namespace Coupling
variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {d : ℕ}

theorem SquaredAt.gaussian_smoothing {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B s : ℝ} (hs : 0 < s) (hc : SquaredAt μ ν f g B) :
    TVAtMost ((μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2))
      ((ν.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2)) (Real.sqrt B/s) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := hc
  let := hκ
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖) := by fun_prop
  have h2 := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  have h1 := h2.integrable (by norm_num : (1:ENNReal)≤2)
  have hcs := integral_mul_sq_le h2 (memLp_const (1:ℝ) (μ:=κ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hcs
  have hB : 0≤B := (integral_nonneg (fun z => sq_nonneg ‖f z.1-g z.2‖)).trans he
  have hsmall : (∫z : Ω × Γ,‖f z.1-g z.2‖ ∂κ)≤Real.sqrt B :=
    (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) hB).2 (hcs.trans he)
  have htv := (TVAtMost_gaussian_mixture κ (fun z => f z.1) (fun z => g z.2)
    (hf.comp measurable_fst) (hg.comp measurable_snd) hs h1).mono
      (div_le_div_of_nonneg_right hsmall hs.le)
  have mapLeft : (κ.prod (stdGaussian (Point d))).map (fun z => f z.1.1+s • z.2)=
      (μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2) := by
    have hp : (κ.prod (stdGaussian (Point d))).map (Prod.map Prod.fst id)=μ.prod (stdGaussian (Point d)) := by
      rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
      exact congrArg (fun m => m.prod (stdGaussian (Point d))) hl
    rw [←hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have mapRight : (κ.prod (stdGaussian (Point d))).map (fun z => g z.1.2+s • z.2)=
      (ν.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2) := by
    have hp : (κ.prod (stdGaussian (Point d))).map (Prod.map Prod.snd id)=ν.prod (stdGaussian (Point d)) := by
      rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
      exact congrArg (fun m => m.prod (stdGaussian (Point d))) hr
    rw [←hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rwa [mapLeft,mapRight] at htv
end Coupling
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TvPre
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

lemma ReservedProgram.tv_of_pre {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (S : ReservedProgram d) (x : Point d) {r η e : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2<1) (hη : 0<η) (he : 0≤e)
    (hres : S.reserve=η/2)
    (hpre : SquaredAt (gaussianTape d S.slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => S.pre.run F (x,g)) (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      (e^2*(circuitD F x)^2)) :
    TVAtMost ((gaussianTape d S.full.slots).map (fun g => S.full.program.run F (x,g)))
      (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+η • z.2)) (2*e*circuitD F x/η) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hf : Measurable (fun g => S.pre.run F (x,g)) :=
    (S.pre.measurable_run F hV).comp (by fun_prop)
  have hh := hpre.gaussian_smoothing hf (by fun_prop) (show 0<η/2 by positivity)
  have hfull : ((gaussianTape d S.slots).prod (stdGaussian (Point d))).map
      (fun z => S.pre.run F (x,z.1)+(η/2) • z.2)=
      (gaussianTape d S.full.slots).map (fun g => S.full.program.run F (x,g)) := by
    let f : (Fin (S.slots+1) → Point d) → Point d := fun g => S.full.program.run F (x,g)
    have hfm : Measurable f :=
      (S.full.program.measurable_run F hV).comp (measurable_const.prodMk measurable_id)
    have hp := ReservedProgram.fullTape_preserving (d:=d) S.slots
    have heq : (fun z : (Fin S.slots → Point d) × Point d =>
        S.pre.run F (x,z.1)+(η/2) • z.2)=f ∘ ReservedProgram.fullTape S.slots := by
      funext z
      dsimp only [f,comp_apply]
      rw [ReservedProgram.full_run]
      simp only [ReservedProgram.fullTape,Fin.append_left,Fin.append_right,hres]
    exact (congrArg (fun k => ((gaussianTape d S.slots).prod (stdGaussian (Point d))).map k) heq).trans
      ((Measure.map_map hfm hp.measurable).symm.trans (congrArg (Measure.map f) hp.map_eq))
  have hnoise := smoothing_add_gaussian
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) (gibbs (primitivePotential F x r))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) id (by fun_prop) measurable_id
    (Real.sqrt 3*η/2) (η/2) η (by
      rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),div_pow]; ring) rfl
  rw [hfull,hnoise] at hh
  have hs : Real.sqrt (e^2*(circuitD F x)^2)=e*circuitD F x := by
    rw [←mul_pow,Real.sqrt_sq (mul_nonneg he (circuitD_nonneg F x))]
  have heq : e*circuitD F x/(η/2)=2*e*circuitD F x/η := by ring
  simpa only [id_eq,hs,heq] using hh

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PosteriorJointIntegral
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

lemma posterior_joint_integral_zero {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {u : Point d × Point d → ℝ}
    (hi : Integrable u (jointPosteriorLaw V h))
    (hu : ∀y,(∫z,u (z,y) ∂gibbs (posteriorPotential V h y))=0) :
    (∫p,u p ∂jointPosteriorLaw V h)=0 := by
  let c := (partition V)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt h)
  have hs := (Real.sqrt_pos.mpr hh).ne'
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.partition_ne_top)
    (EulerDensity.noiseCoefficient_positive d hs).ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.partition_pos.ne')
    (EulerDensity.noiseCoefficient_finite _ _)
  let w := fun p : Point d × Point d => Real.exp (-posteriorPotential V h p.2 p.1)
  have hw0 : ∀p,0≤w p := fun p => (Real.exp_pos _).le
  have hw : Measurable w := by
    have hm := hV.smooth.continuous.measurable
    dsimp [w,posteriorPotential]
    fun_prop
  have hden : Measurable (fun p => ENNReal.ofReal (w p)) := hw.ennreal_ofReal
  have hd := EulerDensity.joint_density hV.smooth.continuous.measurable
    (fun z : Point d => z) measurable_id hs
  simp only [Real.sq_sqrt hh.le] at hd
  have hd' : jointPosteriorLaw V h=
      c • ((volume : Measure (Point d)).prod volume).withDensity (fun p => ENNReal.ofReal (w p)) := by
    have hw' : w=(fun p : Point d × Point d =>
        Real.exp (-V p.1-‖p.2-p.1‖^2/(2*h))) := by
      funext p
      simp only [w,posteriorPotential,norm_sub_rev p.1 p.2]
      congr 1
      ring
    simpa only [jointPosteriorLaw,c,hw'] using hd
  rw [hd'] at hi ⊢
  have hif : Integrable (fun p => w p • u p) ((volume : Measure (Point d)).prod volume) := by
    have hi' := (integrable_smul_measure hc0 hct).mp hi
    rw [integrable_withDensity_iff_integrable_smul' hden
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)] at hi'
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi'
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    hden (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _)]
  rw [integral_prod_symm _ hif]
  have hz : ∀y,(∫z,w (z,y) • u (z,y))=0 := by
    intro y
    exact weighted_integral_zero_of_gibbs (posterior_smooth hV h y).continuous
      ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous) (hu y)
  simp_rw [hz]
  simp

lemma posterior_reconstruction_integral {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {f : Point d → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) :
    (∫y,(∫z,f z ∂gibbs (posteriorPotential V h y)) ∂noisedLaw V h)=∫z,f z ∂gibbs V := by
  let := hV.isProbabilityMeasure_gibbs
  let := noisedLaw_probability hV h
  let := jointPosteriorLaw_probability hV h
  let : ∀y : Point d,IsProbabilityMeasure (gibbs (posteriorPotential V h y)) := fun y =>
    probability_gibbs_of_partition (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
      (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))
  let g := fun y => ∫z,f z ∂gibbs (posteriorPotential V h y)
  have hg : Measurable g := (hf.stronglyMeasurable.integral_kernel
    (κ:=posteriorKernel V hV h)).measurable
  have hgb (y : Point d) : |g y|≤C := bounded_integral hC hb
  have hiz : Integrable (fun p : Point d × Point d => f p.1) (jointPosteriorLaw V h) :=
    bounded_integrable (hf.comp measurable_fst) (fun p => hb p.1)
  have hiy : Integrable (fun p : Point d × Point d => g p.2) (jointPosteriorLaw V h) :=
    bounded_integrable (hg.comp measurable_snd) (fun p => hgb p.2)
  have hz := posterior_joint_integral_zero hV hh (hiz.sub hiy) (fun y => by
    simp only [Pi.sub_apply]
    rw [integral_sub (bounded_integrable hf hb) (integrable_const (g y))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,g,sub_self])
  simp only [Pi.sub_apply] at hz
  rw [integral_sub hiz hiy] at hz
  have hfz : (∫p : Point d × Point d,f p.1 ∂jointPosteriorLaw V h)=∫z,f z ∂gibbs V := by
    rw [←jointPosterior_fst (V:=V) h,integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
  have hgy : (∫p : Point d × Point d,g p.2 ∂jointPosteriorLaw V h)=∫y,g y ∂noisedLaw V h := by
    rw [←jointPosterior_snd (V:=V) h,integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]
  rw [hfz,hgy] at hz
  exact (sub_eq_zero.mp hz).symm

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NoiseKernel
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

lemma noiseKernel_apply (s : ℝ) (x : Point d) :
    noiseKernel s x=(stdGaussian (Point d)).map (fun z => x+s • z) := by
  rw [noiseKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma noiseKernel_comp (s : ℝ) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    noiseKernel s ∘ₘ μ=(μ.prod (stdGaussian (Point d))).map (fun p => p.1+s • p.2) := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.map_apply (by fun_prop) hA,
    Measure.prod_apply (hA.preimage (by fun_prop))]
  apply lintegral_congr
  intro x
  rw [noiseKernel_apply,Measure.map_apply (by fun_prop) hA]
  rfl

lemma proximalKernel_markov {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    IsMarkovKernel (proximalKernel V hV h) := by
  let := posteriorKernel_probability hV hh
  unfold proximalKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measure_eq_of_bounded_integral {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀f : E → ℝ,Measurable f → (∀x,|f x|≤1) → (∫x,f x ∂μ)=∫x,f x ∂ν) : μ=ν := by
  ext s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have he := h (s.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hs)
    (fun x => by by_cases hx : x∈s <;> simp [hx])
  simpa only [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one,measureReal_def] using he

lemma posteriorKernel_invariant {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) : posteriorKernel V hV h ∘ₘ noisedLaw V h=gibbs V := by
  let := hV.isProbabilityMeasure_gibbs
  let := posteriorKernel_probability hV hh
  let := noisedLaw_probability hV h
  apply measure_eq_of_bounded_integral
  intro f hf hb
  rw [kernel_integral_comp _ _ hf hb]
  exact posterior_reconstruction_integral hV hh hf (by norm_num) hb

lemma proximalKernel_invariant {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) : proximalKernel V hV h ∘ₘ noisedLaw V h=noisedLaw V h := by
  let := hV.isProbabilityMeasure_gibbs
  rw [proximalKernel,←Measure.comp_assoc,posteriorKernel_invariant hV hh,
    noiseKernel_comp]
  rfl

lemma kernelAction_measurable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsSFiniteKernel κ] {f : F → ℝ} (hf : Measurable f) :
    Measurable (kernelAction κ f) := hf.stronglyMeasurable.integral_kernel.measurable

lemma kernelAction_bounded {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ] {f : F → ℝ} {C : ℝ} (hC : 0≤C)
    (hb : ∀x,|f x|≤C) : ∀x,|kernelAction κ f x|≤C := fun _ => bounded_integral hC hb

lemma kernelAction_comp {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (κ : Kernel E F) (η : Kernel F G)
    [IsMarkovKernel κ] [IsMarkovKernel η] {f : G → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀x,|f x|≤C) : kernelAction (η ∘ₖ κ) f=kernelAction κ (kernelAction η f) := by
  funext x
  exact Kernel.integral_comp (bounded_integrable hf hb)

lemma noiseKernel_action_lipschitz (s : ℝ) {f : Point d → ℝ} {L C : ℝ}
    (hf : Measurable f) (hb : ∀x,|f x|≤C) (_hL : 0≤L)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    ∀x y,|kernelAction (noiseKernel s) f x-kernelAction (noiseKernel s) f y|≤L*dist x y := by
  intro x y
  have hx : Measurable (fun z : Point d => f (x+s • z)) := hf.comp (by fun_prop)
  have hy : Measurable (fun z : Point d => f (y+s • z)) := hf.comp (by fun_prop)
  simp only [kernelAction,noiseKernel_apply]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_map (by fun_prop) hf.aestronglyMeasurable,
    ←integral_sub (bounded_integrable hx (fun z => hb _)) (bounded_integrable hy (fun z => hb _)),
    ←Real.norm_eq_abs]
  have ht := norm_integral_le_of_norm_le_const (f:=fun z : Point d => f (x+s • z)-f (y+s • z))
    (μ:=stdGaussian (Point d)) (C:=L*dist x y) (Filter.Eventually.of_forall (fun z : Point d => by
    simpa only [Real.norm_eq_abs,dist_add_right] using hl (x+s • z) (y+s • z)))
  simpa [measureReal_def] using ht

lemma proximal_action_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C) (hb : ∀x,|f x|≤C)
    (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) :
    ∀x y,|kernelAction (proximalKernel V hV h) f x-kernelAction (proximalKernel V hV h) f y|
      ≤(L/(1+h))*dist x y := by
  let := posteriorKernel_probability hV hh
  rw [proximalKernel,kernelAction_comp _ _ hf hb]
  intro x y
  have he := (posterior_distanceCoupled hV hh x y).integral_lipschitz hL
    (kernelAction_measurable (noiseKernel (Real.sqrt h)) hf) (kernelAction_bounded _ hC hb)
    (noiseKernel_action_lipschitz (Real.sqrt h) hf hb hL hl)
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv]
  ring

lemma proximal_action_smoothing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} (hf : Measurable f) (hb : ∀x,0≤f x ∧ f x≤1) :
    ∀x y,|kernelAction (proximalKernel V hV h) f x-kernelAction (proximalKernel V hV h) f y|
      ≤(1/((1+h)*Real.sqrt h))*dist x y := by
  let := posteriorKernel_probability hV hh
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  rw [proximalKernel,kernelAction_comp _ _ hf hbf]
  have hn : ∀x y,|kernelAction (noiseKernel (Real.sqrt h)) f x-
      kernelAction (noiseKernel (Real.sqrt h)) f y|≤(1/Real.sqrt h)*dist x y := by
    intro x y
    have htv : TVAtMost (noiseKernel (Real.sqrt h) x) (noiseKernel (Real.sqrt h) y) (‖x-y‖/Real.sqrt h) := by
      simpa only [noiseKernel_apply] using TVAtMost_gaussian_affine x y (Real.sqrt_pos.mpr hh)
    have ht := htv.integral_unit hf hb
    simpa only [kernelAction,noiseKernel_apply,dist_eq_norm,one_div,div_eq_inv_mul,mul_one] using ht
  intro x y
  have he := (posterior_distanceCoupled hV hh x y).integral_lipschitz
    (by positivity : 0≤1/Real.sqrt h) (kernelAction_measurable _ hf)
    (kernelAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf) hn
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

lemma affine_primitive_posterior {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (y : Point d) :
    (gibbs (primitivePotential (affinePotential V y (Real.sqrt h)) 0 1)).map
      (fun z => y+Real.sqrt h • z)=gibbs (posteriorPotential V h y) := by
  have hs := (Real.sqrt_pos.mpr hh).ne'
  rw [gibbs_map_affine ((hV.affinePrimitive y (Real.sqrt h)).continuous_potential 0 1) y hs]
  congr 1
  funext z
  have ha : y+Real.sqrt h • ((Real.sqrt h)⁻¹ • (z-y))=z := by
    rw [smul_smul,mul_inv_cancel₀ hs,one_smul]; abel
  simp only [primitivePotential,affinePotential,one_smul,zero_add,ha,posteriorPotential,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,Real.sq_sqrt hh.le]
  ring

lemma noised_affine_law (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (y : Point d) (s : ℝ) :
    (((μ.prod (stdGaussian (Point d))).map (fun z => z.1+z.2)).map (fun z => y+s • z))=
      noiseKernel s ∘ₘ μ.map (fun z => y+s • z) := by
  haveI : IsProbabilityMeasure (μ.map (fun z => y+s • z)) :=
    Measure.isProbabilityMeasure_map (show Measurable (fun z : Point d => y+s • z) by fun_prop).aemeasurable
  rw [noiseKernel_comp,Measure.map_map (by fun_prop) (by fun_prop)]
  have hp := Measure.map_prod_map μ (stdGaussian (Point d))
    (show Measurable (fun z => y+s • z) by fun_prop) measurable_id
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  change y+s • (p.1+p.2)=(y+s • p.1)+s • p.2
  rw [smul_add,add_assoc]

namespace OracleCompiler

lemma proximalProgram_run (S : ReservedProgram d) (h : ℝ) {V : Point d → ℝ} (hV : Admissible V)
    (y : Point d) (g : Fin S.full.slots → Point d) :
    (proximalProgram S h).run V (y,g)=
      y+Real.sqrt h • S.full.program.run (affinePotential V y (Real.sqrt h)) (0,g) := by
  rw [proximalProgram,Program.map_run,Program.affineOracle_run _ _ _ _ hV.smooth,Program.seedMap_run]

lemma approximateProximalKernel_markov (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) : IsMarkovKernel (approximateProximalKernel S h V hV) := by
  unfold approximateProximalKernel
  apply Kernel.IsMarkovKernel.map
  exact (proximalProgram S h).measurable_run V
    (hV.smooth.continuous.measurable.prodMk hV.gradient_lipschitz.continuous.measurable)

lemma approximateProximalKernel_apply (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (y : Point d) :
    approximateProximalKernel S h V hV y=
      (gaussianTape d S.full.slots).map (fun g => (proximalProgram S h).run V (y,g)) := by
  have hm := (proximalProgram S h).measurable_run V
    (hV.smooth.continuous.measurable.prodMk hV.gradient_lipschitz.continuous.measurable)
  rw [approximateProximalKernel,Kernel.map_apply _ hm,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map hm (by fun_prop)]
  rfl

lemma approximateProximalKernel_tv (S : ℝ → ℝ → ReservedProgram d)
    {V : Point d → ℝ} (hV : Admissible V) {h q K e ηmin : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀y,SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S)
    (y : Point d) :
    TVAtMost (approximateProximalKernel (S 1 1) h V hV y) (proximalKernel V hV h y)
      (2*e*(Real.sqrt d+2*Real.sqrt h*‖y‖)) := by
  let F := affinePotential V y (Real.sqrt h)
  have hF := hV.affinePrimitive y (Real.sqrt h)
  have hs : SampleSize (2*h) q 1 1 := by
    unfold SampleSize
    norm_num
    exact hq
  have hl : (2*(Real.sqrt h)^2)*1^2<1 := by rw [Real.sq_sqrt hh.le]; nlinarith
  have hpre := (hc y).error 1 1 hs hη 0
  have ht := (S 1 1).tv_of_pre hF 0 (r:=1) (η:=1) (by norm_num) hl
    (by norm_num) he hres hpre
  have hf : Measurable (fun g => (S 1 1).full.program.run F (0,g)) :=
    ((S 1 1).full.program.measurable_run F
      (hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable)).comp (by fun_prop)
  have hh' := ht.map (show Measurable (fun z : Point d => y+Real.sqrt h • z) by fun_prop)
  have hprob : IsProbabilityMeasure (gibbs (primitivePotential F 0 1)) :=
    probability_gibbs_of_partition (partition_pos_of_continuous (hF.continuous_potential 0 1)).ne'
      (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential 0 (by norm_num) hl))
  let := hprob
  simp only [one_smul,div_one] at hh'
  rw [noised_affine_law,affine_primitive_posterior hV hh y] at hh'
  rw [Measure.map_map (by fun_prop) hf] at hh'
  have hleft : ((gaussianTape d (S 1 1).full.slots).map
      ((fun z : Point d => y+Real.sqrt h • z) ∘ (fun g => (S 1 1).full.program.run F (0,g))))=
      approximateProximalKernel (S 1 1) h V hV y := by
    rw [approximateProximalKernel_apply]
    congr 1
    funext g
    exact (proximalProgram_run _ _ hV y g).symm
  rw [hleft] at hh'
  change TVAtMost _ (proximalKernel V hV h y) _ at hh'
  apply hh'.mono
  have hg : ‖gradient F 0‖≤2*Real.sqrt h*‖y‖ := by
    rw [gradient_affinePotential hV.smooth]
    simp only [smul_zero,add_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left (hV.gradient_norm_le y) (Real.sqrt_nonneg h)]
  unfold circuitD
  exact mul_le_mul_of_nonneg_left (by simpa only [F] using add_le_add_right hg (Real.sqrt d)) (by positivity)

end OracleCompiler
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

lemma posterior_joint_reconstruction {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {f : Point d × Point d → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀p,|f p|≤C) :
    (∫y,(∫z,f (z,y) ∂gibbs (posteriorPotential V h y)) ∂noisedLaw V h)=
      ∫p,f p ∂jointPosteriorLaw V h := by
  let := hV.isProbabilityMeasure_gibbs
  let := noisedLaw_probability hV h
  let := jointPosteriorLaw_probability hV h
  let := posteriorKernel_probability hV hh
  let g := fun y => ∫z,f (z,y) ∂gibbs (posteriorPotential V h y)
  have hg : Measurable g := (hf.stronglyMeasurable.integral_kernel_prod_left'
    (κ:=posteriorKernel V hV h)).measurable
  have hgb (y : Point d) : |g y|≤C := by
    let : IsProbabilityMeasure (gibbs (posteriorPotential V h y)) :=
      (posteriorKernel_probability hV hh).isProbabilityMeasure y
    exact bounded_integral hC (fun z => hb (z,y))
  have hif := bounded_integrable hf hb (μ:=jointPosteriorLaw V h)
  have hiy := bounded_integrable (hg.comp measurable_snd) (fun p : Point d × Point d => hgb p.2)
    (μ:=jointPosteriorLaw V h)
  have hz := posterior_joint_integral_zero hV hh (hif.sub hiy) (fun y => by
    simp only [Pi.sub_apply,comp_apply]
    let : IsProbabilityMeasure (gibbs (posteriorPotential V h y)) := (posteriorKernel_probability hV hh).isProbabilityMeasure y
    rw [integral_sub]
    · simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,g,sub_self]
    · exact bounded_integrable (hf.comp (show Measurable (fun z : Point d => (z,y)) by fun_prop)) (fun z => hb (z,y))
    · exact integrable_const (g y))
  simp only [Pi.sub_apply] at hz
  rw [integral_sub hif hiy] at hz
  have hgy : (∫p : Point d × Point d,g p.2 ∂jointPosteriorLaw V h)=∫y,g y ∂noisedLaw V h := by
    rw [←jointPosterior_snd (V:=V) h,integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]
  simp only [comp_apply] at hz
  rw [hgy] at hz
  exact (sub_eq_zero.mp hz).symm

lemma halvingKernel_markov {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    IsMarkovKernel (halvingKernel V hV h) := by
  let := proximalKernel_markov hV hh
  unfold halvingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma halvingKernel_apply {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) (y : Point d) :
    halvingKernel V hV h y=(proximalKernel V hV h y).map (fun z => (1/2:ℝ) • (y+z)) := by
  let := proximalKernel_markov hV hh
  rw [halvingKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma halving_gaussian_law {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    ((jointPosteriorLaw V h).prod (stdGaussian (Point d))).map
      (fun p => (1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))=noisedLaw V (h/2) := by
  let := hV.isProbabilityMeasure_gibbs
  let := jointPosteriorLaw_probability hV h
  have hv : (Real.sqrt h/2)^2+(Real.sqrt h/2)^2=(Real.sqrt (h/2))^2 := by
    rw [Real.sq_sqrt (by positivity : 0≤h/2)]
    nlinarith [Real.sq_sqrt hh.le]
  have hm : (jointPosteriorLaw V h).map (fun p => (1/2:ℝ) • (p.1+p.2))=
      ((gibbs V).prod (stdGaussian (Point d))).map (fun p => p.1+(Real.sqrt h/2) • p.2) := by
    rw [jointPosteriorLaw,Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    change (1/2:ℝ) • (p.1+(p.1+Real.sqrt h • p.2))=_
    module
  have hl := smoothing_add_gaussian (jointPosteriorLaw V h) (gibbs V)
    (fun p => (1/2:ℝ) • (p.1+p.2)) id (by fun_prop) measurable_id
    (Real.sqrt h/2) (Real.sqrt h/2) (Real.sqrt (h/2)) hv hm
  convert! hl using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  module

lemma halvingKernel_invariant {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    halvingKernel V hV h ∘ₘ noisedLaw V h=noisedLaw V (h/2) := by
  let := halvingKernel_markov hV hh
  let := proximalKernel_markov hV hh
  let := posteriorKernel_probability hV hh
  let := noisedLaw_probability hV h
  let := noisedLaw_probability hV (h/2)
  let := jointPosteriorLaw_probability hV h
  apply measure_eq_of_bounded_integral
  intro f hf hb
  rw [kernel_integral_comp _ _ hf hb]
  let u : Point d × Point d → ℝ := fun p => ∫g,f ((1/2:ℝ) • (p.1+p.2+Real.sqrt h • g)) ∂stdGaussian (Point d)
  have hu : Measurable u := (show Measurable (fun p : (Point d × Point d) × Point d =>
    f ((1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))) from hf.comp (by fun_prop)).stronglyMeasurable.integral_prod_right.measurable
  have hub (p) : |u p|≤1 := bounded_integral (by norm_num) (fun g => hb _)
  have he := posterior_joint_reconstruction hV hh hu (by norm_num : (0:ℝ)≤1) hub
  have hfib (y : Point d) : (∫z,f z ∂halvingKernel V hV h y)=
      ∫z,u (z,y) ∂gibbs (posteriorPotential V h y) := by
    rw [halvingKernel_apply hV hh,integral_map (by fun_prop) hf.aestronglyMeasurable]
    change kernelAction (proximalKernel V hV h) (fun z => f ((1/2:ℝ) • (y+z))) y=_
    rw [proximalKernel]
    rw [kernelAction_comp _ _ (show Measurable (fun z : Point d => f ((1/2:ℝ) • (y+z))) from hf.comp (by fun_prop)) (fun z => hb _)]
    unfold kernelAction
    apply integral_congr_ae
    filter_upwards [] with z
    rw [noiseKernel_apply,integral_map (by fun_prop) (show Measurable (fun z : Point d => f ((1/2:ℝ) • (y+z))) from hf.comp (by fun_prop)).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with g
    congr 1
    module
  simp_rw [hfib]
  rw [he,←halving_gaussian_law hV hh,integral_map (by fun_prop) hf.aestronglyMeasurable]
  exact (integral_prod _ (bounded_integrable (show Measurable (fun p : (Point d × Point d) × Point d => f ((1/2:ℝ) • (p.1.1+p.1.2+Real.sqrt h • p.2))) from hf.comp (by fun_prop)) (fun p => hb _))).symm

namespace OracleCompiler

lemma approximateHalvingKernel_markov (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) : IsMarkovKernel (approximateHalvingKernel S h V hV) := by
  let := approximateProximalKernel_markov S h hV
  unfold approximateHalvingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma approximateHalvingKernel_apply (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (y : Point d) :
    approximateHalvingKernel S h V hV y=
      (approximateProximalKernel S h V hV y).map (fun z => (1/2:ℝ) • (y+z)) := by
  let := approximateProximalKernel_markov S h hV
  rw [approximateHalvingKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma approximateHalvingKernel_tv (S : ℝ → ℝ → ReservedProgram d)
    {V : Point d → ℝ} (hV : Admissible V) {h q K e ηmin : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀y,SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S)
    (y : Point d) :
    TVAtMost (approximateHalvingKernel (S 1 1) h V hV y) (halvingKernel V hV h y)
      (2*e*(Real.sqrt d+2*Real.sqrt h*‖y‖)) := by
  rw [approximateHalvingKernel_apply,halvingKernel_apply hV hh]
  exact (approximateProximalKernel_tv S hV hh hq hq1 he hη hres hc y).map (by fun_prop)

end OracleCompiler
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E : Type*} [MeasurableSpace E]

lemma markovAction_measurable (κ : Kernel E E) [IsMarkovKernel κ]
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) : Measurable (markovAction κ n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    simpa only [markovAction,iterate_succ_apply'] using kernelAction_measurable κ ih

lemma markovAction_bounded (κ : Kernel E E) [IsMarkovKernel κ]
    {f : E → ℝ} {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) (n : ℕ) :
    ∀x,|markovAction κ n f x|≤C := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    simpa only [markovAction,iterate_succ_apply'] using kernelAction_bounded κ hC ih

lemma markovChain_integral (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) (n : ℕ) :
    (∫x,f x ∂markovChain κ μ n)=∫x,markovAction κ n f x ∂μ := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [markovChain,kernel_integral_comp _ _ hf hb]
    change (∫x,kernelAction κ f x ∂markovChain κ μ n)=_
    rw [ih (kernelAction_measurable κ hf) (kernelAction_bounded κ hC hb)]
    rfl

lemma markovChain_invariant (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) (hμ : κ ∘ₘ μ=μ) (n : ℕ) : markovChain κ μ n=μ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [markovChain,ih,hμ]

lemma markovChain_perturbation (κ η : Kernel E E) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure E) [IsProbabilityMeasure μ] {e : E → ℝ} {a : ℝ}
    (he : ∀x,TVAtMost (κ x) (η x) (e x))
    (hi : ∀n,Integrable e (markovChain η μ n))
    (ha : ∀n,(∫x,e x ∂markovChain η μ n)≤a) (n : ℕ) :
    TVAtMost (markovChain κ μ n) (markovChain η μ n) (n*a) := by
  induction n with
  | zero => intro s hs; simp [markovChain]
  | succ n ih =>
    have hh := (ih.kernel κ).trans (TVAtMost.kernel_mixture (markovChain η μ n) κ η (hi n) he)
    apply hh.mono
    push_cast
    linarith [ha n]

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ChangingChain
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R]

lemma changingChain_constant (κ : Kernel E E) (μ : Measure E) (n : ℕ) :
    changingChain (fun _ => κ) μ n=markovChain κ μ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [changingChain,markovChain,ih]

lemma changingChain_tv (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {e : ℝ}
    (he : TVAtMost μ ν e) (n : ℕ) :
    TVAtMost (changingChain κ μ n) (changingChain κ ν n) e := by
  induction n with
  | zero => exact he
  | succ n ih => exact ih.kernel (κ n)

lemma stateLaw_eq_changingChain (μ : Measure E) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (f : ℕ → E × R → E) (hf : ∀n,Measurable (f n))
    (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    (hk : ∀n x,κ n x=γ.map (fun r => f n (x,r))) (n : ℕ) :
    stateLaw μ γ f n=changingChain κ μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateLaw,changingChain,ih]
    haveI : IsProbabilityMeasure (((changingChain κ μ n).prod γ).map (f n)) :=
      Measure.isProbabilityMeasure_map (hf n).aemeasurable
    apply measure_eq_of_bounded_integral
    intro g hg hb
    rw [kernel_integral_comp _ _ hg hb,integral_map (hf n).aemeasurable hg.aestronglyMeasurable]
    rw [integral_prod _ (show Integrable (fun p => g (f n p)) _ from bounded_integrable (hg.comp (hf n)) (fun p => hb _))]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hk]
    exact (integral_map ((hf n).comp (show Measurable (fun r : R => (x,r)) by fun_prop)).aemeasurable hg.aestronglyMeasurable).symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma integral_norm_le_sqrt_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    (hm : MemLp (fun x : E => x) 2 μ) :
    (∫x,‖x‖ ∂μ)≤Real.sqrt (∫x,‖x‖^2 ∂μ) := by
  have hh := integral_mul_sq_le hm.norm (memLp_const (1:ℝ) (μ:=μ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).2 hh

lemma Admissible.first_moment_bound {V : Point d → ℝ} (hV : Admissible V) :
    Integrable (fun x => ‖x‖) (gibbs V) ∧ (∫x,‖x‖ ∂gibbs V)≤Real.sqrt d := by
  let := hV.isProbabilityMeasure_gibbs
  have hm : MemLp (fun x : Point d => x) 2 (gibbs V) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 hV.second_moment_bound.1
  exact ⟨hm.norm.integrable (by norm_num),(integral_norm_le_sqrt_moment hm).trans
    (Real.sqrt_le_sqrt hV.second_moment_bound.2)⟩

lemma stdGaussian_first_moment_bound (d : ℕ) :
    (∫x : Point d,‖x‖ ∂stdGaussian (Point d))≤Real.sqrt d := by
  simpa only [stdGaussian_sq_norm] using
    integral_norm_le_sqrt_moment (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))

lemma noisedLaw_first_moment {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    Integrable (fun x => ‖x‖) (noisedLaw V h) ∧
      (∫x,‖x‖ ∂noisedLaw V h)≤(1+Real.sqrt h)*Real.sqrt d := by
  let := hV.isProbabilityMeasure_gibbs
  have hiX : Integrable (fun p : Point d × Point d => ‖p.1‖)
      ((gibbs V).prod (stdGaussian (Point d))) := hV.first_moment_bound.1.comp_fst _
  have hiG : Integrable (fun p : Point d × Point d => ‖p.2‖)
      ((gibbs V).prod (stdGaussian (Point d))) :=
    (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable (by norm_num) |>.comp_snd _
  have hi : Integrable (fun p : Point d × Point d => ‖p.1+Real.sqrt h • p.2‖)
      ((gibbs V).prod (stdGaussian (Point d))) :=
    (hiX.add (hiG.const_mul (Real.sqrt h))).mono' (by fun_prop) (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      change ‖p.1+Real.sqrt h • p.2‖≤‖p.1‖+Real.sqrt h*‖p.2‖
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
        norm_add_le p.1 (Real.sqrt h • p.2)))
  refine ⟨(integrable_map_measure (by fun_prop) (by fun_prop)).2 hi,?_⟩
  rw [noisedLaw,integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫p : Point d × Point d,‖p.1‖+Real.sqrt h*‖p.2‖ ∂((gibbs V).prod (stdGaussian (Point d))) := by
      apply integral_mono hi (hiX.add (hiG.const_mul _))
      intro p
      change ‖p.1+Real.sqrt h • p.2‖≤‖p.1‖+Real.sqrt h*‖p.2‖
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
        norm_add_le p.1 (Real.sqrt h • p.2)
    _ = (∫x,‖x‖ ∂gibbs V)+Real.sqrt h*(∫x : Point d,‖x‖ ∂stdGaussian (Point d)) := by
      rw [integral_add hiX (hiG.const_mul _),integral_const_mul]
      simp only [integral_fun_fst,integral_fun_snd,probReal_univ,one_smul]
    _ ≤ Real.sqrt d+Real.sqrt h*Real.sqrt d := by
      exact add_le_add hV.first_moment_bound.2
        (mul_le_mul_of_nonneg_left (stdGaussian_first_moment_bound d) (Real.sqrt_nonneg _))
    _ = _ := by ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal RealInnerProductSpace

variable {d : ℕ}

lemma Admissible.value_difference_bound {V : Point d → ℝ} (hV : Admissible V)
    (x g : Point d) {s : ℝ} (hs : 0 ≤ s) :
    |V (x+s • g)-V x|≤ s*‖x‖^2+(s+s^2)*‖g‖^2 := by
  have ht := quadratic_remainder_of_gradient_lipschitz hV.smooth hV.gradient_lipschitz x (s • g)
  have hi := abs_real_inner_le_norm (s • g) (gradient V x)
  have hg := hV.gradient_norm_le x
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,NNReal.coe_ofNat] at ht hi
  have hh := abs_add_le (V (x+s • g)-V x-inner ℝ (s • g) (gradient V x))
    (inner ℝ (s • g) (gradient V x))
  have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg hs (norm_nonneg g))
  have hsq := mul_nonneg hs (sq_nonneg (‖x‖-‖g‖))
  ring_nf at hh
  nlinarith

theorem noisedLaw_tv {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) :
    TVAtMost (noisedLaw V h) (gibbs V) (2*(2*Real.sqrt h+h)*d) := by
  let := hV.isProbabilityMeasure_gibbs
  have hVm := hV.smooth.continuous.measurable
  let := jointPosteriorLaw_probability hV h
  let H := fun p : Point d × Point d => -V p.1-‖p.2-p.1‖^2/(2*h)
  let c := (partition V)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt h)
  have hm : Measurable H := by have := hV.smooth.continuous.measurable; dsimp [H]; fun_prop
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.partition_ne_top)
    (EulerDensity.noiseCoefficient_positive d (Real.sqrt_pos.mpr hh).ne').ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.partition_pos.ne')
    (EulerDensity.noiseCoefficient_finite _ _)
  have hd : jointPosteriorLaw V h=MetropolisBalance.densityLaw volume c H := by
    have hd := EulerDensity.joint_density hV.smooth.continuous.measurable
      (fun z : Point d => z) measurable_id (Real.sqrt_pos.mpr hh).ne'
    simpa only [jointPosteriorLaw,MetropolisBalance.densityLaw,c,H,Real.sq_sqrt hh.le] using hd
  have he (p : Point d × Point d) : |H (p.1,p.1+Real.sqrt h • p.2)-H (p.1+Real.sqrt h • p.2,p.1)|
      =|V (p.1+Real.sqrt h • p.2)-V p.1| := by
    dsimp [H]
    rw [norm_sub_rev p.1 (p.1+Real.sqrt h • p.2)]
    congr 1
    ring
  let b := fun p : Point d × Point d => Real.sqrt h*‖p.1‖^2+(Real.sqrt h+h)*‖p.2‖^2
  have hib : Integrable b ((gibbs V).prod (stdGaussian (Point d))) :=
    (hV.second_moment_bound.1.comp_fst _ |>.const_mul _).add
      (((memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))).comp_snd _ |>.const_mul _)
  have hb (p : Point d × Point d) : |V (p.1+Real.sqrt h • p.2)-V p.1|≤b p := by
    simpa only [Real.sq_sqrt hh.le] using hV.value_difference_bound p.1 p.2 (Real.sqrt_nonneg h)
  have hir : Integrable (fun p : Point d × Point d => |H p-H p.swap|) (jointPosteriorLaw V h) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    apply hib.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by simpa only [comp_apply,Prod.swap_prod_mk,Real.norm_eq_abs,abs_abs,he] using hb p)
  have hr : (∫p,|H p-H p.swap| ∂jointPosteriorLaw V h)≤(2*Real.sqrt h+h)*d := by
    rw [jointPosteriorLaw,integral_map (by fun_prop) (by fun_prop)]
    simp only [Prod.swap_prod_mk]
    simp_rw [he]
    have hi : Integrable (fun p : Point d × Point d => |V (p.1+Real.sqrt h • p.2)-V p.1|)
        ((gibbs V).prod (stdGaussian (Point d))) :=
      hib.mono' (by fun_prop) (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_abs] using hb p))
    calc
      _ ≤ ∫p,b p ∂((gibbs V).prod (stdGaussian (Point d))) := integral_mono hi hib hb
      _ = Real.sqrt h*(∫x,‖x‖^2 ∂gibbs V)+(Real.sqrt h+h)*d := by
        dsimp only [b]
        rw [integral_add]
        · rw [integral_const_mul,integral_const_mul,integral_fun_fst (fun x : Point d => ‖x‖^2),integral_fun_snd (fun x : Point d => ‖x‖^2)]
          simp only [probReal_univ,one_smul,stdGaussian_sq_norm]
        · exact hV.second_moment_bound.1.comp_fst _ |>.const_mul _
        · simpa only [id_eq] using ((memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))).comp_snd ((gibbs V)) |>.const_mul (Real.sqrt h+h)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hV.second_moment_bound.2 (Real.sqrt_nonneg h)]
  let : IsFiniteMeasure (MetropolisBalance.densityLaw volume c H) := hd ▸ inferInstance
  intro A hA
  let f : Point d → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hbf (x) : |f x|≤1 := by by_cases hx : x∈A <;> simp [f,hx]
  have ht := MetropolisBalance.probability_one_step_defect volume hm hc0 hct
    (hd ▸ hir) hf (by norm_num : (0:ℝ)≤1) hbf
  rw [←hd] at ht
  have hs : (∫p : Point d × Point d,f p.2 ∂jointPosteriorLaw V h)=(noisedLaw V h).real A := by
    rw [←jointPosterior_snd (V:=V) h,←integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  have ht' : (∫p : Point d × Point d,f p.1 ∂jointPosteriorLaw V h)=(gibbs V).real A := by
    rw [←jointPosterior_fst (V:=V) h,←integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  rw [hs,ht'] at ht
  nlinarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma descentScale_pos {h : ℝ} (hh : 0<h) (j : ℕ) : 0<descentScale h j := by unfold descentScale; positivity
lemma descentScale_le {h : ℝ} (hh : 0≤h) (j : ℕ) : descentScale h j≤h := by
  exact div_le_self hh (one_le_pow₀ (by norm_num))
lemma descentScale_succ (h : ℝ) (j : ℕ) : descentScale h (j+1)=descentScale h j/2 := by simp [descentScale,pow_succ,div_div]

lemma halving_chain_error {V : Point d → ℝ} (hV : Admissible V) {h e : ℝ}
    (hh : 0<h) (hh1 : h≤1) (he : 0≤e)
    (κ : ℕ → Kernel (Point d) (Point d)) [∀j,IsMarkovKernel (κ j)]
    (hc : ∀j x,TVAtMost (κ j x) (halvingKernel V hV (descentScale h j) x)
      (2*e*(Real.sqrt d+2*Real.sqrt (descentScale h j)*‖x‖))) (j : ℕ) :
    TVAtMost (changingChain κ (noisedLaw V h) j) (noisedLaw V (descentScale h j))
      (j*(10*e*Real.sqrt d)) := by
  let := noisedLaw_probability hV h
  induction j with
  | zero => intro A hA; simp [changingChain]
  | succ j ih =>
    let hj := descentScale h j
    have hjp : 0<hj := descentScale_pos hh j
    have hj1 : hj≤1 := (descentScale_le hh.le j).trans hh1
    have hs : Real.sqrt hj≤1 := by simpa using Real.sqrt_le_sqrt hj1
    let := noisedLaw_probability hV hj
    let := halvingKernel_markov hV hjp
    let ei := fun x : Point d => 2*e*(Real.sqrt d+2*Real.sqrt hj*‖x‖)
    have hei : Integrable ei (noisedLaw V hj) := by
      exact ((integrable_const _).add ((noisedLaw_first_moment hV hj).1.const_mul _)).const_mul _
    have heint : (∫x,ei x ∂noisedLaw V hj)≤10*e*Real.sqrt d := by
      have hx := (noisedLaw_first_moment hV hj).2
      have hx' : (∫x,‖x‖ ∂noisedLaw V hj)≤2*Real.sqrt d := by
        nlinarith [Real.sqrt_nonneg (d:ℝ)]
      have hxs : Real.sqrt hj*(∫x,‖x‖ ∂noisedLaw V hj)≤2*Real.sqrt d := by
        exact (mul_le_mul_of_nonneg_right hs (integral_nonneg (fun _ => norm_nonneg _))).trans (by simpa using hx')
      dsimp only [ei]
      rw [integral_const_mul,integral_add (integrable_const _) ((noisedLaw_first_moment hV hj).1.const_mul _),integral_const_mul]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      nlinarith
    have hl := TVAtMost.kernel_mixture (noisedLaw V hj) (κ j) (halvingKernel V hV hj) hei (hc j)
    rw [halvingKernel_invariant hV hjp] at hl
    have ht := (ih.kernel (κ j)).trans hl
    change TVAtMost _ (noisedLaw V (hj/2)) _ at ht
    rw [changingChain,descentScale_succ]
    apply ht.mono
    push_cast
    nlinarith

namespace OracleCompiler
lemma approximateHalvingKernel_program (S : ReservedProgram d) (h : ℝ)
    {V : Point d → ℝ} (hV : Admissible V) (x : Point d) :
    approximateHalvingKernel S h V hV x=(gaussianTape d S.full.slots).map
      (fun g => (halvingProgram S h).run V (x,g)) := by
  have hm : Measurable (fun g => (proximalProgram S h).run V (x,g)) :=
    ((proximalProgram S h).measurable_run V hV.continuous_firstOrderReply.measurable).comp (by fun_prop)
  rw [approximateHalvingKernel_apply,approximateProximalKernel_apply,Measure.map_map (by fun_prop) hm]
  congr 1
  funext g
  rw [halvingProgram,Program.map_run]
  rfl
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AverageLipschitz
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma zero_average_lipschitz {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x => ‖x‖) μ) {f : Point d → ℝ}
    (hf : Measurable f) {C L : ℝ} (hb : ∀x,|f x|≤C)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    |f 0-(∫x,f x ∂μ)|≤L*(∫x,‖x‖ ∂μ) := by
  have he : f 0-(∫x,f x ∂μ)=∫x,(f 0-f x) ∂μ := by
    rw [integral_sub (integrable_const _) (bounded_integrable hf hb)]
    simp
  rw [he,←Real.norm_eq_abs,←integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ((integrable_const (f 0)).sub (bounded_integrable hf hb)).norm (hi.const_mul L)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs,dist_zero_left] using hl 0 x

lemma proximal_iterate_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C)
    (hb : ∀x,|f x|≤C) (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) (n : ℕ) :
    ∀x y,|markovAction (proximalKernel V hV h) n f x-markovAction (proximalKernel V hV h) n f y|
      ≤(L/(1+h)^n)*dist x y := by
  let := proximalKernel_markov hV hh
  induction n with
  | zero => simpa only [markovAction,iterate_zero,id_eq,pow_zero,div_one] using hl
  | succ n ih =>
    have he := proximal_action_lipschitz hV hh
      (markovAction_measurable _ hf n) hC (markovAction_bounded _ hC hb n) (by positivity) ih
    intro x y
    simp only [markovAction,iterate_succ_apply']
    convert! he x y using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_succ,div_div]

lemma proximal_iterate_smoothing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} (hf : Measurable f) (hb : ∀x,0≤f x ∧ f x≤1) (n : ℕ) :
    ∀x y,|markovAction (proximalKernel V hV h) (n+1) f x-
      markovAction (proximalKernel V hV h) (n+1) f y|≤
      (1/((1+h)^(n+1)*Real.sqrt h))*dist x y := by
  let := proximalKernel_markov hV hh
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have he := proximal_iterate_lipschitz hV hh (kernelAction_measurable _ hf) (by norm_num : (0:ℝ)≤1)
    (kernelAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf)
    (by positivity : 0≤1/((1+h)*Real.sqrt h)) (proximal_action_smoothing hV hh hf hb) n
  intro x y
  simp only [markovAction,iterate_succ_apply]
  convert! he x y using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [div_div,pow_succ]
  congr 1
  ring

theorem proximal_chain_mixing {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (n : ℕ) :
    TVAtMost (markovChain (proximalKernel V hV h) (Measure.dirac 0) (n+1)) (noisedLaw V h)
      (((1+Real.sqrt h)*Real.sqrt d)/((1+h)^(n+1)*Real.sqrt h)) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  intro A hA
  let f : Point d → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hb (x) : 0≤f x ∧ f x≤1 := by by_cases hx : x∈A <;> simp [f,hx]
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hact := markovChain_integral (proximalKernel V hV h) (Measure.dirac 0) hf (C:=1) (by norm_num) hbf (n+1)
  have hint := markovChain_integral (proximalKernel V hV h) (noisedLaw V h) hf (C:=1) (by norm_num) hbf (n+1)
  rw [markovChain_invariant _ _ (proximalKernel_invariant hV hh)] at hint
  have he := zero_average_lipschitz (noisedLaw_first_moment hV h).1
    (markovAction_measurable _ hf (n+1)) (markovAction_bounded _ (by norm_num : (0:ℝ)≤1) hbf (n+1))
    (proximal_iterate_smoothing hV hh hf hb n)
  simp only [integral_dirac] at hact
  rw [←hint,←hact] at he
  have hif (μ : Measure (Point d)) : (∫x,f x ∂μ)=μ.real A := by
    simp only [f,integral_indicator hA,setIntegral_const,smul_eq_mul,mul_one]
  simp only [hif] at he
  apply he.trans
  calc
    _ ≤ (1/((1+h)^(n+1)*Real.sqrt h))*((1+Real.sqrt h)*Real.sqrt d) :=
      mul_le_mul_of_nonneg_left (noisedLaw_first_moment hV h).2 (by positivity)
    _ = _ := by ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

lemma proximal_chain_observable {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    {f : Point d → ℝ} {L C : ℝ} (hf : Measurable f) (hC : 0≤C)
    (hb : ∀x,|f x|≤C) (hL : 0≤L) (hl : ∀x y,|f x-f y|≤L*dist x y) (n : ℕ) :
    |(∫x,f x ∂markovChain (proximalKernel V hV h) (Measure.dirac 0) n)-
      (∫x,f x ∂noisedLaw V h)|≤L*((1+Real.sqrt h)*Real.sqrt d) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  have hact := markovChain_integral (proximalKernel V hV h) (Measure.dirac 0) hf hC hb n
  have hint := markovChain_integral (proximalKernel V hV h) (noisedLaw V h) hf hC hb n
  rw [markovChain_invariant _ _ (proximalKernel_invariant hV hh)] at hint
  have he := zero_average_lipschitz (noisedLaw_first_moment hV h).1
    (markovAction_measurable _ hf n) (markovAction_bounded _ hC hb n)
    (proximal_iterate_lipschitz hV hh hf hC hb hL hl n)
  simp only [integral_dirac] at hact
  rw [←hint,←hact] at he
  apply he.trans
  have hpow : (1:ℝ)≤(1+h)^n := one_le_pow₀ (by linarith)
  have hdv : L/(1+h)^n≤L := (div_le_self hL hpow)
  exact mul_le_mul hdv (noisedLaw_first_moment hV h).2 (integral_nonneg (fun _ => norm_nonneg _)) hL

lemma TVAtMost.cap_one {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {e : ℝ} (he : TVAtMost μ ν e) : TVAtMost μ ν (min e 1) := by
  intro A hA
  refine le_min (he A hA) ?_
  exact abs_sub_le_iff.mpr ⟨by linarith [measureReal_le_one (μ:=μ) (s:=A),measureReal_nonneg (μ:=ν) (s:=A)],
    by linarith [measureReal_le_one (μ:=ν) (s:=A),measureReal_nonneg (μ:=μ) (s:=A)]⟩

lemma proximal_local_cap_lipschitz {a b : ℝ} (hb : 0≤b) :
    ∀x y : Point d,|min (a+b*‖x‖) 1-min (a+b*‖y‖) 1|≤b*dist x y := by
  intro x y
  have ht := abs_min_sub_min_le_max (a+b*‖x‖) (1:ℝ) (a+b*‖y‖) 1
  simp only [sub_self,abs_zero] at ht
  apply ht.trans
  have he : a+b*‖x‖-(a+b*‖y‖)=b*(‖x‖-‖y‖) := by ring
  rw [he,abs_mul,abs_of_nonneg hb]
  apply max_le
  · simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) hb
  · positivity

theorem proximal_chain_perturbation {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h)
    (κ : Kernel (Point d) (Point d)) [IsMarkovKernel κ] {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (he : ∀x,TVAtMost (κ x) (proximalKernel V hV h x) (a+b*‖x‖)) (n : ℕ) :
    TVAtMost (markovChain κ (Measure.dirac 0) n)
      (markovChain (proximalKernel V hV h) (Measure.dirac 0) n)
      (n*(a+2*b*((1+Real.sqrt h)*Real.sqrt d))) := by
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  let e : Point d → ℝ := fun x => min (a+b*‖x‖) 1
  have hm : Measurable e := by dsimp [e]; fun_prop
  have he0 (x) : 0≤e x := le_min (by positivity) (by norm_num)
  have he1 (x) : |e x|≤1 := by rw [abs_of_nonneg (he0 x)]; exact min_le_right _ _
  apply markovChain_perturbation κ (proximalKernel V hV h) (Measure.dirac 0)
    (fun x => (he x).cap_one) (fun n => bounded_integrable hm he1)
  intro k
  have hstat : (∫x,e x ∂noisedLaw V h)≤a+b*((1+Real.sqrt h)*Real.sqrt d) := by
    calc
      _ ≤ ∫x,(a+b*‖x‖) ∂noisedLaw V h := integral_mono (bounded_integrable hm he1)
        ((integrable_const a).add ((noisedLaw_first_moment hV h).1.const_mul b))
        (fun x => min_le_left _ _)
      _ = a+b*(∫x,‖x‖ ∂noisedLaw V h) := by
        rw [integral_add (integrable_const a) ((noisedLaw_first_moment hV h).1.const_mul b),integral_const_mul]
        simp
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (noisedLaw_first_moment hV h).2 hb) a
  have hc := proximal_chain_observable hV hh hm (by norm_num : (0:ℝ)≤1) he1 hb
    (proximal_local_cap_lipschitz hb) k
  linarith [(le_abs_self ((∫x,e x ∂markovChain (proximalKernel V hV h) (Measure.dirac 0) k)-
      (∫x,e x ∂noisedLaw V h)))]

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TopProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

lemma topProgram_law (S : ReservedProgram d) (h : ℝ) (N J : ℕ)
    {V : Point d → ℝ} (hV : Admissible V) :
    (topSeedLaw S N J).map ((topProgram S h N J).run V)=
      changingChain (fun j => approximateHalvingKernel S (descentScale h j) V hV)
        (markovChain (approximateProximalKernel S h V hV) (Measure.dirac 0) N) J := by
  let (j : ℕ) : IsMarkovKernel (approximateHalvingKernel S (descentScale h j) V hV) :=
    approximateHalvingKernel_markov _ _ _
  let := approximateProximalKernel_markov S h hV
  have hVm := hV.continuous_firstOrderReply.measurable
  rw [topProgram,topSeedLaw,Program.independentSeq_law _ _ hVm,
    Program.fresh_law (fun _ => proximalProgram S h) hVm]
  rw [stateLaw_eq_changingChain _ _ _ (fun _ => (proximalProgram S h).measurable_run V hVm)
    (fun _ => approximateProximalKernel S h V hV) (fun _ => approximateProximalKernel_apply S h hV),
    changingChain_constant]
  rw [Program.fresh_law _ hVm]
  exact stateLaw_eq_changingChain _ _ _
    (fun j => (halvingProgram S (descentScale h j)).measurable_run V hVm)
    _ (fun j => approximateHalvingKernel_program S (descentScale h j) hV) J

lemma affine_correct_from_uniform (S : ℝ → ℝ → ReservedProgram d) {q K e ηmin : ℝ}
    (hc : ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
      SampleCorrect F lam q K e ηmin S)
    {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) (hh1 : 2*h≤1) (y : Point d) :
    SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S := by
  have hp : (0:ℝ)<2*(Real.sqrt h)^2 := by rw [Real.sq_sqrt hh.le]; positivity
  have hl : 2*(Real.sqrt h)^2≤1 := by rwa [Real.sq_sqrt hh.le]
  have he := hc (hV.affinePrimitive y (Real.sqrt h)) (show (0:ℝ≥0)<⟨2*(Real.sqrt h)^2,by positivity⟩ from hp) hl
  change SampleCorrect _ (2*(Real.sqrt h)^2) q K e ηmin S at he
  simpa only [Real.sq_sqrt hh.le] using he

theorem topProgram_accuracy (S : ℝ → ℝ → ReservedProgram d) {q K e ηmin h : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
      SampleCorrect F lam q K e ηmin S)
    (n J : ℕ) {V : Point d → ℝ} (hV : Admissible V) :
    TVAtMost ((topSeedLaw (S 1 1) (n+1) J).map ((topProgram (S 1 1) h (n+1) J).run V))
      (gibbs V)
      (((n+1)*18+J*10)*e*Real.sqrt d+
        ((1+Real.sqrt h)*Real.sqrt d)/((1+h)^(n+1)*Real.sqrt h)+
        2*(2*Real.sqrt (descentScale h J)+descentScale h J)*d) := by
  let T := S 1 1
  have hh1 : h≤1 := by linarith
  have hs : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt hh1
  have hloc := approximateProximalKernel_tv S hV hh hq hq1 he hη hres
    (affine_correct_from_uniform S hc hV hh (by linarith))
  let := approximateProximalKernel_markov T h hV
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  let := noisedLaw_probability hV (descentScale h J)
  let (j : ℕ) : IsMarkovKernel (approximateHalvingKernel T (descentScale h j) V hV) :=
    approximateHalvingKernel_markov _ _ _
  have hp := proximal_chain_perturbation hV hh (approximateProximalKernel T h V hV)
    (a:=2*e*Real.sqrt d) (b:=4*e*Real.sqrt h) (by positivity) (by positivity)
    (fun x => by convert! hloc x using 1; ring) (n+1)
  have hp' : TVAtMost (markovChain (approximateProximalKernel T h V hV) (Measure.dirac 0) (n+1))
      (markovChain (proximalKernel V hV h) (Measure.dirac 0) (n+1))
      ((n+1)*(18*e*Real.sqrt d)) := by
    apply hp.mono
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hss : Real.sqrt h*(1+Real.sqrt h)≤2 := by nlinarith [Real.sqrt_nonneg h]
    nlinarith [mul_le_mul_of_nonneg_right hss (by positivity : 0≤e*Real.sqrt d)]
  have hm := hp'.trans (proximal_chain_mixing hV hh n)
  have hd := halving_chain_error hV hh hh1 he
    (fun j => approximateHalvingKernel T (descentScale h j) V hV)
    (fun j x => approximateHalvingKernel_tv S hV (descentScale_pos hh j)
      (by linarith [descentScale_le hh.le j]) hq1 he hη hres
      (affine_correct_from_uniform S hc hV (descentScale_pos hh j)
        (by linarith [descentScale_le hh.le j])) x) J
  have ht := ((changingChain_tv _ hm J).trans hd).trans
    (noisedLaw_tv hV (descentScale_pos hh J))
  rw [topProgram_law _ _ _ _ hV]
  apply ht.mono
  ring_nf
  rfl

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TopScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

lemma topScale_pos {κ : ℝ} {d : ℕ} (hd : 0<d) : 0<topScale κ d := by
  unfold topScale
  exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hd) _) (by norm_num)
lemma topScale_le_one {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) : topScale κ d≤1/4 := by
  unfold topScale
  exact div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)) (by norm_num)
lemma topScale_inv_rate (κ : ℝ) : LogPowerRate (fun d => (topScale κ d)⁻¹) (-κ) := by
  simpa only [topScale,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_comm] using (LogPowerRate.inv_power κ).const_mul 4

lemma LogPowerRate.natCeil {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (ha : a≤0)
    (hfp : ∀ᶠ d in atTop,0≤f d) : LogPowerRate (fun d => (⌈f d⌉₊:ℝ)) a := by
  apply LogPowerRate.of_le (hf.add ((LogPowerRate.const 1).mono ha))
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [hfp] with d hd
    exact (Nat.ceil_lt_add_one hd).le

lemma proximalRounds_rate {κ : ℝ} (hκ : 0≤κ) :
    LogPowerRate (fun d => (proximalRounds κ d:ℝ)) (-κ) := by
  have hr := (LogPowerRate.log.const_mul (40*(1+κ))).mul (topScale_inv_rate κ)
  rw [zero_add] at hr
  have hc := LogPowerRate.natCeil hr (by linarith) (Eventually.of_forall (fun d => by dsimp [topScale]; positivity [dimensionLog_nonneg d,Real.rpow_nonneg (Nat.cast_nonneg d) (-κ)]))
  simpa only [proximalRounds,Nat.cast_add,Nat.cast_one,div_eq_mul_inv] using hc.add ((LogPowerRate.const 1).mono (by linarith))

lemma descentRounds_rate : LogPowerRate (fun d => (descentRounds d:ℝ)) 0 := by
  exact LogPowerRate.natCeil ((LogPowerRate.log.const_mul 20).div_const (Real.log 2)) le_rfl
    (Eventually.of_forall (fun d => by positivity [dimensionLog_nonneg d,Real.log_pos (by norm_num : (1:ℝ)<2)]))

lemma log_dimension_le {d : ℕ} (hd : 0<d) : Real.log (d:ℝ)≤dimensionLog d := by
  have hh := Real.log_le_log (by exact_mod_cast hd : (0:ℝ)<d) (by linarith : (d:ℝ)≤(d:ℝ)+1)
  unfold dimensionLog
  linarith

lemma proximalRounds_power {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    (d:ℝ)^(20*(1+κ))≤(1+topScale κ d)^(proximalRounds κ d) := by
  let h := topScale κ d
  have hp : 0<h := topScale_pos (by omega)
  have hb : h≤1 := (topScale_le_one hκ hd).trans (by norm_num)
  have hl : h/2≤Real.log (1+h) := by
    have he := Real.le_log_one_add_of_nonneg hp.le
    have he' : h/2≤2*h/(h+2) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    exact he'.trans he
  have hn : 40*(1+κ)*dimensionLog d/h≤(proximalRounds κ d:ℝ) := by
    have he := Nat.le_ceil (40*(1+κ)*dimensionLog d/h)
    dsimp [proximalRounds]
    push_cast
    linarith
  have hn' := (div_le_iff₀ hp).mp hn
  have hln := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (proximalRounds κ d) : (0:ℝ)≤_)
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  rw [Real.rpow_def_of_pos hd0]
  rw [←Real.exp_log (by positivity : 0<(1+h)^(proximalRounds κ d)),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (log_dimension_le (by omega : 0<d)) (by positivity : 0≤20*(1+κ))
  nlinarith

lemma descentRounds_power (d : ℕ) (hd : 1≤d) : (d:ℝ)^20≤(2:ℝ)^(descentRounds d) := by
  have hn := Nat.le_ceil (20*dimensionLog d/Real.log 2)
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hn' := (div_le_iff₀ hp).mp hn
  rw [←Real.exp_log (by positivity : 0<(d:ℝ)^20),Real.log_pow,
    ←Real.exp_log (by positivity : 0<(2:ℝ)^(descentRounds d)),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hd' := log_dimension_le (by omega : 0<d)
  dsimp [descentRounds]
  linarith

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MixingEnvelope
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

lemma LogPowerRate.dimension : LogPowerRate (fun d : ℕ => (d:ℝ)) (-1) := by
  simpa only [neg_neg,Real.rpow_one] using LogPowerRate.power (-1)

lemma mixingEnvelope_rate (κ : ℝ) : LogPowerRate (mixingEnvelope κ) (19+19*κ) := by
  have hh := (((LogPowerRate.dimension.const_mul 2).mul (LogPowerRate.power (20*(1+κ)))).mul
    (topScale_inv_rate κ))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma mixing_error_le {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    ((1+Real.sqrt (topScale κ d))*Real.sqrt d)/
      ((1+topScale κ d)^(proximalRounds κ d)*Real.sqrt (topScale κ d)) ≤ mixingEnvelope κ d := by
  let h := topScale κ d
  have hp : 0<h := topScale_pos (by omega)
  have h1 : h≤1 := (topScale_le_one hκ hd).trans (by norm_num)
  have hs1 : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt h1
  have hs : h≤Real.sqrt h := by nlinarith [Real.sq_sqrt hp.le,Real.sqrt_nonneg h]
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hsd : Real.sqrt d≤d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ)]
  have hnum : (1+Real.sqrt h)*Real.sqrt d≤2*d := by
    nlinarith [Real.sqrt_nonneg (d:ℝ)]
  have hden : (d:ℝ)^(20*(1+κ))*h≤(1+h)^(proximalRounds κ d)*Real.sqrt h :=
    mul_le_mul (proximalRounds_power hκ hd) hs hp.le (by positivity)
  calc
    _ ≤ (2*(d:ℝ))/((1+h)^(proximalRounds κ d)*Real.sqrt h) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2*(d:ℝ))/((d:ℝ)^(20*(1+κ))*h) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      dsimp [mixingEnvelope,h]
      rw [Real.rpow_neg (Nat.cast_nonneg d)]
      ring

lemma descent_error_le {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    2*(2*Real.sqrt (descentScale (topScale κ d) (descentRounds d))+
      descentScale (topScale κ d) (descentRounds d))*d≤6*(d:ℝ)^(-9:ℝ) := by
  let h := descentScale (topScale κ d) (descentRounds d)
  have hp : 0<topScale κ d := topScale_pos (by omega)
  have hpos : 0<h := descentScale_pos hp _
  have h1 : h≤1 := (descentScale_le hp.le _).trans ((topScale_le_one hκ hd).trans (by norm_num))
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hh : h≤1/(d:ℝ)^20 := by
    calc
      _ ≤ 1/(2:ℝ)^(descentRounds d) := div_le_div_of_nonneg_right
        ((topScale_le_one hκ hd).trans (by norm_num : (1:ℝ)/4≤1)) (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (descentRounds_power d hd)
  have hh' : h≤(1/(d:ℝ)^10)^2 := by
    simpa only [div_pow,one_pow,←pow_mul] using hh
  have hs : Real.sqrt h≤1/(d:ℝ)^10 := by
    calc
      _ ≤ Real.sqrt ((1/(d:ℝ)^10)^2) := Real.sqrt_le_sqrt hh'
      _ = _ := Real.sqrt_sq (by positivity)
  have hs1 : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt h1
  have hhs : h≤Real.sqrt h := by nlinarith [Real.sq_sqrt hpos.le,Real.sqrt_nonneg h]
  calc
    _ ≤ 6*(1/(d:ℝ)^10)*d := by
      have he : 2*(2*Real.sqrt h+h)≤6*(1/(d:ℝ)^10) := by linarith
      exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg d)
    _ = _ := by
      rw [Real.rpow_neg (Nat.cast_nonneg d)]
      norm_num
      field_simp

lemma top_asymptotic_errors {κ P : ℝ} (hκ : 0<κ) (hP : κ+3<κ*P)
    {e : ℕ → ℝ} (her : LogPowerRate e (κ*P)) (hep : ∀ᶠ d : ℕ in atTop,0≤e d) :
    ∀ᶠ d : ℕ in atTop,
      (((proximalRounds κ d:ℝ)*18+(descentRounds d:ℝ)*10)*e d*Real.sqrt d+
      ((1+Real.sqrt (topScale κ d))*Real.sqrt d)/
        ((1+topScale κ d)^(proximalRounds κ d)*Real.sqrt (topScale κ d))+
      2*(2*Real.sqrt (descentScale (topScale κ d) (descentRounds d))+
        descentScale (topScale κ d) (descentRounds d))*d)≤1/10 := by
  have hr1 := (((proximalRounds_rate hκ.le).mul_const 18).add
    ((descentRounds_rate.mul_const 10).mono (by linarith))).mul her
  have hr := hr1.mul LogPowerRate.dimension
  have ha := hr.eventually_small (b:=1) (by linarith)
  have hb := (mixingEnvelope_rate κ).eventually_small (b:=1) (by linarith)
  have hc := ((LogPowerRate.power 9).const_mul 6).eventually_small (b:=1) (by norm_num)
  filter_upwards [ha,hb,hc,hep,eventually_ge_atTop (100:ℕ)] with d ha hb hc hep hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hd100 : (100:ℝ)≤d := by exact_mod_cast hd
  have hinv : (d:ℝ)^(-1:ℝ)≤1/100 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hd100
  have hsd : Real.sqrt d≤d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ)]
  have hefirst : (((proximalRounds κ d:ℝ)*18+(descentRounds d:ℝ)*10)*e d*Real.sqrt d)≤(d:ℝ)^(-1:ℝ) :=
    (mul_le_mul_of_nonneg_left hsd (by positivity)).trans ((le_abs_self _).trans ha)
  have hemix := (mixing_error_le hκ.le (by omega : 1≤d)).trans ((le_abs_self _).trans hb)
  have hedesc := (descent_error_le hκ.le (by omega : 1≤d)).trans ((le_abs_self _).trans hc)
  linarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical Topology NNReal

theorem eventually_subpolynomial_sampler_oai {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ d : ℕ in atTop,∃q : ℕ,CanSample d q ∧ (q:ℝ)≤(d:ℝ)^ε := by
  let κ := ε/4
  let P := 10*(1+κ)/κ
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hPeq : κ*P=10*(1+κ) := by dsimp [P]; field_simp
  have hP : 1≤P := by
    apply (le_div_iff₀ hκ).2
    linarith
  have hPerr : κ+3<κ*P := by rw [hPeq]; linarith
  obtain ⟨t,ht,hts,_,K,_,e,her,hep,hproducer⟩ := exists_primitive_producer hκ hP
  have herr := top_asymptotic_errors hκ hPerr her (hep.mono (fun _ h => h.le))
  have hcostRate := (LogPowerRate.power (-(κ*t))).mul
    ((proximalRounds_rate hκ.le).add (descentRounds_rate.mono (by linarith)))
  have hcost := hcostRate.eventually_small (b:= -ε) (by dsimp [κ] at *; nlinarith)
  simp only [neg_neg] at hcost
  filter_upwards [hproducer,herr,hcost,hep,eventually_ge_atTop (2:ℕ)] with d hprod herr hcost hep hd
  obtain ⟨S,B,hB,hbud,hcorr⟩ := hprod
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hd2 : (1:ℝ)<d := by exact_mod_cast (by omega : 1<d)
  have hqpos : 0<(d:ℝ)^(-κ) := Real.rpow_pos_of_pos hd0 _
  have hq1 : (d:ℝ)^(-κ)<1 := Real.rpow_lt_one_of_one_lt_of_neg hd2 (by linarith)
  have hh : 0<topScale κ d := topScale_pos (by omega)
  have hη : (d:ℝ)^(-(κ*t))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by nlinarith)
  let T := S 1 1
  let N := proximalRounds κ d
  let J := descentRounds d
  let q := T.full.calls*N+T.full.calls*J
  refine ⟨q,?_,?_⟩
  · refine ⟨_,inferInstance,topSeedLaw T N J,inferInstance,(topProgram T (topScale κ d) N J).algorithm,?_⟩
    intro V hV
    refine ⟨(topProgram T (topScale κ d) N J).algorithm.measurable_run hV,?_⟩
    rw [show (topProgram T (topScale κ d) N J).algorithm.run V =
      (topProgram T (topScale κ d) N J).run V from funext (Program.algorithm_run _ V)]
    have ha := topProgram_accuracy S hh (show 2*topScale κ d≤(d:ℝ)^(-κ) by unfold topScale; linarith)
      hq1 hep.le hη (hbud 1).reserve hcorr
      ⌈40*(1+κ)*dimensionLog d/topScale κ d⌉₊ J hV
    exact ha.mono (by simpa only [proximalRounds,Nat.cast_add,Nat.cast_one] using herr)
  · have hc : (T.calls:ℝ)≤(d:ℝ)^(κ*t) := (by exact_mod_cast (hbud 1).calls : (T.calls:ℝ)≤B).trans hB
    calc
      (q:ℝ) = (T.calls:ℝ)*((N:ℝ)+J) := by change ((T.calls*N+T.calls*J:ℕ):ℝ)=_; push_cast; ring
      _ ≤ (d:ℝ)^(κ*t)*((N:ℝ)+J) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ |(d:ℝ)^(κ*t)*((N:ℝ)+J)| := le_abs_self _
      _ ≤ _ := hcost

end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.eventually_subpolynomial_sampler_oai := @OAI.LogConcaveSampling.eventually_subpolynomial_sampler_oai
