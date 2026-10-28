-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:57:25.213397+00:00
-- url     : https://prove2.me/submissions/ad4c93d2-99e9-4678-b0d9-1b8cafad2c50

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_array_limit_label_law
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_monomial_tendsto
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_limit_field_along

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
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
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

variable {S : Type*}

lemma sum_range_cutoff (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, if i < m then a i else 0)=∑ i ∈ Finset.range (min n m), a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      by_cases h : n < m
      · have hn : min n m=n := min_eq_left (by omega)
        have hn' : min (n+1) m=n+1 := min_eq_left (by omega)
        rw [hn,hn',ite_eq_left h,Finset.sum_range_succ]
      · have hn : min n m=m := min_eq_right (by omega)
        have hn' : min (n+1) m=m := min_eq_right (by omega)
        rw [hn,hn',ite_eq_right h,add_zero]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLogIntensity
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

lemma standardGaussian_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! hd using 1
  · funext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    norm_num
    ring

lemma standardGaussian_density_mul_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
  ring

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

lemma standardGaussian_integrationByParts {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : Measurable F')
    {C D : ℝ} (hb : ∀ x, |F x| ≤ C) (hb' : ∀ x, |F' x| ≤ D) :
    ∫ x, x * F x ∂gaussianReal 0 1 = ∫ x, F' x ∂gaussianReal 0 1 := by
  have hfm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have h1 : Integrable (fun x => gaussianPDFReal 0 1 x * F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb' x)
  have h2 : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * F x) := by
    have hh := standardGaussian_density_mul_integrable.neg.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    simpa only [neg_mul,Pi.neg_apply] using hh
  have h3 : Integrable (fun x => gaussianPDFReal 0 1 x * F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_deriv x) (fun x _ => hF x) h1 h2 h3
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  rw [he]
  simp only [neg_mul,integral_neg,neg_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

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

lemma tilt_integral_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltIntegral μ v F)
      (∫ x, Real.exp (t * v x) * v x * F x ∂μ) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t 1) (bound := fun _ => Real.exp ((|t|+1)*C) * C * D)
    (F' := fun u x => Real.exp (u * v x) * v x * F x) (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hv.const_mul u |>.exp.mul hF).aestronglyMeasurable)
    (tilt_integrable μ hv hF hC hD hvC hFD t)
    (by fun_prop) (ae_of_all _ fun x u hu => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · have hu' : |u| ≤ |t|+1 := by
      have hh : |u-t| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
      calc
        |u| = |(u-t)+t| := by congr 1; ring
        _ ≤ |u-t|+|t| := abs_add_le _ _
        _ ≤ |t|+1 := by linarith
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (u * v x) ≤ Real.exp ((|t|+1)*C) := by
      apply Real.exp_le_exp.mpr
      apply (le_abs_self (u * v x)).trans
      rw [abs_mul]
      exact mul_le_mul hu' (hvC x) (abs_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul hexp (hvC x) (abs_nonneg _) (Real.exp_pos _).le)
      (hFD x) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hC)
  · convert! (((hasDerivAt_id u).mul_const (v x)).exp.mul_const (F x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]

end Tilt

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

open TopologicalSpace

lemma weak_limit_closed_full {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [HasOuterApproxClosed K]
    {μ : ℕ → ProbabilityMeasure K} {ν : ProbabilityMeasure K}
    (hμ : Tendsto μ atTop (𝓝 ν)) {F : Set K} (hF : IsClosed F)
    (hfull : ∀ n, μ n F = 1) : ν F = 1 := by
  apply le_antisymm (ProbabilityMeasure.apply_le_one _ _)
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have hf (n : ℕ) : (μ n : Measure K) F = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hfull n,ENNReal.coe_one]
  simp only [hf,limsup_const] at h
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact_mod_cast h

lemma compactGGDefect_continuous {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray K) => compactGGDefect μ n i f g) := by
  let f' : CompactArray K →ᵇ ℝ := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let g' (i j : ℕ) : CompactArray K →ᵇ ℝ := g.compContinuous ⟨fun Q => Q i j,by fun_prop⟩
  have hf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f'
  have hg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (g' i j)
  have hfg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f' * g' i j)
  exact (continuous_const.mul (hfg i n) |>.sub (hf.mul (hg 0 1))).sub
    (continuous_finsetSum _ fun j _ => hfg i j)

lemma compactGGDefect_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] {μ : ℕ → ProbabilityMeasure (CompactArray K)}
    {ν : ProbabilityMeasure (CompactArray K)} (hμ : Tendsto μ atTop (𝓝 ν))
    (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ)
    (hdef : Tendsto (fun k => compactGGDefect (μ k) n i f g) atTop (𝓝 0)) :
    compactGGDefect ν n i f g = 0 :=
  tendsto_nhds_unique ((compactGGDefect_continuous n i f g).continuousAt.tendsto.comp hμ) hdef

lemma compactGG_joint_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) {n : ℕ} (hn : 0 < n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ), compactGGDefect μ n i f g = 0) :
    (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i n)) =
      ((n : ℝ≥0)⁻¹) •
        (((μ : Measure (CompactArray K)).map (compactBlock n)).prod
            ((μ : Measure (CompactArray K)).map (fun Q => Q 0 1)) +
          ∑ j ∈ Finset.univ.erase i,
            (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i j))) := by
  classical
  have hb := (compactBlock_continuous (K := K) n).measurable
  have he (k l : ℕ) : Measurable (fun Q : CompactArray K => Q k l) := by fun_prop
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : (CompactBlock K n × K) →ᵇ ℝ :=
    (f.compContinuous ⟨Prod.fst,continuous_fst⟩) * (g.compContinuous ⟨Prod.snd,continuous_snd⟩)
  have hF : ∀ ρ : Measure (CompactBlock K n × K), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ hρ
    exact F.integrable ρ
  change ∫ p, F p ∂_ = ∫ p, F p ∂_
  rw [integral_smul_nnreal_measure,integral_add_measure (hF _ inferInstance) (hF _ inferInstance),
    integral_finsetSum_measure]
  · simp_rw [integral_map (hb.prodMk (he _ _)).aemeasurable F.continuous.aestronglyMeasurable]
    simp only [F,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,NNReal.smul_def,NNReal.coe_inv,NNReal.coe_natCast,smul_eq_mul]
    rw [integral_prod_mul,integral_map hb.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map (he 0 1).aemeasurable g.continuous.aestronglyMeasurable]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := hGG f g
    unfold compactGGDefect at h
    apply (mul_right_inj' hn').mp
    rw [←mul_assoc,mul_inv_cancel₀ hn',one_mul]
    linarith [h]
  · intro j hj
    exact hF _ inferInstance

open scoped Polynomial

lemma trial_integrable (m : Trial) : Integrable m timeLaw := by
  change Integrable m (volume : Measure Time)
  apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (m.nonneg t)]
    exact m.le_one t

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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
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

lemma brownianEval_measurable (t : ℝ≥0) : Measurable (brownianEval t) :=
  (continuous_eval_const t).measurable

lemma usualBrownianSigma_le_completion (P : Measure BrownianPath) (t : Time) :
    usualBrownianSigma P t ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) := by
  unfold usualBrownianSigma
  refine (iInf_le _ (⟨2, lt_of_le_of_lt t.property.2 (by norm_num)⟩ :
    {s : ℝ≥0 // (t : ℝ) < s})).trans ?_
  apply sup_le
  · apply iSup_le
    intro r
    exact (brownianEval_measurable r.val).comap_le.trans
      (fun _ hs => hs.nullMeasurableSet)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact NullMeasurableSet.of_null hs

lemma progressive_joint_complete (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    Measurable (fun p : Time × NullMeasurableSpace BrownianPath P => v p.1 p.2) := by
  have h := (hv 1).mono (show MeasurableSpace.prod inferInstance (usualBrownianSigma P 1) ≤
      MeasurableSpace.prod inferInstance
        (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) from
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (usualBrownianSigma_le_completion P 1))) le_rfl
  have hf : Measurable (fun p : Time × NullMeasurableSpace BrownianPath P =>
      (⟨p.1, p.1.property.2⟩ : Set.Iic (1 : Time))) := measurable_fst.subtype_mk
  exact h.comp (hf.prodMk measurable_snd)

lemma progressive_time_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (ω : BrownianPath) :
    Measurable (fun t : Time => v t ω) :=
  (progressive_joint_complete P hv).comp (measurable_id.prodMk measurable_const)

lemma controlDrift_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (controlDrift m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => controlDrift m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      (progressive_joint_complete P hv)).stronglyMeasurable.integral_prod_left'.measurable
  exact (show NullMeasurable (controlDrift m v) P from h).aemeasurable

lemma pathControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (pathControlCost m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => pathControlCost m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      ((progressive_joint_complete P hv).pow_const 2)).ennreal_ofReal.lintegral_prod_left'
  exact (show NullMeasurable (pathControlCost m v) P from h).aemeasurable

lemma controlledTerminal_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (fun ω => brownianEval 1 ω + controlDrift m v ω) P :=
  (brownianEval_measurable 1).aemeasurable.add (controlDrift_aemeasurable P m hv)

lemma controlReward_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) :
    Integrable (fun ω => f (brownianEval 1 ω + controlDrift m v ω)) P := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp_aemeasurable
      (controlledTerminal_aemeasurable P m hv)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
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

lemma indep_eventuallyMeasurable_left {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m n : MeasurableSpace Ω} (h : Indep m n μ) :
    Indep (eventuallyMeasurableSpace m (ae μ)) n μ := by
  rw [Indep_iff] at h ⊢
  rintro A B ⟨A', hA', hAA'⟩ hB
  rw [measure_congr (hAA'.inter (Filter.EventuallyEq.refl (ae μ) B)), measure_congr hAA']
  exact h A' B hA' hB

lemma nullSigma_le_eventuallyMeasurable (P : Measure BrownianPath)
    (m : MeasurableSpace BrownianPath) :
    nullSigma P ≤ eventuallyMeasurableSpace m (ae P) := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩

lemma rawBrownianSigma_le_past_comap (s : ℝ≥0) :
    rawBrownianSigma s ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic s) => brownianEval r.val ω) inferInstance := by
  apply iSup_le
  intro r
  rintro A ⟨B, hB, rfl⟩
  exact ⟨(fun f : Set.Iic s → ℝ => f r) ⁻¹' B, (measurable_pi_apply r) hB, rfl⟩

lemma usualBrownianSigma_le_ae_raw (P : Measure BrownianPath) (t : Time)
    (s : ℝ≥0) (hts : (t : ℝ) < s) :
    usualBrownianSigma P t ≤ eventuallyMeasurableSpace (rawBrownianSigma s) (ae P) := by
  apply (iInf_le _ (⟨s, hts⟩ : {s : ℝ≥0 // (t : ℝ) < s})).trans
  exact sup_le le_eventuallyMeasurableSpace (nullSigma_le_eventuallyMeasurable P _)

lemma brownian_future_indep_raw (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (s u : ℝ≥0) :
    Indep (rawBrownianSigma s)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P := by
  have h := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply u)
  exact indep_of_indep_of_le_left h (rawBrownianSigma_le_past_comap s)

lemma brownian_future_indep_usual_earlier (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (t : Time) (s u : ℝ≥0)
    (hts : (t : ℝ) < s) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P :=
  indep_of_indep_of_le_left
    (indep_eventuallyMeasurable_left P (brownian_future_indep_raw P hB s u))
    (usualBrownianSigma_le_ae_raw P t s hts)

lemma indep_setIntegral_eq_mul_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hI : Indep m (MeasurableSpace.comap X (borel ℝ)) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A) (hAn : NullMeasurableSet A P)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω in A, f (X ω) ∂P) = P.real A * ∫ ω, f (X ω) ∂P := by
  calc
    _ = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) * f (X ω) ∂P := by
      rw [← integral_indicator₀ hAn]
      congr with ω
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = _ := by
      simp only [Pi.one_def]
      rw [IndepFun.integral_fun_comp_mul_comp
        (hI.indicator_indepFun 1 hA)
        ((aemeasurable_indicator_const_iff 1).2 hAn) hX
        measurable_id.aestronglyMeasurable f.continuous.measurable.aestronglyMeasurable]
      simp only [id_eq, integral_indicator₀ hAn, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ]

lemma indep_comap_of_ae_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ A, MeasurableSet[m] A → NullMeasurableSet A P)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hI : ∀ n, Indep m (MeasurableSpace.comap (X n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  apply (Indep_iff_IndepSets _ _ P).2
  apply indepSets_comap_of_bcf (fun A hA => hm A hA) hY
  intro A hA f
  have hall := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    (hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  have hres := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    ((ae_restrict_of_ae hlim).mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  apply tendsto_nhds_unique hres
  convert hall.const_mul (P.real A) using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact indep_setIntegral_eq_mul_null P (hI n) (hX n) hA (hm A hA) f

lemma brownian_increment_indep_usual (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval r ω -
        brownianEval ⟨t.val, t.property.1⟩ ω) (borel ℝ)) P := by
  let t₀ : ℝ≥0 := ⟨t.val, t.property.1⟩
  have ht₀r : t₀ < r := htr
  obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictAnti_tendsto' ht₀r
  apply indep_comap_of_ae_tendsto P (fun A hA =>
    (usualBrownianSigma_le_completion P t A hA))
    (X := fun n ω => brownianEval r ω - brownianEval (s n) ω)
    (fun n => ((brownianEval_measurable r).sub (brownianEval_measurable (s n))).aemeasurable)
    (((brownianEval_measurable r).sub (brownianEval_measurable t₀)).aemeasurable)
  · intro n
    have hI := brownian_future_indep_usual_earlier P hB t (s n) (r-s n) (hs n).1
    rwa [add_tsub_cancel_of_le (hs n).2.le] at hI
  · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.sub
      (ω.continuous.continuousAt.tendsto.comp hlim)

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
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

lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

lemma controlValue_trial_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |controlValue P f m - controlValue P f n| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  have hmn := controlValue_trial_sub_le P f m n L hf
  have hnm := controlValue_trial_sub_le P f n m L hf
  simp_rw [abs_sub_comm (n _) (m _)] at hnm
  exact abs_le.mpr ⟨by linarith, hmn⟩

lemma usual_measurable_aemeasurable (P : Measure BrownianPath) (t : Time)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    AEMeasurable Y P := by
  have h : NullMeasurable Y P := hY.mono (usualBrownianSigma_le_completion P t) le_rfl
  exact h.aemeasurable

lemma brownian_increment_indep_adapted (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    IndepFun Y (fun ω => brownianEval r ω - brownianEval ⟨t.val, (show 0 ≤ (t : ℝ) from t.property.1)⟩ ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_usual P hB t r htr) hY.comap_le

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

lemma smooth_deriv_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) : LipschitzWith C (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, coe_nnnorm, Real.norm_eq_abs] using hC x

lemma drift_shift_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x z a : ℝ) :
    |f (x+z+a) - f (x+z) - deriv f x * a| ≤ (C : ℝ) * (|z| * |a| + a^2/2) := by
  have ht := first_order_taylor_bound hf C hC (x+z) (x+z+a)
  simp only [add_sub_cancel_left] at ht
  have hd := (smooth_deriv_lipschitz hf C hC).dist_le_mul (x+z) x
  simp only [Real.dist_eq, add_sub_cancel_left] at hd
  calc
    _ = |(f (x+z+a) - f (x+z) - deriv f (x+z) * a) + (deriv f (x+z) - deriv f x) * a| := by congr 1; ring
    _ ≤ |f (x+z+a) - f (x+z) - deriv f (x+z) * a| + |(deriv f (x+z) - deriv f x) * a| := abs_add_le _ _
    _ ≤ (C : ℝ) * a^2/2 + (C : ℝ) * |z| * |a| := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

lemma gaussian_abs_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      (Real.sqrt v)^n * ∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; exact Real.sq_sqrt v.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  simp only [mul_zero, NNReal.mk] at hL
  rw [hv, mul_one] at hL
  rw [← hL.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^n) (gaussianReal 0 v))]
  simp only [Function.comp_apply, id_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

lemma gaussian_law_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Z ω|^n) P := by
  have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (n : ℝ≥0))
  have hi : Integrable (fun x : ℝ => |x|^n) (Measure.map Z P) := by
    rw [hZ.map_eq]
    simpa only [Real.norm_eq_abs, id_eq] using hm.integrable_norm_pow'
  exact (integrable_map_measure hi.aestronglyMeasurable hZ.aemeasurable).mp hi

lemma gaussian_law_sq_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, (Z ω)^2 ∂P) = v := by
  have hi := hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2)
    (gaussianReal 0 v))
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  exact hi.trans hv.symm

lemma gaussian_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₂ C₃ : ℝ) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) :
    |(∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let d₁ := deriv (f : ℝ → ℝ)
  let d₂ := iteratedDeriv 2 (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hm₂ : Measurable d₂ := (hf.continuous_iteratedDeriv 2 (by norm_num)).measurable
  have hi₁ : Integrable (fun ω => d₁ (X ω) * Z ω) P := by
    have hz : Integrable Z P := by
      have hi := gaussian_law_integrable_abs_pow hZ 1
      exact (integrable_norm_iff hZ.aemeasurable.aestronglyMeasurable).mp (by
        simpa only [pow_one, Real.norm_eq_abs] using hi)
    apply hz.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have hi₂ : Integrable (fun ω => d₂ (X ω) * (Z ω)^2) P := by
    have hz : Integrable (fun ω => (Z ω)^2) P := by
      simpa only [sq_abs] using gaussian_law_integrable_abs_pow hZ 2
    apply hz.bdd_mul (hm₂.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₂] using h₂ (X ω)
  have hv₁ : (∫ ω, d₁ (X ω) * Z ω ∂P) = 0 := by
    have hh := (hI.comp hm₁ measurable_id).integral_fun_mul_eq_mul_integral
      (hm₁.comp_aemeasurable hX).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
    have hz : (∫ ω, Z ω ∂P) = 0 := hZ.integral_eq.trans (integral_id_gaussianReal)
    simpa only [Function.comp_apply, id_eq, hz, mul_zero] using hh
  have hv₂ : (∫ ω, d₂ (X ω) * (Z ω)^2 ∂P) = (v : ℝ) * (∫ ω, d₂ (X ω) ∂P) := by
    have hh := (hI.comp hm₂ (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hm₂.comp_aemeasurable hX).aestronglyMeasurable (hZ.aemeasurable.pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at hh
    exact hh.trans (by rw [gaussian_law_sq_mean hZ, mul_comm])
  let R := fun ω => f (X ω + Z ω) - f (X ω) - d₁ (X ω) * Z ω - d₂ (X ω) * (Z ω)^2/2
  have hiR : Integrable R P :=
    (((boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)).sub
      (boundedContinuousFunction_integrable_comp f hX)).sub hi₁).sub (hi₂.div_const 2)
  have hR : ∀ ω, |R ω| ≤ C₃/6 * |Z ω|^3 := by
    intro ω
    have hh := second_order_taylor_bound hf C₃ h₃ (X ω) (X ω + Z ω)
    simpa only [add_sub_cancel_left, R, d₁, d₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : |∫ ω, R ω ∂P| ≤ C₃/6 * ∫ ω, |Z ω|^3 ∂P := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C₃/6 * |Z ω|^3 ∂P := integral_mono hiR.abs
        ((gaussian_law_integrable_abs_pow hZ 3).const_mul _) hR
      _ = _ := integral_const_mul _ _
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, d₂ (X ω) ∂P := by
    have ha := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
    have hb := boundedContinuousFunction_integrable_comp f hX
    have he₁ := integral_sub ((ha.sub hb).sub hi₁) (hi₂.div_const 2)
    have he₂ := integral_sub (ha.sub hb) hi₁
    have he₃ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
    dsimp only [R]
    rw [he₁, he₂, he₃, integral_div, hv₁, hv₂]
    ring
  have hg : (∫ ω, |Z ω|^3 ∂P) = (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 :=
    (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^3) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 3)
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma drift_shift_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (C₁ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P)| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) := by
  let d₁ := deriv (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hiA := bounded_real_integrable hA K (Filter.Eventually.of_forall hAK)
  have hi₁ : Integrable (fun ω => d₁ (X ω) * A ω) P := by
    apply hiA.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have ha := boundedContinuousFunction_integrable_comp f ((hX.add hZ.aemeasurable).add hA)
  have hb := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
  let R := fun ω => f (X ω + Z ω + A ω) - f (X ω + Z ω) - d₁ (X ω) * A ω
  have hiR : Integrable R P := (ha.sub hb).sub hi₁
  have hR : ∀ ω, |R ω| ≤ (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) := by
    intro ω
    apply (drift_shift_taylor_bound hf C₂ h₂ (X ω) (Z ω) (A ω)).trans
    apply mul_le_mul_of_nonneg_left _ C₂.coe_nonneg
    have hsq : A ω ^2 ≤ (K : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (A ω)) K.coe_nonneg).mpr (hAK ω)
    exact add_le_add (mul_le_mul_of_nonneg_left (hAK ω) (abs_nonneg _)) (by linarith)
  have hiz : Integrable (fun ω => |Z ω|) P := by
    simpa only [pow_one] using gaussian_law_integrable_abs_pow hZ 1
  have hbound : |∫ ω, R ω ∂P| ≤
      (C₂ : ℝ) * ((∫ ω, |Z ω| ∂P) * (K : ℝ) + (K : ℝ)^2/2) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) ∂P :=
        integral_mono hiR.abs (((hiz.mul_const K).add (integrable_const _)).const_mul C₂) hR
      _ = _ := by rw [integral_const_mul, integral_add (hiz.mul_const K) (integrable_const _), integral_mul_const]; simp
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω + A ω) ∂P) -
      (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, d₁ (X ω) * A ω ∂P) := by
    have he₁ := integral_sub (ha.sub hb) hi₁
    have he₂ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    exact he₁.trans (by rw [he₂])
  have hg : (∫ ω, |Z ω| ∂P) = Real.sqrt v * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    have hh := (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^1) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 1)
    simpa only [pow_one, Function.comp_apply] using hh
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma gaussian_drift_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₃ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) +
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hG := gaussian_taylor_mean_bound f hf C₁ C₂ C₃ h₁ h₂ h₃ hX hZ hI
  have hD := drift_shift_mean_bound f (hf.of_le (by norm_num)) C₁ C₂ K h₁ h₂ hX hZ hA hAK
  have hh := abs_add_le
    ((∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P))
    ((∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P)
  convert hh.trans (add_le_add hD hG) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma gaussianAverage_semigroup (s t : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (gaussianAverageBCF t f) x = gaussianAverage (s+t) f x := by
  have hi : Integrable (fun z => f (x+z)) ((gaussianReal 0 s) ∗ (gaussianReal 0 t)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact gaussianAverage_integrable (s+t) f x
  have hh := integral_conv hi
  simp only [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [gaussianAverage, gaussianAverageBCF_coe, add_assoc] using hh.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
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

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma heatLog_zero (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : heatLog 0 d f x = f x := by
  by_cases hd : d = 0
  · simp [heatLog, hd]
  · simp [heatLog, hd]

lemma heatLog_semigroup (s t d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    heatLog s d (heatLogBCF t d f) x = heatLog (s+t) d f x := by
  by_cases hd : d = 0
  · subst d
    have he : heatLogBCF t 0 f = gaussianAverageBCF t f := by ext z; simp [heatLog]
    simp only [heatLog, ↓reduceIte, he]
    exact gaussianAverage_semigroup s t f x
  · have he : expBCF d (heatLogBCF t d f) = gaussianAverageBCF t (expBCF d f) := by
      ext z
      exact exp_heatLog t d hd f z
    simp only [heatLog, hd, ↓reduceIte, he, gaussianAverage_semigroup]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

lemma Jet3.gaussianAverage_norms (s : ℝ≥0) (g : Jet3) :
    ‖(g.gaussianAverage s).f‖ ≤ ‖g.f‖ ∧ ‖(g.gaussianAverage s).d1‖ ≤ ‖g.d1‖ ∧
    ‖(g.gaussianAverage s).d2‖ ≤ ‖g.d2‖ ∧ ‖(g.gaussianAverage s).d3‖ ≤ ‖g.d3‖ := by
  have hh (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖ ≤ ‖f‖ := by
    rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
    intro x; exact gaussianAverage_abs_le s f x
  exact ⟨hh _,hh _,hh _,hh _⟩

lemma invBCF_norm_le (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) :
    ‖invBCF g c hc hg‖ ≤ c⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (inv_nonneg.mpr hc.le)]
  intro x; exact inv_bcf_bound hc hg x

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

lemma gaussianAverage_jet_error (s : ℝ≥0) (g : Jet3) (x : ℝ) :
    |gaussianAverage s g.f x - g.f x - (s : ℝ)/2 * g.d2 x| ≤
      ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by
  have hh := gaussian_taylor_mean_bound (P := gaussianReal 0 s) g.f g.contDiff
    ‖g.d1‖ ‖g.d2‖ ‖g.d3‖
    (fun y => by rw [g.deriv_eq]; exact g.d1.norm_coe_le_norm y)
    (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y)
    (fun y => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm y)
    (X := fun _ : ℝ => x) aemeasurable_const (Z := id) HasLaw.id (indepFun_const_left _ _)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, g.deriv2_eq, gaussianAverage, id_eq] using hh

lemma log_linear_error_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a - (b-a)/a| ≤ (b-a)^2 / c^2 := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  have hu := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hu
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have heq : b/a-1 = (b-a)/a := by field_simp
  rw [heq] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hlin : -(Real.log b - Real.log a - (b-a)/a) ≤ (b-a)^2/(a*b) := by
    have he : (b-a)/a + (a/b-1) = (b-a)^2/(a*b) := by field_simp; ring
    linarith
  exact hlin.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc)
    (by nlinarith [mul_le_mul ha hb hc.le ha0.le]))

lemma gaussianAverage_ge_const (s : ℝ≥0) (f : ℝ →ᵇ ℝ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : ℝ) : c ≤ gaussianAverage s f x := by
  have hh := integral_mono (integrable_const c) (gaussianAverage_integrable s f x) (fun z => hc (x+z))
  simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma log_gaussian_generator_error (g : Jet3) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, c ≤ g.f x) (C₂ C₃ : ℝ≥0) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃)
    (s : ℝ≥0) (hs : s ≤ 1) (x : ℝ) :
    |Real.log (gaussianAverage s g.f x) - Real.log (g.f x) -
      (s : ℝ)/2 * g.d2 x / g.f x| ≤
      (((C₂ : ℝ)/2 + (C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))^2/c^2 +
        ((C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))/c) * (s : ℝ) * Real.sqrt s := by
  let A := gaussianAverage s g.f x
  let a := g.f x
  let K := (C₃ : ℝ)/6 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  let D := (C₂ : ℝ)/2 + K
  have ha := hg x
  have hA := gaussianAverage_ge_const s g.f hg x
  have hM : 0 ≤ ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := integral_nonneg (fun z => by positivity)
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by positivity
  have hs0 : 0 ≤ (s : ℝ) := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ 1 := hs
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hrsq := Real.sq_sqrt hs0
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ) * Real.sqrt (s : ℝ) := by nlinarith
  have herr : |A-a-(s : ℝ)/2*g.d2 x| ≤ K * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by gcongr
      _ = _ := by rw [hrcube]; unfold K; ring
  have hdx : |g.d2 x| ≤ C₂ := (g.d2.norm_coe_le_norm x).trans h₂
  have hdelta : |A-a| ≤ D * (s : ℝ) := by
    have habs := abs_add_le (A-a-(s : ℝ)/2*g.d2 x) ((s : ℝ)/2*g.d2 x)
    rw [sub_add_cancel] at habs
    have hterm : |(s : ℝ)/2*g.d2 x| ≤ (s : ℝ)/2*C₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s/2)]
      exact mul_le_mul_of_nonneg_left hdx (by positivity)
    have hkr := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hK hs0)
    dsimp [D]; nlinarith
  have hquad : (A-a)^2/c^2 ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s := by
    have hdsq : (A-a)^2 ≤ (D*(s : ℝ))^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (A-a)) (mul_nonneg hD hs0)).mpr hdelta
      simpa only [sq_abs] using hh
    calc
      _ ≤ (D*(s : ℝ))^2/c^2 := div_le_div_of_nonneg_right hdsq (sq_nonneg c)
      _ = D^2/c^2 * (s : ℝ)^2 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsr hs0)
          (show 0 ≤ D^2/c^2 by positivity)
        nlinarith only [hh]
  have hrem : |A-a-(s : ℝ)/2*g.d2 x|/a ≤ (K/c) * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ (K*(s : ℝ)*Real.sqrt s)/c := div_le_div₀ (by positivity) herr hc ha
      _ = _ := by ring
  have hlog := log_linear_error_le hc ha hA
  change |Real.log A - Real.log a - (s : ℝ)/2*g.d2 x/a| ≤ _
  calc
    _ = |(Real.log A-Real.log a-(A-a)/a) + (A-a-(s : ℝ)/2*g.d2 x)/a| := by congr 1; ring
    _ ≤ |Real.log A-Real.log a-(A-a)/a| + |(A-a-(s : ℝ)/2*g.d2 x)/a| := abs_add_le _ _
    _ = |Real.log A-Real.log a-(A-a)/a| + |A-a-(s : ℝ)/2*g.d2 x|/a := by
      rw [abs_div, abs_of_pos (hc.trans_le ha)]
    _ ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s + (K/c)*(s : ℝ)*Real.sqrt s :=
      add_le_add (hlog.trans hquad) hrem
    _ = _ := by dsimp [D,K]; ring

lemma expBCF_norm_le (d : ℝ) (f : ℝ →ᵇ ℝ) :
    ‖expBCF d f‖ ≤ Real.exp (|d| * ‖f‖) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  exact exp_bcf_bound d f

lemma Jet3.exp_norms (g : Jet3) (d C₀ C₁ C₂ C₃ : ℝ≥0)
    (h₀ : ‖g.f‖ ≤ C₀) (h₁ : ‖g.d1‖ ≤ C₁) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃) :
    let E := Real.exp ((d : ℝ)*C₀)
    ‖(g.exp d).f‖ ≤ E ∧ ‖(g.exp d).d1‖ ≤ (d : ℝ)*E*C₁ ∧
    ‖(g.exp d).d2‖ ≤ E*((d : ℝ)^2*C₁^2 + d*C₂) ∧
    ‖(g.exp d).d3‖ ≤ E*((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*C₁*C₂ + d*C₃) := by
  dsimp only
  have hf : ‖expBCF d g.f‖ ≤ Real.exp ((d : ℝ)*C₀) := by
    refine (expBCF_norm_le d g.f).trans ?_
    rw [abs_of_nonneg d.coe_nonneg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h₀ d.coe_nonneg)
  refine ⟨hf, ?_, ?_, ?_⟩
  · change ‖(d : ℝ) • (expBCF d g.f * g.d1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ) * (‖expBCF d g.f‖ * ‖g.d1‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ (d : ℝ) * (Real.exp ((d : ℝ)*C₀) * C₁) := by gcongr
      _ = _ := by ring
  · change ‖expBCF d g.f * ((d : ℝ)^2 • (g.d1^2) + (d : ℝ) • g.d2)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * (‖(d : ℝ)^2 • (g.d1^2)‖ + ‖(d : ℝ) • g.d2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^2 * ‖g.d1^2‖ + (d : ℝ) * ‖g.d2‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg, abs_pow]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^2 * C₁^2 + (d : ℝ) * C₂) := by
        gcongr
        exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖expBCF d g.f * ((d : ℝ)^3 • (g.d1^3) + (3*(d : ℝ)^2) • (g.d1*g.d2) + (d : ℝ) • g.d3)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * ((‖(d : ℝ)^3 • (g.d1^3)‖ + ‖(3*(d : ℝ)^2) • (g.d1*g.d2)‖) + ‖(d : ℝ) • g.d3‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^3 * ‖g.d1^3‖ + 3*(d : ℝ)^2*‖g.d1*g.d2‖ + (d : ℝ)*‖g.d3‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)^3),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3*(d : ℝ)^2), abs_of_nonneg d.coe_nonneg]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*(C₁*C₂) + (d : ℝ)*C₃) := by
        gcongr
        · exact (norm_pow_le _ _).trans (by gcongr)
        · exact (norm_mul_le _ _).trans (by gcongr)
      _ = _ := by ring

lemma Jet3.heatLog_uniform_bounds (d : ℝ≥0) (g : Jet3) :
    ∃ C₀ C₁ C₂ C₃ : ℝ≥0, ∀ s : ℝ≥0,
      ‖(g.heatLog s d).f‖ ≤ C₀ ∧ ‖(g.heatLog s d).d1‖ ≤ C₁ ∧
      ‖(g.heatLog s d).d2‖ ≤ C₂ ∧ ‖(g.heatLog s d).d3‖ ≤ C₃ := by
  by_cases hd : d = 0
  · subst d
    refine ⟨‖g.f‖₊, ‖g.d1‖₊, ‖g.d2‖₊, ‖g.d3‖₊, ?_⟩
    intro s; simpa only [Jet3.heatLog, ↓reduceDIte, coe_nnnorm] using g.gaussianAverage_norms s
  let e := g.exp d
  let B := (Real.exp (-(d : ℝ)*‖g.f‖))⁻¹
  let r := (d : ℝ)⁻¹
  have hB : 0 ≤ B := by positivity
  have hr : 0 ≤ r := by positivity
  refine ⟨‖g.f‖₊,
    ⟨r*(‖e.d1‖*B), by positivity⟩,
    ⟨r*(‖e.d2‖*B+‖e.d1‖^2*B^2), by positivity⟩,
    ⟨r*(‖e.d3‖*B+3*(‖e.d1‖*‖e.d2‖*B^2)+2*(‖e.d1‖^3*B^3)), by positivity⟩, ?_⟩
  intro s
  let A := e.gaussianAverage s
  let c := Real.exp (-(d : ℝ)*‖g.f‖)
  let hc := Real.exp_pos (-(d : ℝ)*‖g.f‖)
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  have hj : ‖J‖ ≤ B := invBCF_norm_le A.f c hc hA
  obtain ⟨_, h₁,h₂,h₃⟩ := e.gaussianAverage_norms s
  have hf : ‖(g.heatLog s d).f‖ ≤ ‖g.f‖ := by
    rw [g.heatLog_f, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    exact heatLog_abs_le s d g.f
  rw [Jet3.heatLog, dite_eq_right hd]
  refine ⟨by simpa only [Jet3.heatLog, dite_eq_right hd, coe_nnnorm] using hf, ?_, ?_, ?_⟩
  · change ‖r • (A.d1*J)‖ ≤ r * (‖e.d1‖*B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (by gcongr)) hr
  · change ‖r • (A.d2*J - A.d1^2*J^2)‖ ≤ r*(‖e.d2‖*B+‖e.d1‖^2*B^2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖r • (A.d3*J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)

lemma heatLog_generator_uniform (d C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ →
      ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ → ∀ (s : ℝ≥0), s ≤ 1 → ∀ x : ℝ,
        |heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)| ≤
          (C : ℝ) * (s : ℝ) * Real.sqrt s := by
  let M := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg (fun z => by positivity)
  by_cases hd : d = 0
  · subst d
    refine ⟨⟨(C₃ : ℝ)/6*M, by positivity⟩, ?_⟩
    intro g _ _ _ h₃ s _ x
    simp only [heatLog, ↓reduceIte, NNReal.coe_zero, zero_mul, add_zero]
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * M := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * M := by gcongr
      _ = (C₃ : ℝ)/6*M * (s : ℝ) * Real.sqrt s := by
        have hh := Real.sq_sqrt s.coe_nonneg
        calc
          _ = (C₃ : ℝ)/6*M * (Real.sqrt s)^2 * Real.sqrt s := by ring
          _ = _ := by rw [hh]
  let c := Real.exp (-(d : ℝ)*C₀)
  let E := Real.exp ((d : ℝ)*C₀)
  let E₂ : ℝ≥0 := ⟨E*((d : ℝ)^2*C₁^2+(d : ℝ)*C₂), by positivity⟩
  let E₃ : ℝ≥0 := ⟨E*((d : ℝ)^3*C₁^3+3*(d : ℝ)^2*C₁*C₂+(d : ℝ)*C₃), by positivity⟩
  let K := ((E₂ : ℝ)/2+(E₃ : ℝ)/6*M)^2/c^2 + ((E₃ : ℝ)/6*M)/c
  have hc : 0 < c := Real.exp_pos _
  have hK : 0 ≤ K := by positivity
  have hdpos : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  refine ⟨⟨(d : ℝ)⁻¹*K, by positivity⟩, ?_⟩
  intro g h₀ h₁ h₂ h₃ s hs x
  have hh := g.exp_norms d C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃
  have hlo (x : ℝ) : c ≤ (g.exp d).f x := by
    change Real.exp (-(d : ℝ)*C₀) ≤ Real.exp ((d : ℝ)*g.f x)
    apply Real.exp_le_exp.mpr
    have hb : |g.f x| ≤ C₀ := (g.f.norm_coe_le_norm x).trans h₀
    nlinarith [(abs_le.mp hb).1]
  have herr := log_gaussian_generator_error (g.exp d) c hc hlo E₂ E₃ hh.2.2.1 hh.2.2.2 s hs x
  have he : (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x =
      (d : ℝ) * ((s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)) := by
    change (s : ℝ)/2 * (Real.exp ((d : ℝ)*g.f x) * ((d : ℝ)^2*g.d1 x^2 + (d : ℝ)*g.d2 x)) /
      Real.exp ((d : ℝ)*g.f x) = _
    field_simp
    ring
  have hid : heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x+(d : ℝ)*g.d1 x^2) =
      (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (g.exp d).f x) - Real.log ((g.exp d).f x) -
        (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x) := by
    rw [he]
    change _ = (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (expBCF d g.f) x) -
      Real.log (Real.exp ((d : ℝ)*g.f x)) - _)
    rw [Real.log_exp]
    simp only [heatLog, hd, ↓reduceIte]
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
  calc
    _ ≤ (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hdpos.le)
    _ = _ := by change (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) = (d : ℝ)⁻¹*K*(s : ℝ)*Real.sqrt s; ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatTilt
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma heatTilt_zero (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s 0 f h x = gaussianAverage s h x := by
  simp [heatTilt,gaussianAverage,expBCF]

lemma gaussianAverage_affine (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    gaussianAverage s (f+t • h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + t * gaussianAverage s h x := by
  simp only [gaussianAverage,BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
  rw [integral_add (gaussianAverage_integrable s f x)
    ((gaussianAverage_integrable s h x).const_mul t), integral_const_mul]

lemma gaussian_exp_affine_deriv (s : ℝ≥0) (d : ℝ) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * h) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h)) (Real.exp_pos (|d| * ‖f‖)).le
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => exp_bcf_bound d f (x+z)) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [expBCF,BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk,BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [Pi.mul_apply,
      expBCF,BoundedContinuousFunction.mkOfBound_coe,ContinuousMap.coe_mk,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      Pi.add_apply,smul_eq_mul]
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatLog_directional_deriv (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatLog s d (f+u • h) x)
      (heatTilt s d (f+t • h) h x) t := by
  by_cases hd : d = 0
  · subst d
    simp only [heatTilt_zero,heatLog,↓reduceIte,gaussianAverage_affine]
    convert! (hasDerivAt_const t (gaussianAverage s f x)).add
      ((hasDerivAt_id t).mul_const (gaussianAverage s h x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  · have hh := ((gaussian_exp_affine_deriv s d f h t x).log
      (gaussianAverage_exp_pos s d (f+t • h) x).ne').const_mul (d:ℝ)⁻¹
    convert! hh using 1
    · simp only [heatLog,hd,↓reduceIte]
    · unfold heatTilt
      field_simp [NNReal.coe_ne_zero.mpr hd]

lemma heatTilt_nonneg (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    0 ≤ heatTilt s d f h x := by
  apply div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (hh _))
    (gaussianAverage_exp_pos s d f x).le

lemma heatTilt_sq (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    (heatTilt s d f h x)^2 ≤ heatTilt s d f (h^2) x := by
  let c := heatTilt s d f h x
  have hp := heatTilt_nonneg s d f ((h-BoundedContinuousFunction.const ℝ c)^2)
    (fun y => sq_nonneg _) x
  have he : (h-BoundedContinuousFunction.const ℝ c)^2 =
      h^2 + (-2*c) • h + BoundedContinuousFunction.const ℝ (c^2) := by
    ext y
    simp only [BoundedContinuousFunction.coe_pow,BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.const_apply,Pi.pow_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he,heatTilt_add,heatTilt_add,heatTilt_smul,heatTilt_const] at hp
  dsimp only [c] at hp
  nlinarith

lemma Jet3.heatLog_d1 (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    (g.heatLog s d).d1 x = heatTilt s d g.f g.d1 x := by
  by_cases hd : d = 0
  · subst d
    simp only [Jet3.heatLog,↓reduceDIte,heatTilt_zero]
    rfl
  · have he : (g.exp d).d1 = (d:ℝ) • (expBCF d g.f*g.d1) := rfl
    simp only [Jet3.heatLog,hd,↓reduceDIte,Jet3.heatLogPos]
    change (d:ℝ)⁻¹ * (SphericalPerceptronFreeEnergy.gaussianAverage s (g.exp d).d1 x *
      (SphericalPerceptronFreeEnergy.gaussianAverage s (expBCF d g.f) x)⁻¹) = _
    rw [he,SphericalPerceptronFreeEnergy.gaussianAverage_smul]
    unfold heatTilt
    field_simp [NNReal.coe_ne_zero.mpr hd]
    rfl

lemma Jet3.heatLog_d1_sq_le (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    ((g.heatLog s d).d1 x)^2 ≤ heatTilt s d g.f (g.d1^2) x := by
  rw [g.heatLog_d1]
  exact heatTilt_sq s d g.f g.d1 x

lemma gaussian_exp_affine_mul_deriv (s : ℝ≥0) (d : ℝ) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)*k : ℝ →ᵇ ℝ) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * (h*k) : ℝ →ᵇ ℝ) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))*k (x+z)) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h))
    (mul_nonneg (Real.exp_pos (|d| * ‖f‖)).le (norm_nonneg k))
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => by
      rw [abs_mul]
      exact mul_le_mul (exp_bcf_bound d f (x+z)) (k.norm_coe_le_norm (x+z))
        (abs_nonneg _) (Real.exp_pos _).le) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    change Real.exp (d*(f (x+z)+u*h (x+z)))*k (x+z) = _
    rw [show d*(f (x+z)+u*h (x+z))=u*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    change d*(Real.exp (d*(f (x+z)+t*h (x+z)))*(h (x+z)*k (x+z))) = _
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatTilt_directional_deriv (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatTilt s d (f+u • h) k x)
      ((d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)) t := by
  have hh := (gaussian_exp_affine_mul_deriv s d f h k t x).div
    (gaussian_exp_affine_deriv s d f h t x) (gaussianAverage_exp_pos s d (f+t • h) x).ne'
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold heatTilt
  simp only [← BoundedContinuousFunction.coe_mul]
  field_simp

lemma heatTilt_directional_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |(d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)| ≤
      2*(d:ℝ)*‖h‖*‖k‖ := by
  rw [abs_mul,abs_of_nonneg d.coe_nonneg]
  calc
    _ ≤ (d:ℝ)*(|heatTilt s d (f+t • h) (h*k) x| +
        |heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x|) := by
      gcongr; exact abs_sub _ _
    _ ≤ (d:ℝ)*(‖h*k‖ + ‖h‖*‖k‖) := by
      rw [abs_mul]
      gcongr
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
    _ ≤ 2*(d:ℝ)*‖h‖*‖k‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (norm_mul_le h k) d.coe_nonneg]

lemma heatTilt_affine_sub_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |heatTilt s d (f+t • h) k x - heatTilt s d f k x| ≤
      2*(d:ℝ)*‖h‖*‖k‖*|t| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun u _ => (heatTilt_directional_deriv s d f h k u x).hasDerivWithinAt)
    (fun u _ => heatTilt_directional_bound s d f h k u x) convex_univ
    (mem_univ (0:ℝ)) (mem_univ t)
  simpa only [zero_smul,add_zero,sub_zero,Real.norm_eq_abs] using hh

lemma heatLog_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatLog s d (f+h) x - heatLog s d f x - heatTilt s d f h x| ≤
      2*(d:ℝ)*‖h‖^2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun t => heatLog s d (f+t • h) x - heatLog s d f x - t*heatTilt s d f h x)
      (heatTilt s d (f+u • h) h x - heatTilt s d f h x) u := by
    convert! ((heatLog_directional_deriv s d f h u x).sub_const (heatLog s d f x)).sub
      ((hasDerivAt_id u).mul_const (heatTilt s d f h x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u hu => show
      ‖heatTilt s d (f+u • h) h x - heatTilt s d f h x‖ ≤ 2*(d:ℝ)*‖h‖^2 from by
        calc
          _ ≤ 2*(d:ℝ)*‖h‖*‖h‖*|u| := heatTilt_affine_sub_bound s d f h h u x
          _ ≤ 2*(d:ℝ)*‖h‖^2 := by
            rw [abs_of_nonneg hu.1]
            nlinarith [mul_nonneg (show 0 ≤ 2*(d:ℝ)*‖h‖^2 by positivity) (sub_nonneg.mpr hu.2.le)])
  simpa only [zero_smul,one_smul,add_zero,zero_mul,one_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using hh

lemma heatLogBCF_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) :
    ‖heatLogBCF s d (f+h)-heatLogBCF s d f-heatTiltCLM s d f h‖ ≤ 2*(d:ℝ)*‖h‖^2 :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (heatLog_terminal_quadratic_error s d f h)

lemma heatLogBCF_hasFDerivAt (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    HasFDerivAt (heatLogBCF s d) (heatTiltCLM s d f) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : (ℝ →ᵇ ℝ) in 𝓝 0, ‖h‖ < ε/(2*(d:ℝ)+1) :=
    by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ →ᵇ ℝ)
        (show 0 < ε/(2*(d:ℝ)+1) by positivity)] with h hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
  filter_upwards [he] with h hh
  calc
    _ ≤ 2*(d:ℝ)*‖h‖^2 := heatLogBCF_terminal_quadratic_error s d f h
    _ ≤ ε*‖h‖ := by
      have hb : ‖h‖*(2*(d:ℝ)+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      nlinarith [norm_nonneg h,mul_nonneg (norm_nonneg h) (sub_nonneg.mpr hb.le)]

lemma shiftBCF_norm_le (f : ℝ →ᵇ ℝ) (a : ℝ) : ‖shiftBCF f a‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (x+a))

lemma shiftBCF_lipschitz (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    LipschitzWith ‖f'‖₊ (shiftBCF f) := by
  have hl := lipschitzWith_of_nnnorm_deriv_le (C := ‖f'‖₊) (fun x => (hf x).differentiableAt) (fun x => by
    rw [(hf x).deriv]
    exact_mod_cast f'.norm_coe_le_norm x)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change |f (x+a)-f (x+b)| ≤ _
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub,coe_nnnorm] using hl.dist_le_mul (x+a) (x+b)

lemma shiftBCF_Jet3_hasDerivAt (g : Jet3) (a : ℝ) :
    HasDerivAt (shiftBCF g.f) (shiftBCF g.d1 a) a := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < ε/(‖g.d2‖+1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show 0 < ε/(‖g.d2‖+1) by positivity)] with h hh
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
  filter_upwards [he] with h hh
  have hb : ‖shiftBCF g.f (a+h)-shiftBCF g.f a-h • shiftBCF g.d1 a‖ ≤ ‖g.d2‖*h^2/2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    have ht := first_order_taylor_bound (g.contDiff.of_le (by norm_num)) ‖g.d2‖
      (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y) (x+a) (x+(a+h))
    rw [g.deriv_eq] at ht
    convert! ht using 1 <;> simp [shiftBCF,add_comm,add_left_comm,mul_comm]
  calc
    _ ≤ ‖g.d2‖*h^2/2 := hb
    _ ≤ ε*‖h‖ := by
      have ht : |h| * (‖g.d2‖+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs h,abs_nonneg h,norm_nonneg g.d2,
        mul_nonneg (abs_nonneg h) (sub_nonneg.mpr ht.le)]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BcfEvalRingHom
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma shiftBCF_gaussian_integrable (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) (a : ℝ) :
    Integrable (fun z => shiftBCF f (a*z)) (gaussianReal 0 1) := by
  apply Integrable.of_bound ((shiftBCF_lipschitz f f' hf).continuous.comp
    (continuous_const.mul continuous_id)).aestronglyMeasurable ‖f‖
  exact ae_of_all _ (fun z => shiftBCF_norm_le f (a*z))

lemma gaussianAverage_scaling (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s f x = ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt s)^2, sq_nonneg _⟩ : ℝ≥0) = s := by
    ext; exact Real.sq_sqrt s.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt s)
  simp only [mul_zero,NNReal.mk] at hL
  rw [hv,mul_one] at hL
  exact (hL.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun z => f (x+z)) (gaussianReal 0 s))).symm

lemma gaussianAverageBCF_scaling (s : ℝ≥0) (g : Jet3) :
    gaussianAverageBCF s g.f = ∫ z, shiftBCF g.f (Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hi := shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt s)
  ext x
  have he := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hi
  change gaussianAverage s g.f x = _
  rw [gaussianAverage_scaling]
  exact he

lemma gaussianAverageBCF_time_hasDerivAt (g : Jet3) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => gaussianAverageBCF t.toNNReal g.f)
      ((1/2 : ℝ) • gaussianAverageBCF s.toNNReal g.d2) s := by
  let F : ℝ → ℝ → (ℝ →ᵇ ℝ) := fun t z => shiftBCF g.f (Real.sqrt t*z)
  let D : ℝ → ℝ → (ℝ →ᵇ ℝ) := fun t z =>
    (z / (2*Real.sqrt t)) • shiftBCF g.d1 (Real.sqrt t*z)
  have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
    simpa only [pow_one,id_eq] using gaussian_law_integrable_abs_pow
      (HasLaw.id (μ := gaussianReal 0 1)) 1
  have hm (t : ℝ) : AEStronglyMeasurable (F t) (gaussianReal 0 1) := by
    exact (shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt t)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (D s) (gaussianReal 0 1) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_id.div_const _).smul ((shiftBCF_lipschitz g.d1 g.d2 g.has2).continuous.comp
      (continuous_const.mul continuous_id))
  have hb : ∀ᵐ z ∂gaussianReal 0 1, ∀ t ∈ Set.Ioo (s/2) (2*s),
      ‖D t z‖ ≤ |z| / (2*Real.sqrt (s/2)) * ‖g.d1‖ := by
    apply ae_of_all
    intro z t ht
    have ht0 : 0 < t := by linarith [ht.1]
    dsimp [D]
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt t)]
    apply mul_le_mul (div_le_div_of_nonneg_left (abs_nonneg z) (by positivity)
      (by gcongr; exact ht.1.le)) (shiftBCF_norm_le _ _) (norm_nonneg _) (by positivity)
  have hd : ∀ᵐ z ∂gaussianReal 0 1, ∀ t ∈ Set.Ioo (s/2) (2*s),
      HasDerivAt (fun t => F t z) (D t z) t := by
    apply ae_of_all
    intro z t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hh := (shiftBCF_Jet3_hasDerivAt g (Real.sqrt t*z)).scomp t
      ((Real.hasDerivAt_sqrt ht0).mul_const z)
    simpa only [F,D,Function.comp_def,div_eq_mul_inv,_root_.mul_inv_rev,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : s/2 < s) (by linarith : s < 2*s))
    (Filter.Eventually.of_forall hm)
    (shiftBCF_gaussian_integrable g.f g.d1 g.has1 (Real.sqrt s))
    hdm hb ((hz.div_const _).mul_const ‖g.d1‖) hd
  have he : (∫ z, D s z ∂gaussianReal 0 1) =
      (1/2 : ℝ) • gaussianAverageBCF s.toNNReal g.d2 := by
    ext x
    have hev := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hh.1
    have hib := standardGaussian_integrationByParts
      (F := fun z => g.d1 (x+Real.sqrt s*z))
      (F' := fun z => Real.sqrt s*g.d2 (x+Real.sqrt s*z))
      (C := ‖g.d1‖) (D := Real.sqrt s*‖g.d2‖)
      (fun z => by
        have h := (g.has2 (x+Real.sqrt s*z)).comp z
          (((hasDerivAt_id z).const_mul (Real.sqrt s)).const_add x)
        simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using h)
      (by fun_prop)
      (fun z => by simpa only [Real.norm_eq_abs] using g.d1.norm_coe_le_norm (x+Real.sqrt s*z))
      (fun z => by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_left (g.d2.norm_coe_le_norm (x+Real.sqrt s*z))
          (Real.sqrt_nonneg _))
    change (∫ z, (D s z) x ∂gaussianReal 0 1) = (∫ z,D s z ∂gaussianReal 0 1) x at hev
    rw [← hev]
    change (∫ z, z/(2*Real.sqrt s)*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1) =
      (1/2)*gaussianAverage s.toNNReal g.d2 x
    rw [gaussianAverage_scaling,Real.coe_toNNReal s hs.le]
    have hc : (∫ z, z/(2*Real.sqrt s)*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1) =
        (2*Real.sqrt s)⁻¹ * ∫ z, z*g.d1 (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
      rw [← integral_const_mul]; congr 1; ext z; ring
    rw [hc,hib,integral_const_mul]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hs)]
  rw [he] at hh
  apply hh.2.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact (gaussianAverageBCF_scaling t.toNNReal g).trans (by rw [Real.coe_toNNReal t ht.le])

lemma log_lipschitz_above {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b-Real.log a| ≤ c⁻¹*|b-a| := by
  apply (convex_Ici c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt)
    (fun x hx => ?_) ha hb
  rw [Real.norm_eq_abs,abs_inv,abs_of_pos (hc.trans_le hx)]
  exact inv_anti₀ hc hx

lemma heatLogBCF_time_continuousAt (g : Jet3) (d : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    ContinuousAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f) s := by
  by_cases hd : d = 0
  · subst d
    have he : (fun t : ℝ => heatLogBCF t.toNNReal 0 g.f) =
        (fun t => gaussianAverageBCF t.toNNReal g.f) := by ext t x; simp [heatLog]
    rw [he]
    exact (gaussianAverageBCF_time_hasDerivAt g s hs).continuousAt
  let A : ℝ → (ℝ →ᵇ ℝ) := fun t => gaussianAverageBCF t.toNNReal (expBCF d g.f)
  let c : ℝ := Real.exp (-(d : ℝ)*‖g.f‖)
  have hc : 0 < c := Real.exp_pos _
  have hb t : ∀ x, c ≤ A t x := fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg g.f x).1
  have ha : ContinuousAt A s := (gaussianAverageBCF_time_hasDerivAt (g.exp d) s hs).continuousAt
  have hbd t : ‖heatLogBCF t.toNNReal d g.f - heatLogBCF s.toNNReal d g.f‖ ≤
      (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change |heatLog t.toNNReal d g.f x-heatLog s.toNNReal d g.f x| ≤ _
    simp only [heatLog,hd,↓reduceIte,← mul_sub,abs_mul,abs_inv,abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ)⁻¹*(c⁻¹*|A t x-A s x|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_above hc (hb s x) (hb t x)) (by positivity)
      _ ≤ (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ((A t-A s).norm_coe_le_norm x) (by positivity)
  have ht : Tendsto (fun t => (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖) (𝓝 s) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (ha.sub (continuousAt_const (y := A s))).norm.const_mul ((d : ℝ)⁻¹*c⁻¹) |>.tendsto
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ht)

lemma expBCF_eq_normedSpace_exp (d : ℝ) (f : ℝ →ᵇ ℝ) :
    expBCF d f = NormedSpace.exp (d • f) := by
  ext x
  have hh := NormedSpace.map_exp (bcfEvalRingHom x)
    (BoundedContinuousFunction.evalCLM ℝ x).continuous (d • f)
  change _ = (bcfEvalRingHom x) (NormedSpace.exp (d • f))
  rw [hh,← Real.exp_eq_exp_ℝ]
  rfl

lemma expBCF_hasFDerivAt (d : ℝ) (f : ℝ →ᵇ ℝ) :
    HasFDerivAt (expBCF d)
      ((expBCF d f • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))) ∘L
        (d • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ)))) f := by
  have hh := (hasFDerivAt_exp (𝕂 := ℝ) (x := d • f)).comp f
    ((d • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))).hasFDerivAt)
  simpa only [← expBCF_eq_normedSpace_exp,one_apply_eq_self,
    _root_.smul_apply,Function.comp_def] using hh

lemma heatLogBCF_time_hasDerivAt (g : Jet3) (d : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f)
      (heatGenerator d (g.heatLog s.toNNReal d)) s := by
  by_cases hd : d = 0
  · subst d
    convert gaussianAverageBCF_time_hasDerivAt g s hs using 1
    · ext t x; simp [heatLog]
    · simp [heatGenerator,Jet3.heatLog,Jet3.gaussianAverage]
  have hdR : (d : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hd
  let U := heatLogBCF s.toNNReal d g.f
  let L : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
    ((d : ℝ)⁻¹ • expBCF (-(d : ℝ)) U) • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))
  have hlin : Function.LeftInverse L
      ((expBCF d U • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ))) ∘L
        ((d : ℝ) • (1 : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ)))) := by
    intro h
    ext x
    change ((d : ℝ)⁻¹*Real.exp (-(d : ℝ)*U x))*(Real.exp ((d : ℝ)*U x)*((d : ℝ)*h x)) = h x
    calc
      _ = ((d : ℝ)⁻¹*d)*(Real.exp (-(d : ℝ)*U x)*Real.exp ((d : ℝ)*U x))*h x := by ring
      _ = h x := by rw [← Real.exp_add]; simp [hdR]
  have hcomp : expBCF d ∘ (fun t : ℝ => heatLogBCF t.toNNReal d g.f) =ᶠ[𝓝 s]
      (fun t : ℝ => gaussianAverageBCF t.toNNReal (g.exp d).f) := by
    apply Filter.Eventually.of_forall
    intro t
    ext x
    exact exp_heatLog t.toNNReal d hd g.f x
  have hh := HasFDerivAt.of_comp_of_leftInverse
    (heatLogBCF_time_continuousAt g d s hs) (expBCF_hasFDerivAt d U)
    (gaussianAverageBCF_time_hasDerivAt (g.exp d) s hs).hasFDerivAt hcomp hlin
  have he : L ((1/2 : ℝ) • gaussianAverageBCF s.toNNReal (g.exp d).d2) =
      heatGenerator d (g.heatLog s.toNNReal d) := by
    ext x
    have hex : Real.exp (-(d : ℝ)*U x) = (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹ := by
      rw [neg_mul,Real.exp_neg,show Real.exp ((d : ℝ)*U x) = _ from exp_heatLog s.toNNReal d hd g.f x]
    change ((d : ℝ)⁻¹*Real.exp (-(d : ℝ)*U x)) *
      ((1/2)*gaussianAverage s.toNNReal (g.exp d).d2 x) = _
    rw [hex]
    simp only [Jet3.heatLog,hd,↓reduceDIte]
    change _ = (1/2)*((d : ℝ)⁻¹ *
      (gaussianAverage s.toNNReal (g.exp d).d2 x *
        (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹ -
       (gaussianAverage s.toNNReal (g.exp d).d1 x)^2 *
        ((gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹)^2) +
      (d : ℝ)*((d : ℝ)⁻¹ * (gaussianAverage s.toNNReal (g.exp d).d1 x *
        (gaussianAverage s.toNNReal (expBCF d g.f) x)⁻¹))^2)
    field_simp [hdR,(gaussianAverage_exp_pos s.toNNReal d g.f x).ne']
    ring
  apply hh.hasDerivAt.congr_deriv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using he

lemma gaussianAverageBCF_scaling_of_deriv (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    gaussianAverageBCF s f = ∫ z, shiftBCF f (Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hi := shiftBCF_gaussian_integrable f f' hf (Real.sqrt s)
  ext x
  have he := (BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hi
  change gaussianAverage s f x = _
  rw [gaussianAverage_scaling]
  exact he

lemma gaussianAverageBCF_time_continuous_of_deriv (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    Continuous (fun t : ℝ => gaussianAverageBCF t.toNNReal f) := by
  have he : (fun t : ℝ => gaussianAverageBCF t.toNNReal f) =
      (fun t : ℝ => ∫ z, shiftBCF f (Real.sqrt t.toNNReal*z) ∂gaussianReal 0 1) := by
    ext t x
    exact congrArg (fun h : ℝ →ᵇ ℝ => h x) (gaussianAverageBCF_scaling_of_deriv t.toNNReal f f' hf)
  rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t
    exact (shiftBCF_gaussian_integrable f f' hf (Real.sqrt t.toNNReal)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun z => shiftBCF_norm_le f (Real.sqrt t.toNNReal*z))
  · exact integrable_const _
  · apply ae_of_all
    intro z
    apply (shiftBCF_lipschitz f f' hf).continuous.comp
    exact (Real.continuous_sqrt.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).mul_const z

lemma heatTiltBCF_time_continuous_of_deriv (f f' h h' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) (d : ℝ≥0) :
    Continuous (fun t : ℝ => heatTiltBCF t.toNNReal d f h) := by
  let A := expBCF d f
  let A' := (d : ℝ) • (A*f')
  have hA x : HasDerivAt (A:ℝ→ℝ) (A' x) x := by
    change HasDerivAt (fun y => Real.exp ((d : ℝ)*f y)) ((d : ℝ)*(A x*f' x)) x
    exact ((hf x).const_mul (d : ℝ)).exp.congr_deriv (by dsimp [A,expBCF]; ring)
  have hB x : HasDerivAt (A*h : ℝ →ᵇ ℝ) ((A'*h+A*h') x) x := by
    simpa only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
      BoundedContinuousFunction.coe_add,Pi.add_apply] using (hA x).mul (hh x)
  have hca := gaussianAverageBCF_time_continuous_of_deriv A A' hA
  have hcb := gaussianAverageBCF_time_continuous_of_deriv (A*h) (A'*h+A*h') hB
  let c := Real.exp (-(d : ℝ)*‖f‖)
  have hc : 0 < c := Real.exp_pos _
  let J (t : ℝ) := invBCF (gaussianAverageBCF t.toNNReal A) c hc
    (fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg f x).1)
  have hJ : Continuous J := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hb t : ‖J t-J s‖ ≤ c⁻¹^2 * ‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖ := by
      apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
      intro x
      change |(gaussianAverage t.toNNReal A x)⁻¹-(gaussianAverage s.toNNReal A x)⁻¹| ≤ _
      have h1 := (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg f x).1
      have h2 := (gaussianAverage_exp_bounds s.toNNReal d d.coe_nonneg f x).1
      have h1p : 0 < gaussianAverage t.toNNReal A x := hc.trans_le h1
      have h2p : 0 < gaussianAverage s.toNNReal A x := hc.trans_le h2
      rw [inv_sub_inv h1p.ne' h2p.ne',abs_div,abs_mul,
        abs_of_pos h1p,abs_of_pos h2p,abs_sub_comm]
      calc
        _ ≤ ‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖/(c*c) :=
          div_le_div₀ (by positivity) ((gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A).norm_coe_le_norm x)
            (by positivity) (mul_le_mul h1 h2 hc.le h1p.le)
        _ = _ := by ring
    have ht : Tendsto (fun t => c⁻¹^2*‖gaussianAverageBCF t.toNNReal A-gaussianAverageBCF s.toNNReal A‖)
        (𝓝 s) (𝓝 0) := by
      simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
        ((hca.continuousAt (x := s)).sub (continuousAt_const (y := gaussianAverageBCF s.toNNReal A))).norm.const_mul (c⁻¹^2) |>.tendsto
    exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb ht)
  have he : (fun t : ℝ => heatTiltBCF t.toNNReal d f h) =
      (fun t => gaussianAverageBCF t.toNNReal (A*h)*J t) := by
    ext t x
    change gaussianAverage t.toNNReal (A*h) x / gaussianAverage t.toNNReal A x = _
    rfl
  rw [he]
  exact hcb.mul hJ

lemma heatGenerator_hasDerivAt (g : Jet3) (d : ℝ≥0) (x : ℝ) :
    HasDerivAt (heatGenerator d g : ℝ → ℝ)
      (((1/2 : ℝ) • (g.d3+(2*(d:ℝ)) • (g.d1*g.d2))) x) x := by
  have hh := ((g.has3 x).add ((g.has2 x).pow 2 |>.const_mul (d : ℝ))).const_mul (1/2 : ℝ)
  change HasDerivAt (fun y => (1/2 : ℝ)*(g.d2 y+(d:ℝ)*(g.d1 y)^2))
    ((1/2 : ℝ)*(g.d3 x+(2*(d:ℝ))*(g.d1 x*g.d2 x))) x
  exact hh.congr_deriv (by norm_num; ring)

lemma heatTilt_heatGenerator (g : Jet3) (s d : ℝ≥0) :
    heatTiltCLM s d g.f (heatGenerator d g) = heatGenerator d (g.heatLog s d) := by
  by_cases hd : d = 0
  · subst d
    ext x
    simp only [heatGenerator,NNReal.coe_zero,zero_smul,add_zero]
    change heatTilt s 0 g.f ((1/2 : ℝ) • g.d2) x = _
    rw [heatTilt_zero,gaussianAverage_smul]
    simp only [Jet3.heatLog,↓reduceDIte]
    rfl
  have hdR : (d : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hd
  ext x
  have hf : (g.exp d).d2 = (d : ℝ) • (expBCF d g.f*(g.d2+(d : ℝ) • g.d1^2)) := by
    ext z
    simp only [Jet3.exp,BoundedContinuousFunction.coe_smul,BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_mul,BoundedContinuousFunction.coe_pow,
      Pi.add_apply,Pi.mul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  have hf1 : (g.exp d).d1 = (d : ℝ) • (expBCF d g.f*g.d1) := rfl
  change heatTilt s d g.f (heatGenerator d g) x = _
  simp only [heatGenerator,heatTilt_smul,heatTilt_add,Jet3.heatLog,hd,↓reduceDIte]
  change (1/2)*(heatTilt s d g.f g.d2 x + (d:ℝ)*heatTilt s d g.f (g.d1^2) x) =
    (1/2)*((d : ℝ)⁻¹ *
      (gaussianAverage s (g.exp d).d2 x * (gaussianAverage s (expBCF d g.f) x)⁻¹ -
       (gaussianAverage s (g.exp d).d1 x)^2 * ((gaussianAverage s (expBCF d g.f) x)⁻¹)^2) +
      (d : ℝ)*((d : ℝ)⁻¹ * (gaussianAverage s (g.exp d).d1 x *
        (gaussianAverage s (expBCF d g.f) x)⁻¹))^2)
  rw [hf,hf1,gaussianAverage_smul,gaussianAverage_smul]
  have hm : expBCF d g.f*(g.d2+(d : ℝ) • g.d1^2) =
      expBCF d g.f*g.d2+(d : ℝ) • (expBCF d g.f*g.d1^2) := by ext z; simp; ring
  rw [hm,gaussianAverage_add,gaussianAverage_smul]
  unfold heatTilt
  simp only [BoundedContinuousFunction.coe_mul]
  field_simp [hdR,(gaussianAverage_exp_pos s d g.f x).ne']
  ring

lemma heatLogBCF_moving_hasDerivAt (g : Jet3) (d : ℝ≥0)
    (σ : ℝ → ℝ) (G : ℝ → (ℝ →ᵇ ℝ)) (θ v : ℝ) (h h' : ℝ →ᵇ ℝ)
    (hσ : HasDerivAt σ v θ) (hs : 0 < σ θ)
    (hG : HasDerivAt G h θ) (hGθ : G θ = g.f)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) :
    HasDerivAt (fun t => heatLogBCF (σ t).toNNReal d (G t))
      (v • heatGenerator d (g.heatLog (σ θ).toNNReal d) +
        heatTiltCLM (σ θ).toNNReal d g.f h) θ := by
  let L (t : ℝ) := heatTiltCLM (σ t).toNNReal d g.f
  let A (t : ℝ) := heatLogBCF (σ t).toNNReal d g.f
  let K (t : ℝ) := G t-g.f
  have hK0 : Tendsto K (𝓝 θ) (𝓝 0) := by
    simpa only [hGθ,sub_self] using hG.continuousAt.tendsto.sub_const g.f
  have hKo : (fun t => ‖K t‖) =o[𝓝 θ] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by simpa only [norm_zero] using hK0.norm)
  have hKb : (fun t => ‖K t‖) =O[𝓝 θ] (fun t => t-θ) := by
    simpa only [hGθ] using hG.isBigO_sub.norm_left
  have hR : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
      =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
        =O[𝓝 θ] (fun t => ‖K t‖*‖K t‖) := by
      apply Asymptotics.IsBigO.of_bound (2*(d:ℝ))
      apply Filter.Eventually.of_forall
      intro t
      have he := heatLogBCF_terminal_quadratic_error (σ t).toNNReal d g.f (K t)
      simpa only [K,A,L,add_sub_cancel,norm_mul,Real.norm_of_nonneg (norm_nonneg _),pow_two] using he
    exact hb.trans_isLittleO (by simpa only [one_mul] using hKo.mul_isBigO hKb)
  have hE : (fun t => L t (G t-g.f-(t-θ) • h)) =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => L t (G t-g.f-(t-θ) • h)) =O[𝓝 θ]
        (fun t => G t-g.f-(t-θ) • h) := by
      apply Asymptotics.IsBigO.of_bound'
      exact Filter.Eventually.of_forall (fun t => heatTiltBCF_norm_le (σ t).toNNReal d g.f _)
    apply hb.trans_isLittleO
    simpa only [hGθ] using hG.isLittleO
  have hLc : Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 0) := by
    have hc := (heatTiltBCF_time_continuous_of_deriv g.f g.d1 h h' g.has1 hh d).continuousAt.comp
      hσ.continuousAt
    have he := hc.tendsto.sub_const (L θ h)
    change Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 (L θ h-L θ h)) at he
    simpa only [sub_self] using he
  have hLo : (fun t => (t-θ) • (L t h-L θ h)) =o[𝓝 θ] (fun t => t-θ) := by
    have he := (Asymptotics.isBigO_refl (fun t : ℝ => t-θ) (𝓝 θ)).smul_isLittleO
      ((Asymptotics.isLittleO_one_iff ℝ).mpr hLc)
    simpa only [smul_eq_mul,mul_one] using he
  have hA : HasDerivAt A (v • heatGenerator d (g.heatLog (σ θ).toNNReal d)) θ :=
    (heatLogBCF_time_hasDerivAt g d (σ θ) hs).scomp θ hσ
  apply HasDerivAt.of_isLittleO
  apply ((hA.isLittleO.add hR).add hE |>.add hLo).congr_left
  intro t
  simp only [hGθ,K,A,L,map_sub,map_smul,smul_add,smul_sub]
  abel

lemma heatTiltBCF_hasDerivAt (s d : ℝ≥0) (f f' h h' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) (x : ℝ) :
    HasDerivAt (heatTiltBCF s d f h : ℝ→ℝ)
      ((heatTiltBCF s d f h' + (d:ℝ) •
        (heatTiltBCF s d f (f'*h)-heatTiltBCF s d f f'*heatTiltBCF s d f h)) x) x := by
  let A := expBCF d f
  let A' := (d : ℝ) • (A*f')
  have hA y : HasDerivAt (A:ℝ→ℝ) (A' y) y := by
    change HasDerivAt (fun z => Real.exp ((d:ℝ)*f z)) ((d:ℝ)*(A y*f' y)) y
    exact ((hf y).const_mul (d:ℝ)).exp.congr_deriv (by dsimp [A,expBCF]; ring)
  have hB y : HasDerivAt (A*h : ℝ→ᵇ ℝ) ((A'*h+A*h') y) y := by
    simpa only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
      BoundedContinuousFunction.coe_add,Pi.add_apply] using (hA y).mul (hh y)
  have he := (gaussianAverage_hasDerivAt s (A*h) (A'*h+A*h') hB x).div
    (gaussianAverage_hasDerivAt s A A' hA x) (gaussianAverage_exp_pos s d f x).ne'
  change HasDerivAt (fun y => gaussianAverage s (A*h) y / gaussianAverage s A y) _ x
  apply he.congr_deriv
  have hmul : A'*h = (d:ℝ) • (A*(f'*h)) := by ext y; dsimp [A']; ring
  rw [gaussianAverage_add,hmul,gaussianAverage_smul]
  symm
  change (gaussianAverage s (A*h') x/gaussianAverage s A x) +
    (d:ℝ)*((gaussianAverage s (A*(f'*h)) x/gaussianAverage s A x)-
      (gaussianAverage s (A*f') x/gaussianAverage s A x)*
        (gaussianAverage s (A*h) x/gaussianAverage s A x)) = _
  dsimp only [A']
  rw [gaussianAverage_smul]
  simp only [BoundedContinuousFunction.coe_mul]
  field_simp [show gaussianAverage s A x ≠ 0 from (gaussianAverage_exp_pos s d f x).ne']
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedC1
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma BoundedC1.zero : BoundedC1 (0 : ℝ→ᵇ ℝ) := ⟨0,fun x => hasDerivAt_const x 0⟩

lemma BoundedC1.add {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h) :
    BoundedC1 (f+h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨f'+h',fun x => (hf' x).add (hh' x)⟩

lemma BoundedC1.smul {f : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (a : ℝ) :
    BoundedC1 (a • f) := by
  obtain ⟨f',hf'⟩ := hf
  exact ⟨a • f',fun x => (hf' x).const_mul a⟩

lemma BoundedC1.heatTilt {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h)
    (s d : ℝ≥0) : BoundedC1 (heatTiltCLM s d f h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨_,fun x => heatTiltBCF_hasDerivAt s d f f' h h' hf' hh' x⟩

lemma heatGenerator_boundedC1 (g : Jet3) (d : ℝ≥0) : BoundedC1 (heatGenerator d g) :=
  ⟨_,heatGenerator_hasDerivAt g d⟩

lemma parametricHeatVelocity_boundedC1 (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ) :
    BoundedC1 (parametricHeatVelocity g ps t) := by
  induction ps with
  | nil => exact BoundedC1.zero
  | cons p ps ih =>
      exact ((heatGenerator_boundedC1 _ _).smul p.rate).add
        (BoundedC1.heatTilt ⟨_,(parametricHeatJet g ps t).has1⟩ ih _ _)

lemma parametricHeatJet_hasDerivAt (g : Jet3) (ps : List HeatIntervalParam) (θ : ℝ)
    (hp : ∀ p ∈ ps, HasDerivAt p.duration p.rate θ ∧ 0 < p.duration θ) :
    HasDerivAt (fun t => (parametricHeatJet g ps t).f) (parametricHeatVelocity g ps θ) θ := by
  induction ps with
  | nil => exact hasDerivAt_const θ g.f
  | cons p ps ih =>
    have hhead := hp p (List.mem_cons_self ..)
    have htail := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    obtain ⟨h',hh'⟩ := parametricHeatVelocity_boundedC1 g ps θ
    have he := heatLogBCF_moving_hasDerivAt (parametricHeatJet g ps θ) p.coefficient
      p.duration (fun t => (parametricHeatJet g ps t).f) θ p.rate
      (parametricHeatVelocity g ps θ) h' hhead.1 hhead.2 htail rfl hh'
    simpa only [parametricHeatJet,parametricHeatVelocity,Jet3.heatLog_f] using he

lemma weighted_list_tail_nonneg (xs : List (ℝ×ℝ))
    (hc : xs.Pairwise (fun u v => u.2 ≤ v.2))
    (hc0 : ∀ u ∈ xs, 0 ≤ u.2)
    (ht : ∀ ys : List (ℝ×ℝ), ys.IsSuffix xs → 0 ≤ (ys.map Prod.fst).sum) :
    0 ≤ (xs.map (fun u => u.1*u.2)).sum := by
  suffices ∀ (b : ℝ), (∀ u ∈ xs, b ≤ u.2) →
      b*(xs.map Prod.fst).sum ≤ (xs.map (fun u => u.1*u.2)).sum by
    simpa only [zero_mul] using this 0 hc0
  intro b hb
  induction xs generalizing b with
  | nil => simp
  | cons u xs ih =>
    obtain ⟨hum,hrest⟩ := List.pairwise_cons.mp hc
    have htail : ∀ ys : List (ℝ×ℝ), ys.IsSuffix xs → 0 ≤ (ys.map Prod.fst).sum := by
      intro ys hys
      exact ht ys (hys.trans (List.suffix_cons u xs))
    have hi := ih hrest (fun v hv => hc0 v (List.mem_cons_of_mem _ hv)) htail u.2 hum
    have hx := ht (u::xs) (by simp)
    have hu := hb u (List.mem_cons_self ..)
    simp only [List.map_cons,List.sum_cons] at hx ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hx]

lemma heatBoundarySum_cons (g : Jet3) (θ : ℝ) (p q : HeatIntervalParam)
    (ps : List HeatIntervalParam) (a : ℝ) :
    heatBoundarySum g θ (p::q::ps) a =
      (((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate)) •
        heatTiltCLM (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
          ((parametricHeatJet g (q::ps) θ).d1^2) +
      heatTiltCLM (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
        (heatBoundarySum g θ (q::ps) (a+p.rate)) := by
  simp only [heatBoundarySum,heatBoundaryTerms,List.map_cons,List.sum_cons,List.map_map]
  congr 1
  rw [map_list_sum,List.map_map]
  congr 1
  apply List.map_congr_left
  intro z _
  exact (map_smul _ _ _).symm

lemma heatGenerator_sub (g : Jet3) (d e : ℝ≥0) :
    heatGenerator d g-heatGenerator e g = (((d:ℝ)-(e:ℝ))/2) • (g.d1^2) := by
  ext x
  simp only [heatGenerator,BoundedContinuousFunction.coe_sub,BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_pow,Pi.sub_apply,
    Pi.add_apply,Pi.pow_apply,smul_eq_mul]
  ring

lemma parametricHeatVelocity_boundary (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam)
    (a : ℝ) (hend : a+(ps.map HeatIntervalParam.rate).sum = 0) :
    parametricHeatVelocity g ps θ+a • firstHeatGenerator g ps θ =
      (-1/2 : ℝ) • heatBoundarySum g θ ps a := by
  induction ps generalizing a with
  | nil => simp [parametricHeatVelocity,firstHeatGenerator,heatBoundarySum,heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil =>
      simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero] at hend
      simp only [parametricHeatVelocity,firstHeatGenerator,heatBoundarySum,heatBoundaryTerms,
        List.map_nil,List.sum_nil,map_zero,add_zero,smul_zero]
      rw [← add_smul,add_comm p.rate a,hend,zero_smul]
    | cons q ps =>
      have hend' : (a+p.rate)+((q::ps).map HeatIntervalParam.rate).sum = 0 := by
        simpa only [List.map_cons,List.sum_cons,add_assoc] using hend
      have hi := ih (a+p.rate) hend'
      let u := parametricHeatJet g (q::ps) θ
      let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
      have hh := congrArg T hi
      simp only [map_add,map_smul] at hh
      change T (parametricHeatVelocity g (q::ps) θ)+(a+p.rate) • T (heatGenerator q.coefficient u) =
        (-1/2:ℝ) • T (heatBoundarySum g θ (q::ps) (a+p.rate)) at hh
      have hg := congrArg T (heatGenerator_sub u p.coefficient q.coefficient)
      simp only [map_sub,map_smul] at hg
      rw [heatBoundarySum_cons]
      change p.rate • heatGenerator p.coefficient (u.heatLog (p.duration θ).toNNReal p.coefficient)+
        T (parametricHeatVelocity g (q::ps) θ)+
        a • heatGenerator p.coefficient (u.heatLog (p.duration θ).toNNReal p.coefficient) = _
      rw [← heatTilt_heatGenerator u (p.duration θ).toNNReal p.coefficient]
      change p.rate • T (heatGenerator p.coefficient u)+T (parametricHeatVelocity g (q::ps) θ)+
        a • T (heatGenerator p.coefficient u) = (-1/2:ℝ) •
          ((((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate)) • T (u.d1^2)+
            T (heatBoundarySum g θ (q::ps) (a+p.rate)))
      linear_combination (norm := module) hh+(a+p.rate) • hg

lemma heatBoundaryTerms_lower (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) :
    ∀ z ∈ heatBoundaryTerms g θ ps a, ∀ x,
      ((parametricHeatJet g ps θ).d1 x)^2 ≤ z.2 x := by
  induction ps generalizing a with
  | nil => simp [heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil => simp [heatBoundaryTerms]
    | cons q ps =>
      intro z hz x
      let u := parametricHeatJet g (q::ps) θ
      let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
      have hfirst := u.heatLog_d1_sq_le (p.duration θ).toNNReal p.coefficient x
      change ((parametricHeatJet g (p::q::ps) θ).d1 x)^2 ≤ (T (u.d1^2)) x at hfirst
      simp only [heatBoundaryTerms,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hfirst
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
        exact hfirst.trans (heatTilt_mono (p.duration θ).toNNReal p.coefficient u.f
          (u.d1^2) w.2 (fun y => ih (a+p.rate) w hw y) x)

lemma heatBoundaryTerms_ordered (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) :
    (heatBoundaryTerms g θ ps a).Pairwise (fun z w => ∀ x, z.2 x ≤ w.2 x) := by
  induction ps generalizing a with
  | nil => simp [heatBoundaryTerms]
  | cons p ps ih =>
    cases ps with
    | nil => simp [heatBoundaryTerms]
    | cons q ps =>
      simp only [heatBoundaryTerms,List.pairwise_cons]
      constructor
      · intro z hz x
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
        exact heatTilt_mono (p.duration θ).toNNReal p.coefficient (parametricHeatJet g (q::ps) θ).f
          ((parametricHeatJet g (q::ps) θ).d1^2) w.2
          (fun y => heatBoundaryTerms_lower g θ (q::ps) (a+p.rate) w hw y) x
      · rw [List.pairwise_map]
        exact (ih (a+p.rate)).imp (fun hz x => heatTilt_mono (p.duration θ).toNNReal p.coefficient
          (parametricHeatJet g (q::ps) θ).f _ _ hz x)

lemma heatBoundarySum_nonneg (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ)
    (ht : ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)), zs.IsSuffix (heatBoundaryTerms g θ ps a) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : 0 ≤ heatBoundarySum g θ ps a x := by
  let zs := heatBoundaryTerms g θ ps a
  let val (z : ℝ×(ℝ→ᵇ ℝ)) : ℝ×ℝ := (z.1,z.2 x)
  have hc : (zs.map val).Pairwise (fun u v => u.2 ≤ v.2) := by
    rw [List.pairwise_map]
    exact (heatBoundaryTerms_ordered g θ ps a).imp (fun h => h x)
  have hc0 : ∀ u ∈ zs.map val, 0 ≤ u.2 := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    exact (sq_nonneg _).trans (heatBoundaryTerms_lower g θ ps a z hz x)
  have htail : ∀ ys : List (ℝ×ℝ), ys.IsSuffix (zs.map val) → 0 ≤ (ys.map Prod.fst).sum := by
    intro ys hys
    obtain ⟨ws,hws,rfl⟩ := List.suffix_map_iff.mp hys
    simpa only [List.map_map,Function.comp_def,val] using ht ws hws
  have he := weighted_list_tail_nonneg (zs.map val) hc hc0 htail
  change 0 ≤ (BoundedContinuousFunction.evalCLM ℝ x) ((zs.map (fun z => z.1 • z.2)).sum)
  rw [map_list_sum,List.map_map]
  change 0 ≤ (zs.map (fun z => z.1*z.2 x)).sum
  simpa only [List.map_map,Function.comp_def,val] using he

lemma parametricHeatJet_deriv_nonpos (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam)
    (hp : ∀ p ∈ ps, HasDerivAt p.duration p.rate θ ∧ 0 < p.duration θ)
    (hend : (ps.map HeatIntervalParam.rate).sum = 0)
    (ht : ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)), zs.IsSuffix (heatBoundaryTerms g θ ps 0) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : deriv (fun t => (parametricHeatJet g ps t).f x) θ ≤ 0 := by
  have hd := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt θ
    (parametricHeatJet_hasDerivAt g ps θ hp)
  change HasDerivAt (fun t => (parametricHeatJet g ps t).f x) ((parametricHeatVelocity g ps θ) x) θ at hd
  rw [hd.deriv]
  have he := parametricHeatVelocity_boundary g θ ps 0 (by simpa only [zero_add] using hend)
  simp only [zero_smul,add_zero] at he
  rw [he]
  change (-1/2:ℝ)*heatBoundarySum g θ ps 0 x ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (heatBoundarySum_nonneg g θ ps 0 ht x)

lemma heatLogBCF_time_continuousAt_all (g : Jet3) (d : ℝ≥0) (s : ℝ) :
    ContinuousAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f) s := by
  by_cases hd : d = 0
  · subst d
    have he : (fun t : ℝ => heatLogBCF t.toNNReal 0 g.f) =
        (fun t => gaussianAverageBCF t.toNNReal g.f) := by ext t x; simp [heatLog]
    rw [he]
    exact (gaussianAverageBCF_time_continuous_of_deriv g.f g.d1 g.has1).continuousAt
  let A : ℝ → (ℝ →ᵇ ℝ) := fun t => gaussianAverageBCF t.toNNReal (expBCF d g.f)
  let c : ℝ := Real.exp (-(d : ℝ)*‖g.f‖)
  have hc : 0 < c := Real.exp_pos _
  have hb t : ∀ x, c ≤ A t x := fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg g.f x).1
  have ha : ContinuousAt A s := (gaussianAverageBCF_time_continuous_of_deriv (g.exp d).f (g.exp d).d1 (g.exp d).has1).continuousAt
  have hbd t : ‖heatLogBCF t.toNNReal d g.f - heatLogBCF s.toNNReal d g.f‖ ≤
      (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change |heatLog t.toNNReal d g.f x-heatLog s.toNNReal d g.f x| ≤ _
    simp only [heatLog,hd,↓reduceIte,← mul_sub,abs_mul,abs_inv,abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ)⁻¹*(c⁻¹*|A t x-A s x|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_above hc (hb s x) (hb t x)) (by positivity)
      _ ≤ (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ((A t-A s).norm_coe_le_norm x) (by positivity)
  have ht : Tendsto (fun t => (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖) (𝓝 s) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (ha.sub (continuousAt_const (y := A s))).norm.const_mul ((d : ℝ)⁻¹*c⁻¹) |>.tendsto
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ht)

lemma heatLogBCF_terminal_norm_le (s d : ℝ≥0) (f h : ℝ→ᵇ ℝ) :
    ‖heatLogBCF s d f-heatLogBCF s d h‖ ≤ ‖f-h‖ := by
  have hb (u : ℝ→ᵇ ℝ) : ‖heatTiltCLM s d u‖ ≤ 1 := by
    apply (heatTiltCLM s d u).opNorm_le_bound (by norm_num)
    intro v
    change ‖heatTiltBCF s d u v‖ ≤ 1*‖v‖
    simpa only [one_mul] using heatTiltBCF_norm_le s d u v
  simpa only [one_mul] using (convex_univ : Convex ℝ (Set.univ : Set (ℝ→ᵇ ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u _ => (heatLogBCF_hasFDerivAt s d u).hasFDerivWithinAt)
    (fun u _ => hb u) (mem_univ h) (mem_univ f)

lemma heatLogBCF_moving_continuousAt (g : Jet3) (d : ℝ≥0)
    (s : ℝ→ℝ) (F : ℝ→(ℝ→ᵇ ℝ)) (t : ℝ)
    (hs : ContinuousAt s t) (hF : ContinuousAt F t) (he : F t = g.f) :
    ContinuousAt (fun r => heatLogBCF (s r).toNNReal d (F r)) t := by
  have hc := (heatLogBCF_time_continuousAt_all g d (s t)).comp hs
  have hb r : ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s t).toNNReal d (F t)‖ ≤
      ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖ := by
    calc
      _ ≤ ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s r).toNNReal d (F t)‖+
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have H := add_le_add_right (heatLogBCF_terminal_norm_le (s r).toNNReal d (F r) (F t))
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖
        simpa only [he,add_comm] using H
  have hz : Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t) (𝓝 0) := by
    have H := ((hF.sub (continuousAt_const (y := F t))).norm.add
        (hc.sub (continuousAt_const (y := heatLogBCF (s t).toNNReal d g.f))).norm).tendsto
    change Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t)
      (𝓝 (‖F t-F t‖+‖heatLogBCF (s t).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖)) at H
    simpa only [sub_self,norm_zero,zero_add] using H
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb hz)

lemma parametricHeatJet_continuousAt (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ)
    (hp : ∀ p ∈ ps, ContinuousAt p.duration t) :
    ContinuousAt (fun r => (parametricHeatJet g ps r).f) t := by
  induction ps with
  | nil => exact continuousAt_const
  | cons p ps ih =>
    simp only [parametricHeatJet,Jet3.heatLog_f]
    exact heatLogBCF_moving_continuousAt (parametricHeatJet g ps t) p.coefficient p.duration
      (fun r => (parametricHeatJet g ps r).f) t (hp p (List.mem_cons_self))
        (ih fun q hq => hp q (List.mem_cons_of_mem p hq)) rfl

lemma parametricHeatJet_tail_order (g : Jet3) (ps : List HeatIntervalParam)
    (hc : ∀ p ∈ ps, Continuous p.duration)
    (hp : ∀ t ∈ Ioo (0:ℝ) 1, ∀ p ∈ ps, HasDerivAt p.duration p.rate t ∧ 0 < p.duration t)
    (hend : (ps.map HeatIntervalParam.rate).sum = 0)
    (ht : ∀ t ∈ Ioo (0:ℝ) 1, ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)),
      zs.IsSuffix (heatBoundaryTerms g t ps 0) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : (parametricHeatJet g ps 1).f x ≤ (parametricHeatJet g ps 0).f x := by
  have hcont : Continuous (fun t => (parametricHeatJet g ps t).f x) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt g ps t (fun p h => (hc p h).continuousAt))
  have hdiff : DifferentiableOn ℝ (fun t => (parametricHeatJet g ps t).f x) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact ((BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
      (parametricHeatJet_hasDerivAt g ps t (hp t ht))).differentiableAt.differentiableWithinAt
  have hn := antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1) hcont.continuousOn hdiff
    (fun t h => parametricHeatJet_deriv_nonpos g t ps (hp t (by simpa only [interior_Icc] using h))
      hend (ht t (by simpa only [interior_Icc] using h)) x)
  exact hn ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapBlock
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

section Positivity

variable {Ω : Type*} [MeasurableSpace Ω]

lemma negativeMatrices_measurable (n : ℕ) (δ : ℝ) :
    MeasurableSet (negativeMatrices n δ) := by
  unfold negativeMatrices
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _h
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

omit [MeasurableSpace Ω] in
lemma negativeClique_succ (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    negativeClique R (n + 1) δ = negativeClique R n δ ∩
      ⋂ i : Fin n, {ω | R ω i n < -δ} := by
  ext ω
  simp only [mem_inter_iff, mem_iInter, mem_ofPred]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact h i.castSucc j.castSucc (by exact hij)
    · intro i
      exact h i.castSucc (Fin.last n) (by simp)
  · rintro ⟨hold, hnew⟩ i j hij
    by_cases hj : j.val < n
    · exact hold ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ hij
    · have jeq : (j : ℕ) = n := by omega
      have hi : (i : ℕ) < n := by omega
      simpa only [overlapBlock, jeq] using hnew ⟨i, hi⟩

omit [MeasurableSpace Ω] in
lemma negativeClique_two (R : Ω → ℕ → ℕ → ℝ) (δ : ℝ) :
    negativeClique R 2 δ = {ω | R ω 0 1 < -δ} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    have hi : (i : ℕ) = 0 := by omega
    have hj : (j : ℕ) = 1 := by omega
    change R ω 0 1 < -δ at h
    simpa only [overlapBlock, hi, hj] using h

lemma measureReal_inter_iInter_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {E : Set Ω} {T : ι → Set Ω}
    (hT : ∀ i, MeasurableSet (T i)) :
    μ.real E - ∑ i, μ.real (E \ T i) ≤ μ.real (E ∩ ⋂ i, T i) := by
  classical
  have hu : E \ (⋂ i, T i) = ⋃ i ∈ (Finset.univ : Finset ι), E \ T i := by
    ext ω
    simp
  have hbound : μ.real (E \ ⋂ i, T i) ≤ ∑ i, μ.real (E \ T i) := by
    rw [hu]
    exact measureReal_biUnion_finset_le _ _
  have hsum := measureReal_inter_add_sdiff (μ := μ) (s := E) (MeasurableSet.iInter hT)
  linarith

lemma gg_negativeClique_extension (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hGG : GhirlandaGuerra μ R) {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) :
    μ.real {ω | R ω 0 1 < -δ} * μ.real (negativeClique R n δ) ≤
      μ.real (negativeClique R (n + 1) δ) := by
  classical
  let b := μ.real {ω | R ω 0 1 < -δ}
  let p := μ.real (negativeClique R n δ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htail (i : Fin n) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) = p * (b + (n - 1)) / n := by
    have h := hGG n hn i (negativeMatrices n δ) (negativeMatrices_measurable n δ)
      (Iio (-δ)) measurableSet_Iio
    have hpair (j : Fin n) (hji : j ≠ i) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ}) = p := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hsym] with ω hω
      apply propext
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        change R ω i j < -δ
        rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
        · exact h i j hij
        · rw [hω i j]
          exact h j i hij
    change μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) =
      p * b / n + (∑ j ∈ Finset.univ.erase i,
        μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ})) / n at h
    rw [Finset.sum_congr rfl (fun j hj => hpair j (Finset.ne_of_mem_erase hj))] at h
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [h]
    ring
  have hbad (i : Fin n) :
      μ.real (negativeClique R n δ \ {ω | R ω i n < -δ}) = p * (1 - b) / n := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := negativeClique R n δ)
      (t := {ω | R ω i n < -δ}) (measurableSet_lt (hR i n) measurable_const)
    rw [htail i] at h
    change _ + _ = p at h
    apply (eq_div_iff (ne_of_gt hnpos)).mpr
    field_simp at h
    nlinarith
  rw [negativeClique_succ]
  have h := measureReal_inter_iInter_lower μ (E := negativeClique R n δ)
    (T := fun i : Fin n => {ω | R ω i n < -δ})
    (fun i => measurableSet_lt (hR i n) measurable_const)
  simp_rw [hbad] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have he : p - (n : ℝ) * (p * (1 - b) / n) = b * p := by
    field_simp
    ring
  rwa [he] at h

lemma negative_gram_sum_bound {n : ℕ} {Q : Fin n → Fin n → ℝ} {δ : ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i ≤ 1)
    (hneg : ∀ i j, i < j → Q i j < -δ) :
    (∑ i, ∑ j, Q i j) ≤ (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) := by
  classical
  have hrow (i : Fin n) : (∑ j, Q i j) ≤ 1 - δ * ((n : ℝ) - 1) := by
    have hpair (j : Fin n) (hji : j ≠ i) : Q i j ≤ -δ := by
      rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
      · exact (hneg i j hij).le
      · rw [hsym i j]
        exact (hneg j i hij).le
    have hs : (∑ j ∈ Finset.univ.erase i, Q i j) ≤
        ∑ _j ∈ Finset.univ.erase i, -δ :=
      Finset.sum_le_sum fun j hj => hpair j (Finset.ne_of_mem_erase hj)
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by have := i.isLt; omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    have ht := Finset.sum_erase_add Finset.univ (Q i) (Finset.mem_univ i)
    nlinarith [hdiag i]
  calc
    _ ≤ ∑ _i : Fin n, (1 - δ * ((n : ℝ) - 1)) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; ring

lemma negativeClique_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 1 < δ * ((n : ℝ) - 1)) :
    μ (negativeClique R n δ) = 0 := by
  have hnot : ∀ᵐ ω ∂μ, ω ∉ negativeClique R n δ := by
    filter_upwards [hsym, hdiag, hpos n] with ω hωs hωd hωp
    intro hωn
    have hb := negative_gram_sum_bound
      (Q := fun i j : Fin n => R ω i j)
      (fun i j => hωs i j) (fun i => hωd i) hωn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) < 0 :=
      mul_neg_of_pos_of_neg hn' (by linarith)
    linarith
  simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hnot

theorem gg_negative_threshold_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | R ω 0 1 < -δ} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra hb
  have hbpos : 0 < μ.real {ω | R ω 0 1 < -δ} := lt_of_not_ge hb
  have hcpos (k : ℕ) : 0 < μ.real (negativeClique R (k + 2) δ) := by
    induction k with
    | zero => simpa only [zero_add, negativeClique_two] using hbpos
    | succ k hk =>
      have he := gg_negativeClique_extension μ hR hsym hGG (n := k + 2) (by omega) δ
      exact (mul_pos hbpos hk).trans_le he
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  have hkδ : 1 < (k : ℝ) * δ := (div_lt_iff₀ hδ).mp hk
  have he : 1 < δ * (((k + 2 : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  have hz := negativeClique_null μ hsym hdiag hpos (n := k + 2) (by omega) he
  have hz' : μ.real (negativeClique R (k + 2) δ) = 0 := (measureReal_eq_zero_iff (μ := μ)).mpr hz
  linarith [hcpos k]

theorem gg_overlap_nonnegative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) :
    ∀ᵐ ω ∂μ, 0 ≤ R ω 0 1 := by
  have ht (k : ℕ) : ∀ᵐ ω ∂μ, -(1 / ((k : ℝ) + 1)) ≤ R ω 0 1 := by
    rw [ae_iff]
    simpa only [not_le] using gg_negative_threshold_null μ hR hsym hdiag hpos hGG
      (δ := 1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr ht] with ω hω
  have hlim : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  exact le_of_tendsto hlim (Eventually.of_forall hω)

end Positivity

lemma gg_star_growth_impossible {a : ℕ → ℝ} {N ζ : ℝ}
    (hN : 2 ≤ N) (hζ : 0 < ζ) (ha : ∀ k, 0 ≤ a k) (hzero : 0 < a 0)
    (hrec : ∀ k, (N + k) * a (k + 1) = (N + k - 1 + ζ) * a k)
    (hbound : ∀ k : ℕ, (k + 1 : ℝ) * a k ≤ 1) : False := by
  let b : ℕ → ℝ := fun k => (N + k - 1) * a k
  have hbzero : 0 < b 0 := by dsimp [b]; nlinarith
  have hdiff (k : ℕ) : b (k + 1) = b k + ζ * a k := by
    dsimp [b]
    push_cast
    nlinarith [hrec k]
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hdiff]
    exact le_add_of_nonneg_right (mul_nonneg hζ.le (ha k))
  have hblower (k : ℕ) : b 0 ≤ b k := hbmono (Nat.zero_le k)
  have hbupper (k : ℕ) : b k ≤ N := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc
      b k ≤ N * ((k + 1 : ℝ) * a k) := by
        dsimp [b]
        have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
      _ ≤ N := by nlinarith [hbound k]
  have hsum (k : ℕ) : ζ * ∑ j ∈ Finset.range k, a j = b k - b 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, mul_add, ih, hdiff]; ring
  have hasum : Summable a := by
    apply summable_of_sum_range_le ha (c := N / ζ)
    intro k
    apply (le_div_iff₀ hζ).mpr
    nlinarith [hsum k, hbupper k]
  have hdom (k : ℕ) : (1 / (k + 1 : ℝ)) ≤ (N / b 0) * a k := by
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [div_le_iff₀ hk]
    have : b 0 ≤ N * ((k + 1 : ℝ) * a k) := by
      calc b 0 ≤ b k := hblower k
           _ ≤ N * ((k + 1 : ℝ) * a k) := by
             dsimp [b]
             have hknonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
             have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
             nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
    have hn : N * ((k + 1 : ℝ) * a k) / b 0 ≥ 1 :=
      (le_div_iff₀ hbzero).mpr (by simpa using this)
    calc 1 ≤ N * ((k + 1 : ℝ) * a k) / b 0 := hn
         _ = (N / b 0) * a k * (k + 1 : ℝ) := by ring
  have hharm : Summable (fun k : ℕ => 1 / (k + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom (hasum.mul_left (N / b 0))
  have hharm' : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm')

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
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

lemma copyBlock_measurable (r j : ℕ) : Measurable (copyBlock r j) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma copyEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (j : ℕ) : MeasurableSet (copyEvent r s j) :=
  hs.preimage (copyBlock_measurable r j)

lemma copyIndex_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (i : Fin (r + 1)) :
    π (copyIndex r j i) = copyIndex r (π j) i := by
  by_cases hi : i.val = r
  · simp [copyIndex, hi]
  · simp only [copyIndex, ite_eq_right hi]
    exact hπ i (by omega)

lemma copyBlock_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (Q : OverlapArray) :
    copyBlock r j (relabelArray π Q) = copyBlock r (π j) Q := by
  ext a b
  simp only [copyBlock, relabelArray, copyIndex_relabel r j π hπ]

lemma copyEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (s : Set (OverlapBlock (r + 1))) :
    relabelArray π ⁻¹' copyEvent r s j = copyEvent r s (π j) := by
  ext Q
  simp only [copyEvent, mem_preimage, copyBlock_relabel r j π hπ]

lemma uniqueEvent_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    MeasurableSet (uniqueEvent A i) := by
  simp only [uniqueEvent, ofPred_and, ofPred_forall]
  exact (hA i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)

lemma uniqueEvent_disjoint {Ω ι : Type*} (A : ι → Set Ω) :
    Pairwise (fun i j => Disjoint (uniqueEvent A i) (uniqueEvent A j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hi.2 j hij.symm hj.1

lemma uniqueEvent_probability_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (i₀ : ι)
    (hsame : ∀ i, μ.real (uniqueEvent A i) = μ.real (uniqueEvent A i₀)) :
    Fintype.card ι * μ.real (uniqueEvent A i₀) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := Finset.univ)
    (t := uniqueEvent A) (fun i _ => uniqueEvent_measurable A hA i)
    (fun i _ j _ hij => uniqueEvent_disjoint A hij)
  simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa [Measure.real] using h

lemma uniqueEvent_preimage {Ω ι : Type*} {f : Ω → Ω} (A : ι → Set Ω)
    (e : Equiv.Perm ι) (h : ∀ j, f ⁻¹' A j = A (e j)) (i : ι) :
    f ⁻¹' uniqueEvent A i = uniqueEvent A (e i) := by
  ext ω
  have hm (j : ι) : f ω ∈ A j ↔ ω ∈ A (e j) := by
    change ω ∈ f ⁻¹' A j ↔ ω ∈ A (e j)
    rw [h]
  constructor
  · intro hw
    refine ⟨(hm i).mp hw.1, ?_⟩
    intro j hji hj
    apply hw.2 (e.symm j) (fun heq => hji (by rw [← e.apply_symm_apply j, heq]))
    exact (hm _).mpr (by simpa using hj)
  · intro hw
    refine ⟨(hm i).mpr hw.1, ?_⟩
    intro j hji hj
    exact hw.2 (e j) (fun h' => hji (e.injective h')) ((hm j).mp hj)

lemma uniqueCopy_probability_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r k : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) :
    (k + 1 : ℝ) * μ.real (uniqueEvent
      (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) ≤ 1 := by
  let A : Fin (k + 1) → Set OverlapArray := fun j => copyEvent r s (r + j)
  have hA (j) : MeasurableSet (A j) := copyEvent_measurable r hs _
  have hsame (i : Fin (k + 1)) : μ.real (uniqueEvent A i) = μ.real (uniqueEvent A 0) := by
    let e : Equiv.Perm (Fin (k + 1)) := Equiv.swap i 0
    let π : Equiv.Perm ℕ := Equiv.swap (r + i) (r + (0 : Fin (k + 1)))
    have hfix : ∀ a < r, π a = a := by
      intro a ha
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by simp; omega)
    have hinj : Function.Injective (fun j : Fin (k + 1) => r + j.val) := by
      intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel hab
    have hmap (j : Fin (k + 1)) : relabelArray π ⁻¹' A j = A (e j) := by
      dsimp [A]
      rw [copyEvent_relabel r _ π hfix]
      congr 1
      exact (hinj.map_swap i 0 j).symm
    have he : e 0 = i := Equiv.swap_apply_right _ _
    rw [← he, ← uniqueEvent_preimage A e hmap]
    exact (hEx _ _).measureReal_preimage (uniqueEvent_measurable A hA 0).nullMeasurableSet
  have h := uniqueEvent_probability_bound μ A hA 0 hsame
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h

lemma prefixBlock_measurable {n m : ℕ} (h : n ≤ m) : Measurable (prefixBlock h) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma starMatrices_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (k : ℕ) : MeasurableSet (starMatrices r s t k) := by
  simp only [starMatrices, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter (hs.preimage (prefixBlock_measurable _))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply _)) measurable_const

lemma starEvent_preimage (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    overlapBlock id (r + 1 + k) ⁻¹' starMatrices r s t k = starEvent r s t k := by
  ext Q
  have hprefix : prefixBlock (Nat.le_add_right (r + 1) k)
      (overlapBlock id (r + 1 + k) Q) = copyBlock r r Q := by
    ext a b
    simp [prefixBlock, overlapBlock, copyBlock]
  simp only [mem_preimage, starMatrices, mem_ofPred_eq, hprefix, starEvent,
    copyEvent, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hj hne => h' ⟨j, hj⟩ hne⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hne => h' j j.isLt hne⟩

lemma starEvent_succ (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    starEvent r s t (k + 1) =
      starEvent r s t k ∩ {Q | Q r (r + 1 + k) < t} := by
  ext Q
  constructor
  · rintro ⟨hA, hQ⟩
    exact ⟨⟨hA, fun j hj hne => hQ j (by omega) hne⟩,
      hQ (r + 1 + k) (by omega) (by omega)⟩
  · rintro ⟨⟨hA, hQ⟩, hn⟩
    refine ⟨hA, ?_⟩
    intro j hj hne
    by_cases hlt : j < r + 1 + k
    · exact hQ j hlt hne
    · have heq : j = r + 1 + k := by omega
      simpa only [mem_ofPred_eq, heq] using hn

lemma starEvent_zero (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ)
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    starEvent r s t 0 = copyEvent r s r := by
  ext Q
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun j hj hne => hrow Q h j (by omega)⟩

lemma gg_star_recurrence (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hGG : GhirlandaGuerra μ id) {r : ℕ} (hr : 1 ≤ r)
    {s : Set (OverlapBlock (r + 1))} (hs : MeasurableSet s) (t : ℝ) (k : ℕ) :
    ((r + 1 + k : ℕ) : ℝ) * μ.real (starEvent r s t (k + 1)) =
      (((r + 1 + k : ℕ) : ℝ) - 1 + μ.real {Q | Q 0 1 < t}) *
        μ.real (starEvent r s t k) := by
  classical
  let m := r + 1 + k
  let i : Fin m := ⟨r, by dsimp [m]; omega⟩
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := hGG m hm i (starMatrices r s t k) (starMatrices_measurable r hs t k)
    (Iio t) measurableSet_Iio
  rw [starEvent_preimage] at h
  change μ.real (starEvent r s t k ∩ {Q | Q r m < t}) =
    μ.real (starEvent r s t k) * μ.real {Q | Q 0 1 < t} / m +
    (∑ j ∈ Finset.univ.erase i,
      μ.real (starEvent r s t k ∩ {Q | Q r j < t})) / m at h
  have hpair (j : Fin m) (hne : j ≠ i) :
      starEvent r s t k ∩ {Q | Q r j < t} = starEvent r s t k := by
    apply inter_eq_left.mpr
    intro Q hQ
    exact hQ.2 j j.isLt (fun heq => hne (Fin.ext heq))
  rw [Finset.sum_congr rfl (fun j hj => congrArg μ.real
    (hpair j (Finset.ne_of_mem_erase hj)))] at h
  have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
  rw [← starEvent_succ] at h
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) h
  field_simp at hmul
  dsimp [m] at hmul
  nlinarith [hmul]

lemma duplicateEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (j : ℕ) : MeasurableSet (duplicateEvent r s t j) :=
  ((copyEvent_measurable r hs r).inter (copyEvent_measurable r hs j)).inter
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurable_const)

lemma duplicateEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (hr : π r = r)
    (s : Set (OverlapBlock (r + 1))) (t : ℝ) :
    relabelArray π ⁻¹' duplicateEvent r s t j = duplicateEvent r s t (π j) := by
  ext Q
  simp only [duplicateEvent, copyEvent, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    copyBlock_relabel r r π hπ, copyBlock_relabel r j π hπ, hr, relabelArray]

lemma duplicateEvent_null_future (μ : Measure OverlapArray)
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) {j : ℕ} (hj : r + 1 ≤ j) :
    μ (duplicateEvent r s t j) = 0 := by
  let π : Equiv.Perm ℕ := Equiv.swap (r + 1) j
  have hfix : ∀ a ≤ r, π a = a := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  calc
    μ (duplicateEvent r s t j) = μ (relabelArray π ⁻¹' duplicateEvent r s t (r + 1)) := by
      rw [duplicateEvent_relabel r (r + 1) π (fun a ha => hfix a ha.le) (hfix r le_rfl)]
      simp only [π, Equiv.swap_apply_left]
    _ = μ (duplicateEvent r s t (r + 1)) :=
      (hEx _ _).measure_preimage (duplicateEvent_measurable r hs t (r + 1)).nullMeasurableSet
    _ = 0 := hzero

lemma star_unique_bound_of_no_duplication (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) (k : ℕ) :
    (k + 1 : ℝ) * μ.real (starEvent r s t k) ≤ 1 := by
  have hnul (j : Fin (k + 1)) : ∀ᵐ Q ∂μ, j ≠ 0 → Q ∉ duplicateEvent r s t (r + j) := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hz : μ (duplicateEvent r s t (r + j)) = 0 :=
        duplicateEvent_null_future μ hEx r hs t hzero (by
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with Q hQ
      exact fun _ => hQ
  have hae : starEvent r s t k ≤ᵐ[μ]
      uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0 := by
    filter_upwards [ae_all_iff.mpr hnul] with Q hQ
    intro hstar
    refine ⟨by simpa using hstar.1, ?_⟩
    intro j hj hmem
    apply hQ j hj
    refine ⟨⟨hstar.1, hmem⟩, ?_⟩
    exact hstar.2 (r + j) (by have := j.isLt; omega) (by
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega)
  have hle : μ.real (starEvent r s t k) ≤ μ.real
      (uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans
    (uniqueCopy_probability_bound μ hEx r k hs)

lemma edge_probability_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    (a b i j : ℕ) (t : ℝ) :
    μ.real {Q | Q (Equiv.swap a b i) (Equiv.swap a b j) < t} =
      μ.real {Q | Q i j < t} := by
  exact (hEx a b).measureReal_preimage
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i))
      measurable_const).nullMeasurableSet

theorem gg_duplicate_last (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (copyEvent r s r))
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    0 < μ.real (duplicateEvent r s t (r + 1)) := by
  by_contra hbad
  have hz : μ (duplicateEvent r s t (r + 1)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (le_antisymm (not_lt.mp hbad) (measureReal_nonneg))
  have heq : μ.real {Q | Q r 0 < t} = μ.real {Q | Q 0 1 < t} := by
    have h₁ := edge_probability_swap μ hEx 1 r 1 0 t
    have h₂ := edge_probability_swap μ hEx 0 1 0 1 t
    have hr0 : (0 : ℕ) ≠ r := by omega
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : ℕ) ≠ 1) hr0] at h₁ h₂
    exact h₁.trans h₂
  have hζ : 0 < μ.real {Q | Q 0 1 < t} := by
    rw [← heq]
    refine hA.trans_le (measureReal_mono ?_)
    exact fun Q hQ => hrow Q hQ 0 (by omega)
  apply gg_star_growth_impossible (a := fun k => μ.real (starEvent r s t k))
    (N := (r + 1 : ℕ)) (ζ := μ.real {Q | Q 0 1 < t})
    (by exact_mod_cast (by omega : 2 ≤ r + 1)) hζ (fun _ => measureReal_nonneg)
  · rwa [starEvent_zero r s t hrow]
  · intro k
    simpa only [Nat.cast_add] using gg_star_recurrence μ hGG hr hs t k
  · exact star_unique_bound_of_no_duplication μ hEx r hs t hz

lemma relabelBlock_measurable {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Measurable (relabelBlock e) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma fin_swap_val {n : ℕ} (p q a : Fin n) :
    (Equiv.swap p q a).val = Equiv.swap p.val q.val a.val :=
  Fin.val_injective.map_swap p q a

lemma relabelBlock_swap {n : ℕ} (p q : Fin n) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q) (overlapBlock id n Q) =
      overlapBlock id n (relabelArray (Equiv.swap p.val q.val) Q) := by
  ext a b
  simp only [relabelBlock, overlapBlock, id_eq, relabelArray, fin_swap_val]

lemma relabelArray_swap_swap (p q : ℕ) (Q : OverlapArray) :
    relabelArray (Equiv.swap p q) (relabelArray (Equiv.swap p q) Q) = Q := by
  ext a b
  simp [relabelArray]

lemma replaceBlock_last (r j : ℕ) (Q : OverlapArray) :
    replaceBlock (Fin.last r) j Q = copyBlock r j Q := by
  have h (a : Fin (r + 1)) : replaceIndex (Fin.last r) j a = copyIndex r j a := by
    simp [replaceIndex, copyIndex, Fin.ext_iff]
  ext a b
  simp only [replaceBlock, copyBlock, h]

lemma replaceBlock_swap {n : ℕ} (p q : Fin n) {j : ℕ} (hj : n ≤ j) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q)
      (replaceBlock q j (relabelArray (Equiv.swap p.val q.val) Q)) =
        replaceBlock p j Q := by
  have h (a : Fin n) : Equiv.swap p.val q.val (replaceIndex q j (Equiv.swap p q a)) =
      replaceIndex p j a := by
    by_cases ha : a = p
    · subst a
      simp only [Equiv.swap_apply_left, replaceIndex, ↓reduceIte]
      exact Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by have := q.isLt; omega)
    · have he : Equiv.swap p q a ≠ q := by
        intro h
        apply ha
        have := congrArg (Equiv.swap p q) h
        simpa using this
      simp only [replaceIndex, ite_eq_right he, ite_eq_right ha, fin_swap_val,
        Equiv.swap_apply_self]
  ext a b
  exact congrArg₂ Q (h a) (h b)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
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

lemma block_event_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    {n : ℕ} (p q : Fin n) {s : Set (OverlapBlock n)} (hs : MeasurableSet s) :
    μ.real (overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s)) =
      μ.real (overlapBlock id n ⁻¹' s) := by
  have heq : overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s) =
      relabelArray (Equiv.swap p.val q.val) ⁻¹' (overlapBlock id n ⁻¹' s) := by
    ext Q
    change relabelBlock (Equiv.swap p q) (overlapBlock id n Q) ∈ s ↔ _
    rw [relabelBlock_swap]
    rfl
  rw [heq]
  exact (hEx _ _).measureReal_preimage
    (hs.preimage (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))).nullMeasurableSet

theorem gg_duplicate_index (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) (p : Fin (r + 1)) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' s))
    (hrow : ∀ Q ∈ overlapBlock id (r + 1) ⁻¹' s,
      ∀ j : Fin (r + 1), j ≠ p → Q p j < t) :
    0 < μ.real ((overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
      {Q | Q p (r + 1) < t}) := by
  let q : Fin (r + 1) := Fin.last r
  let e := Equiv.swap p q
  let π := Equiv.swap p.val q.val
  let s' := relabelBlock e ⁻¹' s
  have hs' : MeasurableSet s' := hs.preimage (relabelBlock_measurable e)
  have hbase : copyEvent r s' r = overlapBlock id (r + 1) ⁻¹' s' := by
    ext Q
    change copyBlock r r Q ∈ s' ↔ overlapBlock id (r + 1) Q ∈ s'
    have hb : copyBlock r r Q = overlapBlock id (r + 1) Q := by
      ext a b
      simp [copyBlock, overlapBlock]
    rw [hb]
  have hA' : 0 < μ.real (copyEvent r s' r) := by
    rw [hbase]
    exact (block_event_swap μ hEx p q hs).symm ▸ hA
  have hrow' : ∀ Q ∈ copyEvent r s' r, ∀ j < r, Q r j < t := by
    intro Q hQ j hj
    have hmem : relabelArray π Q ∈ overlapBlock id (r + 1) ⁻¹' s := by
      rw [hbase] at hQ
      change relabelBlock e (overlapBlock id (r + 1) Q) ∈ s at hQ
      rwa [relabelBlock_swap] at hQ
    let a : Fin (r + 1) := ⟨j, by omega⟩
    have hne : e a ≠ p := by
      intro h
      have h' := congrArg e h
      have haq : a = q := by simpa [e] using h'
      have := congrArg Fin.val haq
      dsimp [a, q] at this
      omega
    have h := hrow (relabelArray π Q) hmem (e a) hne
    have hp : π p.val = r := by simp [π, q]
    have ha : π (e a).val = j := by simp [π, e, fin_swap_val, a]
    simpa only [relabelArray, hp, ha] using h
  have hD := gg_duplicate_last μ hEx hGG hr hs' t hA' hrow'
  have hset : relabelArray π ⁻¹' duplicateEvent r s' t (r + 1) =
      (overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
        {Q | Q p (r + 1) < t} := by
    ext Q
    have hfirst : copyBlock r r (relabelArray π Q) ∈ s' ↔
        overlapBlock id (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r r (relabelArray π Q)) ∈ s ↔ _
      have hb : copyBlock r r (relabelArray π Q) =
          overlapBlock id (r + 1) (relabelArray π Q) := by
        ext a b
        simp [copyBlock, overlapBlock]
      rw [hb, relabelBlock_swap, relabelArray_swap_swap]
    have hsecond : copyBlock r (r + 1) (relabelArray π Q) ∈ s' ↔
        replaceBlock p (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r (r + 1) (relabelArray π Q)) ∈ s ↔ _
      rw [← replaceBlock_last]
      change relabelBlock (Equiv.swap p q)
        (replaceBlock q (r + 1) (relabelArray (Equiv.swap p.val q.val) Q)) ∈ s ↔ _
      rw [replaceBlock_swap p q (le_refl _)]
    have hp : π r = p.val := by exact Equiv.swap_apply_right _ _
    have hnew : π (r + 1) = r + 1 :=
      Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by dsimp [q]; omega)
    change ((copyBlock r r (relabelArray π Q) ∈ s' ∧
      copyBlock r (r + 1) (relabelArray π Q) ∈ s') ∧
      Q (π r) (π (r + 1)) < t) ↔ ((overlapBlock id (r + 1) Q ∈ s ∧
        replaceBlock p (r + 1) Q ∈ s) ∧ Q p (r + 1) < t)
    rw [hfirst, hsecond, hp, hnew]
  rw [← hset]
  rwa [(hEx _ _).measureReal_preimage
    (duplicateEvent_measurable r hs' t (r + 1)).nullMeasurableSet]

lemma patternMatrices_measurable {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) :
    MeasurableSet (patternMatrices labels C) := by
  simp only [patternMatrices, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (hC _ _).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma pattern_append_of_duplicate {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (p : Fin n) (t : ℝ) (hdiag : C (labels p) (labels p) = Iio t)
    (Q : OverlapArray) (hSym : ∀ i j, Q i j = Q j i)
    (hA : overlapBlock id n Q ∈ patternMatrices labels C)
    (hB : replaceBlock p n Q ∈ patternMatrices labels C) (hedge : Q p n < t) :
    overlapBlock id (n + 1) Q ∈ patternMatrices (appendLabel labels (labels p)) C := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) j
    by_cases hb : b = p
    · subst b
      simpa [overlapBlock, hdiag, hSym n p] using hedge
    · have h := hB p b (Ne.symm hb)
      simpa [replaceBlock, replaceIndex, hb, overlapBlock] using h
  · intro j
    refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) j
    · by_cases ha : a = p
      · subst a
        simpa [overlapBlock, hdiag] using hedge
      · have h := hB a p ha
        simpa [replaceBlock, replaceIndex, ha, overlapBlock] using h
    · have h := hA a b (fun h => hab (congrArg Fin.castSucc h))
      simpa [overlapBlock] using h

theorem gg_pattern_append (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {r : ℕ} (hr : 1 ≤ r) (labels : Fin (r + 1) → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin (r + 1)) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (r + 1 + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  have hd := gg_duplicate_index μ hEx hGG hr p (patternMatrices_measurable labels C hC) t hA
    (fun Q hQ j hj => hcut _ _ (hQ p j (Ne.symm hj)))
  apply hd.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hSym] with Q hQ
  exact fun h => pattern_append_of_duplicate labels C p t hdiag Q hQ h.1.1 h.1.2 h.2

lemma gg_pattern_append_nat (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {n : ℕ} (hn : 2 ≤ n) (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin n) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (n + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  cases n with
  | zero => omega
  | succ r => exact gg_pattern_append μ hEx hGG hSym (by omega) labels C hC p t hdiag hcut hA

lemma appendLabel_tripleLabels {n : ℕ} (hn : 3 ≤ n) :
    appendLabel (tripleLabels n) (tripleLabels n ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩) =
      tripleLabels (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · apply Fin.ext
    simp [tripleLabels]
  · simp [tripleLabels]

theorem gg_triple_pattern (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (C : Fin 3 → Fin 3 → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (t : ℝ)
    (hdiag : ∀ k, C k k = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) C)) :
    ∀ n ≥ 3, 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices (tripleLabels n) C) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hA
  | succ n hn ih =>
    have h := gg_pattern_append_nat μ hEx hGG hSym (by omega) (tripleLabels n) C hC
      ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩ t (hdiag _) hcut ih
    rwa [appendLabel_tripleLabels hn] at h

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma inner_replicaMean {n : ℕ} (v w : Fin n → H) :
    ⟪replicaMean v, replicaMean w⟫_ℝ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪v i, w j⟫_ℝ := by
  simp only [replicaMean, real_inner_smul_left, real_inner_smul_right]
  rw [sum_inner]
  simp_rw [inner_sum]
  ring

lemma replicaMean_norm_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) {c : ℝ}
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ c) :
    ‖replicaMean v‖ ^ 2 ≤ c + (1 - c) / n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow (i : Fin n) : (∑ j, ⟪v i, v j⟫_ℝ) ≤ 1 + ((n : ℝ) - 1) * c := by
    have hs : (∑ j ∈ Finset.univ.erase i, ⟪v i, v j⟫_ℝ) ≤
        ∑ _j ∈ Finset.univ.erase i, c :=
      Finset.sum_le_sum fun j hj => hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [real_inner_self_eq_norm_sq]
    linarith [hdiag i]
  rw [← real_inner_self_eq_norm_sq, inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, v j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (1 + ((n : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = c + (1 - c) / n := by field_simp; ring

lemma replicaMean_norm_le_one {n : ℕ} (hn : 0 < n) (v : Fin n → H)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1) : ‖replicaMean v‖ ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : ‖∑ i, v i‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        nlinarith [hdiag i, norm_nonneg (v i)]
      _ = n := by simp
  calc
    ‖replicaMean v‖ = (n : ℝ)⁻¹ * ‖∑ i, v i‖ := by
      simp [replicaMean, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0

lemma inner_replicaMean_le {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ ≤ a) : ⟪replicaMean v, replicaMean w⟫_ℝ ≤ a := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = a := by field_simp

lemma le_inner_replicaMean {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, a ≤ ⟪v i, w j⟫_ℝ) : a ≤ ⟪replicaMean v, replicaMean w⟫_ℝ := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := by field_simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)

lemma duplicate_ordered_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c t : ℝ} (hab : a ≤ b)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ t)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ ≤ a)
    (h13 : ∀ i j, b ≤ ⟪v 0 i, v 2 j⟫_ℝ)
    (h23 : ∀ i j, c ≤ ⟪v 1 i, v 2 j⟫_ℝ) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_le_one hn (v 0) (hdiag 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ ≤ a := inner_replicaMean_le hn _ _ h12
  have hxz : b ≤ ⟪x, z⟫_ℝ := le_inner_replicaMean hn _ _ h13
  have hyz : c ≤ ⟪y, z⟫_ℝ := le_inner_replicaMean hn _ _ h23
  change ‖x‖ ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdiff : ‖z - y‖ ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith
  have hinner : b - a ≤ ⟪x, z - y⟫_ℝ := by rw [inner_sub_right]; linarith
  have hnonneg : 0 ≤ ⟪x, z - y⟫_ℝ := by linarith
  have habsq : (b - a) ^ 2 ≤ ⟪x, z - y⟫_ℝ ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hab) hnonneg).mpr hinner
  have hcs : ⟪x, z - y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖z - y‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (z - y)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg _))).mpr h
    simpa only [sq_abs, mul_pow] using hs
  exact habsq.trans (hcs.trans ((mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)).trans
    (by simpa using hdiff)))

lemma posSemidef_standard_basis_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (i j : Fin n) :
    letI := B.toSeminormedAddCommGroup hB
    letI := B.toInnerProductSpace hB
    ⟪(Pi.single i 1 : Fin n → ℝ), Pi.single j 1⟫_ℝ = B i j := by
  change (B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1) = B i j
  simp

lemma triangleConstraints_measurable (a b c t : ℝ) (k l : Fin 3) :
    MeasurableSet (triangleConstraints a b c t k l) := by
  unfold triangleConstraints
  split_ifs <;> measurability

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
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

lemma triangleConstraints_diag (a b c t : ℝ) (k : Fin 3) :
    triangleConstraints a b c t k k = Iio t := by simp [triangleConstraints]

lemma triangleConstraints_cut {a : ℝ} (b c t : ℝ) (hat : a ≤ t) (k l : Fin 3) :
    triangleConstraints a b c t k l ⊆ Iio t := by
  unfold triangleConstraints
  split_ifs
  · exact Subset.rfl
  · exact Iio_subset_Iio hat
  · exact Ioo_subset_Iio_self
  · exact Ioo_subset_Iio_self

lemma tripleIndex_ne {n : ℕ} {k l : Fin 3} (hkl : k ≠ l) (i j : Fin n) :
    tripleIndex k i ≠ tripleIndex l j := by
  intro h
  have := congrArg (tripleLabels (3 * n)) h
  exact hkl (by simpa using this)

lemma tripleIndex_inj {n : ℕ} (k : Fin 3) {i j : Fin n} (hij : i ≠ j) :
    tripleIndex k i ≠ tripleIndex k j := by
  intro h
  apply hij
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [tripleIndex] at h'
  omega

lemma triangle_pattern_psd_bound {n : ℕ} (hn : 0 < n)
    (B : OverlapBlock (3 * n)) (hB : Matrix.PosSemidef B)
    (hdiag : ∀ i, B i i ≤ 1) {a b c t : ℝ} (hab : a ≤ b)
    (hpattern : B ∈ patternMatrices (tripleLabels (3 * n)) (triangleConstraints a b c t)) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let _ := Matrix.toSeminormedAddCommGroup B hB
  let _ := Matrix.toInnerProductSpace B hB
  let v : Fin 3 → Fin n → (Fin (3 * n) → ℝ) := fun k i => Pi.single (tripleIndex k i) 1
  have hv (k l : Fin 3) (i j : Fin n) :
      ⟪v k i, v l j⟫_ℝ = B (tripleIndex k i) (tripleIndex l j) :=
    posSemidef_standard_basis_inner B hB _ _
  apply duplicate_ordered_blocks_bound hn v hab
  · intro k i
    rw [← real_inner_self_eq_norm_sq, hv]
    exact hdiag _
  · intro k i j hij
    rw [hv]
    have h := hpattern _ _ (tripleIndex_inj k hij)
    simp only [tripleLabels_tripleIndex, triangleConstraints_diag, mem_Iio] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 1) i j)
    simp [triangleConstraints] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (1 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le

theorem gg_triangle_pattern_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹'
      patternMatrices (tripleLabels 3) (triangleConstraints a b c t))) :
    (b - a) ^ 2 ≤ 2 * (t - c) := by
  have hall := gg_triple_pattern μ hEx hGG hSym (triangleConstraints a b c t)
    (triangleConstraints_measurable a b c t) t (triangleConstraints_diag a b c t)
    (triangleConstraints_cut b c t hat) hA
  have hbound (n : ℕ) : (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ)) := by
    have hpos := hall (3 * (n + 1)) (by omega)
    have hne : μ (overlapBlock id (3 * (n + 1)) ⁻¹'
        patternMatrices (tripleLabels (3 * (n + 1))) (triangleConstraints a b c t)) ≠ 0 := by
      intro hz
      simp [Measure.real, hz] at hpos
    obtain ⟨Q, hQ, hG, hD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (hGram.and hdiag))
    have h := triangle_pattern_psd_bound (by omega : 0 < n + 1)
      (overlapBlock id (3 * (n + 1)) Q) (hG _) (fun i => hD i) hab hQ
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have ht : Tendsto (fun n : ℕ => 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ))) atTop
      (𝓝 (2 * (t - c))) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul (2 * (1 - t))
    have h' := h.const_add (2 * (t - c))
    simpa only [mul_zero, add_zero, mul_one_div, mul_div_assoc] using h'
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

lemma triangleEvent_pattern {a b c t : ℝ} (hat : a ≤ t) (Q : OverlapArray)
    (hSym : ∀ i j, Q i j = Q j i) (hQ : Q ∈ triangleEvent a b c t) :
    overlapBlock id 3 Q ∈ patternMatrices (tripleLabels 3) (triangleConstraints a b c t) := by
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  have hQt : Q 0 1 < t := hQ.1.trans_le hat
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapBlock, tripleLabels, triangleConstraints, triangleEvent]

lemma gg_triangleEvent_null (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t) (hgap : 2 * (t - c) < (b - a) ^ 2) :
    μ (triangleEvent a b c t) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (triangleEvent a b c t) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hle : μ.real (triangleEvent a b c t) ≤ μ.real
      (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) (triangleConstraints a b c t)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hSym] with Q hQ
    exact triangleEvent_pattern hat Q hQ
  exact hgap.not_ge (gg_triangle_pattern_bound μ hEx hGG hSym hGram hdiag hab hat (hpos.trans_le hle))

lemma exists_rational_triangle_box {x y z : ℝ} (hxy : x < y) (hyz : y ≤ z) :
    ∃ a b c t : ℚ, (a : ℝ) ≤ b ∧ (a : ℝ) ≤ t ∧
      2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 ∧
      x < a ∧ (b : ℝ) < y ∧ y < t ∧ (c : ℝ) < z ∧ z < t := by
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  have hδ : 0 < ((b : ℝ) - a) ^ 2 / 8 := by positivity
  obtain ⟨c, hzc, hcz⟩ := exists_rat_btwn (show z - ((b : ℝ) - a) ^ 2 / 8 < z by linarith)
  obtain ⟨t, hzt, htz⟩ := exists_rat_btwn (show z < z + ((b : ℝ) - a) ^ 2 / 8 by linarith)
  refine ⟨a, b, c, t, hab.le, (hay.trans_le hyz).le.trans hzt.le, ?_, hxa, hby,
    hyz.trans_lt hzt, hcz, hzt⟩
  nlinarith

lemma gg_no_ordered_crossing (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ (Q 0 1 < Q 0 2 ∧ Q 0 2 ≤ Q 1 2) := by
  have hBoxes : ∀ᵐ Q ∂μ, ∀ a b c t : ℚ,
      (a : ℝ) ≤ b → (a : ℝ) ≤ t → 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 →
      Q ∉ triangleEvent a b c t := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro t
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hat : (a : ℝ) ≤ t
      · by_cases hgap : 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
            (gg_triangleEvent_null μ hEx hGG hSym hGram hdiag hab hat hgap)] with Q hQ
          exact fun _ _ _ => hQ
        · exact Eventually.of_forall fun _ _ _ h => (hgap h).elim
      · exact Eventually.of_forall fun _ _ h => (hat h).elim
    · exact Eventually.of_forall fun _ h => (hab h).elim
  filter_upwards [hBoxes] with Q hQ
  rintro ⟨hxy, hyz⟩
  obtain ⟨a, b, c, t, hab, hat, hgap, hbox⟩ := exists_rational_triangle_box hxy hyz
  exact hQ a b c t hab hat hgap hbox

lemma gram_array_symmetric (Q : OverlapArray)
    (hGram : ∀ n, Matrix.PosSemidef (overlapBlock id n Q)) : ∀ i j, Q i j = Q j i := by
  intro i j
  let n := max i j + 1
  let a : Fin n := ⟨i, by dsimp [n]; omega⟩
  let b : Fin n := ⟨j, by dsimp [n]; omega⟩
  have h := (hGram n).isHermitian.apply b a
  simpa [overlapBlock, a, b] using h

theorem gg_ultrametric (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, min (Q 0 1) (Q 0 2) ≤ Q 1 2 := by
  have hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i :=
    hGram.mono fun Q hQ => gram_array_symmetric Q hQ
  have hno := gg_no_ordered_crossing μ hEx hGG hSym hGram hdiag
  have hno' := (hEx 0 1).quasiMeasurePreserving.ae hno
  have hsmall : ∀ᵐ Q ∂μ, min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
    filter_upwards [hno, hno', hSym] with Q hQ hQ' hs
    simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide] at hQ'
    rw [hs 1 0] at hQ'
    by_cases h : Q 0 2 ≤ Q 1 2
    · rw [min_eq_left h]
      exact le_of_not_gt fun hh => hQ ⟨hh, h⟩
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact le_of_not_gt fun hh => hQ' ⟨hh, h'⟩
  have hsmall' := (hEx 0 2).quasiMeasurePreserving.ae hsmall
  filter_upwards [hsmall', hSym] with Q hQ hs
  simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
    show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide] at hQ
  simpa only [hs 2 0, hs 1 0, hs 2 1, min_comm] using hQ

lemma scalarArray_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (scalarArray f) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarBlock_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) {n : ℕ} :
    Measurable (scalarBlock f (n := n)) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarArray_swap_invariant (μ : Measure PairedOverlapArray)
    (hEx : PairedSwapInvariant μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    OverlapSwapInvariant (μ.map (scalarArray f)) := by
  intro i j
  have heq : relabelArray (Equiv.swap i j) ∘ scalarArray f =
      scalarArray f ∘ pairedRelabel (Equiv.swap i j) := rfl
  refine ⟨Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _), ?_⟩
  rw [Measure.map_map _ (scalarArray_measurable hf), heq,
    ← Measure.map_map (scalarArray_measurable hf) (hEx i j).measurable,
    (hEx i j).map_eq]
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma scalarArray_gg (μ : Measure PairedOverlapArray)
    (hGG : JointGhirlandaGuerra μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    GhirlandaGuerra (μ.map (scalarArray f)) id := by
  intro n hn i s hs t ht
  have hblock : Measurable (overlapBlock (id : OverlapArray → OverlapArray) n) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hedge (i j : ℕ) : Measurable (fun Q : OverlapArray => Q i j) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hmap (u : Set OverlapArray) (hu : MeasurableSet u) :
      (μ.map (scalarArray f)).real u = μ.real (scalarArray f ⁻¹' u) := by
    rw [measureReal_def, Measure.map_apply (scalarArray_measurable hf) hu]
    rfl
  simp only [id_eq]
  rw [hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i n ∈ t})
      ((hs.preimage hblock).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hblock), hmap {Q | Q 0 1 ∈ t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i j ∈ t})
    ((hs.preimage hblock).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact hGG n hn i (scalarBlock f ⁻¹' s) (hs.preimage (scalarBlock_measurable hf))
    (f ⁻¹' t) (ht.preimage hf)

lemma measurableSet_gram_arrays :
    MeasurableSet {Q : OverlapArray | ∀ n, Matrix.PosSemidef (overlapBlock id n Q)} := by
  apply IsClosed.measurableSet
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  have hiff (Q : OverlapArray) :=
    Matrix.posSemidef_iff_dotProduct_mulVec (M := overlapBlock id n Q)
  simp_rw [hiff]
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {Q : OverlapArray | Matrix.conjTranspose (overlapBlock id n Q) = overlapBlock id n Q}
    apply isClosed_eq <;> unfold overlapBlock <;> fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold overlapBlock
    fun_prop

lemma scalarArray_ultrametric (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, min (f (Q 0 1)) (f (Q 0 2)) ≤ f (Q 1 2) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hu := gg_ultrametric ν (scalarArray_swap_invariant μ hEx hf)
    (scalarArray_gg μ hGG hf) hg hd
  exact ae_of_ae_map hm.aemeasurable hu

lemma gg_ultrametric_triangle (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (Q 0 1) (Q 0 2) (Q 1 2) := by
  have h := gg_ultrametric μ hEx hGG hGram hdiag
  have h₁ := (hEx 0 1).quasiMeasurePreserving.ae h
  have h₂ := (hEx 0 2).quasiMeasurePreserving.ae h
  filter_upwards [h, h₁, h₂, hGram] with Q hQ hQ₁ hQ₂ hg
  have hs := gram_array_symmetric Q hg
  refine ⟨hQ, ?_, ?_⟩
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide, hs 1 0] using hQ₁
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide, hs 2 0, hs 2 1, hs 1 0,
      min_comm] using hQ₂

lemma scalarArray_ultrametric_triangle (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (f (Q 0 1)) (f (Q 0 2)) (f (Q 1 2)) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  exact ae_of_ae_map hm.aemeasurable
    (gg_ultrametric_triangle ν (scalarArray_swap_invariant μ hEx hf)
      (scalarArray_gg μ hGG hf) hg hd)

lemma ultrametric_triangle_small_eq {a b c : ℝ} (h : UltrametricTriangle a b c)
    (hab : a < b) : c = a := by
  have hlo : a ≤ c := by simpa only [min_eq_left hab.le] using h.1
  have hhi : c ≤ a := by
    rcases le_total b c with hbc | hcb
    · have : b ≤ a := by simpa only [min_eq_left hbc] using h.2.2
      exact (hab.not_ge this).elim
    · simpa only [min_eq_right hcb] using h.2.2
  exact le_antisymm hhi hlo

lemma ultrametric_sum_no_crossing {a b c x y z : ℝ}
    (hR : UltrametricTriangle a b c) (hT : UltrametricTriangle x y z)
    (hSum : min ((a + x) / 2) ((b + y) / 2) ≤ (c + z) / 2) :
    ¬ (a < b ∧ y < x) := by
  rintro ⟨hab, hyx⟩
  have hc := ultrametric_triangle_small_eq hR hab
  have hz : z = y := ultrametric_triangle_small_eq
    (show UltrametricTriangle y x z from ⟨by simpa only [min_comm] using hT.1,
      hT.2.2, hT.2.1⟩) hyx
  rw [hc, hz] at hSum
  rcases le_total ((a + x) / 2) ((b + y) / 2) with h | h
  · rw [min_eq_left h] at hSum
    linarith
  · rw [min_eq_right h] at hSum
    linarith

theorem joint_gg_no_crossing (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    (hR : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)))
    (hT : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.snd Q)))
    (hdR : ∀ᵐ Q ∂μ, ∀ i, (Q i i).1 ≤ 1)
    (hdT : ∀ᵐ Q ∂μ, ∀ i, (Q i i).2 ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2) := by
  have huR := scalarArray_ultrametric_triangle μ hEx hGG measurable_fst hR hdR
  have huT := scalarArray_ultrametric_triangle μ hEx hGG measurable_snd hT hdT
  let f : ℝ × ℝ → ℝ := fun x => (x.1 + x.2) / 2
  have hf : Measurable f := by fun_prop
  have hG : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)) := by
    filter_upwards [hR, hT] with Q hQ₁ hQ₂ n
    have heq : overlapBlock id n (scalarArray f Q) =
        (1 / 2 : ℝ) • (overlapBlock id n (scalarArray Prod.fst Q) +
          overlapBlock id n (scalarArray Prod.snd Q)) := by
      ext i j
      simp [overlapBlock, scalarArray, f, smul_eq_mul, div_eq_mul_inv, add_mul,
        mul_comm]
    rw [heq]
    exact ((hQ₁ n).add (hQ₂ n)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hd : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1 := by
    filter_upwards [hdR, hdT] with Q hQ₁ hQ₂ i
    dsimp [f]
    linarith [hQ₁ i, hQ₂ i]
  have huS := scalarArray_ultrametric μ hEx hGG hf hG hd
  filter_upwards [huR, huT, huS] with Q hQ₁ hQ₂ hQ₃
  exact ultrametric_sum_no_crossing hQ₁ hQ₂ hQ₃

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereKernel
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

theorem joint_gg_crossed_regions_null (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ)
    (hNo : ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2))
    (s t : Set (ℝ × ℝ)) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : ∀ u ∈ s, ∀ v ∈ t, u.1 < v.1 ∧ v.2 < u.2) :
    μ {Q | Q 0 1 ∈ s} = 0 ∨ μ {Q | Q 0 1 ∈ t} = 0 := by
  let S : Set (PairedOverlapBlock 2) := {A | A 0 1 ∈ s}
  have hS : MeasurableSet S := hs.preimage
    ((measurable_pi_apply 1).comp (measurable_pi_apply 0))
  have hnull : μ (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hNo] with Q hQ
    rintro ⟨h₁, h₂⟩
    exact hQ (hst (Q 0 1) h₁ (Q 0 2) h₂)
  have hid := hGG 2 (by omega) 0 S hS t ht
  have hzero : μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    simp only [measureReal_def, hnull, ENNReal.toReal_zero]
  have hsum : 0 ≤ ∑ j ∈ (Finset.univ.erase (0 : Fin 2)),
      μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 j ∈ t}) :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hprod : μ.real {Q | Q 0 1 ∈ s} * μ.real {Q | Q 0 1 ∈ t} = 0 := by
    change μ.real (pairedBlock 2 ⁻¹' S) * μ.real {Q | Q 0 1 ∈ t} = 0
    simp only [Fin.val_zero, Nat.cast_ofNat] at hid
    rw [hzero] at hid
    have h₁ := measureReal_nonneg (μ := μ) (s := pairedBlock 2 ⁻¹' S)
    have h₂ := measureReal_nonneg (μ := μ) (s := {Q | Q 0 1 ∈ t})
    nlinarith [mul_nonneg h₁ h₂]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  · right
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)

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

lemma map_snd_restrict_prod (μ : Measure (Time × Time)) (s t : Set Time)
    (ht : MeasurableSet t) :
    ((μ.restrict (s ×ˢ univ)).map Prod.snd) t = μ (s ×ˢ t) := by
  rw [Measure.map_apply measurable_snd ht,
    Measure.restrict_apply (ht.preimage measurable_snd)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

lemma map_fst_restrict_prod (μ : Measure (Time × Time)) (s t : Set Time)
    (hs : MeasurableSet s) :
    ((μ.restrict (univ ×ˢ t)).map Prod.fst) s = μ (s ×ˢ t) := by
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst)]
  congr 1
  ext x
  simp

lemma measure_prod_ext_Iic (μ ν : Measure (Time × Time)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ r t, μ (Iic r ×ˢ Iic t) = ν (Iic r ×ˢ Iic t)) : μ = ν := by
  have hrow (r : Time) : (μ.restrict (Iic r ×ˢ univ)).map Prod.snd =
      (ν.restrict (Iic r ×ˢ univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro t
    rw [map_snd_restrict_prod μ _ _ measurableSet_Iic,
      map_snd_restrict_prod ν _ _ measurableSet_Iic]
    exact h r t
  apply Measure.ext_prod
  intro s t hs ht
  have hcol : (μ.restrict (univ ×ˢ t)).map Prod.fst =
      (ν.restrict (univ ×ˢ t)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro r
    rw [map_fst_restrict_prod μ _ _ measurableSet_Iic,
      map_fst_restrict_prod ν _ _ measurableSet_Iic]
    have hr := congrArg (fun ζ : Measure Time => ζ t) (hrow r)
    simpa only [map_snd_restrict_prod μ _ _ ht, map_snd_restrict_prod ν _ _ ht] using hr
  have hc := congrArg (fun ζ : Measure Time => ζ s) hcol
  simpa only [map_fst_restrict_prod μ _ _ hs, map_fst_restrict_prod ν _ _ hs] using hc

theorem no_crossing_lower_orthant (μ : Measure (Time × Time))
    (hNo : ∀ r t : Time, μ (Iic r ×ˢ Ioi t) = 0 ∨ μ (Ioi r ×ˢ Iic t) = 0)
    (r t : Time) :
    μ (Iic r ×ˢ Iic t) = min (μ (Iic r ×ˢ univ)) (μ (univ ×ˢ Iic t)) := by
  have h₁ : Iic r ×ˢ univ ∩ univ ×ˢ Iic t = Iic r ×ˢ Iic t := by
    ext x
    simp only [mem_inter_iff, mem_prod, mem_Iic, mem_univ, and_true, true_and]
  have h₂ : (Iic r ×ˢ univ) \ (univ ×ˢ Iic t) = Iic r ×ˢ Ioi t := by ext x; simp
  have h₃ : (univ ×ˢ Iic t) \ (Iic r ×ˢ univ) = Ioi r ×ˢ Iic t := by ext x; simp [and_comm]
  have ha := measure_inter_add_sdiff (μ := μ) (t := univ ×ˢ Iic t) (Iic r ×ˢ univ)
    (MeasurableSet.univ.prod measurableSet_Iic)
  have hb := measure_inter_add_sdiff (μ := μ) (t := Iic r ×ˢ univ) (univ ×ˢ Iic t)
    (measurableSet_Iic.prod MeasurableSet.univ)
  rw [h₁, h₂] at ha
  rw [inter_comm, h₁, h₃] at hb
  rcases hNo r t with h | h
  · rw [h, add_zero] at ha
    rw [← ha, min_eq_left (measure_mono (by intro x hx; exact ⟨mem_univ _, hx.2⟩))]
  · rw [h, add_zero] at hb
    rw [← hb, min_eq_right (measure_mono (by intro x hx; exact ⟨hx.1, mem_univ _⟩))]

theorem no_crossing_quantile_coupling (μ : Measure (Time × Time)) [IsProbabilityMeasure μ]
    (hNo : ∀ r t : Time, μ (Iic r ×ˢ Ioi t) = 0 ∨ μ (Ioi r ×ˢ Iic t) = 0) :
    (volume : Measure Time).map
      (fun u => (boundedQuantile (μ.map Prod.fst) u, boundedQuantile (μ.map Prod.snd) u)) = μ := by
  apply measure_prod_ext_Iic
  intro r t
  rw [Measure.map_apply ((boundedQuantile_measurable _).prodMk (boundedQuantile_measurable _))
    (measurableSet_Iic.prod measurableSet_Iic), no_crossing_lower_orthant μ hNo]
  let a : Time := ⟨boundedCDF (μ.map Prod.fst) r,
    boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩
  let b : Time := ⟨boundedCDF (μ.map Prod.snd) t,
    boundedCDF_nonneg _ _, boundedCDF_le_one _ _⟩
  have hp : (fun u => (boundedQuantile (μ.map Prod.fst) u,
      boundedQuantile (μ.map Prod.snd) u)) ⁻¹' (Iic r ×ˢ Iic t) = Iic (min a b) := by
    ext u
    simp only [mem_preimage, mem_prod, mem_Iic, le_min_iff, boundedQuantile_le_iff]
    rfl
  rw [hp, unitInterval.volume_Iic]
  change ENNReal.ofReal (min (boundedCDF (μ.map Prod.fst) r)
    (boundedCDF (μ.map Prod.snd) t)) = _
  rw [ENNReal.ofReal_min, boundedCDF, boundedCDF, measureReal_def, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
    Measure.map_apply measurable_fst measurableSet_Iic,
    Measure.map_apply measurable_snd measurableSet_Iic]
  congr 2 <;> ext x <;> simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

end
variable {I : Type} [Fintype I]

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

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

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma countableGaussianCovariance_posSemidef {S : Type*} [MeasurableSpace S]
    (v : ℕ → S → ℝ) (L : S → ℕ) (r : ℕ) (x : Fin r → S) :
    Matrix.PosSemidef (fun i j => countableGaussianCovariance v v L (x i) (x j)) := by
  classical
  have he : ∀ᶠ n in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (x i) (x j) = countableGaussianCovariance v v L (x i) (x j) := by
    simp only [Filter.eventually_all]
    exact fun i j => gaussianPrefixCovariance_eventually_eq v v L (x i) (x j)
  obtain ⟨n,hn⟩ := he.exists
  let A : Matrix (Fin n) (Fin r) ℝ := fun a i => maskedGaussianCoefficient v L a.val (x i)
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  have hm : (fun i j => countableGaussianCovariance v v L (x i) (x j)) = Aᴴ * A := by
    funext i j
    rw [← hn i j]
    simp only [gaussianPrefixCovariance,A]
    rfl
  rw [hm]
  exact hp

lemma sourceSpinArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).1:ℝ)) := by
  exact Matrix.posSemidef_gram ℝ (fun i : Fin r => (x i).1.val)

lemma sourceTreeArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).2:ℝ)) := by
  let q : Fin (k+1) → Fin 1 → ℝ := fun l _ => (l.val:ℝ)/(k+1:ℕ)
  let V : NormalizedSpin N → EuclideanSpace ℝ (Fin 1) := fun _ => WithLp.toLp 2 (fun _ => 1)
  let v := indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V
  have hq : ∀ i, Monotone (fun l => q l i) := by
    intro i a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have he (i j : Fin r) : countableGaussianCovariance v v
      (indexedGaussianRowLength (I := Fin 1) k) (x i) (x j) = ((sourceJointArray x i j).2:ℝ) := by
    rw [profileGaussianRow_covariance q (by intro; simp [q]) hq V V]
    simp [q,V,sourceJointArray,sourceJointOverlap]
  have hp := countableGaussianCovariance_posSemidef v
    (indexedGaussianRowLength (I := Fin 1) k) r (fun i => x i)
  simpa only [he] using hp

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma infinite_iid_reindex_preserving (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i => x (e i))
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have he : (fun x : ℕ → S => fun i => x (e i)) = MeasurableEquiv.piCongrLeft (fun _ : ℕ => S) e.symm := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact ⟨(MeasurableEquiv.piCongrLeft _ e.symm).measurable,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.symm⟩

end

lemma annealedInfiniteReplica_reindex {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
    (H : A → S → ℝ) (hH : Measurable (Function.uncurry H)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun a : A×(ℕ→S) => (a.1,fun i => a.2 (e i)))
      (annealedInfiniteReplicaMeasure κ P H hH) (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun x : ℕ→S => fun i => x (e i)) := by fun_prop
  have he : (kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map (fun x i => x (e i)) =
      kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ := by
    ext a s hs
    rw [Kernel.map_apply _ hm _]
    exact congrArg (fun μ : Measure (ℕ→S) => μ s)
      (infinite_iid_reindex_preserving (gibbsProbabilityKernel κ H a) e).map_eq
  refine ⟨by fun_prop, ?_⟩
  change (P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map
    (Prod.map id (fun x i => x (e i))) = _
  rw [← Measure.compProd_map hm,he]
  rfl

lemma compactRelabel_continuous {K : Type*} [TopologicalSpace K] (e : Equiv.Perm ℕ) :
    Continuous (compactRelabel (K:=K) e) := by unfold compactRelabel; fun_prop

lemma sourceGibbsArray_exchangeable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) e
  have hm : Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) :=
    (sourceJointArray_measurable (n+1) k).comp measurable_snd
  refine ⟨(compactRelabel_continuous e).measurable, ?_⟩
  change Measure.map _ (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ∘
    (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => (a.1,fun i => a.2 (e i)))) _ = _
  rw [← Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

lemma compact_exchangeability_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    {μ : ℕ → ProbabilityMeasure (CompactArray K)} {ν : ProbabilityMeasure (CompactArray K)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (e : Equiv.Perm ℕ)
    (he : ∀ n, MeasurePreserving (compactRelabel (K:=K) e) (μ n : Measure _) (μ n : Measure _)) :
    MeasurePreserving (compactRelabel (K:=K) e) (ν : Measure _) (ν : Measure _) := by
  have hc := compactRelabel_continuous (K:=K) e
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hc
  have he' (n : ℕ) : (μ n).map hc.measurable.aemeasurable = μ n := by
    apply Subtype.ext
    exact (he n).map_eq
  simp_rw [he'] at hmap
  have hv := tendsto_nhds_unique hmap hμ
  exact ⟨hc.measurable,congrArg Subtype.val hv⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGEvents
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma compactGG_events (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock CompactJointOverlap n →ᵇ ℝ) (g : CompactJointOverlap →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock CompactJointOverlap n)) (hs : MeasurableSet s)
    (t : Set CompactJointOverlap) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock CompactJointOverlap n × CompactJointOverlap) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=CompactJointOverlap) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray CompactJointOverlap => Q i j) := by fun_prop
  rw [map_measureReal_apply (hb.prodMk (hm _ _)) (hs.prod ht),
    measureReal_nnreal_smul_apply,measureReal_add_apply] at he
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (μ : Measure _).map (fun Q => (compactBlock n Q,Q i j))).real (s×ˢt) =
      ∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}) := by
    simp only [measureReal_def,Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (by intro _ _; finiteness)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_apply (hb.prodMk (hm _ _)) (hs.prod ht)]
    rfl
  rw [hsum] at he
  have hprod : (((μ : Measure _).map (compactBlock n)).prod
      ((μ : Measure _).map (fun Q : CompactArray CompactJointOverlap => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

lemma compactPairReal_measurable : Measurable compactPairReal := by unfold compactPairReal; fun_prop
lemma compactArrayReal_measurable : Measurable compactArrayReal := by
  unfold compactArrayReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))
lemma compactBlockReal_measurable (n : ℕ) : Measurable (compactBlockReal (n:=n)) := by
  unfold compactBlockReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))

instance compactRealLaw_probability (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactRealLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff compactArrayReal_measurable.aemeasurable).2 inferInstance

lemma compactRealLaw_gg (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0) :
    JointGhirlandaGuerra (compactRealLaw μ) := by
  intro n hn i s hs t ht
  have hb : Measurable (pairedBlock n) := by unfold pairedBlock; fun_prop
  have hedge (a b : ℕ) : Measurable (fun Q : PairedOverlapArray => Q a b) := by fun_prop
  have hmap (u : Set PairedOverlapArray) (hu : MeasurableSet u) :
      (compactRealLaw μ).real u=(μ : Measure _).real (compactArrayReal ⁻¹' u) :=
    map_measureReal_apply compactArrayReal_measurable hu
  rw [hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i n∈t}) ((hs.preimage hb).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hb), hmap {Q | Q 0 1∈t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i j∈t})
    ((hs.preimage hb).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact compactGG_events μ n (by omega) i (hGG n i)
    (compactBlockReal ⁻¹' s) (hs.preimage (compactBlockReal_measurable n))
    (compactPairReal ⁻¹' t) (ht.preimage compactPairReal_measurable)

lemma compactRealLaw_exchangeable (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _)) :
    PairedSwapInvariant (compactRealLaw μ) := by
  intro i j
  have hp : Measurable (pairedRelabel (Equiv.swap i j)) := by unfold pairedRelabel; fun_prop
  refine ⟨hp,?_⟩
  unfold compactRealLaw
  rw [Measure.map_map hp compactArrayReal_measurable]
  change Measure.map (compactArrayReal ∘ compactRelabel (Equiv.swap i j)) _ = _
  rw [← Measure.map_map compactArrayReal_measurable (hEx _).measurable,(hEx _).map_eq]

lemma compactRealLaw_gram (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q))) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.snd Q))) := by
  constructor
  · exact ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst)) |>.mpr hR
  · exact ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_snd)) |>.mpr hT

lemma compactRealLaw_diagonals (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).1≤1) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).2≤1) := by
  constructor
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).1.property.2)
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).2.property.2)

lemma compact_gg_no_crossing (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val) := by
  obtain ⟨hgr,hgt⟩ := compactRealLaw_gram μ hR hT
  obtain ⟨hdr,hdt⟩ := compactRealLaw_diagonals μ
  have hh := joint_gg_no_crossing (compactRealLaw μ) (compactRealLaw_exchangeable μ hEx)
    (compactRealLaw_gg μ hGG) hgr hgt hdr hdt
  exact (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mp hh

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

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

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

lemma quantileTrial_eq_integral (q : Time → Time) (hq : Measurable q) (t : Time) :
    quantileTrial q t=∫ u, (if q u ≤ t then (1:ℝ) else 0) ∂timeLaw := by
  change timeLaw.real {u | q u ≤ t}=∫ u, {u | q u ≤ t}.indicator (fun _ => (1:ℝ)) u ∂timeLaw
  rw [integral_indicator (measurableSet_le hq measurable_const),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedTrialLaw
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

lemma weightedTrialLaw_probability {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) : IsProbabilityMeasure (weightedTrialLaw w q) := by
  constructor
  simp only [weightedTrialLaw,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem
    (mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one]

lemma weightedTrialLaw_integral {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (g : Time→ℝ) :
    (∫ x, g x ∂weightedTrialLaw w q)=∑ i, w i*g (q i) := by
  unfold weightedTrialLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma weightedTrialLaw_Iic {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (t : Time) :
    (weightedTrialLaw w q).real (Iic t)=∑ i, if q i≤t then w i else 0 := by
  simp only [weightedTrialLaw,Measure.real,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic,smul_eq_mul,Set.indicator_apply,mem_Iic,Pi.one_apply]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [ENNReal.toReal_ofReal (hw i)]
  · intro i _
    split_ifs <;> simp

lemma quantileTrial_weightedTrialLaw {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    quantileTrial (boundedQuantile (weightedTrialLaw w q))=weightedStepTrial w q hw hw1 := by
  have := weightedTrialLaw_probability w q hw hw1
  apply Trial.ext_fun
  intro t
  change (timeLaw {u | boundedQuantile (weightedTrialLaw w q) u≤t}).toReal=_
  have he := congrArg (fun μ : Measure Time => μ (Iic t)) (boundedQuantile_law (weightedTrialLaw w q))
  rw [Measure.map_apply (boundedQuantile_measurable _) measurableSet_Iic] at he
  change (timeLaw {u | boundedQuantile (weightedTrialLaw w q) u≤t})=_ at he
  rw [he]
  exact weightedTrialLaw_Iic w q hw t

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlledPrefix
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

lemma heatLog_control_step_error (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      ∀ (s : ℝ≥0), s ≤ 1 → ∀ (X Z A : Ω → ℝ), AEMeasurable X P →
        HasLaw Z (gaussianReal 0 s) P → IndepFun X Z P → AEMeasurable A P →
        (∀ ω, |A ω| ≤ (L : ℝ)*s) →
        |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, heatLog s d g.f (X ω) ∂P) -
          (∫ ω, g.d1 (X ω)*A ω ∂P) + (d : ℝ)*(s : ℝ)/2 * (∫ ω, (g.d1 (X ω))^2 ∂P)| ≤
          (C : ℝ)*(s : ℝ)*Real.sqrt s := by
  obtain ⟨C,hC⟩ := heatLog_generator_uniform d C₀ C₁ C₂ C₃
  let M₁ := ∫ z : ℝ, |z| ∂gaussianReal 0 1
  let M₃ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun z => abs_nonneg z)
  have hM₃ : 0 ≤ M₃ := integral_nonneg (fun z => by positivity)
  let K := (C₂ : ℝ)*((L : ℝ)*M₁+(L : ℝ)^2/2) + (C₃ : ℝ)/6*M₃
  have hK : 0 ≤ K := by positivity
  refine ⟨⟨K+C, by positivity⟩, ?_⟩
  intro Ω _ P _ g h₀ h₁ h₂ h₃ s hs X Z A hX hZ hI hA hAK
  have hG := gaussian_drift_taylor_mean_bound g.f g.contDiff C₁ C₃ C₂ (L*s)
    (fun y => by rw [g.deriv_eq]; exact (g.d1.norm_coe_le_norm y).trans h₁)
    (fun y => by rw [g.deriv2_eq]; exact (g.d2.norm_coe_le_norm y).trans h₂)
    (fun y => by rw [g.deriv3_eq]; exact (g.d3.norm_coe_le_norm y).trans h₃)
    hX hZ hI hA (by simpa only [NNReal.coe_mul] using hAK)
  rw [g.deriv_eq, g.deriv2_eq] at hG
  have hs0 := s.coe_nonneg
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := Real.sqrt_le_one.mpr hs
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith [Real.sq_sqrt hs0]
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ)*Real.sqrt s := by nlinarith [Real.sq_sqrt hs0]
  have hG' : |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P)| ≤
      K*(s : ℝ)*Real.sqrt s := by
    refine hG.trans ?_
    simp only [NNReal.coe_mul, hrcube]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsr hs0)
      (show 0 ≤ (C₂ : ℝ)*(L : ℝ)^2/2 by positivity)
    dsimp [K,M₁,M₃] at *
    nlinarith only [ht]
  have hiF := boundedContinuousFunction_integrable_comp g.f hX
  have hiH := boundedContinuousFunction_integrable_comp (heatLogBCF s d g.f) hX
  change Integrable (fun ω => heatLog s d g.f (X ω)) P at hiH
  have hi₂ := boundedContinuousFunction_integrable_comp g.d2 hX
  have hi₁₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hX
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₁₂
  let R := fun ω => heatLog s d g.f (X ω) - g.f (X ω) -
    (s : ℝ)/2*(g.d2 (X ω)+(d : ℝ)*(g.d1 (X ω))^2)
  have hiR : Integrable R P := (hiH.sub hiF).sub ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
  have hR : |∫ ω, R ω ∂P| ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (f := R) (μ := P) (Filter.Eventually.of_forall fun ω =>
        show ‖R ω‖ ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s by
          simpa only [Real.norm_eq_abs, R] using hC g h₀ h₁ h₂ h₃ s hs (X ω))
  have hRe : (∫ ω, R ω ∂P) = (∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)) := by
    have he := integral_sub (hiH.sub hiF) ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
    simp only [Pi.sub_apply, Pi.add_apply] at he
    dsimp only [R]
    rw [he, integral_sub hiH hiF, integral_const_mul, integral_add hi₂ (hi₁₂.const_mul d), integral_const_mul]
  rw [hRe] at hR
  have hh := abs_sub
    ((∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P))
    ((∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)))
  have hh' := hh.trans (add_le_add hG' hR)
  convert! hh' using 1
  · congr 1; ring
  · change (K+(C : ℝ))*(s : ℝ)*Real.sqrt s = K*(s : ℝ)*Real.sqrt s + (C : ℝ)*(s : ℝ)*Real.sqrt s
    ring

lemma usualBrownianSigma_mono (P : Measure BrownianPath) {s t : Time} (hst : s ≤ t) :
    usualBrownianSigma P s ≤ usualBrownianSigma P t := by
  apply le_iInf
  intro r
  exact iInf_le_of_le (⟨r.val, lt_of_le_of_lt hst r.property⟩ : {r : ℝ≥0 // (s : ℝ) < r}) le_rfl

lemma brownianEval_usual_measurable (P : Measure BrownianPath) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (brownianEval ⟨t.val,t.property.1⟩) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro r
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨⟨t.val,t.property.1⟩, r.property.le⟩ : {s : ℝ≥0 // s ≤ r.val}) le_rfl

lemma progressive_prefix_integral_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
  let : MeasurableSpace BrownianPath := usualBrownianSigma P t
  have hm : Measurable (fun p : Set.Iic t × BrownianPath => a p.1.val * v p.1.val p.2) :=
    (ha.comp (measurable_subtype_coe.comp measurable_fst)).mul (hv t)
  have hi := hm.stronglyMeasurable.integral_prod_left (f := fun r ω => a r.val * v r.val ω) (μ := Measure.comap Subtype.val timeLaw)
  have he : (fun ω => ∫ r : Set.Iic t, a r.val * v r.val ω ∂Measure.comap Subtype.val timeLaw) =
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
    funext ω
    exact integral_subtype_comap (μ := timeLaw) (s := Set.Iic t) measurableSet_Iic (fun r => a r * v r ω)
  rw [he] at hi
  exact hi.measurable

lemma progressive_interval_integral_aemeasurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (s t : Time) :
    AEMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P := by
  have hm := (ha.comp measurable_fst).mul (progressive_joint_complete P hv)
  have hi := hm.stronglyMeasurable.integral_prod_left (β := NullMeasurableSpace BrownianPath P)
    (f := fun r ω => a r * v r ω) (μ := timeLaw.restrict (Set.Ioc s t))
  exact (show NullMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P from hi.measurable).aemeasurable

lemma controlledPrefix_usual_measurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) (controlledPrefix m v t) :=
  (brownianEval_usual_measurable P t).add (progressive_prefix_integral_measurable P hv m m.measurable t)

lemma timeSpan_coe {s t : Time} (hst : s ≤ t) :
    (timeSpan s t : ℝ) = (t : ℝ)-(s : ℝ) := Real.coe_toNNReal _ (sub_nonneg.mpr hst)

lemma timeSpan_le_one (s t : Time) : timeSpan s t ≤ 1 := by
  apply Real.toNNReal_le_one.mpr
  linarith [t.property.2,s.property.1]

lemma timeLaw_real_Ioc {s t : Time} (hst : s ≤ t) :
    timeLaw.real (Set.Ioc s t) = (t : ℝ)-(s : ℝ) := by
  simp only [timeLaw_eq_volume, Measure.real, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

lemma timeLaw_integral_const_Ioc {s t : Time} (hst : s ≤ t) (a : ℝ) :
    (∫ _r in Set.Ioc s t, a ∂timeLaw) = ((t : ℝ)-(s : ℝ))*a := by
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, ← Measure.real,
    timeLaw_real_Ioc hst, smul_eq_mul]

lemma bounded_control_integrable (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    Integrable (fun r => m r * v r ω^2) timeLaw ∧ Integrable (fun r => m r * v r ω) timeLaw :=
  weightedTime_integrable m (progressive_time_measurable P hv ω)
    ((pathControlCost_le_bound m L hL ω).trans_lt (by finiteness))

lemma controlledPrefix_increment (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    controlledPrefix m v t ω = controlledPrefix m v s ω +
      (brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω) +
      ∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw := by
  have hi := (bounded_control_integrable P m L hv hL ω).2
  have he := setIntegral_union (s := Set.Iic s) (t := Set.Ioc s t)
    (Set.Iic_disjoint_Ioc (a := s) (c := t) le_rfl) measurableSet_Ioc
    hi.integrableOn hi.integrableOn
  rw [Set.Iic_union_Ioc_eq_Iic hst] at he
  unfold controlledPrefix
  rw [he]
  ring

lemma bounded_interval_drift (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    |∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw| ≤ (L : ℝ) * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm (L : ℝ)]
  calc
    _ ≤ ∫ r in Set.Ioc s t, |m r*v r ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ) ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).2.integrableOn.abs (integrable_const _)
      intro r
      change |m r * v r ω| ≤ (L : ℝ)
      rw [abs_mul, abs_of_nonneg (m.nonneg r)]
      exact (mul_le_mul_of_nonneg_left (hL r ω) (m.nonneg r)).trans
        (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst L

lemma intervalControlCost_nonneg (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) :
    0 ≤ intervalControlCost m v s t ω := integral_nonneg (fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))

lemma intervalControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time) :
    AEMeasurable (intervalControlCost m v s t) P :=
  progressive_interval_integral_aemeasurable P (fun r => (hv r).pow_const 2) m m.measurable s t

lemma intervalControlCost_le_bound (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    intervalControlCost m v s t ω ≤ (L : ℝ)^2 * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm ((L : ℝ)^2)]
  calc
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ)^2 ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).1.integrableOn (integrable_const _)
      intro r
      have hh : (v r ω)^2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr (hL r ω)
      exact (mul_le_mul_of_nonneg_left hh (m.nonneg r)).trans (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst _

lemma intervalControlCost_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ t ω, |v t ω| ≤ L) {s t : Time} (hst : s ≤ t) :
    Integrable (intervalControlCost m v s t) P :=
  bounded_real_integrable (intervalControlCost_aemeasurable P m hv s t) ((L : ℝ)^2*timeSpan s t)
    (Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (intervalControlCost_nonneg m v s t ω)]
      exact intervalControlCost_le_bound P m L hv hL hst ω)

lemma interval_square_completion (P : Measure BrownianPath) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ))
    (a : ℝ) (ω : BrownianPath) :
    2*a*(∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw) -
      (d : ℝ)*(timeSpan s t : ℝ)*a^2 ≤ intervalControlCost m v s t ω := by
  have hi := bounded_control_integrable P m L hv hL ω
  have him : Integrable (fun r => m r) timeLaw := by
    apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m.nonneg r)]; exact m.le_one r
  have hmono := setIntegral_mono_on (s := Set.Ioc s t) ((hi.2.const_mul (2*a)).sub (him.const_mul (a^2))).integrableOn
    hi.1.integrableOn measurableSet_Ioc (fun r _ => by
      change 2*a*(m r*v r ω) - a^2*m r ≤ m r*(v r ω)^2
      nlinarith [mul_nonneg (m.nonneg r) (sq_nonneg (v r ω-a))])
  have he : (∫ r in Set.Ioc s t, m r ∂timeLaw) = (d : ℝ)*timeSpan s t := by
    rw [setIntegral_congr_fun measurableSet_Ioc hm, timeLaw_integral_const_Ioc hst, timeSpan_coe hst, mul_comm]
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hi.2.const_mul (2*a)).integrableOn (him.const_mul (a^2)).integrableOn,
    integral_const_mul, integral_const_mul, he] at hmono
  convert! hmono using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma brownian_increment_timeSpan (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {s t : Time} (hst : s ≤ t) :
    HasLaw (fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω)
      (gaussianReal 0 (timeSpan s t)) P := by
  have he : timeSpan s t = nndist (t : ℝ) (s : ℝ) := by
    apply NNReal.coe_injective
    rw [timeSpan_coe hst, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  rw [he]
  exact (hB.toIsPreBrownianReal.hasLaw_sub ⟨t.val,t.property.1⟩ ⟨s.val,s.property.1⟩).congr
    (Filter.Eventually.of_forall fun ω => rfl)

lemma brownian_control_cell_upper (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) ≤
        (∫ ω, intervalControlCost m v s t ω ∂P)/2 +
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := by
    intro ω
    exact (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hi₁ := boundedContinuousFunction_integrable_comp g.d1 hXm
  have hi₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hXm
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₂
  have hiA := bounded_real_integrable hAm ((L : ℝ)*timeSpan s t) (Filter.Eventually.of_forall hAb)
  have hiJ : Integrable (fun ω => g.d1 (X ω)*A ω) P :=
    hiA.bdd_mul ((g.d1.continuous.measurable.comp_aemeasurable hXm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => g.d1.norm_coe_le_norm (X ω))
  have hq := integral_mono ((hiJ.const_mul 2).sub (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))))
    (intervalControlCost_integrable P m L hv hL hst.le)
    (fun ω => by
      change 2*(g.d1 (X ω)*A ω) - (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 ≤ _
      nlinarith only [interval_square_completion P m L d hv hL hst.le hm (g.d1 (X ω)) ω])
  simp only [Pi.sub_apply] at hq
  rw [integral_sub (hiJ.const_mul 2) (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))),
    integral_const_mul, integral_const_mul] at hq
  exact le_trans (by linarith only [(abs_le.mp he).2,hq]) le_rfl

lemma antitoneOn_of_superlinear_increment (F : Time → ℝ) (C : ℝ)
    {a b : Time} (hab : a ≤ b)
    (h : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt ((t : ℝ)-(s : ℝ))) : F b ≤ F a := by
  have hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt (((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro s hs t ht hst
      have hstreal : (s : ℝ) < (t : ℝ) := hst
      let u : Time := ⟨((s : ℝ)+(t : ℝ))/2, by
        constructor <;> linarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
      have hsu : s < u := by change (s : ℝ) < ((s : ℝ)+(t : ℝ))/2; linarith only [hstreal]
      have hut : u < t := by change ((s : ℝ)+(t : ℝ))/2 < (t : ℝ); linarith only [hstreal]
      have hu : u ∈ Set.Icc a b := ⟨hs.1.trans hsu.le,hut.le.trans ht.2⟩
      have h₁ := ih s hs u hu hsu
      have h₂ := ih u hu t ht hut
      have e₁ : (u : ℝ)-(s : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      have e₂ : (t : ℝ)-(u : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      rw [e₁] at h₁
      rw [e₂] at h₂
      have e₃ : ((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^(n+1) = (((t : ℝ)-(s : ℝ))/2)*(1/2 : ℝ)^n := by rw [pow_succ]; ring
      rw [e₃]
      linarith only [h₁,h₂]
  rcases hab.eq_or_lt with heq | hlt
  · simp [heq]
  have hlim : Tendsto (fun n : ℕ => C*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))*(1/2 : ℝ)^n)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using (hp.const_mul ((b : ℝ)-(a : ℝ))).sqrt.const_mul (C*((b : ℝ)-(a : ℝ)))
  have he := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbnd n a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hlt)
  linarith only [he]

lemma timeSpan_add {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    timeSpan a b + timeSpan b c = timeSpan a c := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add,timeSpan_coe hab,timeSpan_coe hbc,timeSpan_coe (hab.trans hbc)]
  ring

lemma intervalControlCost_add (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) (ω : BrownianPath) :
    intervalControlCost m v a c ω = intervalControlCost m v a b ω + intervalControlCost m v b c ω := by
  have hi := (bounded_control_integrable P m L hv hL ω).1
  have he := setIntegral_union (s := Set.Ioc a b) (t := Set.Ioc b c)
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi.integrableOn hi.integrableOn
  rwa [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at he

lemma expected_intervalControlCost_add (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ r ω, |v r ω| ≤ L) {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, intervalControlCost m v a c ω ∂P) =
      (∫ ω, intervalControlCost m v a b ω ∂P) + (∫ ω, intervalControlCost m v b c ω ∂P) := by
  simp only [intervalControlCost_add P m L hv hL hab hbc]
  exact integral_add (intervalControlCost_integrable P m L hv hL hab)
    (intervalControlCost_integrable P m L hv hL hbc)

lemma brownian_control_interval_upper (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b : Time} (hab : a ≤ b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) (g : Jet3) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) ≤
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  obtain ⟨C,hC⟩ := brownian_control_cell_upper d L C₀ C₁ C₂ C₃
  let F : Time → ℝ := fun t =>
    (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
      (∫ ω, intervalControlCost m v a t ω ∂P)/2
  have hF := antitoneOn_of_superlinear_increment F (C : ℝ) hab (by
    intro s hs t ht hst
    have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
    obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
    have hh := hC P hB m v hv hL s t hst hmst (g.heatLog (timeSpan t b) d) h₀ h₁ h₂ h₃
    rw [g.heatLog_f] at hh
    simp only [heatLogBCF_coe, heatLog_semigroup, timeSpan_add hst.le ht.2] at hh
    have hcost := expected_intervalControlCost_add P m L hv hL hs.1 hst.le
    rw [timeSpan_coe hst.le] at hh
    dsimp [F]
    linarith only [hh,hcost])
  have he₁ : timeSpan b b = 0 := by simp [timeSpan]
  have he₂ : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  dsimp [F] at hF
  simp only [he₁,heatLog_zero,he₂,integral_zero,zero_div,sub_zero] at hF
  linarith only [hF]

lemma progressive_patchControl (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time)
    {a : BrownianPath → ℝ} (ha : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) a) :
    Progressive P (patchControl v s t a) := by
  intro T
  by_cases hs : s ≤ T
  · have haT := ha.mono (usualBrownianSigma_mono P hs) le_rfl
    apply Measurable.ite _ (haT.comp measurable_snd) (hv T)
    exact (measurableSet_Ioc : MeasurableSet (Set.Ioc s t)).preimage
      (measurable_subtype_coe.comp measurable_fst)
  · have he : (fun p : Set.Iic T × BrownianPath => patchControl v s t a p.1.val p.2) =
        (fun p : Set.Iic T × BrownianPath => v p.1.val p.2) := by
      funext p
      apply ite_eq_right
      intro h
      exact hs (h.1.le.trans p.1.property)
    rw [he]
    exact hv T

lemma patchControl_bound {v : Time → BrownianPath → ℝ} {L : ℝ≥0}
    (hv : ∀ r ω, |v r ω| ≤ L) (s t : Time) {a : BrownianPath → ℝ}
    (ha : ∀ ω, |a ω| ≤ L) : ∀ r ω, |patchControl v s t a r ω| ≤ L := by
  intro r ω
  simp only [patchControl]
  split <;> first | exact ha ω | exact hv r ω

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
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

lemma patchControl_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    controlledPrefix m (patchControl v s t a) r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma patchControl_cost_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) (q : Time) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    intervalControlCost m (patchControl v s t a) q r ω = intervalControlCost m v q r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.2.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma brownian_control_feedback_cell (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∀ r ∈ Set.Ioc s t, ∀ ω, v r ω = g.d1 (controlledPrefix m v s ω)) →
      |(∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) -
        (∫ ω, intervalControlCost m v s t ω ∂P)/2| ≤
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃ hV
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := fun ω =>
    (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hA : ∀ ω, A ω = (d : ℝ)*(timeSpan s t : ℝ)*g.d1 (X ω) := by
    intro ω
    dsimp only [A]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hQ : ∀ ω, intervalControlCost m v s t ω =
      (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 := by
    intro ω
    rw [intervalControlCost,setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hJ : (∫ ω, g.d1 (X ω)*A ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hA]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by ring
  have hQi : (∫ ω, intervalControlCost m v s t ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hQ,integral_const_mul]
  rw [hJ] at he
  rw [hQi]
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma brownian_control_patch_gain (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ (v : Time → BrownianPath → ℝ), Progressive P v →
      (∀ r ω, |v r ω| ≤ L) → ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc s t, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g s - (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) ≤
          backwardScore P m w a b d g t := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  let L := max L₀ C₁
  obtain ⟨C,hC⟩ := brownian_control_feedback_cell d L C₀ C₁ C₂ C₃
  refine ⟨L,C,le_max_left _ _,?_⟩
  intro v hv hL s hs t ht hst
  let j := g.heatLog (timeSpan t b) d
  let A := fun ω => j.d1 (controlledPrefix m v s ω)
  have hAm : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) A :=
    j.d1.continuous.measurable.comp (controlledPrefix_usual_measurable P m hv s)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
  have hAL : ∀ ω, |A ω| ≤ L := fun ω =>
    ((j.d1.norm_coe_le_norm _).trans h₁).trans (show (C₁ : ℝ) ≤ L from le_max_right _ _)
  let w := patchControl v s t A
  have hw : Progressive P w := progressive_patchControl P hv s t hAm
  have hwL : ∀ r ω, |w r ω| ≤ L := patchControl_bound hL s t hAL
  have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
  have hXe : ∀ ω, controlledPrefix m w s ω = controlledPrefix m v s ω :=
    patchControl_prefix m v s t A le_rfl
  have hQe : ∀ ω, intervalControlCost m w a s ω = intervalControlCost m v a s ω :=
    patchControl_cost_prefix m v s t A a le_rfl
  have hfeedback : ∀ r ∈ Set.Ioc s t, ∀ ω, w r ω = j.d1 (controlledPrefix m w s ω) := by
    intro r hr ω
    rw [hXe]
    exact ite_eq_left hr
  have hh := hC P hB m w hw hwL s t hst hmst j h₀ h₁ h₂ h₃ hfeedback
  change |(∫ ω, (g.heatLog (timeSpan t b) d).f (controlledPrefix m w t ω) ∂P) - _ - _| ≤ _ at hh
  rw [g.heatLog_f] at hh
  simp only [heatLogBCF_coe,heatLog_semigroup,timeSpan_add hst.le ht.2,hXe] at hh
  have hcost := expected_intervalControlCost_add P m L hw hwL hs.1 hst.le
  simp only [hQe] at hcost
  refine ⟨w,hw,hwL,?_,?_⟩
  · intro r hr ω
    exact ite_eq_right hr
  · dsimp [backwardScore]
    linarith only [(abs_le.mp hh).1,hcost]

lemma timeMesh_coe (a b : Time) (n k : ℕ) (hk : k ≤ n+1) :
    (timeMesh a b n k : ℝ) = (a : ℝ)+((b : ℝ)-(a : ℝ))*((k : ℝ)/(n+1)) := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hh : (k : ℝ)/(n+1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hp).mpr
      exact_mod_cast hk
  simp only [timeMesh, Set.projIcc_of_mem zero_le_one hh, Set.Icc.coe_convexComb]
  ring

lemma timeMesh_zero (a b : Time) (n : ℕ) : timeMesh a b n 0 = a := by
  apply Subtype.ext
  rw [timeMesh_coe a b n 0 (Nat.zero_le _)]
  simp

lemma timeMesh_last (a b : Time) (n : ℕ) : timeMesh a b n (n+1) = b := by
  apply Subtype.ext
  rw [timeMesh_coe a b n (n+1) le_rfl]
  push_cast
  rw [div_self (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

lemma timeMesh_between {a b : Time} (hab : a ≤ b) (n k : ℕ) (hk : k ≤ n+1) :
    timeMesh a b n k ∈ Set.Icc a b := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hq : 0 ≤ (k : ℝ)/(n+1) := by positivity
  have hr : (k : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr (by exact_mod_cast hk)
  have habr : (a : ℝ) ≤ (b : ℝ) := hab
  constructor <;> change _ ≤ (show ℝ from ↑_)
  · rw [timeMesh_coe a b n k hk]
    nlinarith
  · rw [timeMesh_coe a b n k hk]
    nlinarith

lemma timeMesh_step {a b : Time} (hab : a < b) (n k : ℕ) (hk : k < n+1) :
    timeMesh a b n k < timeMesh a b n (k+1) := by
  change (timeMesh a b n k : ℝ) < (timeMesh a b n (k+1) : ℝ)
  rw [timeMesh_coe a b n k hk.le, timeMesh_coe a b n (k+1) hk]
  have hh : (a : ℝ) < (b : ℝ) := hab
  have hp : (0 : ℝ) < n+1 := by positivity
  apply add_lt_add_of_le_of_lt le_rfl
  apply mul_lt_mul_of_pos_left _ (sub_pos.mpr hh)
  apply div_lt_div_of_pos_right _ hp
  exact_mod_cast Nat.lt_succ_self k

lemma timeMesh_step_size (a b : Time) (n k : ℕ) (hk : k < n+1) :
    (timeMesh a b n (k+1) : ℝ) - (timeMesh a b n k : ℝ) = ((b : ℝ)-(a : ℝ))/(n+1) := by
  rw [timeMesh_coe a b n k hk.le,timeMesh_coe a b n (k+1) hk]
  push_cast
  ring

lemma brownian_control_interval_lower_mesh (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ n : ℕ,
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) -
          (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,hLL,hgain⟩ := brownian_control_patch_gain P hB m d L₀ g hm
  refine ⟨L,C,hLL,?_⟩
  intro n
  let τ := timeMesh a b n
  let δ : ℝ := ((b : ℝ)-(a : ℝ))/(n+1)
  let E : ℝ := (C : ℝ)*δ*Real.sqrt δ
  have hind : ∀ k : ℕ, k ≤ n+1 →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g a - (k : ℝ)*E ≤ backwardScore P m w a b d g (τ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨v,hv,fun r ω => (hvL r ω).trans (show (L₀ : ℝ) ≤ L from hLL),?_,?_⟩
      · intro _ _ _; rfl
      · simp only [τ,timeMesh_zero,Nat.cast_zero,zero_mul,sub_zero,le_refl]
    | succ k ih =>
      intro hk
      obtain ⟨u,hu,huL,huout,huScore⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hk' : k < n+1 := hk
      have hs := timeMesh_between hab.le n k hk'.le
      have ht := timeMesh_between hab.le n (k+1) hk
      have hst := timeMesh_step hab n k hk'
      obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hgain u hu huL (τ k) hs (τ (k+1)) ht hst
      have heδ : (timeSpan (τ k) (τ (k+1)) : ℝ) = δ := by
        rw [timeSpan_coe hst.le]
        exact timeMesh_step_size a b n k hk'
      rw [heδ] at hwScore
      refine ⟨w,hw,hwL,?_,?_⟩
      · intro r hr ω
        have hr' : r ∉ Set.Ioc (τ k) (τ (k+1)) := fun hh =>
          hr ⟨hs.1.trans_lt hh.1,hh.2.trans ht.2⟩
        rw [hwout r hr' ω]
        exact huout r hr ω
      · change backwardScore P m u a b d g (τ k) - E ≤ _ at hwScore
        rw [Nat.cast_succ]
        linarith only [huScore,hwScore]
  obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hind (n+1) le_rfl
  have he : ((n+1 : ℕ) : ℝ)*E =
      (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) := by
    dsimp [E,δ]
    push_cast
    field_simp
  have hz : timeSpan b b = 0 := by simp [timeSpan]
  have hq : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  simp only [τ,timeMesh_last,he,backwardScore,hz,heatLog_zero,hq,integral_zero,zero_div,sub_zero] at hwScore
  exact ⟨w,hw,hwL,hwout,hwScore⟩

lemma brownian_control_interval_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,_,hmesh⟩ := brownian_control_interval_lower_mesh P hB m d L₀ g hab hm v hv hvL
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ((b : ℝ)-(a : ℝ))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he : Tendsto (fun n : ℕ => (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)))
      atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul ((C : ℝ)*((b : ℝ)-(a : ℝ)))
  obtain ⟨n,hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
  obtain ⟨w,hw,hwL,hwout,hwval⟩ := hmesh n
  exact ⟨L,w,hw,hwL,hwout,by linarith⟩

lemma controls_equal_cost_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r s : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    intervalControlCost m w s r ω = intervalControlCost m v s r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.2.trans hr) hh.1) ω]

lemma HeatChain.upper {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 ≤
        (∫ ω, h.f (controlledPrefix m v a ω) ∂P) := by
  induction H with
  | nil a => simp [intervalControlCost]
  | @cons a t b h d hat htb hm tail ih =>
    have hi := brownian_control_interval_upper P hB m L d hv hL hat.le hm h
    have hc := expected_intervalControlCost_add P m L hv hL hat.le htb
    rw [Jet3.heatLog_f]
    simp only [heatLogBCF_coe]
    linarith only [ih,hi,hc]

lemma HeatChain.lower {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ K) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, h.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  induction H generalizing v L ε with
  | nil a =>
    refine ⟨L,v,hv,hL,fun _ _ _ => rfl,?_⟩
    simp only [intervalControlCost,Set.Ioc_self,Measure.restrict_empty,integral_zero_measure,
      integral_zero,zero_div,sub_zero]
    linarith
  | @cons a t b h d hat htb hm tail ih =>
    obtain ⟨K,u,hu,huK,huout,huval⟩ :=
      brownian_control_interval_lower P hB m d L h hat hm v hv hL (by positivity : 0 < ε/2)
    obtain ⟨K',w,hw,hwK,hwout,hwval⟩ := ih K u hu huK (by positivity : 0 < ε/2)
    have hc := expected_intervalControlCost_add P m K' hw hwK hat.le htb
    have he : ∀ ω, intervalControlCost m w a t ω = intervalControlCost m u a t ω :=
      controls_equal_cost_prefix hwout le_rfl
    simp only [he] at hc
    refine ⟨K',w,hw,hwK,?_,?_⟩
    · intro r hr ω
      rw [hwout r (fun hh => hr ⟨hat.trans hh.1,hh.2⟩) ω]
      exact huout r (fun hh => hr ⟨hh.1,hh.2.trans htb⟩) ω
    · rw [Jet3.heatLog_f]
      simp only [heatLogBCF_coe]
      linarith only [huval,hwval,hc]

lemma controlledPrefix_one (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    controlledPrefix m v 1 ω = brownianEval 1 ω + controlDrift m v ω := by
  simp only [controlledPrefix,controlDrift,show Set.Iic (1 : Time) = Set.univ from Set.Iic_top,
    Measure.restrict_univ]
  rfl

lemma controlledPrefix_zero (P : Measure BrownianPath) (hB : IsBrownianReal brownianEval P)
    (m : Trial) (v : Time → BrownianPath → ℝ) : controlledPrefix m v 0 =ᵐ[P] fun _ => 0 := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp only [controlledPrefix,show Set.Iic (0 : Time) = {0} from Set.Iic_bot,
    Measure.restrict_singleton,measure_singleton,zero_smul,integral_zero_measure,add_zero]
  exact hω

lemma intervalControlCost_full (m : Trial) (v : Time → BrownianPath → ℝ)
    (ω : BrownianPath) (hm : Measurable (v · ω)) :
    intervalControlCost m v 0 1 ω = (pathControlCost m v ω).toReal := by
  unfold intervalControlCost
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := timeLaw)), show Set.Icc (0 : Time) 1 = Set.univ from Set.Icc_bot_top,
    Measure.restrict_univ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))
    ((m.measurable.mul (hm.pow_const 2)).aestronglyMeasurable)

lemma expected_intervalControlCost_full (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, intervalControlCost m v 0 1 ω ∂P) = (controlCost P m v).toReal := by
  simp only [intervalControlCost_full m v _ (progressive_time_measurable P hv _)]
  exact integral_pathControlCost P m hv hc

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

lemma HeatChain.controlValue_eq {m : Trial} {g h : Jet3}
    (H : HeatChain m g 0 1 h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : controlValue P g.f m = h.f 0 := by
  apply le_antisymm
  · apply controlValue_le_of_bounded_controls P g.f m ‖g.d1‖₊ g.lipschitz
    intro v hv hc hL
    have hh := H.upper P hB ‖g.d1‖₊ hv hL
    have he : (∫ ω, h.f (controlledPrefix m v 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m v] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hv hc] at hh
    simp only [controlledPrefix_one] at hh
    exact hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨K,w,hw,hwK,_,hwval⟩ := H.lower P hB 0 (fun _ _ => 0) (progressive_zero P)
      (by simp) hε
    have hc : controlCost P m w < ∞ := (controlCost_le_bound P m K hwK).trans_lt (by finiteness)
    have he : (∫ ω, h.f (controlledPrefix m (fun _ _ => 0) 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m (fun _ _ => 0)] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hw hc] at hwval
    simp only [controlledPrefix_one] at hwval
    have hsup : controlPayoff P g.f m w ≤ controlValue P g.f m :=
      le_csSup (controlPayoffs_bddAbove P g.f m) ⟨w,hw,hc,rfl⟩
    change h.f 0 - ε ≤ controlPayoff P g.f m w at hwval
    linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_QuantileControlContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cdfIndicator_integrable (a : Time) : Integrable (cdfIndicator a) timeLaw := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    ((measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable)
  exact ae_of_all _ fun _ => by split_ifs <;> norm_num

lemma cdfIndicator_integral (a : Time) : (∫ t, cdfIndicator a t ∂timeLaw)=1-(a:ℝ) := by
  have he := timeTail_atom_integral a 0 1
  rw [show Ici (0:Time)=univ from Ici_bot,Measure.restrict_univ] at he
  change (∫ s, (if a ≤ s then (1:ℝ) else 0) ∂timeLaw)=1*(1-max (a:ℝ) 0) at he
  simpa only [cdfIndicator,one_mul,max_eq_left a.2.1] using he

lemma cdfIndicator_order {a b : Time} (hab : a≤b) (t : Time) : cdfIndicator b t ≤ cdfIndicator a t := by
  unfold cdfIndicator
  by_cases hb : b≤t
  · rw [ite_eq_left hb,ite_eq_left (hab.trans hb)]
  · rw [ite_eq_right hb]
    split_ifs <;> norm_num

lemma cdfIndicator_abs_integral (a b : Time) :
    (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=|(a:ℝ)-b| := by
  have hle {a b : Time} (hab : a≤b) :
      (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=(b:ℝ)-a := by
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (cdfIndicator_order hab _))]
    rw [integral_sub (cdfIndicator_integrable a) (cdfIndicator_integrable b),
      cdfIndicator_integral,cdfIndicator_integral]
    ring
  rcases le_total a b with hab | hba
  · rw [hle hab,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ)≤b from hab))]
  · simp_rw [abs_sub_comm (cdfIndicator a _) (cdfIndicator b _)]
    rw [hle hba,abs_of_nonneg (sub_nonneg.mpr (show (b:ℝ)≤a from hba))]

lemma quantileTrial_L1_le (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    (∫ t, |quantileTrial q t-quantileTrial r t| ∂timeLaw)≤
      ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  let F := fun p : Time×Time => |cdfIndicator (q p.2) p.1-cdfIndicator (r p.2) p.1|
  have hmq : Measurable (fun p : Time×Time => cdfIndicator (q p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hq.comp measurable_snd) measurable_fst) measurable_const
  have hmr : Measurable (fun p : Time×Time => cdfIndicator (r p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hr.comp measurable_snd) measurable_fst) measurable_const
  have hF : Integrable F (timeLaw.prod timeLaw) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) ((hmq.sub hmr).abs.aestronglyMeasurable)
    exact ae_of_all _ fun p => by dsimp [F,cdfIndicator]; split_ifs <;> norm_num
  have hpoint (t : Time) : |quantileTrial q t-quantileTrial r t|≤∫ u, F (t,u) ∂timeLaw := by
    rw [quantileTrial_eq_integral q hq,quantileTrial_eq_integral r hr]
    have hi (v : Time→Time) (hv : Measurable v) :
        Integrable (fun u => if v u≤t then (1:ℝ) else 0) timeLaw := by
      apply Integrable.mono' (integrable_const (1:ℝ))
        ((measurable_const.ite (measurableSet_le hv measurable_const) measurable_const).aestronglyMeasurable)
      exact ae_of_all _ fun _ => by split_ifs <;> norm_num
    rw [← integral_sub (hi q hq) (hi r hr)]
    simpa only [Real.norm_eq_abs,F,cdfIndicator] using (norm_integral_le_integral_norm
      (fun u : Time => (if q u≤t then (1:ℝ) else 0)-(if r u≤t then (1:ℝ) else 0)))
  calc
    _ ≤ ∫ t, ∫ u, F (t,u) ∂timeLaw ∂timeLaw :=
      integral_mono ((trial_integrable (quantileTrial q)).sub (trial_integrable (quantileTrial r))).abs
        hF.integral_prod_left hpoint
    _ = ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
      rw [integral_integral_swap hF]
      exact integral_congr_ae (ae_of_all _ fun u => cdfIndicator_abs_integral (q u) (r u))

theorem controlValue_quantile_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    |controlValue P g.f (quantileTrial q)-controlValue P g.f (quantileTrial r)|≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  apply (controlValue_trial_abs_sub_le P g.f _ _ ‖g.d1‖₊ g.lipschitz).trans
  exact mul_le_mul_of_nonneg_left (quantileTrial_L1_le q r hq hr) (by positivity)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma Jet3.eq_of_f_eq {g h : Jet3} (he : g.f=h.f) : g=h := by
  have h1 : g.d1=h.d1 := by
    ext x
    rw [← g.deriv_eq,← h.deriv_eq,he]
  have h2 : g.d2=h.d2 := by
    ext x
    rw [← g.deriv2_eq,← h.deriv2_eq,he]
  have h3 : g.d3=h.d3 := by
    ext x
    rw [← g.deriv3_eq,← h.deriv3_eq,he]
  cases g
  cases h
  simp_all

lemma Jet3.heatLog_zero_time (g : Jet3) (d : ℝ≥0) : g.heatLog 0 d=g := by
  apply Jet3.eq_of_f_eq
  ext x
  simp only [Jet3.heatLog_f,heatLogBCF_coe,heatLog_zero]

lemma finiteStepControlJet_chain (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ)) :
    HeatChain m g (q 0) (q (Fin.last n)) (finiteStepControlJet g n q d) := by
  induction n with
  | zero => exact HeatChain.nil (q 0)
  | succ n ih =>
    have ih' := ih (fun i => q i.succ) (fun i => d i.succ)
      (hq.comp (Fin.strictMono_succ.monotone)) (fun i => hm i.succ)
    change HeatChain m g (q 1) (q (Fin.last (n+1))) _ at ih'
    have h01 : q 0≤q 1 := hq (Fin.zero_le _)
    rcases lt_or_eq_of_le h01 with hlt | he
    · exact HeatChain.cons (d 0) hlt (hq (Fin.le_last _)) (hm 0) ih'
    · simpa only [finiteStepControlJet,he,timeSpan,sub_self,Real.toNNReal_zero,
        Jet3.heatLog_zero_time] using ih'

lemma finiteStepControlJet_value (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f m=(finiteStepControlJet g n q d).f 0 := by
  have H := finiteStepControlJet_chain g m n q d hq hm
  rw [hq0,hq1] at H
  exact H.controlValue_eq P hB

lemma leftWeightedStepTrial_ae {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    (leftWeightedStepTrial w q hw hw1 : Time→ℝ)=ᵐ[timeLaw] weightedStepTrial w q hw hw1 := by
  have he : ∀ᵐ t ∂timeLaw, ∀ i, t≠q i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simp
  filter_upwards [he] with t ht
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i≤t
  · rw [ite_eq_left hi,ite_eq_left (lt_of_le_of_ne hi (Ne.symm (ht i)))]
  · rw [ite_eq_right hi,ite_eq_right (not_lt_of_ge (le_of_not_ge hi))]

lemma leftWeightedStepTrial_interval (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (i : Fin n) {r : Time} (hr : r∈Ioc (q i.castSucc) (q i.succ)) :
    leftWeightedStepTrial w q hw hw1 r=(weightedControlCoefficient n w hw i:ℝ) := by
  change (∑ j, if q j < r then w j else 0) = ∑ j, if j ≤ i.castSucc then w j else 0
  apply Finset.sum_congr rfl
  intro j _
  have he : q j < r ↔ j ≤ i.castSucc := by
    constructor
    · intro hj
      by_contra hn
      have hij : i.succ ≤ j := by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hn ⊢
        omega
      exact not_lt_of_ge ((hq hij).trans' hr.2) hj
    · intro hj
      exact (hq hj).trans_lt hr.1
  simp only [he]

theorem weightedStepTrial_controlValue (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      (finiteStepControlJet g n q (weightedControlCoefficient n w hw)).f 0 := by
  have he := leftWeightedStepTrial_ae w q hw hw1
  have hv := controlValue_trial_abs_sub_le P g.f (weightedStepTrial w q hw hw1)
    (leftWeightedStepTrial w q hw hw1) ‖g.d1‖₊ g.lipschitz
  have hz : (∫ t, |weightedStepTrial w q hw hw1 t-leftWeightedStepTrial w q hw hw1 t| ∂timeLaw)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with t ht
    simp only [ht,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hv
  have hv' := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))
  rw [hv']
  exact finiteStepControlJet_value g _ n q (weightedControlCoefficient n w hw) hq hq0 hq1
    (fun i r hr => leftWeightedStepTrial_interval n w q hw hw1 hq i hr) P hB

lemma paddedControlNodes_mono {n : ℕ} (q : Fin (n+1)→Time) (hq : Monotone q) :
    Monotone (paddedControlNodes q) := by
  have hs : Monotone (Fin.snoc q 1) := by
    simpa only [Fin.insertNth_last'] using Fin.insertNth_last_monotone hq 1 (show q (Fin.last n)≤1 from le_top)
  simpa only [Fin.insertNth_zero',paddedControlNodes] using
    Fin.insertNth_zero_monotone hs 0 (show (0:Time)≤(Fin.snoc q 1 : Fin (n+2)→Time) 0 from bot_le)

lemma paddedControlTrial_eq {n : ℕ} (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    weightedStepTrial (paddedControlWeights w) (paddedControlNodes q)
      (paddedControlWeights_nonneg w hw) (paddedControlWeights_sum w hw1)=
        weightedStepTrial w q hw hw1 := by
  apply Trial.ext_fun
  intro t
  change (∑ i, if paddedControlNodes q i≤t then paddedControlWeights w i else 0)=
    ∑ i, if q i≤t then w i else 0
  unfold paddedControlNodes paddedControlWeights
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,ite_self,zero_add]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,ite_self,add_zero]

theorem sourceWeightedTrial_controlValue (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      (finiteStepControlJet g (n+2) (paddedControlNodes q)
        (weightedControlCoefficient (n+2) (paddedControlWeights w) (paddedControlWeights_nonneg w hw))).f 0 := by
  rw [← paddedControlTrial_eq w q hw hw1]
  exact weightedStepTrial_controlValue (n+2) _ _ (paddedControlWeights_nonneg w hw)
    (paddedControlWeights_sum w hw1) (paddedControlNodes_mono q hq)
    (by simp [paddedControlNodes]) (by simp [paddedControlNodes]) g P hB

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControlTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma linearStepIntervals_start (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => r i) d) 0=
      finiteStepControlJet g n q d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet,
      sub_zero,one_mul,zero_mul,add_zero,timeSpan]
    rw [ih]

lemma linearStepIntervals_end (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => r i) d) 1=
      finiteStepControlJet g n r d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet,
      sub_self,zero_mul,one_mul,zero_add,timeSpan]
    rw [ih]

lemma linearStepIntervals_boundary (g : Jet3) (θ : ℝ) (n : ℕ)
    (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    (heatBoundaryTerms g θ (linearStepIntervals n q r d) (r 0-q 0)).map Prod.fst=
      stepBoundaryWeights n (fun i => r i-q i) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [linearStepIntervals,heatBoundaryTerms,List.map_cons,List.map_map,
        Function.comp_def,stepBoundaryWeights]
      have he : r 0-q 0+((r 1-q 1)-(r 0-q 0))=r 1-q 1 := by ring
      rw [he]
      congr 1
      exact ih (fun i => q i.succ) (fun i => r i.succ) (fun i => d i.succ)

lemma linearStepIntervals_rate (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    ((linearStepIntervals n q r d).map HeatIntervalParam.rate).sum=
      (r (Fin.last n)-q (Fin.last n))-(r 0-q 0) := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    simp only [linearStepIntervals,List.map_cons,List.sum_cons]
    rw [ih]
    simp only [Fin.succ_last,Fin.succ_zero_eq_one]
    ring

lemma linearStepIntervals_continuous (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    ∀ p∈linearStepIntervals n q r d, Continuous p.duration := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
    · exact ih _ _ _ p hp

lemma linearStepIntervals_deriv (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0)
    (hq : StrictMono q) (hr : StrictMono r) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ∀ p∈linearStepIntervals n q r d, HasDerivAt p.duration p.rate θ ∧ 0<p.duration θ := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · constructor
      · convert! (((hasDerivAt_const θ 1).sub (hasDerivAt_id θ)).mul_const (q 1-q 0)).add
          ((hasDerivAt_id θ).mul_const (r 1-r 0)) using 1
        all_goals try with_reducible_and_instances rfl
        dsimp
        ring
      · exact add_pos (mul_pos (sub_pos.mpr hθ.2) (sub_pos.mpr (hq (by simp))))
          (mul_pos hθ.1 (sub_pos.mpr (hr (by simp))))
    · exact ih _ _ _ (hq.comp Fin.strictMono_succ) (hr.comp Fin.strictMono_succ) p hp

lemma finiteStepControlJet_tail_order_strict (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : StrictMono q) (hr : StrictMono r)
    (h0 : q 0=r 0) (h1 : q (Fin.last n)=r (Fin.last n))
    (ht : ∀ zs : List ℝ, zs.IsSuffix (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d) →
      0≤zs.sum) (x : ℝ) :
    (finiteStepControlJet g n r d).f x≤(finiteStepControlJet g n q d).f x := by
  rw [← linearStepIntervals_start g n q r d,← linearStepIntervals_end g n q r d]
  apply parametricHeatJet_tail_order
  · exact linearStepIntervals_continuous n _ _ d
  · intro θ hθ
    exact linearStepIntervals_deriv n _ _ d ((Subtype.strictMono_coe _).comp hq)
      ((Subtype.strictMono_coe _).comp hr) θ hθ
  · rw [linearStepIntervals_rate,h0,h1]
    ring
  · intro θ _ zs hz
    apply ht
    have hb := linearStepIntervals_boundary g θ n (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) d
    rw [h0,sub_self] at hb
    rw [← hb]
    exact hz.map _

lemma uniformControlNodes_strict (n : ℕ) : StrictMono (uniformControlNodes n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

lemma blendControlNodes_strict {n : ℕ} (q e : Fin (n+1)→Time) (t : Time)
    (hq : Monotone q) (he : StrictMono e) (ht : 0<(t:ℝ)) : StrictMono (blendControlNodes q e t) := by
  intro i j hij
  change (1-(t:ℝ))*(q i:ℝ)+(t:ℝ)*(e i:ℝ)<(1-(t:ℝ))*(q j:ℝ)+(t:ℝ)*(e j:ℝ)
  exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hq hij.le) (sub_nonneg.mpr t.2.2))
    (mul_lt_mul_of_pos_left (he hij) ht)

lemma linearStepIntervals_eval (g : Jet3) (n : ℕ) (q e : Fin (n+1)→Time)
    (d : Fin n→ℝ≥0) (t : Time) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => e i) d) t=
      finiteStepControlJet g n (blendControlNodes q e t) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet]
    rw [ih]
    congr 1
    unfold timeSpan blendControlNodes
    congr 1
    ring

lemma stepBoundaryWeights_scale (n : ℕ) (v : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) (c : ℝ) :
    stepBoundaryWeights n (fun i => c*v i) d=(stepBoundaryWeights n v d).map (c*·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [stepBoundaryWeights,List.map_cons]
      rw [ih]
      congr 1
      ring

lemma stepBoundaryWeights_blend {n : ℕ} (q r e : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (t : Time) :
    stepBoundaryWeights n (fun i => (blendControlNodes r e t i:ℝ)-blendControlNodes q e t i) d=
      (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d).map ((1-(t:ℝ))*·) := by
  rw [← stepBoundaryWeights_scale]
  congr 1
  funext i
  simp only [blendControlNodes]
  ring

theorem finiteStepControlJet_tail_order (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q) (hr : Monotone r)
    (h0 : q 0=r 0) (h1 : q (Fin.last n)=r (Fin.last n))
    (ht : ∀ zs : List ℝ, zs.IsSuffix (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d) →
      0≤zs.sum) (x : ℝ) :
    (finiteStepControlJet g n r d).f x≤(finiteStepControlJet g n q d).f x := by
  let e := uniformControlNodes n
  have he : StrictMono e := uniformControlNodes_strict n
  let F := fun s : ℝ => (parametricHeatJet g
    (linearStepIntervals n (fun i => q i) (fun i => e i) d) s).f x
  let G := fun s : ℝ => (parametricHeatJet g
    (linearStepIntervals n (fun i => r i) (fun i => e i) d) s).f x
  have hF : ContinuousAt F 0 :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt _ _ _ (fun p hp =>
        (linearStepIntervals_continuous n _ _ d p hp).continuousAt))
  have hG : ContinuousAt G 0 :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt _ _ _ (fun p hp =>
        (linearStepIntervals_continuous n _ _ d p hp).continuousAt))
  have hi (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) : G s≤F s := by
    let t : Time := ⟨s,hs.1.le,hs.2.le⟩
    change (parametricHeatJet g _ (t:ℝ)).f x≤(parametricHeatJet g _ (t:ℝ)).f x
    rw [linearStepIntervals_eval,linearStepIntervals_eval]
    apply finiteStepControlJet_tail_order_strict g n _ _ d
      (blendControlNodes_strict q e t hq he hs.1) (blendControlNodes_strict r e t hr he hs.1)
    · apply Subtype.ext
      simp only [blendControlNodes,h0]
    · apply Subtype.ext
      simp only [blendControlNodes,h1]
    · intro zs hz
      rw [stepBoundaryWeights_blend] at hz
      obtain ⟨ys,hy,rfl⟩ := List.suffix_map_iff.mp hz
      rw [List.sum_map_mul_left]
      simpa using mul_nonneg (sub_nonneg.mpr hs.2.le) (ht ys hy)
  let : NeBot (𝓝[Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot zero_lt_one
  have hlim : G 0≤F 0 := le_of_tendsto_of_tendsto hG.continuousWithinAt.tendsto
    hF.continuousWithinAt.tendsto (eventually_mem_nhdsWithin.mono fun s hs => hi s hs)
  simpa only [F,G,linearStepIntervals_start] using hlim

lemma stepBoundaryWeights_ofFn (n : ℕ) (v : Fin (n+2)→ℝ) (d : Fin (n+1)→ℝ≥0) :
    stepBoundaryWeights (n+1) v d=
      List.ofFn (fun i : Fin n => ((d i.succ:ℝ)-(d i.castSucc:ℝ))*v i.succ.castSucc) := by
  induction n with
  | zero => simp [stepBoundaryWeights]
  | succ n ih =>
    rw [stepBoundaryWeights,List.ofFn_succ,ih]
    rfl

lemma weightedControlCoefficient_gap (n : ℕ) (w : Fin (n+2)→ℝ) (hw : ∀ i, 0≤w i) (i : Fin n) :
    (weightedControlCoefficient (n+1) w hw i.succ:ℝ)-
      weightedControlCoefficient (n+1) w hw i.castSucc=w i.succ.castSucc := by
  have he (j : Fin (n+2)) :
      (if j ≤ i.succ.castSucc then w j else 0)=
        (if j ≤ i.castSucc.castSucc then w j else 0)+(if j=i.succ.castSucc then w j else 0) := by
    by_cases hj : j=i.succ.castSucc
    · subst j
      have hn : ¬i.succ.castSucc ≤ i.castSucc.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]
        omega
      simp only [le_refl,ite_true,hn,ite_false,zero_add]
    · have hle : j ≤ i.succ.castSucc ↔ j ≤ i.castSucc.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]
        have hne : j.val≠i.val+1 := by simpa [Fin.ext_iff] using hj
        omega
      simp only [hj,hle,ite_false,add_zero]
  change (∑ j, if j ≤ i.succ.castSucc then w j else 0)-
    (∑ j, if j ≤ i.castSucc.castSucc then w j else 0)=_
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

lemma paddedControl_boundaryWeights (n : ℕ) (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i)
    (q r : Fin (n+1)→Time) :
    stepBoundaryWeights (n+2)
      (fun i => (paddedControlNodes r i:ℝ)-paddedControlNodes q i)
      (weightedControlCoefficient (n+2) (paddedControlWeights w) (paddedControlWeights_nonneg w hw))=
        List.ofFn (fun i => w i*((r i:ℝ)-q i)) := by
  rw [stepBoundaryWeights_ofFn]
  congr 1
  funext i
  rw [weightedControlCoefficient_gap]
  simp [paddedControlWeights,paddedControlNodes,Fin.castSucc_succ]

lemma listOfFn_suffix_sum_nonneg (n : ℕ) (v : Fin n→ℝ)
    (ht : ∀ k : ℕ, 0≤∑ i, if k ≤ i.val then v i else 0) :
    ∀ zs : List ℝ, zs.IsSuffix (List.ofFn v) → 0≤zs.sum := by
  induction n with
  | zero =>
    intro zs hz
    simpa using (show zs=[] from by simpa using hz) ▸ (le_refl (0:ℝ))
  | succ n ih =>
    intro zs hz
    rw [List.ofFn_succ] at hz
    obtain ⟨ys,hys⟩ := hz
    cases ys with
    | nil =>
      have he : zs=v 0 ::List.ofFn (fun i => v i.succ) := by simpa using hys
      rw [he,← List.ofFn_succ,List.sum_ofFn]
      simpa using ht 0
    | cons a ys =>
      have he : ys++zs=List.ofFn (fun i => v i.succ) := (List.cons.inj hys).2
      apply ih (fun i => v i.succ) ?_ zs ⟨ys,he⟩
      intro k
      have H := ht (k+1)
      rw [Fin.sum_univ_succ] at H
      simpa only [Fin.val_zero,(show ¬k+1≤0 by omega),ite_false,zero_add,Fin.val_succ,
        Nat.add_le_add_iff_right] using H

theorem sourceWeightedTrial_control_tail_order (n : ℕ) (w : Fin (n+1)→ℝ)
    (q r : Fin (n+1)→Time) (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ k : ℕ, 0≤∑ i, if k ≤ i.val then w i*((r i:ℝ)-q i) else 0)
    (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w r hw hw1)≤
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [sourceWeightedTrial_controlValue n w r hw hw1 hr g P hB,
    sourceWeightedTrial_controlValue n w q hw hw1 hq g P hB]
  apply finiteStepControlJet_tail_order g (n+2) _ _ _ (paddedControlNodes_mono q hq)
    (paddedControlNodes_mono r hr)
  · simp [paddedControlNodes]
  · simp [paddedControlNodes]
  · rw [paddedControl_boundaryWeights n w hw q r]
    exact listOfFn_suffix_sum_nonneg (n+1) _ ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformQuantileCells
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma uniformQuantileGrid_strict (n : ℕ) : StrictMono (uniformQuantileGrid n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

lemma uniformQuantileGrid_zero (n : ℕ) : uniformQuantileGrid n 0=0 := by
  apply Subtype.ext
  norm_num [uniformQuantileGrid]

lemma uniformQuantileGrid_last (n : ℕ) : uniformQuantileGrid n (Fin.last (n+1))=1 := by
  apply Subtype.ext
  change ((n+1:ℕ):ℝ)/(n+1)=1
  push_cast
  exact div_self (by positivity)

lemma uniformQuantileCell_mono (n : ℕ) : Monotone (uniformQuantileCell n) := by
  intro u v huv
  change min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ≤ min ⌊(n+1:ℝ)*(v:ℝ)⌋₊ n
  exact min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (show (u:ℝ)≤v from huv) (by positivity)))

lemma uniformQuantileCell_measurable (n : ℕ) : Measurable (uniformQuantileCell n) :=
  (uniformQuantileCell_mono n).measurable

lemma uniformQuantileCell_floor {n : ℕ} {u : Time} (hu : (u:ℝ)<1) :
    (uniformQuantileCell n u).val=⌊(n+1:ℝ)*(u:ℝ)⌋₊ := by
  change min _ n=_
  apply min_eq_left
  have hf : ⌊(n+1:ℝ)*(u:ℝ)⌋₊<n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) u.2.1)]
    push_cast
    nlinarith
  omega

lemma uniformQuantileCell_bounds (n : ℕ) (u : Time) :
    uniformQuantileGrid n (uniformQuantileCell n u).castSucc≤u ∧
      u≤uniformQuantileGrid n (uniformQuantileCell n u).succ := by
  by_cases hu : (u:ℝ)<1
  · have he := uniformQuantileCell_floor (n:=n) hu
    constructor
    · change ((uniformQuantileCell n u).val:ℝ)/(n+1)≤u
      rw [he,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity) u.2.1)
    · change (u:ℝ)≤((_ : ℕ):ℝ)/(n+1)
      rw [Fin.val_succ,he,le_div_iff₀ (by positivity)]
      push_cast
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((n+1:ℝ)*(u:ℝ))).le
  · have he : u=1 := Subtype.ext (le_antisymm u.2.2 (le_of_not_gt hu))
    subst u
    have hcell : uniformQuantileCell n 1=Fin.last n := by
      apply Fin.ext
      change min ⌊(n+1:ℝ)*1⌋₊ n=n
      rw [mul_one,show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
      omega
    rw [hcell,Fin.succ_last,uniformQuantileGrid_last]
    exact ⟨le_top,le_rfl⟩

lemma uniformQuantileCell_atom {n : ℕ} {u : Time} (hu : (u:ℝ)<1) (i : Fin (n+1)) :
    uniformQuantileCell n u=i ↔
      u∈Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
  rw [Fin.ext_iff,uniformQuantileCell_floor hu]
  rw [Nat.floor_eq_iff (mul_nonneg (by positivity) u.2.1)]
  change ((i:ℝ)≤(n+1:ℝ)*(u:ℝ) ∧ (n+1:ℝ)*(u:ℝ)<(i:ℝ)+1) ↔
    ((i:ℝ)/(n+1)≤(u:ℝ) ∧ (u:ℝ)<((i.val+1:ℕ):ℝ)/(n+1))
  rw [div_le_iff₀ (by positivity),lt_div_iff₀ (by positivity)]
  push_cast
  ring_nf

lemma uniformQuantileCell_weight (n : ℕ) (i : Fin (n+1)) :
    timeLaw.real ((uniformQuantileCell n) ⁻¹' {i})=1/(n+1:ℝ) := by
  have hae : ((uniformQuantileCell n) ⁻¹' {i})=ᵐ[timeLaw]
      Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
    have hnot : ∀ᵐ u ∂timeLaw, u≠1 := by exact ae_iff.mpr (by simp)
    filter_upwards [hnot] with u hu
    exact propext (uniformQuantileCell_atom (lt_of_le_of_ne u.2.2 (fun he => hu (Subtype.ext he))) i)
  rw [measureReal_congr hae]
  simp only [Measure.real,timeLaw_eq_volume,unitInterval.volume_Ico]
  rw [ENNReal.toReal_ofReal]
  · dsimp [uniformQuantileGrid]
    push_cast
    ring
  · exact sub_nonneg.mpr ((uniformQuantileGrid_strict n).monotone (Fin.castSucc_le_succ i))

lemma uniformQuantileCell_integral (n : ℕ) (F : Fin (n+1)→ℝ) :
    (∫ u, F (uniformQuantileCell n u) ∂timeLaw)=∑ i, (1/(n+1:ℝ))*F i := by
  rw [integral_finite_label _ (uniformQuantileCell_measurable n)]
  simp_rw [uniformQuantileCell_weight]

lemma uniformQuantileCell_upper {n : ℕ} (k : Fin (n+1)) (u : Time) :
    k ≤ uniformQuantileCell n u ↔ uniformQuantileGrid n k.castSucc≤u := by
  change k.val ≤ min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ↔ (k:ℝ)/(n+1)≤u
  rw [le_min_iff,and_iff_left (Nat.le_of_lt_succ k.isLt),Nat.le_floor_iff (mul_nonneg (by positivity) u.2.1),
    div_le_iff₀ (by positivity)]
  rw [mul_comm (u:ℝ)]

lemma uniformQuantileCell_tail_integral (n : ℕ) (F : Fin (n+1)→ℝ) (k : Fin (n+1)) :
    (∫ u in Ici (uniformQuantileGrid n k.castSucc), F (uniformQuantileCell n u) ∂timeLaw)=
      ∑ i, if k ≤ i then (1/(n+1:ℝ))*F i else 0 := by
  rw [← integral_indicator measurableSet_Ici]
  have he (u : Time) : (Ici (uniformQuantileGrid n k.castSucc)).indicator
      (fun u => F (uniformQuantileCell n u)) u=
      (if k ≤ uniformQuantileCell n u then F (uniformQuantileCell n u) else 0) := by
    simp only [Set.indicator_apply,mem_Ici,← uniformQuantileCell_upper]
  simp_rw [he]
  rw [uniformQuantileCell_integral n (fun i => if k ≤ i then F i else 0)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileUpperTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma unit_valued_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) : Integrable (fun u => (q u:ℝ)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_subtype_coe.comp hq).aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (q u).property.1]
    exact (q u).property.2

lemma quantile_stoploss_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) (r : ℝ) :
    Integrable (fun u => max ((q u:ℝ)-r) 0) μ :=
  ((unit_valued_integrable μ hq).sub (integrable_const r)).sup (integrable_const 0)

lemma time_tail_constant (t : Time) (r : ℝ) :
    (∫ _point : Time in Ici t, r)=(1-(t:ℝ))*r := by
  rw [integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Ici,smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr t.property.2)]

lemma upper_tail_le_stoploss {q : Time→Time} (hq : Measurable q) (t : Time) (r : ℝ) :
    (∫ u : Time in Ici t, (q u:ℝ)) ≤
      (1-(t:ℝ))*r+∫ u : Time, max ((q u:ℝ)-r) 0 := by
  have hi := unit_valued_integrable volume hq
  have hs := quantile_stoploss_integrable volume hq r
  have he : (∫ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u)=
      (∫ u : Time in Ici t, (q u:ℝ))-(1-(t:ℝ))*r := by
    rw [integral_indicator measurableSet_Ici,integral_sub hi.integrableOn (integrable_const r),
      time_tail_constant]
  have hm := integral_mono ((hi.sub (integrable_const r)).indicator measurableSet_Ici) hs
    (show ∀ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u ≤ max ((q u:ℝ)-r) 0 from by
      intro u
      by_cases hu : u∈Ici t
      · rw [indicator_of_mem hu]; exact le_max_left _ _
      · rw [indicator_of_notMem hu]; exact le_max_right _ _)
  change (∫ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u) ≤ _ at hm
  rw [he] at hm
  linarith

lemma upper_tail_eq_stoploss {p : Time→Time} (hp : Monotone p) (t : Time) :
    (∫ u : Time in Ici t, (p u:ℝ))=
      (1-(t:ℝ))*(p t:ℝ)+∫ u : Time, max ((p u:ℝ)-(p t:ℝ)) 0 := by
  have hi := unit_valued_integrable volume hp.measurable
  have he : (fun u : Time => max ((p u:ℝ)-(p t:ℝ)) 0)=
      (Ici t).indicator (fun u => (p u:ℝ)-(p t:ℝ)) := by
    funext u
    by_cases hu : t≤u
    · rw [indicator_of_mem (show u∈Ici t from hu),max_eq_left (sub_nonneg.mpr (show (p t:ℝ)≤(p u:ℝ) from hp hu))]
    · rw [indicator_of_notMem (show u∉Ici t from hu),max_eq_right (sub_nonpos.mpr (show (p u:ℝ)≤(p t:ℝ) from hp (le_of_not_ge hu)))]
  rw [he,integral_indicator measurableSet_Ici,integral_sub hi.integrableOn (integrable_const _),
    time_tail_constant]
  ring

theorem upper_tail_order_of_stoploss {q p : Time→Time} (hq : Measurable q) (hp : Monotone p)
    (hstop : ∀ r : ℝ, (∫ u : Time, max ((q u:ℝ)-r) 0)≤
      ∫ u : Time, max ((p u:ℝ)-r) 0) (t : Time) :
    (∫ u : Time in Ici t, (q u:ℝ))≤∫ u : Time in Ici t, (p u:ℝ) := by
  rw [upper_tail_eq_stoploss hp t]
  exact (upper_tail_le_stoploss hq t (p t:ℝ)).trans (add_le_add le_rfl (hstop (p t:ℝ)))

lemma boundedQuantile_stoploss (μ : Measure Time) [IsProbabilityMeasure μ] (r : ℝ) :
    (∫ u : Time, max ((boundedQuantile μ u:ℝ)-r) 0)=∫ x : Time, max (x.val-r) 0 ∂μ := by
  conv_rhs => rw [← boundedQuantile_law μ]
  rw [integral_map (boundedQuantile_measurable μ).aemeasurable (by fun_prop)]

lemma uniformQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileLower n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (show i.castSucc ≤ j.castSucc from hij))
lemma uniformQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileUpper n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (Fin.succ_le_succ_iff.mpr hij))
lemma sampleQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileLower n q) :=
  (uniformQuantileLower_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileUpper n q) :=
  (uniformQuantileUpper_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantile_bracket (n : ℕ) {q : Time→Time} (hq : Monotone q) (u : Time) :
    sampleQuantileLower n q u ≤ q u ∧ q u ≤ sampleQuantileUpper n q u :=
  ⟨hq (uniformQuantileCell_bounds n u).1,hq (uniformQuantileCell_bounds n u).2⟩

lemma sampleQuantile_gap_integral (n : ℕ) (q : Time→Time) :
    (∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw)=
      ((q 1:ℝ)-q 0)/(n+1:ℝ) := by
  change (∫ u, (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i)
    (uniformQuantileCell n u) ∂timeLaw)=_
  rw [uniformQuantileCell_integral n (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i),← Finset.mul_sum]
  unfold uniformQuantileUpper uniformQuantileLower
  rw [finite_sum_successive_differences (n+1) (fun i => (q (uniformQuantileGrid n i):ℝ)),
    uniformQuantileGrid_last,uniformQuantileGrid_zero]
  ring

lemma sampleQuantileLower_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hl.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonpos (sub_nonpos.mpr (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1))]
      have ht : (q u:ℝ) ≤ sampleQuantileUpper n q u := hb.2
      linarith
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma sampleQuantileUpper_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileUpper n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hu.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (show (q u:ℝ) ≤ sampleQuantileUpper n q u from hb.2))]
      exact sub_le_sub_left (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1) _
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma sampleQuantile_trial (n : ℕ) (q : Fin (n+1)→Time) :
    quantileTrial (fun u => q (uniformQuantileCell n u))=
      weightedStepTrial (fun _ => 1/(n+1:ℝ)) q (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n) := by
  apply Trial.ext_fun
  intro t
  have hm : Measurable (fun u => q (uniformQuantileCell n u)) :=
    (measurable_of_finite q).comp (uniformQuantileCell_measurable n)
  rw [quantileTrial_eq_integral _ hm]
  rw [uniformQuantileCell_integral n (fun i => if q i ≤ t then (1:ℝ) else 0)]
  change (∑ i, (1/(n+1:ℝ))*(if q i ≤ t then (1:ℝ) else 0))=∑ i, if q i ≤ t then 1/(n+1:ℝ) else 0
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_QuantileControlTail
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

lemma sampledQuantile_tail_order (n : ℕ) {q r : Time→Time} (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ t : Time, (∫ u in Ici t, (q u:ℝ) ∂timeLaw) ≤ ∫ u in Ici t, (r u:ℝ) ∂timeLaw)
    (k : ℕ) : 0 ≤ ∑ i : Fin (n+1), if k ≤ i.val then
      (1/(n+1:ℝ))*((uniformQuantileUpper n r i:ℝ)-uniformQuantileLower n q i) else 0 := by
  by_cases hk : k<n+1
  · let j : Fin (n+1) := ⟨k,hk⟩
    have h1 : (∫ u in Ici (uniformQuantileGrid n j.castSucc), (sampleQuantileLower n q u:ℝ) ∂timeLaw) ≤
        ∫ u in Ici (uniformQuantileGrid n j.castSucc), (sampleQuantileUpper n r u:ℝ) ∂timeLaw := by
      calc
        _ ≤ ∫ u in Ici (uniformQuantileGrid n j.castSucc), (q u:ℝ) ∂timeLaw := by
          apply integral_mono (unit_valued_integrable _ (sampleQuantileLower_mono n hq).measurable)
            (unit_valued_integrable _ hq.measurable)
          exact fun u => (sampleQuantile_bracket n hq u).1
        _ ≤ ∫ u in Ici (uniformQuantileGrid n j.castSucc), (r u:ℝ) ∂timeLaw := ht _
        _ ≤ _ := by
          apply integral_mono (unit_valued_integrable _ hr.measurable)
            (unit_valued_integrable _ (sampleQuantileUpper_mono n hr).measurable)
          exact fun u => (sampleQuantile_bracket n hr u).2
    change (∫ u in Ici (uniformQuantileGrid n j.castSucc),
      (uniformQuantileLower n q (uniformQuantileCell n u):ℝ) ∂timeLaw) ≤
      ∫ u in Ici (uniformQuantileGrid n j.castSucc),
        (uniformQuantileUpper n r (uniformQuantileCell n u):ℝ) ∂timeLaw at h1
    rw [uniformQuantileCell_tail_integral n (fun i => (uniformQuantileLower n q i:ℝ)) j,
      uniformQuantileCell_tail_integral n (fun i => (uniformQuantileUpper n r i:ℝ)) j] at h1
    have he : (∑ i : Fin (n+1), if k ≤ i.val then
        (1/(n+1:ℝ))*((uniformQuantileUpper n r i:ℝ)-uniformQuantileLower n q i) else 0)=
      (∑ i : Fin (n+1), if j ≤ i then (1/(n+1:ℝ))*(uniformQuantileUpper n r i:ℝ) else 0)-
      (∑ i : Fin (n+1), if j ≤ i then (1/(n+1:ℝ))*(uniformQuantileLower n q i:ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (if k ≤ i.val then _ else _)=(if k ≤ i.val then _ else _)-(if k ≤ i.val then _ else _)
      split_ifs <;> ring
    rw [he]
    exact sub_nonneg.mpr h1
  · have hz : ∀ i : Fin (n+1), ¬k ≤ i.val := fun i => by have := i.isLt; omega
    simp only [hz,ite_false,Finset.sum_const_zero,le_refl]

lemma sampleQuantile_control_error (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q : Time→Time) (hq : Monotone q) (n : ℕ) :
    |controlValue P g.f (quantileTrial (sampleQuantileLower n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) ∧
    |controlValue P g.f (quantileTrial (sampleQuantileUpper n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) := by
  constructor
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileLower_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity))
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileUpper_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileUpper_L1 n hq) (by positivity))

theorem sourceQuantile_control_tail_order (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (g : Jet3) (q r : Time→Time)
    (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ t : Time, (∫ u in Ici t, (q u:ℝ) ∂timeLaw) ≤ ∫ u in Ici t, (r u:ℝ) ∂timeLaw) :
    controlValue P g.f (quantileTrial r) ≤ controlValue P g.f (quantileTrial q) := by
  have hi (n : ℕ) : controlValue P g.f (quantileTrial (sampleQuantileUpper n r)) ≤
      controlValue P g.f (quantileTrial (sampleQuantileLower n q)) := by
    unfold sampleQuantileUpper sampleQuantileLower
    rw [sampleQuantile_trial,sampleQuantile_trial]
    exact sourceWeightedTrial_control_tail_order n _ _ _ (uniformQuantileWeights_nonneg n)
      (uniformQuantileWeights_sum n) (uniformQuantileLower_mono n hq) (uniformQuantileUpper_mono n hr)
      (sampledQuantile_tail_order n hq hr ht) g P hB
  have hz : Tendsto (fun n : ℕ => (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((3/2:ℝ)*(‖g.d1‖₊:ℝ)^2)
  have hl : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileLower n q))) atTop
      (𝓝 (controlValue P g.f (quantileTrial q))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
    simpa only [Real.dist_eq] using (sampleQuantile_control_error P g q hq n).1
  have hu : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileUpper n r))) atTop
      (𝓝 (controlValue P g.f (quantileTrial r))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
    simpa only [Real.dist_eq] using (sampleQuantile_control_error P g r hr n).2
  exact le_of_tendsto_of_tendsto hu hl (Eventually.of_forall hi)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactJointMonomials
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma compactJointMonomial_zero : compactJointMonomial 0 0 = 1 := by ext x; simp

lemma compactJointMonomial_add (p d p' d' : ℕ) :
    compactJointMonomial (p+p') (d+d') = compactJointMonomial p d * compactJointMonomial p' d' := by
  ext x
  simp only [compactJointMonomial_apply,BoundedContinuousFunction.mul_apply,pow_add]
  ring

lemma compactJointMonomial_separates (x y : CompactJointOverlap) (h : x≠y) :
    ∃ p d, compactJointMonomial p d x ≠ compactJointMonomial p d y := by
  by_contra hn
  push Not at hn
  apply h
  apply Prod.ext <;> apply Subtype.ext
  · simpa using hn 1 0
  · simpa using hn 0 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FieldArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceFieldPolynomial_eval {k : ℕ} (a : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    (sourceFieldPolynomial a).eval ((l.val:ℝ)/(k+1:ℕ))=a l := by
  unfold sourceFieldPolynomial
  apply Lagrange.eval_interpolate_at_node (s := Finset.univ)
    (v := fun l : Fin (k+1) => (l.val:ℝ)/(k+1:ℕ)) (i := l) a
  · intro i hi j hj he
    apply Fin.ext
    have hv : (i.val:ℝ)=(j.val:ℝ) := (div_left_inj' (by positivity : ((k+1:ℕ):ℝ)≠0)).mp he
    exact_mod_cast hv
  · exact Finset.mem_univ l

lemma sourceFieldPolynomial_continuous {k : ℕ} (a : Fin (k+1)→ℝ) :
    Continuous (fun t : unitInterval => (sourceFieldPolynomial a).eval t.val) :=
  (sourceFieldPolynomial a).continuous.comp continuous_subtype_val

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma source_global_contact_perturbation_min (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q hw hw1 δ)
      (sourceContactCompactDomain n k α H) a) :
    IsMinOn (fun u => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
      sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u)
      (Icc (fun _ => 1) (fun _ => 2)) a.2.2 := by
  intro u hu
  change quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2 ≤
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u
  have he := hmin (show (a.1,a.2.1,u)∈sourceContactCompactDomain n k α H from
    ⟨ha.1,ha.2.1,hu⟩)
  unfold sourceStepContactObjective sourceJointPressure at he
  change -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2 ≤
    -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u at he
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGibbsArray_closed_full (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : Set (CompactArray CompactJointOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1)×IndexedLeaf k, sourceJointArray x ∈ F) :
    sourceGibbsArrayLaw n k f p d h u z t F=1 := by
  have hp : (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) F=1
  rw [Measure.map_apply (show Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) from
      (sourceJointArray_measurable (n+1) k).comp measurable_snd) hF.measurableSet,hp]
  exact measure_univ

lemma compact_spin_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma compact_tree_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma sourceGibbsArray_limit_gram (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)) := by
  constructor
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_spin_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_spin_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_spin_gram_closed r) (fun x => sourceSpinArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_tree_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_tree_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_tree_gram_closed r) (fun x => sourceTreeArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGDensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

lemma compactGGTestCLM_apply {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    compactGGTestCLM μ n i f g = compactGGDefect μ n i f g := by
  classical
  simp [compactGGTestCLM,compactGGDefect,boundedTestIntegral]

lemma compactJoint_monomials_total (L : (CompactJointOverlap →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ p d, L (compactJointMonomial p d)=0) : L=0 := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact CompactJointOverlap ℝ ℝ
  let L' := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let m (a : ℕ×ℕ) : C(CompactJointOverlap,ℝ) := (compactJointMonomial a.1 a.2).toContinuousMap
  have hm0 : m 0=1 := by ext x; simp [m]
  have hmadd (a b : ℕ×ℕ) : m (a+b)=m a*m b := by
    ext x
    exact congrArg (fun f : CompactJointOverlap →ᵇ ℝ => f x) (compactJointMonomial_add _ _ _ _)
  let M : Submonoid C(CompactJointOverlap,ℝ) :=
    { carrier := Set.range m
      one_mem' := ⟨0,hm0⟩
      mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hmadd a b⟩ }
  let A := Algebra.adjoin ℝ (M : Set C(CompactJointOverlap,ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p,d,hpd⟩ := compactJointMonomial_separates x y hxy
    have hmem : m (p,d) ∈ A :=
      Algebra.subset_adjoin (show m (p,d) ∈ M from ⟨(p,d),rfl⟩)
    exact ⟨m (p,d),⟨m (p,d),hmem,rfl⟩,hpd⟩
  have hA : (A : Set C(CompactJointOverlap,ℝ)) ⊆ (L'.ker : Set C(CompactJointOverlap,ℝ)) := by
    have hspan : Submodule.span ℝ (M : Set C(CompactJointOverlap,ℝ)) ≤ L'.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨p,d⟩,rfl⟩
      change L (e ((compactJointMonomial p d).toContinuousMap)) = 0
      have he : e ((compactJointMonomial p d).toContinuousMap) = compactJointMonomial p d := by
        ext x; rfl
      rw [he]
      exact hL p d
    intro f hf
    apply hspan
    change f ∈ A.toSubmodule at hf
    simpa only [A,Algebra.adjoin_eq_span,Submonoid.closure_eq] using hf
  have hclosed := L'.isClosed_ker
  have hc := closure_minimal hA hclosed
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hall (f : C(CompactJointOverlap,ℝ)) : L' f=0 := by
    apply hc
    change f ∈ A.topologicalClosure
    rw [htop]
    trivial
  ext g
  have h := hall (e.symm g)
  simpa [L'] using h

lemma compactGG_of_joint_monomials (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
    (h : ∀ p d, compactGGDefect μ n i f (compactJointMonomial p d)=0)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect μ n i f g=0 := by
  have hz := compactJoint_monomials_total (compactGGTestCLM μ n i f)
    (fun p d => (compactGGTestCLM_apply μ n i f _).trans (h p d))
  rw [← compactGGTestCLM_apply,hz]
  rfl

end

lemma compactGGDefect_one (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    compactGGDefect μ r i G 1=0 := by
  have hr : 1 ≤ r := by have := i.isLt; omega
  simp only [compactGGDefect,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one,
    integral_const,probReal_univ,smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem
    (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub hr,Nat.cast_one]
  ring

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ) (z : Fin k→ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ→ℝ≥0) (h : ℕ→Fin (k+1)→ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n, u n∈Icc (fun _=>1) (fun _=>2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j=>p j.val) (fun j=>d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1)=>1) (fun _=>2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_limit_joint_gg
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (fun a=>p a.val) (fun a=>d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect ν r i G g=0 := by
  apply compactGG_of_joint_monomials ν r i G
  intro a b
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    subst a b
    simpa only [compactJointMonomial_zero] using compactGGDefect_one ν r i G
  obtain ⟨j,hp,hd⟩ := hcover a b (by omega)
  apply compactGGDefect_limit hlim
  simpa only [hp,hd,Function.comp_def] using
    (source_contact_monomial_tendsto k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht j r i G).comp hs.tendsto_atTop

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SynchronizedLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

lemma source_contact_limit_exchangeable (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (ν : Measure _) (ν : Measure _) :=
  compact_exchangeability_limit hlim e (fun n => sourceGibbsArray_exchangeable
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) e)

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (z : Fin k → ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ) → Fin (n+1) → ℝ)
variable (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
variable (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht hcover
lemma source_contact_limit_no_crossing {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val) := by
  obtain ⟨hR,hT⟩ := sourceGibbsArray_limit_gram k f (fun _ a => p a.val)
    (fun _ a => d a.val) h u z t s hlim
  exact compact_gg_no_crossing ν
    (source_contact_limit_exchangeable k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
    (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover)
    hR hT

end

lemma sourceLabelLaw_integral (k : ℕ) (w : Fin (k+1)→ℝ) (hw : ∀ l, 0≤w l)
    (g : unitInterval→ℝ) (hg : Measurable g) :
    (∫ x, g x ∂sourceLabelLaw k w)=∑ l, w l*g (sourceLabelLevel k l) := by
  unfold sourceLabelLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac' g _ hg.stronglyMeasurable,
      ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro l _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma scalarArray_nonnegative (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ) {f : ℝ×ℝ→ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, 0 ≤ f (Q 0 1) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>  measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hs : ∀ᵐ Q ∂ν, ∀ i j, Q i j=Q j i := hg.mono fun Q hQ =>  gram_array_symmetric Q hQ
  have hp (n : ℕ) : ∀ᵐ Q ∂ν, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Q i j := by
    filter_upwards [hg] with Q hQ
    simpa [dotProduct,Matrix.mulVec,overlapBlock] using (hQ n).dotProduct_mulVec_nonneg (fun _ =>  (1:ℝ))
  have hn := gg_overlap_nonnegative ν (fun i j =>  by fun_prop) hs hd hp (scalarArray_gg μ hGG hf)
  exact ae_of_ae_map hm.aemeasurable hn

lemma compact_spin_nonnegative (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n =>  (Q i j).1.val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0 ≤ (Q 0 1).1.val := by
  have hr : ∀ᵐ Q ∂compactRealLaw ν, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst)) |>.mpr hR
  exact ae_of_ae_map compactArrayReal_measurable.aemeasurable
    (scalarArray_nonnegative (compactRealLaw ν) hGG measurable_fst hr (compactRealLaw_diagonals ν).1)

lemma compactPositivePairLaw_no_crossing (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hNo : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val)) (r t : Time) :
    compactPositivePairLaw ν (Iic r×ˢIoi t)=0 ∨ compactPositivePairLaw ν (Ioi r×ˢIic t)=0 := by
  let A : Set (ℝ×ℝ) := {x | max 0 x.1 ≤ r.val ∧ t.val < x.2}
  let B : Set (ℝ×ℝ) := {x | r.val < max 0 x.1 ∧ x.2 ≤ t.val}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hB : MeasurableSet B := by dsimp [B]; measurability
  have hno : ∀ᵐ Q ∂compactRealLaw ν, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2) :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mpr hNo
  have hh := joint_gg_crossed_regions_null (compactRealLaw ν) hGG hno A B hA hB
    (by
      intro a ha b hb
      refine ⟨?_,hb.2.trans_lt ha.2⟩
      have hm : max 0 a.1 < max 0 b.1 := ha.1.trans_lt hb.1
      exact lt_of_not_ge fun h =>  (not_le_of_gt hm) (max_le_max_left 0 h))
  have he (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) :
      (compactRealLaw ν) {Q | Q 0 1∈S}=(ν : Measure (CompactArray CompactJointOverlap)) {Q | compactPairReal (Q 0 1)∈S} := by
    exact Measure.map_apply compactArrayReal_measurable (hS.preimage (by fun_prop))
  rw [he A hA,he B hB] at hh
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  unfold compactPositivePairLaw
  rw [Measure.map_apply hm (measurableSet_Iic.prod measurableSet_Ioi),
    Measure.map_apply hm (measurableSet_Ioi.prod measurableSet_Iic)]
  exact hh

lemma compactPositivePairLaw_quantile (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hNo : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val)) :
    (volume : Measure Time).map (fun u =>
      (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u,
       boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) u))=compactPositivePairLaw ν :=
  no_crossing_quantile_coupling _ (compactPositivePairLaw_no_crossing ν hGG hNo)

lemma compactPositivePairLaw_label (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val)) :
    (compactPositivePairLaw ν).map Prod.snd=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2) := by
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  unfold compactPositivePairLaw
  rw [Measure.map_map measurable_snd hm]
  apply Measure.map_congr
  filter_upwards [hT] with Q hQ
  apply Subtype.ext
  exact gram_array_symmetric (fun i j => (Q i j).2.val) hQ 0 1

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (w : Fin (k+1) → ℝ)
variable (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
variable (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
variable (hh0 : ∀ n l, 0 ≤ h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ) → Fin (n+1) → ℝ)
variable (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) (stepCumulative w) (t n) v)
  (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
variable {H T : ℝ} (hH : 0 ≤ H) (hhH : ∀ n, h n 0 ≤ H) (ht : ∀ n, (t n:ℝ) ≤ T)
variable (hcover : ∀ a b : ℕ, 1 ≤ a+b → ∃ j, p j=a ∧ d j=b)

include hw hw1 hh0 hh hu hmin hH hhH ht hcover in

theorem source_contact_limit_quantile
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0 ≤ (Q 0 1).1.val) ∧
    (compactPositivePairLaw ν).map Prod.snd=sourceLabelLaw k w ∧
    (volume : Measure Time).map (fun a =>
      (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) a,
       boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) a))=compactPositivePairLaw ν := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hg := source_contact_limit_joint_gg k f p d (stepCumulative w) hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover
  have hgg := compactRealLaw_gg ν hg
  obtain ⟨hr,htt⟩ := sourceGibbsArray_limit_gram k f (fun _ a => p a.val)
    (fun _ a => d a.val) h u (stepCumulative w) t s hlim
  have hn := source_contact_limit_no_crossing k f p d (stepCumulative w) hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hcover hs hlim
  refine ⟨compact_spin_nonnegative ν hgg hr,?_,compactPositivePairLaw_quantile ν hgg hn⟩
  rw [compactPositivePairLaw_label ν htt]
  exact source_array_limit_label_law k f p d w hw hw1 h hh0 hh u
    (fun n j => ne_of_gt ((by norm_num : (0:ℝ) < 1).trans_le ((hu n).1 j))) t
    (fun b hb => by simpa only [zero_add] using hcover 0 b (by omega)) hs hlim


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContactLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

section

lemma compactPositivePairLaw_field_integral
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val))
    (hn : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0≤(Q 0 1).1.val)
    {k : ℕ} (a : Fin (k+1)→ℝ) :
    (∫ Q, sourceFieldArrayTest a Q ∂ν)=
      ∫ x : Time×Time, (sourceFieldPolynomial a).eval x.2.val*x.1.val
        ∂compactPositivePairLaw ν := by
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  rw [compactPositivePairLaw, integral_map hm.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hR,hT,hn] with Q hr ht hn
  dsimp [sourceFieldArrayTest,compactPositivePair]
  rw [max_eq_right hn, gram_array_symmetric (fun i j => (Q i j).1.val) hr 0 1,
    gram_array_symmetric (fun i j => (Q i j).2.val) ht 0 1]

end

lemma sourceLabelLaw_ae (k : ℕ) (w : Fin (k+1)→ℝ) {P : Time→Prop}
    (hP : ∀ i, P (sourceLabelLevel k i)) : ∀ᵐ x ∂sourceLabelLaw k w, P x := by
  rw [sourceLabelLaw,← Measure.sum_fintype,Measure.ae_sum_iff]
  intro i
  exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq,Filter.eventually_pure] using hP i) _

lemma sourceThresholdDirection_nonneg {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) (i : Fin (k+1)) :
    0 ≤ sourceThresholdDirection q r i := by unfold sourceThresholdDirection; split_ifs <;> norm_num

lemma sourceThresholdDirection_le_one {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) (i : Fin (k+1)) :
    sourceThresholdDirection q r i≤1 := by unfold sourceThresholdDirection; split_ifs <;> norm_num

lemma sourceThresholdDirection_monotone {k : ℕ} {q : Fin (k+1)→Time} (hq : Monotone q) (r : ℝ) :
    Monotone (sourceThresholdDirection q r) := by
  intro i j hij
  unfold sourceThresholdDirection
  split_ifs with hi hj hj <;> try norm_num
  exact False.elim (hj (hi.trans (hq hij)))

lemma sourceThresholdDirection_stoploss {k : ℕ} (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time) (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)=
      (∑ i, w i*(q i:ℝ)*sourceThresholdDirection q r i)-r*∑ i, w i*sourceThresholdDirection q r i := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [sourceThresholdDirection]
  split_ifs with hi
  · rw [max_eq_left (sub_nonneg.mpr hi)]; ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hi))]; ring

lemma source_field_stoploss {k : ℕ} (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hq : Monotone q)
    (μ : Measure (Time×Time)) [IsProbabilityMeasure μ]
    (hlabel : μ.map Prod.snd=sourceLabelLaw k w)
    (hfield : ∀ a : Fin (k+1)→ℝ, (∀ i, 0≤a i) → Monotone a →
      (∑ i, w i*(q i:ℝ)*a i)≤∫ x, (sourceFieldPolynomial a).eval x.2.val*x.1.val ∂μ)
    (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)≤∫ x : Time, max (x.val-r) 0 ∂μ.map Prod.fst := by
  let a := sourceThresholdDirection q r
  let g : Time×Time→ℝ := fun x => (sourceFieldPolynomial a).eval x.2.val
  have hg : Continuous g := (sourceFieldPolynomial_continuous a).comp continuous_snd
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hprod : Integrable (fun x : Time×Time => g x*x.1.val) μ :=
    (hg.mul (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : ∀ᵐ x ∂μ, g x∈Icc 0 1 := by
    have hb' : ∀ᵐ t ∂μ.map Prod.snd, (sourceFieldPolynomial a).eval t.val∈Icc 0 1 := by
      rw [hlabel]
      apply sourceLabelLaw_ae
      intro i
      change (sourceFieldPolynomial a).eval ((i.val:ℝ)/(k+1:ℕ))∈Icc 0 1
      rw [sourceFieldPolynomial_eval]
      exact ⟨sourceThresholdDirection_nonneg q r i,sourceThresholdDirection_le_one q r i⟩
    exact ae_of_ae_map measurable_snd.aemeasurable hb'
  have hint : (∫ x, g x ∂μ)=∑ i, w i*a i := by
    have he := sourceLabelLaw_integral k w hw (fun t => (sourceFieldPolynomial a).eval t.val)
      (sourceFieldPolynomial_continuous a).measurable
    rw [← hlabel,integral_map measurable_snd.aemeasurable
      (sourceFieldPolynomial_continuous a).measurable.aestronglyMeasurable] at he
    simpa only [sourceLabelLevel,sourceFieldPolynomial_eval] using he
  have hm : ∫ x, g x*x.1.val-r*g x ∂μ ≤ ∫ x : Time×Time, max (x.1.val-r) 0 ∂μ := by
    apply integral_mono_ae (hprod.sub (hgi.const_mul r))
      ((show Continuous (fun x : Time×Time => max (x.1.val-r) 0) from by fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    filter_upwards [hb] with x hx
    change g x*x.1.val-r*g x ≤ max (x.1.val-r) 0
    by_cases hr : r≤x.1.val
    · rw [max_eq_left (sub_nonneg.mpr hr)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hx.2)]
    · rw [max_eq_right (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hr)) hx.1]
  rw [integral_sub hprod (hgi.const_mul r),integral_const_mul,hint] at hm
  rw [integral_map measurable_fst.aemeasurable (by fun_prop),sourceThresholdDirection_stoploss]
  exact (sub_le_sub_right (hfield a (sourceThresholdDirection_nonneg q r)
    (sourceThresholdDirection_monotone hq r)) _).trans hm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ContactControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

section Contact
variable (k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))

variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

variable (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)

include hc hmin hcap hH hcover hs hlim hq in
lemma source_global_contact_limit_stoploss_along (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)≤
      ∫ x : Time, max (x.val-r) 0 ∂(compactPositivePairLaw ν).map Prod.fst := by
  have hm n := source_global_contact_perturbation_min n k P f (fun i => p i.val) (fun i => d i.val)
    w q (fun i => (hw i).le) hw1 δ α H (hc n) (hmin n)
  obtain ⟨hn,hl,-⟩ := source_contact_limit_quantile k f p d w hw hw1
    (fun n => (c n).1) (fun n => (c n).2.1) (fun n => (hc n).2.1.1.1)
    (fun n => (hc n).2.1.2) (fun n => (c n).2.2) (fun n => (hc n).2.2) hm hH
    (fun n => (hc n).2.1.1.2 0) (T := (α:ℝ)) (fun n => (hc n).1.2) hcover hs hlim
  obtain ⟨hr,ht⟩ := sourceGibbsArray_limit_gram k f (fun _ i => p i.val) (fun _ i => d i.val)
    (fun n => (c n).2.1) (fun n => (c n).2.2) (stepCumulative w) (fun n => (c n).1) s hlim
  apply source_field_stoploss w q (fun i => (hw i).le) hq (compactPositivePairLaw ν) hl
  intro a ha0 ha
  rw [← compactPositivePairLaw_field_integral ν hr ht hn a]
  exact source_global_contact_limit_field_along k P f p d w q hw hw1 δ α H c hc hmin hlim hcap ha0 ha

include hc hmin hcap hH hcover hs hlim hq in

theorem source_global_contact_limit_tail_order_along :
    quantileTrial (boundedQuantile (weightedTrialLaw w q))=
      weightedStepTrial w q (fun i => (hw i).le) hw1 ∧
    ∀ t : Time, (∫ u : Time in Ici t, (boundedQuantile (weightedTrialLaw w q) u:ℝ))≤
      ∫ u : Time in Ici t, (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u:ℝ) := by
  have := weightedTrialLaw_probability w q (fun i => (hw i).le) hw1
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  refine ⟨quantileTrial_weightedTrialLaw w q (fun i => (hw i).le) hw1,?_⟩
  apply upper_tail_order_of_stoploss (boundedQuantile_measurable _)
    (boundedQuantile_monotone _)
  intro r
  rw [boundedQuantile_stoploss,boundedQuantile_stoploss,weightedTrialLaw_integral w q (fun i => (hw i).le)]
  exact source_global_contact_limit_stoploss_along k P f p d w q hw hw1 hq δ α H c hc hmin hH hcover hs hlim hcap r

end Contact

variable (k : ℕ) (P : Measure BrownianPath) (g : Jet3) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P g.f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))
variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

variable (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)

include hc hmin hH hcover hs hlim hcap hq in
 theorem source_global_contact_control_order_along_oai [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) ≤
      controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1) := by
  obtain ⟨he,ht⟩ := source_global_contact_limit_tail_order_along k P g.f p d w q hw hw1 hq δ α H c
    hc hmin hH hcover hs hlim hcap
  have := weightedTrialLaw_probability w q (fun i => (hw i).le) hw1
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  rw [← he]
  apply sourceQuantile_control_tail_order P hB g _ _ (boundedQuantile_monotone _)
    (boundedQuantile_monotone _)
  simpa only [timeLaw_eq_volume] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along_oai := @OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along_oai
