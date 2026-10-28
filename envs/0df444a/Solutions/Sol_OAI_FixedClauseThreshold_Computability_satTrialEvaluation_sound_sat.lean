-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:11.610989+00:00
-- url     : https://prove2.me/submissions/9878e2f7-26f5-46aa-9d0d-bd9b84f1b8f9

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_DilutedSpinGlass_symmetric_trial_lower_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_finiteTrial_upper_fixedField_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_relaxedPoissonMinimum_subcritical_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

variable {n : ℕ}

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem logSumExp_stability {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (h : ∀ i, |f i-g i| ≤ C) :
    |Real.log (∑ i, Real.exp (f i)) - Real.log (∑ i, Real.exp (g i))| ≤ C := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+C) :
      Real.log (∑ i, Real.exp (f i)) ≤ Real.log (∑ i, Real.exp (g i)) + C := by
    have hb : (∑ i, Real.exp (f i)) ≤ (∑ i, Real.exp (g i))*Real.exp C := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (h i))
    have hl := Real.log_le_log (sum_exp_pos f) hb
    rwa [Real.log_mul (sum_exp_pos g).ne' (Real.exp_pos C).ne', Real.log_exp] at hl
  exact abs_le.mpr ⟨by have := aux g f (fun i => by have := (abs_le.mp (h i)).1; linarith); linarith,
    by have := aux f g (fun i => by have := (abs_le.mp (h i)).2; linarith); linarith⟩

theorem logWeight_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) :
    |logWeight theta h indices σ| ≤ (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta j).1 (fun l => σ (indices j l))))
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simp only [abs_mul, abs_spin, mul_one, le_refl]))

theorem logPartition_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    |logPartition theta h indices - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  have hs : Real.log (∑ _σ : Fin N → Spin, Real.exp (0:ℝ)) = (N:ℝ)*Real.log 2 := by
    simp only [Real.exp_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_fun, Fintype.card_fin, show Fintype.card Spin = 2 from rfl,
      Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  simpa only [logPartition, hs, sub_zero] using
    logSumExp_stability (logWeight theta h indices) (fun _ => 0)
      (fun σ => by simpa using logWeight_bound theta h indices σ)

theorem indexAverage_bound {p N k : ℕ} (hN : 0 < N)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    |indexAverage theta h - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hc : (0:ℝ) < Fintype.card (Fin k → Fin p → Fin N) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [indexAverage, div_sub' (ne_of_gt hc), abs_div,
    abs_of_pos hc, div_le_iff₀ hc]
  rw [show (∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) -
      (Fintype.card (Fin k → Fin p → Fin N):ℝ) * ((N:ℝ)*Real.log 2) =
        ∑ indices : Fin k → Fin p → Fin N,
          (logPartition theta h indices - (N:ℝ)*Real.log 2) by simp [Finset.sum_sub_distrib]]
  calc
    _ ≤ ∑ _indices : Fin k → Fin p → Fin N,
        ((∑ j, ‖(theta j).1‖) + ∑ i, |h i|) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun indices _ => logPartition_bound theta h indices))
    _ = _ := by simp [mul_comm, mul_add]

theorem continuous_logPartition {p N k : ℕ} (indices : Fin k → Fin p → Fin N) :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      logPartition z.1 z.2 indices) := by
  unfold logPartition
  apply Continuous.log
  · unfold logWeight
    fun_prop
  · intro z
    exact (sum_exp_pos _).ne'

theorem continuous_indexAverage {p N k : ℕ} :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      indexAverage z.1 z.2) := by
  unfold indexAverage
  exact (continuous_finsetSum _ (fun indices _ => continuous_logPartition indices)).div_const _


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalAverages
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

/-- Integrate a deterministic logarithmic stability estimate without imposing
moments beyond the integrable envelope. -/
theorem probabilistic_center_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f g : X → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hb : ∀ᵐ x ∂μ, |f x-c| ≤ g x) :
    Integrable f μ ∧ |(∫ x, f x ∂μ)-c| ≤ ∫ x, g x ∂μ := by
  have hfc : Integrable (fun x => f x-c) μ :=
    hg.mono' (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  have hfi : Integrable f μ := by
    simpa only [Pi.add_def, sub_add_cancel] using hfc.add (integrable_const c)
  refine ⟨hfi, ?_⟩
  have hi : (∫ x, f x ∂μ)-c = ∫ x, f x-c ∂μ := by
    rw [integral_sub hfi (integrable_const c)]
    simp
  rw [hi]
  exact abs_integral_le_integral_abs.trans (integral_mono_ae hfc.abs hg hb)

theorem indexAverage_integrable_and_fieldAverage_bound {p : ℕ} (M : Model p)
    (hM : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N k : ℕ}
    (hN : 0 < N) (theta : Fin k → InteractionSample p) :
    Integrable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) ∧
    |fieldAverage M (N := N) theta - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
  have hi : Integrable (fun h : Fin N → ℝ => ∑ i, |h i|)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) := by
    exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)
  have he : (∫ h : Fin N → ℝ, (∑ j, ‖(theta j).1‖) + ∑ i, |h i|
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)) =
        (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
    rw [integral_add (integrable_const _) hi, integral_finsetSum _
      (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)]
    simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM.aestronglyMeasurable]
    simp [fieldMoment]
  have hm : AEStronglyMeasurable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) :=
    (continuous_indexAverage.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  simpa only [fieldAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hm
      ((integrable_const _).add hi) (ae_of_all _ (indexAverage_bound hN theta))

theorem stronglyMeasurable_fieldAverage {p : ℕ} (M : Model p) (N k : ℕ) :
    StronglyMeasurable (fieldAverage M (N := N) (k := k)) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (continuous_indexAverage (p := p) (N := N) (k := k)).stronglyMeasurable.integral_prod_right

theorem fieldAverage_integrable_and_disorderAverage_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ}
    (hN : 0 < N) (k : ℕ) :
    Integrable (fieldAverage M (N := N) (k := k))
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) ∧
    |disorderAverage M N k - (N:ℝ)*Real.log 2| ≤
      k * interactionMoment M + N * fieldMoment M := by
  have hi : Integrable (fun theta : Fin k → InteractionSample p => ∑ j, ‖(theta j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
    integrable_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)
  have he : (∫ theta : Fin k → InteractionSample p,
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
        k * interactionMoment M + N * fieldMoment M := by
    rw [integral_add hi (integrable_const _), integral_finsetSum _
      (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
    simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable]
    simp [interactionMoment]
  simpa only [disorderAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (stronglyMeasurable_fieldAverage M N k).aestronglyMeasurable
      (hi.add (integrable_const _)) (ae_of_all _ (fun theta =>
        (indexAverage_integrable_and_fieldAverage_bound M hh hN theta).2))


theorem disorderAverage_integrable_and_pressure_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ} (hN : 0 < N) :
    Integrable (disorderAverage M N) (poissonMeasure (M.alpha * N)) ∧
      |pressure M N - Real.log 2| ≤ (M.alpha:ℝ) * interactionMoment M + fieldMoment M := by
  have hi : Integrable (fun k : ℕ => (k:ℝ) * interactionMoment M + N * fieldMoment M)
      (poissonMeasure (M.alpha * N)) :=
    ((poisson_integrable_count _).mul_const _).add (integrable_const _)
  have he : (∫ k : ℕ, (k:ℝ) * interactionMoment M + N * fieldMoment M
      ∂poissonMeasure (M.alpha * N)) =
      ((M.alpha:ℝ)*N) * interactionMoment M + N * fieldMoment M := by
    rw [integral_add ((poisson_integrable_count _).mul_const _) (integrable_const _),
      integral_mul_const, poisson_mean]
    simp
  have hb := probabilistic_center_bound (poissonMeasure (M.alpha * N))
    (f := disorderAverage M N) (c := (N:ℝ)*Real.log 2)
    StronglyMeasurable.of_discrete.aestronglyMeasurable hi
    (ae_of_all _ (fun k => (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).2))
  refine ⟨hb.1, ?_⟩
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hp : pressure M N = (∫ k, disorderAverage M N k ∂poissonMeasure (M.alpha * N)) / N := rfl
  rw [hp, div_sub' (ne_of_gt hNr), abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  rw [he] at hb
  nlinarith [hb.2]


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass

theorem edge_pos {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    0 < edge theta x := by
  have hb := (weighted_exp_bounds (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
    (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
    (product_q_sum x) (fun s => norm_le_pi_norm theta s)).1
  simpa only [edge, mul_comm] using (Real.exp_pos _).trans_le hb

/-- The message-free uniform edge bound, with only the physical interaction norm. -/
theorem log_edge_bound {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)| ≤ ‖theta‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta s)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MeasureHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyStabilityMeasurableSpace
local instance measureHierarchyStabilityBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (eta : ι → Hierarchy r) :
    |logMean r f m eta-logMean r g m eta| ≤ D := by
  induction r with
  | zero => exact hD eta
  | succ r ih =>
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_stability (ProbabilityMeasure.pi eta).toMeasure (hm 0)
      hfc.measurable hgc.measurable hfb hgb (ih (fun i => m i.succ) (fun i => hm i.succ))

theorem trialLog_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m f-trialLog r ζ m g| ≤ D := by
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC m hm
  let μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure
  have hiF : Integrable (logMean r f m) μ := MeasureMean.bounded_integrable μ hfc.measurable hfb
  have hiG : Integrable (logMean r g m) μ := MeasureMean.bounded_integrable μ hgc.measurable hgb
  change |(∫ eta, logMean r f m eta ∂μ)-(∫ eta, logMean r g m eta ∂μ)| ≤ D
  rw [← integral_sub hiF hiG]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun eta =>
      (show ‖logMean r f m eta - logMean r g m eta‖ ≤ D from by
        simpa only [Real.norm_eq_abs] using logMean_stability r f g hf hg hB hC hD m hm eta)))

 theorem continuous_edge {p : ℕ} (theta : Interaction p) : Continuous (edge theta) := by
  unfold edge
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))

 theorem continuous_log_edge {p : ℕ} (theta : Interaction p) :
    Continuous (fun x => Real.log (edge theta x)) :=
  (continuous_edge theta).log (fun x => (edge_pos theta x).ne')

end DilutedSpinGlass

namespace DilutedSpinGlass

theorem weighted_exp_pos {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    0 < ∑ i, w i * Real.exp (f i) :=
  (Real.exp_pos (-‖f‖)).trans_le
    (weighted_exp_bounds w f hw hs (fun i => norm_le_pi_norm f i)).1

/-- Stability before any disorder averaging; no lower bound on the positive
message probabilities or moment condition on the messages occurs. -/
theorem weighted_log_exp_stability {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {D : ℝ}
    (hD : ∀ i, |f i-g i| ≤ D) :
    |Real.log (∑ i, w i * Real.exp (f i)) -
      Real.log (∑ i, w i * Real.exp (g i))| ≤ D := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+D) :
      Real.log (∑ i, w i * Real.exp (f i)) ≤
        Real.log (∑ i, w i * Real.exp (g i)) + D := by
    have hle : (∑ i, w i * Real.exp (f i)) ≤
        (∑ i, w i * Real.exp (g i)) * Real.exp D := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hw i))
    have hl := Real.log_le_log (weighted_exp_pos w f hw hs) hle
    rw [Real.log_mul (weighted_exp_pos w g hw hs).ne' (Real.exp_pos D).ne', Real.log_exp] at hl
    exact hl
  have hfg := aux f g (fun i => by have h := (abs_le.mp (hD i)).2; linarith)
  have hgf := aux g f (fun i => by have h := (abs_le.mp (hD i)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_edge_stability {p : ℕ} (theta theta' : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)-Real.log (edge theta' x)| ≤ ‖theta-theta'‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_stability (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta theta'
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') s)

theorem message_stability {p : ℕ} (theta theta' : Interaction p)
    (x : Fin (p-1) → ℝ) (ε : Spin) :
    |message theta x ε-message theta' x ε| ≤ ‖theta-theta'‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_stability (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε)) (fun s => theta' (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') (appendSpin s ε))

theorem siteLog_stability {p k : ℕ} (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x - siteLog theta' h' x| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
  have hf : ∀ ε : Spin,
      |(h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)| ≤
        |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
    intro ε
    rw [show (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε) =
        (h-h') * spin ε + ∑ j, (message (theta j).1 (fun l => x (j,l)) ε -
          message (theta' j).1 (fun l => x (j,l)) ε) by rw [Finset.sum_sub_distrib]; ring]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_stability _ _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_stability (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun ε => h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

theorem trial_edge_stability {p : ℕ} (r : ℕ) (theta theta' : Interaction p)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (fun x => Real.log (edge theta x)) -
      trialLog r ζ m (fun x => Real.log (edge theta' x))| ≤ ‖theta-theta'‖ :=
  trialLog_stability r _ _ (continuous_log_edge theta) (continuous_log_edge theta')
    (log_edge_bound theta) (log_edge_bound theta') (log_edge_stability theta theta') m hm ζ

theorem trial_site_stability {p k : ℕ} (r : ℕ)
    (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (siteLog theta h)-trialLog r ζ m (siteLog theta' h')| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ :=
  trialLog_stability r _ _ (continuous_siteLog theta h) (continuous_siteLog theta' h')
    (siteLog_bound theta h) (siteLog_bound theta' h') (siteLog_stability theta theta' h h') m hm ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteHierarchyDense
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

lemma atomicProbability_reindex {X ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : ι → X) (w : AtomicWeights ι) :
    atomicProbability (fun j => x (e.symm j))
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩ =
      atomicProbability x w := by
  apply Subtype.ext
  change (∑ j : κ,(w.val (e.symm j):ℝ≥0∞) • Measure.dirac (x (e.symm j))) = _
  exact e.symm.sum_comp (fun i => (w.val i:ℝ≥0∞) • Measure.dirac (x i))

lemma continuous_atomicProbability_atoms {X ι : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (w : AtomicWeights ι) :
    Continuous (fun x : ι → X => atomicProbability x w) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (f.continuous.comp (continuous_apply i)))

/-- Finite laws supported on any dense set are weakly dense. -/
lemma finite_atomic_dense {X : Type} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (D : Set X) (hD : Dense D) :
    Dense {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w} := by
  classical
  let S := {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w}
  have ha (ι : Type) [Fintype ι] (x : ι → X) (w : AtomicWeights ι) :
      atomicProbability x w ∈ closure S := by
    have hd : Dense (Set.univ.pi (fun _ : ι => D)) := dense_pi Set.univ (fun _ _ => hD)
    obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (hd x)
    apply isClosed_closure.mem_of_tendsto ((continuous_atomicProbability_atoms w).tendsto x |>.comp ht)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι,fun j => z n (e.symm j),
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩,?_,?_⟩
    · intro j
      exact hz n (e.symm j) (Set.mem_univ _)
    · exact (atomicProbability_reindex e (z n) w).symm
  intro μ
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ h.approx h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := simple_map_atomic (h.approx n) μ
  rw [← hw]
  exact ha _ _ w

attribute [local instance] OAI.DilutedSpinGlass.finiteHierarchyDenseMeasurableSpace
local instance finiteHierarchyDenseBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma finiteHierarchy_dense (r : ℕ) : Dense {ζ : Hierarchy r | FiniteHierarchy r ζ} := by
  induction r with
  | zero => simpa only [FiniteHierarchy,Set.ofPred_true] using (dense_univ : Dense (Set.univ : Set (Hierarchy 0)))
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    let : SeparableSpace (Hierarchy r) := (hierarchy_properties r).2
    exact finite_atomic_dense {ζ : Hierarchy r | FiniteHierarchy r ζ} ih

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TopologyDecay
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {Ω β : Type} [Fintype Ω] [Fintype β]

attribute [local instance] OAI.DilutedSpinGlass.finiteMapDecEq
lemma expect_map (P : FiniteLaw Ω) (f : Ω → β) (g : β → ℝ) :
    (P.map f).expect g=P.expect (fun a => g (f a)) := by
  classical
  change (∑ b, P.expect (fun a => if f a=b then 1 else 0)*g b)=_
  simp_rw [← expect_mul_right]
  rw [← expect_fintype_sum]
  apply expect_congr
  intro a
  simp

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TrialPhysical
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators NNReal

lemma trial_edge_lipschitz {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith 1 (fun θ : Interaction p => trialLog r ζ m (fun x => Real.log (edge θ x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ θ'
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using trial_edge_stability r θ θ' m hm ζ

lemma trial_site_lipschitz {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith (k+1) (fun z : (Fin k → InteractionSample p) × ℝ => trialLog r ζ m (siteLog z.1 z.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq]
  have h1 : |z.2-w.2|≤dist z w := by
    change |z.2-w.2|≤ max (dist z.1 w.1) (dist z.2 w.2)
    simpa only [Real.dist_eq] using le_max_right (dist z.1 w.1) (dist z.2 w.2)
  have h2 : ∑ j,‖(z.1 j).1-(w.1 j).1‖≤(k:ℝ)*dist z w := by
    calc
      _ ≤ ∑ j : Fin k,dist z w := Finset.sum_le_sum (fun j _ => by
        rw [← dist_eq_norm]
        exact (show dist (z.1 j).1 (w.1 j).1≤dist (z.1 j) (w.1 j) from le_max_left _ _).trans
          ((dist_le_pi_dist z.1 w.1 j).trans (show dist z.1 w.1≤dist z w from le_max_left _ _)))
      _ = _ := by simp
  have h := trial_site_stability r z.1 w.1 z.2 w.2 m hm ζ
  push_cast
  nlinarith

lemma trial_edge_bound {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Interaction p) :
    |trialLog r ζ m (fun x => Real.log (edge θ x))|≤‖θ‖ :=
  (trialLog_continuous_bound r _ (continuous_log_edge θ) (log_edge_bound θ) m hm).2 ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FunctionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)

include hm in
lemma integrable_trial_site_field (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    Integrable (fun h => trialLog r ζ m (siteLog θ h)) M.field.toMeasure := by
  apply (hh.add (integrable_const (∑ j,‖(θ j).1‖))).mono'
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)

include hm in
lemma trialSiteField_bound (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    |trialSiteField M m ζ θ|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖ := by
  have hb := norm_integral_le_of_norm_le (f := fun h => trialLog r ζ m (siteLog θ h)) (hh.add (integrable_const (∑ j,‖(θ j).1‖)))
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteField,Real.norm_eq_abs,integral_add hh (integrable_const _),integral_const,
    probReal_univ,one_smul] using hb

include hm in
lemma stronglyMeasurable_trialSiteField (ζ : Hierarchy (r+1)) (k : ℕ) :
    StronglyMeasurable (trialSiteField M m (k := k) ζ) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((trial_site_lipschitz (p := p) (k := k) r m hm ζ).continuous.stronglyMeasurable).integral_prod_right

include hm in
lemma trialSiteField_continuous {k : ℕ} (θ : Fin k → InteractionSample p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteField M m ζ θ) := by
  apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j,‖(θ j).1‖)
  · intro ζ
    exact (integrable_trial_site_field M m hm hh ζ θ).aestronglyMeasurable
  · intro ζ
    exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)
  · exact hh.add (integrable_const _)
  · exact ae_of_all _ (fun h => (trialLog_continuous_bound r _ (continuous_siteLog θ h)
      (siteLog_bound θ h) m hm).1)

lemma interaction_sum_integrable (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    Integrable (fun θ : Fin k → InteractionSample p => ∑ j,‖(θ j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)

lemma integral_interaction_sum (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    (∫ θ : Fin k → InteractionSample p,∑ j,‖(θ j).1‖ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

include hm in
lemma trialSiteDisorder_bound (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    |trialSiteDisorder M m ζ k|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  have hb := norm_integral_le_of_norm_le (f := trialSiteField M m (k := k) ζ) ((integrable_const _).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteDisorder,Real.norm_eq_abs,integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k] using hb

include hm in
lemma trialSiteDisorder_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteDisorder M m ζ k) := by
  apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
    (∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖)
  · intro ζ; exact (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)
  · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
  · exact ae_of_all _ (fun θ => trialSiteField_continuous M m hm θ hh)

include hm in
lemma functional_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => functional M r ζ m) := by
  have hs : Continuous (fun ζ : Hierarchy (r+1) => ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure))
    · intro ζ; exact (measurable_of_countable _).aestronglyMeasurable
    · intro ζ; exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteDisorder_bound M m hm hθ hh ζ k)
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ (trialSiteDisorder_continuous M m hm hθ hh)
  have he : Continuous (fun ζ : Hierarchy (r+1) => ∫ θ : InteractionSample p,
      trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro ζ
      exact (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_edge_bound r m hm ζ θ.1)
    · exact hθ
    · exact ae_of_all _ (fun θ => (trialLog_continuous_bound r _ (continuous_log_edge θ.1) (log_edge_bound θ.1) m hm).1)
  exact (continuous_const.add hs).sub (continuous_const.mul he)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RealEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
local instance realEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

namespace FiniteLaw
lemma asProbability_map {Ω Λ X : Type} [Fintype Ω] [Fintype Λ]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [MetrizableSpace X]
    (P : FiniteLaw Ω) (f : Ω → Λ) (v : Λ → X) :
    (P.map f).asProbability v = P.asProbability (fun x => v (f x)) := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  apply Subtype.ext
  change ((P.map f).asProbability v).toMeasure = (P.asProbability (fun x => v (f x))).toMeasure
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  simp only [integral_asProbability,expect_map]
end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
lemma realEncode_embed (f : Ω → Λ) (g : Λ → Ω)
    (h : Function.LeftInverse g f) (r : ℕ) (T : KernelTower Ω r)
    (V : FinitePath Ω r → ℝ) :
    realEncode r (embed f g r T) (fun y => V (pathMap g r y)) = realEncode r T V := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω r) at T
    change (Ω × FinitePath Ω r) → ℝ at V
    rcases T with ⟨P,Q⟩
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    change (P.map f).asProbability (fun a => realEncode r (embed f g r (Q (g a)))
      (fun y => V (g a,pathMap g r y))) =
      P.asProbability (fun a => realEncode r (Q a) (fun y => V (a,y)))
    have hc (a : Λ) := ih (Q (g a)) (fun y => V (g a,y))
    simp_rw [hc]
    rw [FiniteLaw.asProbability_map]
    congr 1
    funext a
    rw [h a]

end KernelTower

/-- Every genuinely finitely branching measure hierarchy has a finite alphabet
realization. Padding changes no law; in particular this imposes no restriction
on the original variational class after density. -/
lemma finiteHierarchy_realization (r : ℕ) (ζ : Hierarchy r) (hζ : FiniteHierarchy r ζ) :
    ∃ (n : ℕ) (_hn : 0 < n) (T : KernelTower (Fin n) r) (V : FinitePath (Fin n) r → ℝ),
      KernelTower.realEncode r T V = ζ := by
  classical
  induction r with
  | zero => exact ⟨1,by omega,(),fun _ => ζ,rfl⟩
  | succ r ih =>
    obtain ⟨k,x,w,hx,rfl⟩ := hζ
    choose n hn T V hV using fun i => ih (x i) (hx i)
    let P : FiniteLaw (Fin k) := ⟨fun i => w.val i,fun i => (w.val i).coe_nonneg,
      by simpa only [NNReal.coe_sum,NNReal.coe_one] using congrArg ((↑) : ℝ≥0 → ℝ) w.property⟩
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k=0 := by omega
      subst k
      have hh := P.total
      simp at hh
    let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
    let (i : Fin k) : Nonempty (Fin (n i)) := ⟨⟨0,hn i⟩⟩
    let d : (i : Fin k) → Fin (n i) := fun i => ⟨0,hn i⟩
    let Ω := Fin k × ((i : Fin k) → Fin (n i))
    let f (i : Fin k) (a : Fin (n i)) : Ω := (i,Function.update d i a)
    let g (i : Fin k) (a : Ω) : Fin (n i) := a.2 i
    have hgf (i : Fin k) : Function.LeftInverse (g i) (f i) := by
      intro a
      exact Function.update_self i a d
    let U : KernelTower Ω (r+1) :=
      (P.map (fun i => (i,d)), fun a => KernelTower.embed (f a.1) (g a.1) r (T a.1))
    let W : FinitePath Ω (r+1) → ℝ := fun y =>
      V y.1.1 (KernelTower.pathMap (g y.1.1) r y.2)
    have hU : KernelTower.realEncode (r+1) U W = atomicProbability x w := by
      let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
      change (P.map (fun i => (i,d))).asProbability (fun a =>
        KernelTower.realEncode r (KernelTower.embed (f a.1) (g a.1) r (T a.1))
          (fun y => V a.1 (KernelTower.pathMap (g a.1) r y))) = _
      simp_rw [KernelTower.realEncode_embed _ _ (hgf _),hV]
      rw [FiniteLaw.asProbability_map]
      congr 1
    let e := Fintype.equivFin Ω
    refine ⟨Fintype.card Ω,Fintype.card_pos,
      KernelTower.embed e e.symm (r+1) U,
      fun y => W (KernelTower.pathMap e.symm (r+1) y),?_⟩
    rw [KernelTower.realEncode_embed e e.symm e.symm_apply_apply]
    exact hU

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_IntegralError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integrable_pi_sum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ) :
    Integrable (fun x : ι → X => ∑ i,g (x i)) (Measure.pi (fun _ : ι => μ)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : ι => μ) hg)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FunctionalStability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ d,0 < m d) (ζ : Hierarchy (r+1))

include hm

lemma trialDisorderAt_measurable (k : ℕ) : Measurable (trialDisorderAt M m ζ k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (trial_site_lipschitz r m hm ζ).continuous.stronglyMeasurable.integral_prod_left.measurable

lemma trialDisorderAt_bound
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : ℝ) : |trialDisorderAt M m ζ k h|≤|h|+k*interactionMoment M := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p => trialLog r ζ m (siteLog z h))
    ((integrable_const |h|).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z h)))
  simpa only [trialDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

lemma trialSite_integrable_prod
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×ℝ => trialLog r ζ m (siteLog z.1 z.2))
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply ((hh.comp_snd _).add ((interaction_sum_integrable M hθ k).comp_fst _)).mono'
    (trial_site_lipschitz r m hm ζ).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z.1 z.2))

lemma trialDisorderAt_integral
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h,trialDisorderAt M m ζ k h ∂M.field.toMeasure)=trialSiteDisorder M m ζ k :=
  (integral_integral_swap (trialSite_integrable_prod M m hm ζ hθ hh k)).symm

lemma trialDisorderAt_joint_integrable
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    Integrable (fun z : ℕ×ℝ => trialDisorderAt M m ζ z.1 z.2)
      ((poissonMeasure t).prod M.field.toMeasure) := by
  apply ((hh.comp_snd _).add (((poisson_integrable_count t).mul_const (interactionMoment M)).comp_fst _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => trialDisorderAt_measurable M m hm ζ k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trialDisorderAt_bound M m hm ζ hθ z.1 z.2))

lemma trialPoisson_field_order
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    (∫ h,∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure t ∂M.field.toMeasure)=
      ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure t := by
  rw [← integral_integral_swap (trialDisorderAt_joint_integrable M m hm ζ hθ hh t)]
  simp_rw [trialDisorderAt_integral M m hm ζ hθ hh]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePoissonSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalFieldOrder
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p N : ℕ} [NeZero N]

lemma centeredDisorderAt_bound (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : Fin N → ℝ) :
    |centeredDisorderAt M k h|≤k*interactionMoment M+∑ i,|h i| := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p =>
      indexAverage z h-(N:ℝ)*Real.log 2)
    ((interaction_sum_integrable M hθ k).add (integrable_const (∑ i,|h i|)))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z h)))
  simpa only [centeredDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (interaction_sum_integrable M hθ k) (integrable_const _),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

omit [NeZero N] in
lemma centeredDisorderAt_measurable (M : Model p) (k : ℕ) :
    Measurable (centeredDisorderAt (N := N) M k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).stronglyMeasurable.integral_prod_left.measurable

lemma centeredIndex_integrable_prod (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×(Fin N → ℝ) =>
      indexAverage z.1 z.2-(N:ℝ)*Real.log 2)
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod
        (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply (((interaction_sum_integrable M hθ k).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
    ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z.1 z.2))

lemma centeredDisorderAt_integral (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h : Fin N → ℝ,centeredDisorderAt M k h ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
      disorderAverage M N k-(N:ℝ)*Real.log 2 := by
  simp only [centeredDisorderAt]
  rw [← integral_integral_swap (centeredIndex_integrable_prod M hθ hh k)]
  simp_rw [integral_sub (indexAverage_integrable_and_fieldAverage_bound M hh (NeZero.pos N) _).1
    (integrable_const _),integral_const,probReal_univ,one_smul]
  simpa only [fieldAverage,disorderAverage,integral_const,probReal_univ,one_smul] using
    (integral_sub (fieldAverage_integrable_and_disorderAverage_bound M hθ hh (NeZero.pos N) k).1
      (integrable_const ((N:ℝ)*Real.log 2)))

lemma centeredDisorderAt_joint_integrable (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (r : ℝ≥0) :
    Integrable (fun z : ℕ×(Fin N → ℝ) => centeredDisorderAt M z.1 z.2)
      ((poissonMeasure r).prod (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  apply ((((poisson_integrable_count r).mul_const (interactionMoment M)).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => centeredDisorderAt_measurable M k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (centeredDisorderAt_bound M hθ z.1 z.2))

lemma centeredPressure_field_order (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    (∫ h : Fin N → ℝ,∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N)
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
        (N:ℝ)*(pressure M N-Real.log 2) := by
  rw [← integral_integral_swap (centeredDisorderAt_joint_integrable M hθ hh (M.alpha*N))]
  simp_rw [centeredDisorderAt_integral M hθ hh]
  rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh (NeZero.pos N)).1
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  change (∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))-(N:ℝ)*Real.log 2=
    (N:ℝ)*((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))/(N:ℝ)-Real.log 2)
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  field_simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PressureLiminf
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter

lemma pressure_bounded {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    IsBoundedUnder (· ≤ ·) atTop (pressure M) ∧ IsBoundedUnder (· ≥ ·) atTop (pressure M) := by
  have he : ∀ᶠ N in atTop, |pressure M N-Real.log 2| ≤ (M.alpha:ℝ)*interactionMoment M+fieldMoment M := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (disorderAverage_integrable_and_pressure_bound M hθ hh hN).2
  constructor
  · apply isBoundedUnder_of_eventually_le (a := Real.log 2+(M.alpha:ℝ)*interactionMoment M+fieldMoment M)
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).2]
  · apply isBoundedUnder_of_eventually_ge (a := Real.log 2-((M.alpha:ℝ)*interactionMoment M+fieldMoment M))
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).1]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RawPatternIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma rawReplicaMoment_eq_product {p n : ℕ} (M : Model p)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    rawReplicaMoment M P=∫ z : InteractionSample p,(-z.2.2.1)^n*
      ∏ l : Fin p,(P l).expect (fun s => ∏ a : Fin n,z.2.2.2 l (s a)) ∂M.disorder.toMeasure := by
  unfold rawReplicaMoment
  apply integral_congr_ae
  filter_upwards [] with z
  have he (s : Fin p → Fin n → Spin) :
      (∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,z.2.2.2 l (s l a))=
        (-z.2.2.1)^n*∏ l : Fin p,∏ a : Fin n,z.2.2.2 l (s l a) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Finset.prod_comm]
  simp_rw [he]
  rw [FiniteLaw.expect_mul_left]
  congr 1
  exact FiniteLaw.expect_pi_product P (fun l s => ∏ a : Fin n,z.2.2.2 l (s a))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATModel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem literalFactor_nonneg (sign value : Bool) : 0 ≤ literalFactor sign value := by
  unfold literalFactor
  split <;> norm_num

theorem product_literalFactor (J s : Fin 3 → Bool) :
    (∏ l, literalFactor (J l) (s l)) = if ∀ l, s l ≠ J l then 1 else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_eq_one
    intro l _
    simp [literalFactor, h l]
  · obtain ⟨l, hl⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp only [not_not] at hl
    simp [literalFactor, hl]

theorem satSample_factorization (β : ℝ) (J s : Fin 3 → Bool) :
    Real.exp ((satSample β J).1 s) =
      (satSample β J).2.1 *
        (1 + (satSample β J).2.2.1 * ∏ l, (satSample β J).2.2.2 l (s l)) := by
  simp only [satSample, satInteraction, product_literalFactor]
  split_ifs <;> simp

theorem satSample_product_bound {β : ℝ} (hβ : 0 < β) (J s : Fin 3 → Bool) :
    |(satSample β J).2.2.1 * ∏ l, (satSample β J).2.2.2 l (s l)| < 1 := by
  have he : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-β)
  simp only [satSample, product_literalFactor]
  split_ifs
  · rw [mul_one, abs_of_neg (by linarith)]
    linarith
  · norm_num

theorem satModel_supported (a : ℝ≥0) (β : ℝ) :
    ∀ᵐ z ∂(satModel a β).disorder.toMeasure, ∃ J, satSample β J = z := by
  have h := ae_map_mem_range (satSample β) (Set.finite_range _).measurableSet signLaw.toMeasure
  simpa [satModel, ProbabilityMeasure.toMeasure_map] using h

theorem satModel_interaction_integrable (a : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (fun z : InteractionSample 3 => ‖z.1‖) (satModel a β).disorder.toMeasure := by
  apply Integrable.of_bound (by fun_prop) β
  filter_upwards [satModel_supported a β] with z hz
  obtain ⟨J, rfl⟩ := hz
  simpa only [norm_norm, satSample] using satInteraction_norm_le hβ J

theorem satModel_field_integrable (a : ℝ≥0) (β : ℝ) :
    Integrable (fun h : ℝ => |h|) (satModel a β).field.toMeasure := by
  change Integrable (fun h : ℝ => |h|) (Measure.dirac 0)
  exact integrable_dirac (by simp)

theorem signLaw_equiv (e : (Fin 3 → Bool) ≃ (Fin 3 → Bool)) :
    Measure.map e signLaw.toMeasure = signLaw.toMeasure := by
  apply Measure.ext_of_singleton
  intro J
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton J)]
  have he : e ⁻¹' {J} = {e.symm J} := by
    ext K
    change e K = J ↔ K = e.symm J
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      simpa using congrArg e h
  rw [he]
  change (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {e.symm J} =
    (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {J}
  rw [PMF.toMeasure_apply_singleton, PMF.toMeasure_apply_singleton] <;> simp

theorem satInteraction_permute (β : ℝ) (e : Equiv.Perm (Fin 3)) (J s : Fin 3 → Bool) :
    satInteraction β J (fun l => s (e l)) =
      satInteraction β (permuteSigns e J) s := by
  have h : (∀ l, s (e l) ≠ J l) ↔ ∀ l, s l ≠ J (e.symm l) := by
    constructor
    · intro h l
      simpa using h (e.symm l)
    · intro h l
      simpa using h (e l)
  simp only [satInteraction, permuteSigns, Equiv.coe_fn_mk]
  exact if_congr h rfl rfl

theorem satModel_symmetric (a : ℝ≥0) (β : ℝ) (e : Equiv.Perm (Fin 3)) :
    IdentDistrib (fun z : InteractionSample 3 => z.1)
      (fun z : InteractionSample 3 => fun s : Fin 3 → Spin => z.1 (fun l => s (e l)))
      (satModel a β).disorder.toMeasure (satModel a β).disorder.toMeasure := by
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map (satSample β) signLaw.toMeasure) =
      Measure.map _ (Measure.map (satSample β) signLaw.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_of_countable _),
      Measure.map_map (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop) (measurable_of_countable _)]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (fun J => fun s => satInteraction β J (fun l => s (e l))) signLaw.toMeasure
    simp_rw [satInteraction_permute]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (satInteraction β ∘ permuteSigns e) signLaw.toMeasure
    rw [← Measure.map_map (measurable_of_countable (satInteraction β))
      (measurable_of_countable (permuteSigns e)), signLaw_equiv]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SignLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem signLaw_eq_pi :
    signLaw.toMeasure = Measure.pi (fun _ : Fin 3 =>
      (PMF.uniformOfFintype Bool).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro J
  norm_num [signLaw, Measure.pi_singleton, PMF.uniformOfFintype_apply, ← ENNReal.inv_pow]

theorem signLaw_integral (f : (Fin 3 → Bool) → ℝ) :
    (∫ J, f J ∂signLaw.toMeasure) = (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect f := by
  change (∫ J, f J ∂(PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp [FiniteLaw.expect, FiniteLaw.uniform]

theorem signLaw_product (f : Fin 3 → Bool → ℝ) :
    (∫ J, (∏ l, f l (J l)) ∂signLaw.toMeasure) =
      ∏ l, (FiniteLaw.uniform : FiniteLaw Bool).expect (f l) := by
  rw [signLaw_integral, uniformFiniteLaw_pi, FiniteLaw.expect_pi_product]

theorem signLaw_independent :
    iIndepFun (fun l (J : Fin 3 → Bool) => literalFactor (J l)) signLaw.toMeasure := by
  rw [signLaw_eq_pi]
  exact iIndepFun_pi (fun _ => (measurable_of_countable literalFactor).aemeasurable)

theorem satModel_independent (a : ℝ≥0) (β : ℝ) :
    iIndepFun (fun l (z : InteractionSample 3) => z.2.2.2 l)
      (satModel a β).disorder.toMeasure := by
  have hm (l : Fin 3) : Measurable (fun z : InteractionSample 3 => z.2.2.2 l) := by
    fun_prop
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun l => (hm l).aemeasurable)]
  change Measure.map (fun z : InteractionSample 3 => fun l => z.2.2.2 l)
      (Measure.map (satSample β) signLaw.toMeasure) =
    Measure.pi (fun l => Measure.map (fun z : InteractionSample 3 => z.2.2.2 l)
      (Measure.map (satSample β) signLaw.toMeasure))
  rw [Measure.map_map (Measurable.of_eval hm) (measurable_of_countable _)]
  simp_rw [Measure.map_map (hm _) (measurable_of_countable (satSample β))]
  exact signLaw_independent.map_fun_eq_pi_map
    (fun _ => (measurable_of_countable _).aemeasurable)

theorem satModel_identically_distributed (a : ℝ≥0) (β : ℝ) (l j : Fin 3) :
    IdentDistrib (fun z : InteractionSample 3 => z.2.2.2 l)
      (fun z : InteractionSample 3 => z.2.2.2 j)
      (satModel a β).disorder.toMeasure (satModel a β).disorder.toMeasure := by
  have hm (i : Fin 3) : Measurable (fun z : InteractionSample 3 => z.2.2.2 i) := by
    fun_prop
  refine ⟨(hm l).aemeasurable, (hm j).aemeasurable, ?_⟩
  change Measure.map _ (Measure.map (satSample β) signLaw.toMeasure) =
    Measure.map _ (Measure.map (satSample β) signLaw.toMeasure)
  rw [Measure.map_map (hm l) (measurable_of_countable _),
    Measure.map_map (hm j) (measurable_of_countable _), signLaw_eq_pi]
  change Measure.map (literalFactor ∘ (fun J : Fin 3 → Bool => J l)) _ =
    Measure.map (literalFactor ∘ (fun J : Fin 3 → Bool => J j)) _
  rw [← Measure.map_map (measurable_of_countable literalFactor) (measurable_pi_apply l),
    ← Measure.map_map (measurable_of_countable literalFactor) (measurable_pi_apply j),
    (measurePreserving_eval _ l).map_eq, (measurePreserving_eval _ j).map_eq]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedPressure
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem satModel_logWeight {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool)
    (s : Fin n → Bool) :
    logWeight (fun j => satSample β (signs j)) (fun _ => 0) indices s =
      -β * relaxedViolations s indices signs := by
  classical
  have h (j : Fin m) : satInteraction β (signs j) (fun l => s (indices j l)) =
      -β * (if ¬relaxedClauseSatisfied s (indices j) (signs j) then 1 else 0) := by
    simp [satInteraction, relaxedClauseSatisfied, not_exists]
  simp only [logWeight, satSample, zero_mul, Finset.sum_const_zero, add_zero, h,
    ← Finset.mul_sum]
  congr 1
  simp only [relaxedViolations, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, ite_not, apply_ite, Nat.cast_one, Nat.cast_zero]

theorem satModel_logPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    DilutedSpinGlass.logPartition (fun j => satSample β (signs j)) (fun _ => 0) indices =
      relaxedLogPartition β indices signs := by
  simp only [DilutedSpinGlass.logPartition, satModel_logWeight,
    relaxedLogPartition, relaxedPartition]

theorem zeroField_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ h, f h ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))) =
      f (fun _ => 0) := by
  have h : (fun h : Fin n → ℝ => fun i => h i) =ᵐ[
      Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))] (fun _ => fun _ => 0) :=
    Measure.ae_eq_pi (fun _ => ae_eq_dirac (fun x : ℝ => x))
  calc
    _ = ∫ _h, f (fun _ => 0) ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [h] with h hh
      exact congrArg f hh
    _ = _ := by simp

theorem signLaw_pi_integral (m : ℕ) (f : (Fin m → Fin 3 → Bool) → ℝ) :
    (∫ J, f J ∂Measure.pi (fun _ : Fin m => signLaw.toMeasure)) =
      (∑ J, f J) / Fintype.card (Fin m → Fin 3 → Bool) := by
  have he : Measure.pi (fun _ : Fin m => signLaw.toMeasure) =
      (PMF.uniformOfFintype (Fin m → Fin 3 → Bool)).toMeasure := by
    apply Measure.ext_of_singleton
    intro J
    simp [Measure.pi_singleton, signLaw, Nat.cast_pow,
      ENNReal.inv_pow]
  rw [he, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv]
  ring

theorem disorder_pi_integral (a : ℝ≥0) (β : ℝ) (m : ℕ)
    (f : (Fin m → InteractionSample 3) → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂Measure.pi (fun _ : Fin m => (satModel a β).disorder.toMeasure)) =
      (∑ J : Fin m → Fin 3 → Bool, f (fun j => satSample β (J j))) /
        Fintype.card (Fin m → Fin 3 → Bool) := by
  change (∫ z, f z ∂Measure.pi (fun _ : Fin m =>
    Measure.map (satSample β) signLaw.toMeasure)) = _
  rw [← Measure.pi_map_pi (fun _ : Fin m =>
    (measurable_of_countable (satSample β)).aemeasurable)]
  rw [integral_map (measurable_of_countable (fun J : Fin m → Fin 3 → Bool =>
    fun j => satSample β (J j))).aemeasurable
    hf.aestronglyMeasurable]
  exact signLaw_pi_integral m _

theorem satModel_pressure (a : ℝ≥0) (β : ℝ) (n : ℕ) :
    pressure (satModel a β) n = relaxedPoissonPressure a β n := by
  unfold pressure relaxedPoissonPressure
  congr 1
  apply integral_congr_ae
  filter_upwards [] with m
  change (∫ z : Fin m → InteractionSample 3,
      ∫ h : Fin n → ℝ,
        (∑ indices : Fin m → Fin 3 → Fin n, DilutedSpinGlass.logPartition z h indices) /
          Fintype.card (Fin m → Fin 3 → Fin n)
        ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))
      ∂Measure.pi (fun _ : Fin m => (satModel a β).disorder.toMeasure)) = _
  simp_rw [zeroField_integral]
  rw [disorder_pi_integral a β m _ (by
    unfold DilutedSpinGlass.logPartition logWeight
    fun_prop)]
  simp only [satModel_logPartition, relaxedFixedLogPartition]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped BigOperators

theorem relaxedMinimum_attained {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    ∃ s, relaxedViolations s indices signs = relaxedMinimumViolations indices signs := by
  unfold relaxedMinimumViolations
  exact Nat.find_spec (p := fun v => ∃ s, relaxedViolations s indices signs = v) _

theorem relaxedMinimum_le {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) (s : Fin n → Bool) :
    relaxedMinimumViolations indices signs ≤ relaxedViolations s indices signs :=
  Nat.find_min' _ ⟨s, rfl⟩

theorem relaxedLogPartition_lower {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    -β * relaxedMinimumViolations indices signs ≤ relaxedLogPartition β indices signs := by
  obtain ⟨s, hs⟩ := relaxedMinimum_attained indices signs
  have he : Real.exp (-β * relaxedMinimumViolations indices signs) ≤
      relaxedPartition β indices signs := by
    rw [← hs]
    exact Finset.single_le_sum (fun a _ =>
      (Real.exp_pos (-β * relaxedViolations a indices signs)).le) (Finset.mem_univ s)
  have := Real.log_le_log (Real.exp_pos _) he
  simpa only [Real.log_exp, relaxedLogPartition] using this

theorem relaxedLogPartition_upper {n m : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    relaxedLogPartition β indices signs ≤
      n * Real.log 2 - β * relaxedMinimumViolations indices signs := by
  have hb : relaxedPartition β indices signs ≤ (2 : ℝ)^n *
      Real.exp (-β * relaxedMinimumViolations indices signs) := by
    calc
      _ ≤ ∑ _s : Fin n → Bool, Real.exp (-β * relaxedMinimumViolations indices signs) := by
        apply Finset.sum_le_sum
        intro s _
        apply Real.exp_le_exp.mpr
        have h : (relaxedMinimumViolations indices signs : ℝ) ≤
            relaxedViolations s indices signs := by exact_mod_cast relaxedMinimum_le indices signs s
        nlinarith
      _ = _ := by simp
  have hz : 0 < relaxedPartition β indices signs :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h := Real.log_le_log hz hb
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h
  simpa only [relaxedLogPartition, sub_eq_add_neg, neg_mul] using h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RootEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem clauseMinimum_le_length {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs ≤ m := by
  exact (relaxedMinimum_le _ _ (fun _ => false)).trans
    ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_AuxiliaryEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem relaxedFixedMinimum_nonneg (n m : ℕ) : 0 ≤ relaxedFixedMinimum n m :=
  uniformMean_nonneg (fun _ => Nat.cast_nonneg _)

theorem relaxedFixedMinimum_le (n m : ℕ) [NeZero n] : relaxedFixedMinimum n m ≤ m := by
  calc
    _ ≤ uniformMean (fun _cs : Fin m → RelaxedClause n => (m : ℝ)) :=
      uniformMean_mono (fun cs => by exact_mod_cast clauseMinimum_le_length cs)
    _ = _ := uniformMean_const _

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CavityExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators

theorem exp_edgeExpression (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    Real.exp (expressionValue (edgeExpression β J xs)) =
      edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i)) := by
  unfold edgeExpression edge
  simp only [exp_binaryLogSumExpression, exp_boltzmannAtom, clausePenalty_cast]
  rw [sum_bool_vector_succ]
  simp_rw [sum_bool_vector_succ]
  simp only [Fintype.sum_unique]
  rfl

theorem edgeExpression_value (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    expressionValue (edgeExpression β J xs) =
      Real.log (edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i))) := by
  rw [← exp_edgeExpression, Real.log_exp]

attribute [local irreducible] edgeExpression siteExpression

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalHierarchy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory Set Filter TopologicalSpace
open scoped Topology BigOperators NNReal

attribute [local instance] OAI.FixedClauseThreshold.Computability.rationalHierarchyMeasurableSpace
theorem rationalTreeValue_finite (r : ℕ) (x : RationalTree r) :
    FiniteHierarchy r (rationalTreeValue r x) := by
  induction r with
  | zero => trivial
  | succ r ih =>
    obtain ⟨n, q, x⟩ := x
    exact ⟨n, fun i => rationalTreeValue r (x i), q.toAtomic,
      fun i => ih (x i), rfl⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PacketExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic

attribute [local irreducible] fieldExpression edgeExpression siteExpression trialExpression

attribute [local irreducible] fieldVector

attribute [local irreducible] edgeLeaf

theorem edgeLeaf_value (p : ℚ × (Fin 3 → Bool)) (cs : List Code) :
    expressionValue (edgeLeaf p cs) =
      Real.log (edge (satInteraction (p.1 : ℝ) p.2) (leafFields 3 cs)) := by
  simp only [edgeLeaf, edgeExpression_value, fieldVector, fieldExpression_value]
  rfl

theorem edgeTrialExpression_value (β : ℚ) (J : Fin 3 → Bool)
    (root : Code) (ms : List ℚ) :
    expressionValue (edgeTrialExpression β J root ms) =
      trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x)) := by
  exact trialExpression_eq_trialLog edgeLeaf (β,J) _ (fun cs => edgeLeaf_value _ cs) root ms

attribute [local irreducible] siteData

attribute [local irreducible] siteLeaf

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DisorderEnumeration
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open scoped BigOperators Classical

attribute [local irreducible] siteTrialExpression edgeTrialExpression

theorem averagedEdgeExpression_value (β : ℚ) (root : Code) (ms : List ℚ) :
    expressionValue (averagedEdgeExpression β root ms) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J =>
        trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
          (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x))) := by
  simp only [averagedEdgeExpression, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_map, Function.comp_def, signAlphabet, Finset.sum_map_toList,
    edgeTrialExpression_value]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, ← Finset.mul_sum]
  norm_num

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_InterpolationUpper
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteTrial_pressure_le (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r (finiteTrialLaw r Q U x) m := by
  let ζ := finiteTrialLaw r Q U x
  let μ := Measure.pi (fun _ : Fin N => M.field.toMeasure)
  let S : ℝ → ℝ := fun h => ∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure (M.alpha*(q+1))
  let E := ∫ z,trialLog r ζ m (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure
  have hp : ∀ d,0 < m d := fun d => (hm.2 d).1
  have hS : Integrable S M.field.toMeasure :=
    (trialDisorderAt_joint_integrable M m hp ζ hM.interaction_integrable hM.field_integrable _).integral_prod_right
  have hF := (centeredDisorderAt_joint_integrable (N := N) M hM.interaction_integrable
    hM.field_integrable (M.alpha*N)).integral_prod_right
  have hiS (s : Fin N) : Integrable (fun h : Fin N → ℝ => S (h s)) μ :=
    integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) (i := s) hS
  have hb (h : Fin N → ℝ) :
      (∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N))+(M.alpha:ℝ)*N*q*E ≤ ∑ s,S (h s) := by
    have he := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat M hM a r Q U x m hm h
    simpa only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_uniform,
      centeredDisorderAt,indexAverage,trialDisorderAt,S,E,ζ] using he
  have hi := integral_mono (hF.add (integrable_const ((M.alpha:ℝ)*N*q*E)))
    (integrable_finsetSum Finset.univ (fun s _ => hiS s)) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hF (integrable_const _),integral_const,probReal_univ,one_smul,
    centeredPressure_field_order M hM.interaction_integrable hM.field_integrable,
    integral_finsetSum _ (fun s _ => hiS s)] at hi
  dsimp only [μ] at hi
  simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hS.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  dsimp only [S] at hi
  rw [trialPoisson_field_order M m hp ζ hM.interaction_integrable hM.field_integrable] at hi
  have hN : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  unfold functional
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  change pressure M N ≤ Real.log 2+(∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*(q+1)))-
    (M.alpha:ℝ)*q*E
  nlinarith

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteHierarchy_pressure_le (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (hζ : FiniteHierarchy (r+1) ζ)
    (m : Fin r → ℝ) (hm : Exponents m) : pressure M N ≤ functional M r ζ m := by
  obtain ⟨n,hn,T,V,hT⟩ := finiteHierarchy_realization (r+1) ζ hζ
  let a : Fin n := ⟨0,hn⟩
  have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_pressure_le (N := N) M hM a r T.1 T.2 (fun b y => V (b,y)) m hm
  have he : finiteTrialLaw r T.1 T.2 (fun b y => V (b,y))=ζ := hT
  rwa [he] at h

end
end FixedClauseThreshold.Computability.PositiveInterpolation

namespace FixedClauseThreshold.Computability.PositiveInterpolation
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma pressure_le_functional (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r ζ m := by
  have hc : IsClosed {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} :=
    isClosed_le continuous_const (functional_continuous M m (fun d => (hm.2 d).1)
      hM.interaction_integrable hM.field_integrable)
  have hs : {ζ : Hierarchy (r+1) | FiniteHierarchy (r+1) ζ} ⊆
      {ζ : Hierarchy (r+1) | pressure M N ≤ functional M r ζ m} := by
    intro η hη
    exact FixedClauseThreshold.Computability.PositiveInterpolation.finiteHierarchy_pressure_le M hM r η hη m hm
  exact closure_minimal hs hc ((finiteHierarchy_dense (r+1)) ζ)

end
end FixedClauseThreshold.Computability.PositiveInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SignMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability
open DilutedSpinGlass
open scoped BigOperators

theorem signFeature_nonneg {n : ℕ} (P : FiniteLaw (Fin n → Spin)) :
    0 ≤ signFeature P := by
  apply FiniteLaw.expect_nonneg
  intro J
  apply FiniteLaw.expect_nonneg
  intro s
  exact Finset.prod_nonneg (fun _ _ => literalFactor_nonneg _ _)

theorem signFeature_cubic_nonnegative {n : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (j : Fin 3) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ (1 - Real.exp (-β))^n * (∏ _ : Fin 3, signFeature P) -
      3 * ((1 - Real.exp (-β))^n *
        ∏ l : Fin 3, signFeature (if l = j then P else B)) +
      2 * ((1 - Real.exp (-β))^n * ∏ _ : Fin 3, signFeature B) := by
  have he : 0 ≤ 1 - Real.exp (-β) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hp := signFeature_nonneg P
  have hb := signFeature_nonneg B
  have hid : (1 - Real.exp (-β))^n * (∏ _ : Fin 3, signFeature P) -
      3 * ((1 - Real.exp (-β))^n *
        ∏ l : Fin 3, signFeature (if l = j then P else B)) +
      2 * ((1 - Real.exp (-β))^n * ∏ _ : Fin 3, signFeature B) =
      (1 - Real.exp (-β))^n * (signFeature P - signFeature B)^2 *
        (signFeature P + 2 * signFeature B) := by
    fin_cases j <;> simp [Fin.prod_univ_three] <;> ring
  rw [hid]
  positivity

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ReplicaPositivity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory PositiveInterpolation
open scoped BigOperators NNReal

theorem satModel_rawMoment {n : ℕ} (a : ℝ≥0) (β : ℝ)
    (P : Fin 3 → FiniteLaw (Fin n → Spin)) :
    rawReplicaMoment (satModel a β) P =
      (1 - Real.exp (-β)) ^ n * ∏ l, signFeature (P l) := by
  rw [rawReplicaMoment_eq_product]
  change (∫ z : InteractionSample 3, (-z.2.2.1)^n *
      ∏ l, (P l).expect (fun s => ∏ i, z.2.2.2 l (s i))
      ∂Measure.map (satSample β) signLaw.toMeasure) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    (by unfold FiniteLaw.expect; fun_prop)]
  simp only [satSample, neg_sub]
  rw [integral_const_mul]
  rw [signLaw_product (fun l J => (P l).expect (fun s => ∏ i, literalFactor J (s i)))]
  rfl

theorem satModel_raw_nonnegative {n : ℕ} (a : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β)
    (j : Fin 3) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ rawReplicaMoment (satModel a β) (fun _ : Fin 3 => P) -
      (3 : ℝ) * rawReplicaMoment (satModel a β) (fun l => if l = j then P else B) +
      (2 : ℝ) * rawReplicaMoment (satModel a β) (fun _ : Fin 3 => B) := by
  rw [satModel_rawMoment, satModel_rawMoment, satModel_rawMoment]
  exact signFeature_cubic_nonnegative hβ j P B

theorem satModel_interpolation_admissible {a : ℝ≥0} (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) : InterpolationAdmissible (satModel a β) := by
  refine ⟨by norm_num, ha, satModel_interaction_integrable a hβ.le,
    satModel_field_integrable a β, ?_, satModel_independent a β,
    satModel_identically_distributed a β, ?_, ?_, ?_, ?_⟩
  · filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    refine ⟨by norm_num [satSample], fun s => ?_⟩
    exact ⟨satSample_factorization β J s, satSample_product_bound hβ J s⟩
  · apply (indepFun_const_left (Real.exp (-β) - 1)
      (fun z : InteractionSample 3 => z.2.2.2)).congr
    · filter_upwards [satModel_supported a β] with z hz
      obtain ⟨J, rfl⟩ := hz
      rfl
    · rfl
  · intro n _
    apply (integrable_const ((1 - Real.exp (-β)) ^ n)).congr
    filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    simp [satSample]
  · intro n _
    apply integral_nonneg_of_ae
    filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    change 0 ≤ (-(Real.exp (-β) - 1)) ^ n
    apply pow_nonneg
    have he : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · intro n _ j P B
    exact satModel_raw_nonnegative a hβ.le j P B

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATVariational
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem satPressure_tendsto {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    Tendsto (pressure (satModel a β)) atTop (nhds (satPressure a β)) := by
  have hθ := satModel_interaction_integrable a hβ.le
  have hh := satModel_field_integrable a β
  have hb := pressure_bounded (satModel a β) hθ hh
  have hs : limsup (pressure (satModel a β)) atTop ≤ satPressure a β := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r, ζ, m, hm, happrox⟩ := symmetric_trial_lower_sat (satModel a β) ha
      hθ hh (satModel_symmetric a β) hε
    have hu : limsup (pressure (satModel a β)) atTop ≤ functional (satModel a β) r ζ m := by
      apply limsup_le_of_le hb.2.isCobounded_le
      filter_upwards [eventually_gt_atTop 0] with N hN
      let : NeZero N := ⟨Nat.ne_of_gt hN⟩
      exact PositiveInterpolation.pressure_le_functional (satModel a β)
        (satModel_interpolation_admissible ha hβ) r ζ m hm
    exact hu.trans happrox
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hs hb.1 hb.2

theorem relaxedPressure_tendsto {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    Tendsto (relaxedPoissonPressure a β) atTop (nhds (satPressure a β)) := by
  have he : pressure (satModel a β) = relaxedPoissonPressure a β :=
    funext (satModel_pressure a β)
  rw [← he]
  exact satPressure_tendsto ha hβ

theorem satPressure_le_rational_trial {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    satPressure a β ≤ functional (satModel a β) r (rationalTreeValue (r+1) t) m := by
  apply le_of_tendsto (satPressure_tendsto ha hβ)
  filter_upwards [eventually_gt_atTop 0] with N hN
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact PositiveInterpolation.finiteHierarchy_pressure_le (satModel a β)
    (satModel_interpolation_admissible ha hβ) r _ (rationalTreeValue_finite _ _) m hm

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDisorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open scoped BigOperators NNReal Classical

theorem integral_sat_packet (a : ℝ≥0) (β : ℝ) (k : ℕ)
    (f : (Fin k → InteractionSample 3) → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂Measure.pi (fun _ : Fin k => (satModel a β).disorder.toMeasure)) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin 3 → Bool)).expect
        (fun J => f (fun i => satSample β (J i))) := by
  change (∫ θ, f θ ∂Measure.pi (fun _ : Fin k =>
    Measure.map (satSample β) signLaw.toMeasure)) = _
  rw [← Measure.pi_map_pi (μ := fun _ : Fin k => signLaw.toMeasure)
    (f := fun _ J => satSample β J) (fun _ => (measurable_of_countable _).aemeasurable)]
  rw [integral_map
    (φ := fun J : Fin k → Fin 3 → Bool => fun i => satSample β (J i))
    (Measurable.of_eval (fun i => (measurable_of_countable (satSample β)).comp
      (measurable_pi_apply i))).aemeasurable hf.aestronglyMeasurable]
  have he : signLaw.toMeasure = finiteUniform (Fin 3 → Bool) := rfl
  rw [he, finiteUniform_pi, integral_finiteUniform]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, smul_eq_mul, ← Finset.mul_sum]

theorem integral_sat_edge (a : ℝ≥0) (β : ℝ) (f : InteractionSample 3 → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂(satModel a β).disorder.toMeasure) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J => f (satSample β J)) := by
  change (∫ θ, f θ ∂Measure.map (satSample β) signLaw.toMeasure) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    hf.aestronglyMeasurable, signLaw_integral]

theorem packet_functional (a : ℝ≥0) (β : ℚ) (root : Code) (ms : List ℚ)
    (hm : ∀ i : Fin ms.length, 0 < ms.get i) :
    functional (satModel a β) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
      (fun i => (ms.get i : ℝ)) =
    Real.log 2 + (∫ k, packetSiteValue β root ms k ∂poissonMeasure (a*3)) -
      (a : ℝ)*2*packetEdgeValue β root ms := by
  let ζ := rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root)
  let m : Fin ms.length → ℝ := fun i => ms.get i
  have hp : ∀ i, 0 < m i := fun i => by
    dsimp only [m]
    exact_mod_cast hm i
  have hs (k : ℕ) : (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂(satModel a β).field.toMeasure
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) =
      packetSiteValue β root ms k := by
    change (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂Measure.dirac 0
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) = _
    simp only [integral_dirac]
    have hf : Measurable (fun θ : Fin k → InteractionSample 3 =>
        trialLog ms.length ζ m (siteLog θ 0)) := by
      simpa only [Function.comp_def, id_eq] using
        ((trial_site_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))).measurable
    rw [integral_sat_packet a (β : ℝ) k _ hf]
    exact (averagedSiteExpression_value β root ms k).symm
  have he : (∫ θ : InteractionSample 3,
      trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))
      ∂(satModel a β).disorder.toMeasure) = packetEdgeValue β root ms := by
    have hf : Measurable (fun θ : InteractionSample 3 =>
        trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))) := by
      simpa only [Function.comp_def] using
        ((trial_edge_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_fst (X := Interaction 3) (Y := ℝ × ℝ × (Fin 3 → Bool → ℝ)))).measurable
    rw [integral_sat_edge a (β : ℝ) _ hf]
    exact (averagedEdgeExpression_value β root ms).symm
  unfold functional
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ hs

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDescriptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic

theorem rationalAt_get (ms : List ℚ) (i : Fin ms.length) : rationalAt ms i.val = ms.get i := by
  simp [rationalAt]

attribute [local irreducible] rationalAt

theorem exponentCheck_iff (ms : List ℚ) :
    exponentCheck ms = true ↔ Exponents (fun i : Fin ms.length => (ms.get i : ℝ)) := by
  simp only [exponentCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h
    constructor
    · intro i j hij
      have hi := ((h i.val i.isLt).2 j.val j.isLt).resolve_left (Nat.not_le_of_gt hij)
      rw [rationalAt_get ms i, rationalAt_get ms j] at hi
      change (ms.get i : ℝ) < ms.get j
      exact_mod_cast hi
    · intro i
      have hi := (h i.val i.isLt).1
      rw [rationalAt_get ms i] at hi
      change 0 < (ms.get i : ℝ) ∧ (ms.get i : ℝ) < 1
      exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
  · intro h i hi
    refine ⟨?_, ?_⟩
    · have hb := h.2 ⟨i,hi⟩
      change 0 < (ms.get ⟨i,hi⟩ : ℝ) ∧ (ms.get ⟨i,hi⟩ : ℝ) < 1 at hb
      rw [rationalAt_get ms ⟨i,hi⟩]
      exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    · intro j hj
      by_cases hij : j ≤ i
      · exact Or.inl hij
      right
      have hm := h.1 (show (⟨i,hi⟩ : Fin ms.length) < ⟨j,hj⟩ from Nat.lt_of_not_ge hij)
      change (ms.get ⟨i,hi⟩ : ℝ) < ms.get ⟨j,hj⟩ at hm
      rw [rationalAt_get ms ⟨i,hi⟩, rationalAt_get ms ⟨j,hj⟩]
      exact_mod_cast hm

theorem exponentCheck_positive {ms : List ℚ} (h : exponentCheck ms = true) :
    positiveExponents ms = true := by
  rw [positiveExponents_iff]
  intro i
  have hp := (((exponentCheck_iff ms).mp h).2 i).1
  change 0 < (ms.get i : ℝ) at hp
  exact_mod_cast hp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_EffectiveTrialValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open PeriodicLattice.CertifiedReal RapidForcing.EffectiveArithmetic
open scoped NNReal

attribute [local irreducible] averagedSiteExpression averagedEdgeExpression positiveExponents

attribute [local irreducible] guardedSiteValue packetEdgeValue

theorem trialValue_eq_functional (t : TrialData)
    (hm : exponentCheck t.2.2.2 = true) :
    trialValue t = functional (satModel (trialDensityNN t) (t.2.1 : ℝ)) t.2.2.2.length
      (rationalTreeValue (t.2.2.2.length+1) (decodeTree (t.2.2.2.length+1) t.2.2.1))
      (fun i => (t.2.2.2.get i : ℝ)) := by
  have hp := exponentCheck_positive hm
  have he (k : ℕ) : guardedSiteValue t k = packetSiteValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2 k := by
    simp only [guardedSiteValue, guardedSiteExpression, hp, ite_true, packetSiteValue]
  have hf := packet_functional (trialDensityNN t) (t.2.1 : ℚ) t.2.2.1 t.2.2.2
    ((positiveExponents_iff _).mp hp)
  simp only [Rat.cast_natCast] at hf
  rw [hf]
  have hc : (trialDensityNN t : ℝ) = (max 0 t.1 : ℚ) := rfl
  simp only [trialValue, he, hc]
  push_cast
  ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CompiledTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec PeriodicLattice.CertifiedReal
open scoped NNReal

theorem satTrialEvaluation_valid {j : ℕ} (hj : satTrialEvaluation.valid j = true) :
    0 < (decodeTrial j).1 ∧ 0 < (decodeTrial j).2.1 ∧
      exponentCheck (decodeTrial j).2.2.2 = true :=
  (trialDataValid_iff _).mp hj

theorem satTrialEvaluation_bound {j : ℕ} (hj : satTrialEvaluation.valid j = true) :
    satPressure (trialDensityNN (decodeTrial j)) ((decodeTrial j).2.1 : ℝ) ≤
      satTrialEvaluation.value j := by
  have ht := satTrialEvaluation_valid hj
  change _ ≤ trialValue (decodeTrial j)
  rw [trialValue_eq_functional _ ht.2.2]
  apply satPressure_le_rational_trial
  · change (0 : ℝ) < (max 0 (decodeTrial j).1 : ℚ)
    exact_mod_cast lt_max_of_lt_right ht.1
  · exact_mod_cast ht.2.1
  · exact (exponentCheck_iff _).mp ht.2.2

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PressureSigns
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

attribute [local irreducible] relaxedLogPartition

theorem relaxedFixedLogPartition_eq_mean (n m : ℕ) (β : ℝ) :
    relaxedFixedLogPartition n m β = uniformMean
      (fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2)) := by
  let e : (Fin m → RelaxedClause n) ≃
      (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) :=
    Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin 3 → Fin n) (fun _ => Fin 3 → Bool)
  calc
    _ = uniformMean (fun p : (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) =>
        relaxedLogPartition β p.1 p.2) := by
      rw [uniformMean_prod, uniformMean_comm]
      rfl
    _ = uniformMean (fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (e cs).1 (e cs).2) :=
      (uniformMean_equiv e (fun p : (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) =>
        relaxedLogPartition β p.1 p.2)).symm
    _ = _ := uniformMean_congr (fun _ => rfl)

theorem relaxedFixedLogPartition_lower (n m : ℕ) (β : ℝ) :
    -β * relaxedFixedMinimum n m ≤ relaxedFixedLogPartition n m β := by
  rw [relaxedFixedLogPartition_eq_mean, relaxedFixedMinimum, ← uniformMean_const_mul]
  exact uniformMean_mono (fun _ => relaxedLogPartition_lower _ _ _)

theorem relaxedFixedLogPartition_bound (n m : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β) :
    |relaxedFixedLogPartition n m β| ≤ n*Real.log 2 + β*m := by
  rw [relaxedFixedLogPartition_eq_mean, abs_le]
  constructor
  · have h := uniformMean_mono (f := fun _cs : Fin m → RelaxedClause n => -(β*(m : ℝ)))
        (g := fun cs => relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2))
        (fun cs => ?_)
    · rw [uniformMean_const] at h
      have hl : 0 ≤ (n : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by norm_num))
      linarith
    · have hl := relaxedLogPartition_lower β (fun j => (cs j).1) (fun j => (cs j).2)
      have hm : (clauseMinimum cs : ℝ) ≤ m := by exact_mod_cast clauseMinimum_le_length cs
      change -β * (clauseMinimum cs : ℝ) ≤ _ at hl
      exact le_trans (by nlinarith) hl
  · have h := uniformMean_mono (f := fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2))
        (g := fun _ => (n : ℝ)*Real.log 2 + β*m) (fun cs => ?_)
    · simpa only [uniformMean_const] using h
    · have hu := relaxedLogPartition_upper hβ (fun j => (cs j).1) (fun j => (cs j).2)
      have hpos := mul_nonneg hβ (Nat.cast_nonneg (clauseMinimum cs) : (0 : ℝ) ≤ _)
      nlinarith [mul_nonneg hβ (Nat.cast_nonneg m)]

theorem relaxedPoissonPressure_lower (n : ℕ) [NeZero n] (a : ℝ≥0)
    {β : ℝ} (hβ : 0 ≤ β) :
    -β * (relaxedPoissonMinimum n a / n) ≤ relaxedPoissonPressure a β n := by
  have hE : Integrable (fun m => relaxedFixedMinimum n m) (poissonMeasure (a*n)) := by
    apply (poisson_integrable_count (a*n)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun m => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (relaxedFixedMinimum_nonneg n m)] using
        relaxedFixedMinimum_le n m)
  have hZ : Integrable (fun m => relaxedFixedLogPartition n m β) (poissonMeasure (a*n)) := by
    apply (((integrable_const ((n : ℝ)*Real.log 2)).add
      ((poisson_integrable_count (a*n)).const_mul β))).mono'
        (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (relaxedFixedLogPartition_bound n · hβ)
  have h := integral_mono (hE.const_mul (-β)) hZ (fun m => relaxedFixedLogPartition_lower n m β)
  rw [integral_const_mul] at h
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [relaxedPoissonMinimum, relaxedPoissonPressure, mul_div_assoc] using hd

theorem satPressure_subcritical {a : ℝ≥0} (ha : 0 < a)
    (haα : (a : ℝ) < limitingCenter 3) {β : ℝ} (hβ : 0 < β) :
    0 ≤ satPressure a β := by
  have hl := (relaxedPoissonMinimum_subcritical_sat haα).const_mul (-β)
  have hb : ∀ᶠ n : ℕ in atTop,
      -β * (relaxedPoissonMinimum n a / n) ≤ relaxedPoissonPressure a β n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact relaxedPoissonPressure_lower n a hβ.le
  simpa only [mul_zero] using le_of_tendsto_of_tendsto hl (relaxedPressure_tendsto ha hβ) hb

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped NNReal

theorem trialDensityNN_of_pos {t : TrialData} (ht : 0 < t.1) :
    (trialDensityNN t : ℝ) = (t.1 : ℝ) := by
  change ((max 0 t.1 : ℚ) : ℝ) = (t.1 : ℝ)
  rw [max_eq_right ht.le]

theorem satTrialEvaluation_sound_sat_oai {j : ℕ} (hj : satTrialEvaluation.valid j = true)
    (hneg : satTrialEvaluation.value j < 0) :
    limitingCenter 3 ≤ (satTrialEvaluation.density j : ℝ) := by
  by_contra h
  have hv := satTrialEvaluation_valid hj
  have ha : (0 : ℝ≥0) < trialDensityNN (decodeTrial j) := by
    change (0 : ℝ) < (trialDensityNN (decodeTrial j) : ℝ)
    rw [trialDensityNN_of_pos hv.1]
    exact_mod_cast hv.1
  have hb : (0 : ℝ) < ((decodeTrial j).2.1 : ℝ) := by exact_mod_cast hv.2.1
  have hbelow : (trialDensityNN (decodeTrial j) : ℝ) < limitingCenter 3 := by
    rw [trialDensityNN_of_pos hv.1]
    exact lt_of_not_ge h
  have hp := satPressure_subcritical ha hbelow hb
  exact (not_lt_of_ge (hp.trans (satTrialEvaluation_bound hj))) hneg

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat_oai := @OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat_oai
