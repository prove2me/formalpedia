-- Prove2me | solution 1 for OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:27.024872+00:00
-- url     : https://prove2.me/submissions/73b30e3b-ab5d-4500-ae3b-df4f7cbb5166

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_Q243FI003
import Theorems.Thm_OAI_Problem367_ConstructedArtanhFormula_exists_artanh_decomposition

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RoundedStoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.RoundedStoppingTimes

private theorem mesh_pos (n : ℕ) : (0 : ℝ≥0) < n + 1 := by positivity

theorem le_round (n : ℕ) (t : ℝ≥0) : t ≤ round n t := by
  rw [round, le_div_iff₀ (mesh_pos n)]
  exact Nat.le_ceil _

theorem round_le_add (n : ℕ) (t : ℝ≥0) :
    round n t ≤ t + 1 / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), add_mul,
    div_mul_cancel₀ _ (ne_of_gt (mesh_pos n))]
  exact (Nat.ceil_lt_add_one zero_le).le

theorem round_le_iff (n : ℕ) (s t : ℝ≥0) :
    round n s ≤ t ↔ s ≤ (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), ← Nat.le_floor_iff zero_le,
    Nat.ceil_le, le_div_iff₀ (mesh_pos n)]

theorem floor_div_le (n : ℕ) (t : ℝ≥0) :
    (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) ≤ t := by
  rw [div_le_iff₀ (mesh_pos n)]
  exact Nat.floor_le zero_le

theorem tendsto_round (t : ℝ≥0) : Tendsto (fun n => round n t) atTop (𝓝 t) := by
  have hu : Tendsto (fun n : ℕ => t + 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_round n t) (fun n => round_le_add n t)

theorem roundTop_le_iff (n : ℕ) (s : WithTop ℝ≥0) (t : ℝ≥0) :
    roundTop n s ≤ t ↔
      s ≤ (((⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) := by
  cases s with
  | top => simp only [roundTop_top, WithTop.top_le_iff, WithTop.coe_ne_top]
  | coe s => simpa only [roundTop_coe, WithTop.coe_le_coe] using round_le_iff n s t

theorem countable_range_roundTop (n : ℕ) : (Set.range (roundTop n)).Countable := by
  refine ((Set.countable_range (fun k : ℕ =>
    ((k : ℝ≥0) / (n + 1 : ℝ≥0) : WithTop ℝ≥0))).insert ⊤).mono ?_
  rintro _ ⟨t, rfl⟩
  cases t with
  | top => exact Set.mem_insert _ _
  | coe t =>
    exact Set.mem_insert_of_mem _ ⟨⌈t * (n + 1 : ℝ≥0)⌉₊, rfl⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {F : Filtration ℝ≥0 m}

theorem isStoppingTime_roundTop {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (n : ℕ) : IsStoppingTime F (fun ω => roundTop n (τ ω)) := by
  intro t
  simp only [roundTop_le_iff]
  exact F.mono (floor_div_le n t) _ (hτ _)

theorem countable_range_roundTop_comp (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => roundTop n (τ ω))).Countable :=
  (countable_range_roundTop n).mono (Set.range_comp_subset_range _ _)

theorem tendsto_min_roundTop_untopA (t : ℝ≥0) (s : WithTop ℝ≥0) :
    Tendsto (fun n => (min (t : WithTop ℝ≥0) (roundTop n s)).untopA)
      atTop (𝓝 (min (t : WithTop ℝ≥0) s).untopA) := by
  cases s with
  | top => simp
  | coe s =>
    simpa only [roundTop_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe] using
      (tendsto_const_nhds.min (tendsto_round s) :
        Tendsto (fun n => min t (round n s)) atTop (𝓝 (min t s)))

theorem exists_countable_range_approximation {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    ∃ τn : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsStoppingTime F (τn n)) ∧
      (∀ n, (Set.range (τn n)).Countable) ∧
      (∀ (ω : Ω) (t : ℝ≥0), Tendsto (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA)
        atTop (𝓝 (min (t : WithTop ℝ≥0) (τ ω)).untopA)) := by
  exact ⟨fun n ω => roundTop n (τ ω), isStoppingTime_roundTop hτ,
    countable_range_roundTop_comp τ, fun ω t => tendsto_min_roundTop_untopA t (τ ω)⟩

end Problem367.RoundedStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousOptionalStopping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousOptionalStopping

theorem countable_range_const {Ω α : Type*} (a : α) :
    (range (fun _ : Ω => a)).Countable := by
  apply (countable_singleton a).mono
  rintro x ⟨ω, rfl⟩
  exact mem_singleton a

theorem countable_range_min {Ω α : Type*} [LinearOrder α] {f g : Ω → α}
    (hf : (range f).Countable) (hg : (range g).Countable) :
    (range (fun ω => min (f ω) (g ω))).Countable := by
  apply (hf.union hg).mono
  rintro x ⟨ω, rfl⟩
  rcases le_total (f ω) (g ω) with h | h
  · exact Or.inl ⟨ω, min_eq_left h |>.symm⟩
  · exact Or.inr ⟨ω, min_eq_right h |>.symm⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem integrable_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    Integrable (stoppedValue M τ) μ := by
  exact integrable_condExp.congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount).symm

theorem integral_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by
  rw [integral_congr_ae
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount)]
  exact integral_condExp hτ.measurableSpace_le

theorem martingale_stoppedProcess_of_countable
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hτ : IsStoppingTime F τ) (hcount : (range τ).Countable) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    exact integrable_stoppedValue_of_countable hM ((isStoppingTime_const F t).min hτ)
      (countable_range_min (countable_range_const _) hcount) (fun _ => min_le_left _ _)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  classical
  let ν : Ω → WithTop ℝ≥0 := Aᶜ.piecewise (fun _ => s) (fun _ => t)
  have hν : IsStoppingTime F ν := isStoppingTime_piecewise_const hst hA.compl
  have hνcount : (range ν).Countable := by
    apply (Set.to_countable ({(s : WithTop ℝ≥0), (t : WithTop ℝ≥0)} : Set (WithTop ℝ≥0))).mono
    rintro value ⟨sample, rfl⟩
    change ν sample = (s : WithTop ℝ≥0) ∨ ν sample = (t : WithTop ℝ≥0)
    by_cases hsample : sample ∈ A
    · right
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_true_eq_false, ite_false, if_false]
    · left
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_false_eq_true, ite_true, if_true]
  have hνle (ω : Ω) : ν ω ≤ t := by
    by_cases hω : ω ∈ A
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_true_eq_false, ite_false, if_false]
      exact le_rfl
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_false_eq_true, ite_true, if_true]
      exact WithTop.coe_le_coe.mpr hst
  let π : Ω → WithTop ℝ≥0 := fun ω => min (ν ω) (τ ω)
  have hπ := hν.min hτ
  have hπcount := countable_range_min hνcount hcount
  have hmeanπ := integral_stoppedValue_of_countable hM hπ hπcount
    (fun ω => (min_le_left _ _).trans (hνle ω))
  have hmeans := integral_stoppedValue_of_countable hM ((isStoppingTime_const F s).min hτ)
    (countable_range_min (countable_range_const _) hcount)
    (fun ω => (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hst))
  have hpiece : stoppedValue M π =
      A.piecewise (stoppedProcess M τ t) (stoppedProcess M τ s) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [π, ν, Set.piecewise, hω, stoppedValue, stoppedProcess]
  change (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, M t ω ∂μ at hmeanπ
  have hmean : (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, stoppedProcess M τ s ω ∂μ :=
    hmeanπ.trans hmeans.symm
  rw [hpiece, integral_piecewise (F.le s A hA) (hint t).integrableOn
    (hint s).integrableOn] at hmean
  have hsplit := integral_add_compl (F.le s A hA) (hint s)
  linarith

theorem martingale_stoppedProcess_of_approximation
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hMn (n : ℕ) : Martingale (stoppedProcess M (τn n)) F μ :=
    martingale_stoppedProcess_of_countable hM hprog (hτn n) (hcount n)
  have hbound (T : ℝ≥0) (g : Ω → ℝ)
      (hg : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
      (σ : Ω → WithTop ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖stoppedProcess M σ T ω‖ ≤ g ω := by
    filter_upwards [hg] with ω hω
    exact hω _ (WithTop.untopA_le (min_le_left _ _))
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    exact hg.mono' ((had t).mono (F.le t)).aestronglyMeasurable (hbound t g hgb τ)
  have hlim (t : ℝ≥0) (A : Set Ω) :
      Tendsto (fun n => ∫ ω in A, stoppedProcess M (τn n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, stoppedProcess M τ t ω ∂μ)) := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    apply tendsto_integral_of_dominated_convergence g
      (fun n => ((hMn n).integrable t).aestronglyMeasurable.restrict) hg.restrict
      (fun n => ae_restrict_of_ae (hbound t g hgb (τn n)))
    filter_upwards [ae_restrict_of_ae hc] with ω hcω
    exact (hcω.tendsto _).comp (htime ω t)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  exact tendsto_nhds_unique (hlim s A)
    (Filter.Tendsto.congr (fun n => ((hMn n).setIntegral_eq hst hA).symm) (hlim t A))

theorem martingale_stoppedProcess_of_continuous_dominated
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) : Martingale (stoppedProcess M τ) F μ := by
  obtain ⟨τn, hτn, hcount, htime⟩ :=
    RoundedStoppingTimes.exists_countable_range_approximation hτ
  exact martingale_stoppedProcess_of_approximation hM hprog hc hdom hτ τn hτn hcount htime

end Problem367.ContinuousOptionalStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem isStronglyProgressive_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ} (ha : IsStronglyProgressive F a) :
    IsStronglyProgressive F (nnrealTimePrimitive a) := by
  intro T
  have hi : StronglyMeasurable[Subtype.instMeasurableSpace.prod (F T)]
      (fun p : Iic T × Ω => ∫ r : ℝ,
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0) := by
    have hc := stronglyMeasurable_clipped_nnreal_process ha T
    let : MeasurableSpace Ω := F T
    have hf : StronglyMeasurable (fun q : (Iic T × Ω) × ℝ =>
        a (min q.2.toNNReal T) q.1.2) :=
      hc.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hs : MeasurableSet {q : (Iic T × Ω) × ℝ |
        0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (measurable_subtype_coe.comp (measurable_subtype_coe.comp
            (measurable_fst.comp measurable_fst))))
    have hu : StronglyMeasurable (Function.uncurry (fun p : Iic T × Ω => fun r : ℝ =>
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0)) := by
      exact hf.piecewise hs stronglyMeasurable_zero
    exact hu.integral_prod_right
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) (p.1 : ℝ≥0)
  · have hrt : r.toNNReal ≤ T :=
      (by simpa using Real.toNNReal_mono hr.2 : r.toNNReal ≤ (p.1 : ℝ≥0)).trans p.1.2
    simp only [Set.indicator_of_mem hr, Set.mem_Ioc] at hr ⊢
    rw [ite_eq_left hr, min_eq_left hrt]
  · simp only [Set.indicator_of_notMem hr]
    exact (ite_eq_right hr).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IntegrableTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {a : ℝ≥0 → Ω → ℝ}

theorem ae_intervalIntegrable_horizons_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (n : ℝ) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [(ha n).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hω

theorem ae_continuous_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

omit [MeasurableSpace Ω] in
theorem nnrealTimePrimitive_nonneg {ω : Ω}
    (ha : ∀ t, 0 ≤ a t ω) (t : ℝ≥0) : 0 ≤ nnrealTimePrimitive a t ω :=
  intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (fun r => ha r.toNNReal)

theorem ae_monotone_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω) :
    ∀ᵐ ω ∂μ, Monotone (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha, hnonneg] with ω hi hp
  intro s t hst
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hit : IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp (hi n)).mono_set
        (Ioc_subset_Ioc le_rfl hn))
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
    (Filter.Eventually.of_forall (fun r => hp r.toNNReal)) hit

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_RightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

theorem martingale_rightCont_of_L1_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F P)
    (hcont : ∀ s, Tendsto (fun t => eLpNorm (X t - X s) 1 P)
      (𝓝[>] s) (𝓝 0)) :
    Martingale X F.rightCont P := by
  have had : StronglyAdapted F.rightCont X :=
    fun s => (hX.stronglyAdapted s).mono (F.le_rightCont s)
  refine ⟨had, ?_⟩
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact (condExp_of_stronglyMeasurable (F.rightCont.le s) (had s)
      (hX.integrable s)).eventuallyEq
  · apply (ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s)
      (hX.integrable t) (fun A hA _ => (hX.integrable s).integrableOn) ?_
      (had s).aestronglyMeasurable).symm
    intro A hA hAfin
    have hlim := tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Eventually.of_forall hX.integrable) (hcont s) A
    have heq : ∀ᶠ u in 𝓝[>] s, (∫ ω in A, X u ω ∂P) = ∫ ω in A, X t ω ∂P := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds]
        with u hsu hut
      have hFu : F.rightCont s ≤ F u := by
        rw [F.rightCont_eq]
        exact iInf₂_le u hsu
      exact hX.setIntegral_eq hut.le (hFu A hA)
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_DominatedMartingaleRightContinuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

namespace Problem367.DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure μ] in
theorem tendsto_L1_of_ae_continuous_dominated
    (hint : ∀ t, Integrable (M t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) (s : ℝ≥0) :
    Tendsto (fun t => eLpNorm (M t - M s) 1 μ) (𝓝 s) (𝓝 0) := by
  obtain ⟨g, hg, hgb⟩ := hdom (s + 1)
  have hcont : ContinuousAt (fun t => ∫ ω, ‖M t ω - M s ω‖ ∂μ) s := by
    apply continuousAt_of_dominated
      (Eventually.of_forall (fun t => ((hint t).sub (hint s)).aestronglyMeasurable.norm))
      (bound := fun ω => 2 * g ω)
    · filter_upwards [eventually_lt_nhds (lt_add_one s)] with t ht
      filter_upwards [hgb] with ω hω
      have hst : s ≤ s + 1 := le_add_of_nonneg_right zero_le
      have hb := (norm_sub_le (M t ω) (M s ω)).trans
        (add_le_add (hω t ht.le) (hω s hst))
      simpa only [Pi.sub_apply, norm_norm, two_mul] using hb
    · exact hg.const_mul 2
    · filter_upwards [hc] with ω hω
      exact (hω.sub continuous_const).norm.continuousAt
  have heq (t : ℝ≥0) : eLpNorm (M t - M s) 1 μ =
      ENNReal.ofReal (∫ ω, ‖M t ω - M s ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hint t).sub (hint s))]
    rfl
  simp_rw [heq]
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.continuousAt.comp hcont).tendsto

theorem martingale_rightCont_of_ae_continuous_dominated
    (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) :
    Martingale M F.rightCont μ := by
  apply Problem367.martingale_rightCont_of_L1_rightContinuous hM
  intro s
  exact (tendsto_L1_of_ae_continuous_dominated hM.integrable hc hdom s).mono_left
    nhdsWithin_le_nhds

theorem isStronglyProgressive_mono_filtration
    {G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) (hM : IsStronglyProgressive F M) :
    IsStronglyProgressive G M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hFG t)))

theorem martingale_stoppedProcess_rightCont
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_dominated
    (martingale_rightCont_of_ae_continuous_dominated hM hc hdom)
    (isStronglyProgressive_mono_filtration F.le_rightCont hprog) hc hdom hτ

theorem martingale_stopped_compensatedSquare_rightCont
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hcomp : Martingale (fun t ω => (M t ω)^2 - A t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (fun t ω => (stoppedProcess M τ t ω)^2 - stoppedProcess A τ t ω)
      F.rightCont μ := by
  have hprog : IsStronglyProgressive F (fun t ω => (M t ω)^2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => (M t ω)^2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  apply martingale_stoppedProcess_rightCont hcomp hprog hc _ hτ
  intro T
  refine ⟨fun ω => C^2 + A T ω, (integrable_const _).add (hAint T), ?_⟩
  filter_upwards [hb, hA0, hAmono] with ω hbw hA0w hAmonow
  intro t ht
  have hMsq : (M t ω)^2 ≤ C^2 := by
    have := (sq_le_sq₀ (abs_nonneg (M t ω)) hC).mpr (hbw t)
    simpa only [sq_abs] using this
  calc
    |(M t ω)^2 - A t ω| ≤ |(M t ω)^2| + |A t ω| := abs_sub _ _
    _ = (M t ω)^2 + A t ω := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hA0w t)]
    _ ≤ C^2 + A T ω := add_le_add hMsq (hAmonow ht)

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Problem367.StoppedTimePrimitive

theorem integral_indicator_min (a : ℝ → ℝ) (t u : ℝ≥0) :
    (∫ r in (0 : ℝ)..(t : ℝ), if r ≤ u then a r else 0) =
      ∫ r in (0 : ℝ)..(min t u : ℝ≥0), a r := by
  rcases le_total t u with h | h
  · rw [min_eq_left h]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le t.coe_nonneg] at hr
    exact ite_eq_left (hr.2.trans h)
  · rw [min_eq_right h]
    exact intervalIntegral.integral_indicator ⟨u.coe_nonneg, h⟩

theorem stoppedProcess_primitive {Ω : Type*} (a : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (nnrealTimePrimitive a) τ t ω =
      nnrealTimePrimitive (stopDensity a τ) t ω := by
  cases hτ : τ ω with
  | top => simp only [stoppedProcess, nnrealTimePrimitive, stopDensity, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top, ite_true, if_true]
  | coe u =>
    simp only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, nnrealTimePrimitive, stopDensity, WithTop.coe_le_coe,
      Real.toNNReal_le_iff_le_coe]
    exact (integral_indicator_min (fun r => a r.toNNReal ω) t u).symm

theorem continuous_stoppedProcess {Ω E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} {ω : Ω} (hX : Continuous (fun t => X t ω))
    (τ : Ω → WithTop ℝ≥0) : Continuous (fun t => stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [stoppedProcess, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe] using hX
  | coe u =>
    simpa only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using hX.comp (continuous_id.min continuous_const)

theorem monotone_stoppedProcess {Ω E : Type*} [Preorder E]
    {X : ℝ≥0 → Ω → E} {ω : Ω} (hX : Monotone (fun t => X t ω))
    (τ : Ω → WithTop ℝ≥0) : Monotone (fun t => stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [stoppedProcess, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe] using hX
  | coe u =>
    simpa only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using hX.comp (monotone_id.min monotone_const)

theorem stopTime_eq_iff_le {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (min (t : WithTop ℝ≥0) (τ ω)).untopA = t ↔ (t : WithTop ℝ≥0) ≤ τ ω := by
  cases hτ : τ ω with
  | top => simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top]
  | coe u => simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, min_eq_left_iff, WithTop.coe_le_coe]

theorem isStronglyProgressive_stopDensity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (ha : IsStronglyProgressive F a) (hτ : IsStoppingTime F τ) :
    IsStronglyProgressive F (stopDensity a τ) := by
  intro T
  let : MeasurableSpace Ω := F T
  have hs : MeasurableSet {p : Iic T × Ω | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2} := by
    simp only [← stopTime_eq_iff_le]
    exact measurableSet_eq_fun (isStronglyProgressive_min_stopping_time hτ T).measurable
      measurable_fst.subtype_val
  exact (ha T).piecewise hs stronglyMeasurable_const

theorem stoppedProcess_weighted_primitive {Ω E : Type*}
    (X : ℝ≥0 → Ω → E) (f : E → ℝ) (a : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (nnrealTimePrimitive (fun s ω => f (X s ω) * a s ω)) τ t ω =
      nnrealTimePrimitive (fun s ω => f (stoppedProcess X τ s ω) * stopDensity a τ s ω) t ω := by
  rw [stoppedProcess_primitive]
  congr 1
  funext s ω
  by_cases h : (s : WithTop ℝ≥0) ≤ τ ω
  · simp only [stopDensity, h, ite_true, if_true, stoppedProcess_eq_of_le h]
  · simp only [stopDensity, h, ite_false, if_false, mul_zero]

end Problem367.StoppedTimePrimitive

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InteriorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

theorem radius_nonneg (n : ℕ) : 0 ≤ radius n := by
  have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hi : ((n : ℝ) + 2)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact sub_nonneg.mpr hi

theorem radius_lt_one (n : ℕ) : radius n < 1 := by
  have hp : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
  unfold radius
  linarith

end Problem367.PosteriorInteriorLocalization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_StoppingTimes
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

theorem isStoppingTime_decision {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {p : Ω → Prop} [DecidablePred p]
    (q : ℝ≥0) (hp : MeasurableSet[F q] {ω | p ω}) :
    IsStoppingTime F (fun ω => if p ω then (q : WithTop ℝ≥0) else ⊤) := by
  intro t
  by_cases hqt : q ≤ t
  · have heq : {ω | (if p ω then (q : WithTop ℝ≥0) else ⊤) ≤ t} = {ω | p ω} := by
      ext ω
      by_cases hpω : p ω
      · simp only [hpω, ite_true, if_true, mem_ofPred_eq, iff_true]
        exact WithTop.coe_le_coe.mpr hqt
      · simp only [hpω, ite_false, if_false, mem_ofPred_eq, iff_false]
        exact not_le.mpr (WithTop.coe_lt_top t)
    rw [heq]
    exact F.mono hqt _ hp
  · have heq : {ω | (if p ω then (q : WithTop ℝ≥0) else ⊤) ≤ t} = ∅ := by
      ext ω
      by_cases hpω : p ω
      · simp only [hpω, ite_true, if_true, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hqt (WithTop.coe_le_coe.mp h)
      · simp only [hpω, ite_false, if_false, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact not_le.mpr (WithTop.coe_lt_top t)
    rw [heq]
    exact @MeasurableSet.empty Ω (F t)

theorem isStoppingTime_rationalExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (r : ℝ) :
    IsStoppingTime F (rationalExit M r) := by
  apply IsStoppingTime.iInf
  intro q
  apply isStoppingTime_decision
  let : MeasurableSpace Ω := F (q : ℝ≥0)
  exact (hM (q : ℝ≥0)).abs measurableSet_Ioi

theorem exists_earlier_nnrat {f : ℝ≥0 → ℝ} {t : ℝ≥0} {r : ℝ}
    (hc : ContinuousAt f t) (ht : 0 < t) (hr : r < f t) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < t ∧ r < f (q : ℝ≥0) := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (f t - r) (sub_pos.mpr hr)
  have htR : (0 : ℝ) < t := ht
  have hlo : max (0 : ℝ) ((t : ℝ) - δ) < t :=
    max_lt htR (sub_lt_self _ hδ)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlo
  have hq0 : 0 ≤ q := Rat.cast_nonneg.mp (le_of_lt ((le_max_left _ _).trans_lt hqlo))
  let qn : ℚ≥0 := ⟨q, hq0⟩
  have hqn : ((qn : ℝ≥0) : ℝ) = (q : ℝ) := by
    norm_cast
  have hqt : (qn : ℝ≥0) < t := by exact_mod_cast (hqn ▸ hqhi)
  refine ⟨qn, hqt, ?_⟩
  have hd : dist (qn : ℝ≥0) t < δ := by
    rw [NNReal.dist_eq, hqn, abs_of_neg (sub_neg.mpr hqhi)]
    have := (le_max_right (0 : ℝ) ((t : ℝ) - δ)).trans_lt hqlo
    linarith
  have hsmall := hcont hd
  rw [Real.dist_eq] at hsmall
  have hleft := (abs_lt.mp hsmall).1
  linarith

theorem abs_le_of_le_rationalExit {Ω : Type*} {M : ℝ≥0 → Ω → ℝ}
    {r : ℝ} {ω : Ω} (hc : Continuous (fun t => M t ω))
    (hzero : |M 0 ω| ≤ r) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ rationalExit M r ω) : |M t ω| ≤ r := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hzero
  by_contra hbound
  obtain ⟨q, hqt, hq⟩ := exists_earlier_nnrat hc.abs.continuousAt
    (pos_iff_ne_zero.mpr ht0) (lt_of_not_ge hbound)
  have hexit : rationalExit M r ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0) := by
    exact (iInf_le (fun p : ℚ≥0 => if r < |M (p : ℝ≥0) ω| then
      ((p : ℝ≥0) : WithTop ℝ≥0) else ⊤) q).trans
        (by simp only [hq, ite_true, if_true, le_refl])
  have hle : t ≤ (q : ℝ≥0) := WithTop.coe_le_coe.mp (ht.trans hexit)
  exact (not_lt_of_ge hle) hqt

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n :=
  PosteriorInteriorLocalization.radius_nonneg n

theorem threshold_lt_one (n : ℕ) : threshold n < 1 :=
  PosteriorInteriorLocalization.radius_lt_one n

theorem isStoppingTime_posteriorExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (n : ℕ) :
    IsStoppingTime F (posteriorExit M n) :=
  (isStoppingTime_rationalExit hM (threshold n)).min_const ((n : ℝ≥0) + 1)

end Problem367.PosteriorStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CompensatorStopping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorCompensatorStopping

open PosteriorStoppingTimes

theorem jointExit_le_posteriorExit {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : jointExit M A n ω ≤ posteriorExit M n ω := min_le_left _ _

theorem isStoppingTime_jointExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous] {M A : ℝ≥0 → Ω → ℝ}
    (hM : Adapted F M) (hA : Adapted F A) (n : ℕ) :
    IsStoppingTime F (jointExit M A n) :=
  (isStoppingTime_posteriorExit hM n).min (isStoppingTime_rationalExit hA _)

theorem abs_stoppedProcess_le_of_le_exit {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {r : ℝ}
    (hc : Continuous (fun t => X t ω)) (hzero : |X 0 ω| ≤ r)
    (hτ : τ ω ≤ rationalExit X r ω) (t : ℝ≥0) :
    |stoppedProcess X τ t ω| ≤ r := by
  let s : WithTop ℝ≥0 := min (t : WithTop ℝ≥0) (τ ω)
  have hsne : s ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hsne
  have huτ : (u : WithTop ℝ≥0) ≤ rationalExit X r ω := by
    rw [hu]
    exact (min_le_right _ _).trans hτ
  change |X s.untopA ω| ≤ r
  rw [← hu]
  exact abs_le_of_le_rationalExit hc hzero huτ

theorem abs_stopped_posterior_le {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess M (jointExit M A n) t ω| ≤ threshold n := by
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simpa only [hzero, abs_zero] using threshold_nonneg n) _ t
  exact (jointExit_le_posteriorExit M A n ω).trans (min_le_left _ _)

theorem abs_stopped_compensator_le {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => A t ω)) (hzero : A 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess A (jointExit M A n) t ω| ≤ (n : ℝ) + 1 := by
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simp only [hzero, abs_zero] <;> positivity) (min_le_right _ _) t

end Problem367.PosteriorCompensatorStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LocalizedArtanhFormula
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.LocalizedArtanhFormula
open ArtanhMartingaleFormula PosteriorStoppingTimes PosteriorCompensatorStopping
open StoppedTimePrimitive DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_stopDensity [SFinite μ]
    {F : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (ha : IsStronglyProgressive F a) (hτ : IsStoppingTime F τ) (T : ℝ≥0)
    (hint : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ)) :
    Integrable (fun p : ℝ × Ω => stopDensity a τ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
  have hprog := isStronglyProgressive_stopDensity ha hτ
  have hmeas : StronglyMeasurable
      (fun p : ℝ × Ω => stopDensity a τ p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hprog).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply hint.norm.mono' hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simp only [stopDensity]
  split_ifs <;> simp

theorem exists_jointExit_artanh_decomposition_oai [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M a : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive a t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hproga : IsStronglyProgressive F a)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hzero : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ 1)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω)
    (ha : ∀ T : ℝ≥0, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (n : ℕ) (T : ℝ≥0) :
    let τ := jointExit M (nnrealTimePrimitive a) n
    let N := stoppedProcess M τ
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum N (fun t ω => firstWeight (N t ω)) T k ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (N T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + stoppedProcess
          (nnrealTimePrimitive (fun t ω => secondWeight (M t ω) * a t ω)) τ T ω := by
  let A := nnrealTimePrimitive a
  let τ := jointExit M A n
  let N := stoppedProcess M τ
  have hproga' := isStronglyProgressive_mono_filtration F.le_rightCont hproga
  have hprogM' := isStronglyProgressive_mono_filtration F.le_rightCont hprogM
  have hprogA := isStronglyProgressive_nnrealTimePrimitive hproga
  have hprogA' := isStronglyProgressive_mono_filtration F.le_rightCont hprogA
  have hτ : IsStoppingTime F.rightCont τ :=
    isStoppingTime_jointExit hprogM'.stronglyAdapted.adapted hprogA'.stronglyAdapted.adapted n
  have hai (k : ℕ) : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (k : ℝ))).prod μ) := by
    simpa only [NNReal.coe_natCast] using ha (k : ℝ≥0)
  have hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω) :=
    ae_continuous_nnrealTimePrimitive_of_joint hai
  have hmonoA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω) :=
    ae_monotone_nnrealTimePrimitive_of_joint hai hnonneg
  have hAint (t : ℝ≥0) : Integrable (A t) μ :=
    nnrealTimePrimitive_integrable (ha t)
  have hApos : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω :=
    hnonneg.mono (fun ω hω t => nnrealTimePrimitive_nonneg hω t)
  have hA0 (ω : Ω) : A 0 ω = 0 := by simp [A, nnrealTimePrimitive]
  have hN : Martingale N F.rightCont μ :=
    martingale_stoppedProcess_rightCont hM hprogM hcM
      (fun _ => ⟨fun _ => 1, integrable_const _,
        hbound.mono (fun ω hω t _ => hω t)⟩) hτ
  have hQτ := martingale_stopped_compensatedSquare_rightCont hQ hprogM hprogA
    hcM hcA (by norm_num : (0 : ℝ) ≤ 1) hbound hApos hmonoA hAint hτ
  have hcN : ∀ᵐ ω ∂μ, ContinuousOn (fun t => N t ω) (Icc 0 T) :=
    hcM.mono (fun ω hω => (continuous_stoppedProcess hω τ).continuousOn)
  have hcB : ∀ᵐ ω ∂μ, ContinuousOn (fun t => stoppedProcess A τ t ω) (Icc 0 T) :=
    hcA.mono (fun ω hω => (continuous_stoppedProcess hω τ).continuousOn)
  have hmonoB : ∀ᵐ ω ∂μ, MonotoneOn (fun t => stoppedProcess A τ t ω) (Icc 0 T) :=
    hmonoA.mono (fun ω hω => (monotone_stoppedProcess hω τ).monotoneOn _)
  have hbN : ∀ᵐ ω ∂μ, ∀ t, |N t ω| ≤ threshold n := by
    filter_upwards [hcM, hzero] with ω hc hz
    exact abs_stopped_posterior_le hc hz n
  have hB0 (ω : Ω) : stoppedProcess A τ 0 ω = 0 := by
    rw [stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from zero_le)]
    exact hA0 ω
  have htotal : ∀ᵐ ω ∂μ,
      stoppedProcess A τ T ω - stoppedProcess A τ 0 ω ≤ (n : ℝ) + 1 := by
    filter_upwards [hcA] with ω hc
    rw [hB0, sub_zero]
    exact (le_abs_self _).trans (abs_stopped_compensator_le hc (hA0 ω) n T)
  have hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      stoppedProcess A τ t ω = stoppedProcess A τ 0 ω +
        nnrealTimePrimitive (stopDensity a τ) t ω := by
    apply Eventually.of_forall
    intro ω t _
    rw [hB0, zero_add]
    exact stoppedProcess_primitive a τ t ω
  obtain ⟨L, hLm, hL2, hlim, heq⟩ :=
    ConstructedArtanhFormula.exists_artanh_decomposition T hN hQτ
      (stronglyMeasurable_joint_of_isStronglyProgressive (hprogM'.stoppedProcess hτ)).measurable
      hcN hcB hmonoB (threshold_nonneg n) (threshold_lt_one n) hbN
      (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) htotal
      (integrable_stopDensity hproga' hτ T (ha T)) hprimitive
  refine ⟨L, hLm, hL2, hlim, ?_⟩
  filter_upwards [heq] with ω hω
  have hN0 : N 0 ω = M 0 ω :=
    stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from zero_le)
  rw [hN0] at hω
  rw [stoppedProcess_weighted_primitive M secondWeight a τ T ω]
  exact hω

end Problem367.LocalizedArtanhFormula

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition_oai.{u_1} := @OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition_oai.{u_1}
