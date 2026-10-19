-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:13:38.911622+00:00
-- url     : https://prove2.me/submissions/6512e731-ad53-4dd5-8004-12797436b292

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/EntropyDimension.lean:L45-L89
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_eventual_lower_of_limit
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_large_uniform_mass_set
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_le_of_ball_mass
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_support_card_le

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem mass_le_one {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) (b : β) : mass μ f b ≤ 1 := by
  exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem entropy_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) : 0 ≤ entropy μ f :=
  tsum_nonneg (fun b => Real.negMulLog_nonneg (mass_nonneg μ f b) (mass_le_one μ f b))

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem label_joint_measurable (s : ℝ) : Measurable (fun ux : ℝ × ℝ => label s ux.1 ux.2) :=
  ((measurable_snd.div_const s).add measurable_fst).floor

theorem measurable_mass_label (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) (b : ℤ) :
    Measurable (fun u => mass μ (label s u) b) := by
  have h := measurable_measure_prodMk_left (ν := μ)
    ((measurableSet_singleton b).preimage (label_joint_measurable s))
  exact h.ennreal_toReal

theorem measurable_grid (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (grid μ s) :=
  Measurable.tsum (fun b => Real.continuous_negMulLog.measurable.comp (measurable_mass_label μ s b))

theorem label_ae_uniform (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ := by
  filter_upwards [label_ae_finite μ hs hB] with x hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.floor_le_floor (by linarith [hu.1] : -B/s ≤ -B/s+u)).trans hlo,
    hhi.trans (Int.floor_le_floor (by linarith [hu.2] : B/s+u ≤ B/s+1))⟩

theorem grid_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (s u : ℝ) : 0 ≤ grid μ s u :=
  entropy_nonneg μ _

theorem grid_le_card (μ : Measure ℝ) [IsProbabilityMeasure μ] {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    grid μ s u ≤ (Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card := by
  rw [grid, entropy_eq_sum μ _ _ (label_ae_uniform μ hs hB hu)]
  calc
    _ ≤ ∑ b ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Real.negMulLog_le_one_sub_self (mass_nonneg μ _ b)).trans
        (sub_le_self _ (mass_nonneg μ _ b))
    _ = _ := by simp

theorem grid_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) : Integrable (grid μ s) (volume.restrict (Set.Icc 0 1)) := by
  obtain ⟨B,_,hB⟩ := hμ
  apply (integrable_const ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)).mono'
    (measurable_grid μ s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (grid_nonneg μ s u)]
  exact grid_le_card μ hs hB hu

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyDimension ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension.MeasureEntropy

theorem grid_le_of_quarter_power_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u d η : ℝ} (hB0 : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1)
    (hd : 0 ≤ d) (hη0 : 0 ≤ η)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, (s/4)^d ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 6+d*Real.log 4+η*Real.log (2*B+3)+
      (d+η)*Real.log (1/s) := by
  have hq : 0 < (s/4)^d := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : (s/4)^d ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) hd
  have hh := grid_le_of_ball_mass μ hs hq hB hu E hη hball
  have hq3 : 1 ≤ 3/(s/4)^d := (le_div_iff₀ hq).mpr (by linarith)
  rw [max_eq_right hq3] at hh
  have hnum : 0 < 2*B+3 := by linarith
  have hcard := grid_support_card_le hB0 hs hs1
  have hbase : 1 ≤ (2*B+3)/s := (le_div_iff₀ hs).mpr (by linarith)
  have hlog : Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) ≤
      Real.log ((2*B+3)/s) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hbase hcard)
  have hm := mul_le_mul_of_nonneg_left hlog hη0
  have he : Real.log 2+Real.log (3/(s/4)^d)+η*Real.log ((2*B+3)/s) =
      Real.log 6+d*Real.log 4+η*Real.log (2*B+3)+(d+η)*Real.log (1/s) := by
    rw [Real.log_div (by norm_num) hq.ne',Real.log_rpow (by positivity),
      Real.log_div hs.ne' (by norm_num),Real.log_div hnum.ne' hs.ne',
      Real.log_div (by norm_num) hs.ne',Real.log_one]
    have h6 : Real.log (6 : ℝ)=Real.log 2+Real.log 3 := by
      rw [show (6 : ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    rw [h6]
    ring
  rw [← he]
  linarith

theorem entropy_bound_of_radial_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d D : ℝ} (hd : 0 ≤ d) (hD : d < D)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C := by
  let e := (d+D)/2
  let η := (D-d)/4
  have hde : d < e := by dsimp [e]; linarith
  have he : 0 ≤ e := le_trans hd hde.le
  have hη : 0 < η := by dsimp [η]; linarith
  have heη : e+η ≤ D := by dsimp [e,η]; linarith
  have hD0 : 0 ≤ D := hd.trans hD.le
  obtain ⟨E,hE,hEc,R,hR,hball⟩ := LocalMass.large_uniform_mass_set μ he hη (by
    filter_upwards [hlim,μ.support_mem_ae] with x hx hs
    exact LocalMass.eventual_lower_of_limit μ hs hde hx)
  obtain ⟨B,hB0,hB⟩ := hc
  let C₀ := Real.log 6+e*Real.log 4+η*Real.log (2*B+3)
  let C := max C₀ ((2*B+3)/R)
  refine ⟨C,?_⟩
  intro s hs hs1
  have hlog : 0 ≤ Real.log (1/s) := Real.log_nonneg ((one_le_div hs).mpr hs1.le)
  have hgrid : ∀ u ∈ Set.Icc (0 : ℝ) 1, grid μ s u ≤ D*Real.log (1/s)+C := by
    intro u hu
    by_cases hsR : s < R
    · have hh := grid_le_of_quarter_power_ball_mass μ hB0 hs hs1.le he hη.le hB hu E hEc
        (fun x hx => by
          have hr := hball x hx (s/2) (by positivity) (by linarith)
          simpa only [show s/2/2=s/4 by ring] using hr)
      have hm := mul_le_mul_of_nonneg_right heη hlog
      have hC : C₀ ≤ C := le_max_left _ _
      dsimp only [C₀] at hC
      linarith
    · have hRs : R ≤ s := le_of_not_gt hsR
      have hh := (grid_le_card μ hs hB hu).trans (grid_support_card_le hB0 hs hs1.le)
      have hdiv : (2*B+3)/s ≤ (2*B+3)/R :=
        div_le_div_of_nonneg_left (by linarith) hR hRs
      have hC : (2*B+3)/R ≤ C := le_max_right _ _
      have hm := mul_nonneg hD0 hlog
      linarith
  have hh := integral_mono_ae (grid_integrable μ ⟨B,hB0,hB⟩ hs)
    (integrable_const (D*Real.log (1/s)+C)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hgrid u hu)
  simpa [averaged,integral_const,Measure.real_def] using hh

end EntropyRateDimension.MeasureEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit := @_root_.OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit
