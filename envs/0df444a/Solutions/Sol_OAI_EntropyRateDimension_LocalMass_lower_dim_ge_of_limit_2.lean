-- Prove2me | solution 2 for OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:10:40.019454+00:00
-- url     : https://prove2.me/submissions/dc6c47f1-e273-4800-8a3e-6258b9481592

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean:L138-L159
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalMass ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension
namespace LocalMass

theorem restrict_le_hausdorff (μ : Measure ℝ) (E : Set ℝ) {a R : ℝ}
    (_ha : 0 ≤ a) (hR : 0 < R)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a) :
    μ.restrict E ≤ Measure.hausdorffMeasure a := by
  apply Measure.le_hausdorffMeasure a (μ.restrict E) (ENNReal.ofReal (R/2))
    (ENNReal.ofReal_pos.mpr (by positivity))
  intro A hA
  have hAtop : ediam A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hA
  have hdiam : diam A < R := by
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (R/2) ≠ ⊤) hA
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact lt_of_le_of_lt hh (by linarith)
  have hcltop : ediam (closure A) ≠ ⊤ := by rwa [ediam_closure]
  by_cases hE : (closure A ∩ E).Nonempty
  · obtain ⟨x,hxA,hxE⟩ := hE
    have hh : ∀ r : ℝ, diam A < r → r < R →
        (μ.restrict E) A ≤ (ENNReal.ofReal r)^a := by
      intro r hdr hrR
      have hr : 0 < r := lt_of_le_of_lt (diam_nonneg) hdr
      calc
        (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
        _ = μ (closure A ∩ E) := Measure.restrict_apply isClosed_closure.measurableSet
        _ ≤ μ (closedBall x r) := measure_mono (fun y hy => by
          apply mem_closedBall.mpr
          have hd := dist_le_diam_of_mem' hcltop hy.1 hxA
          rw [diam_closure] at hd
          exact hd.trans hdr.le)
        _ ≤ _ := hball x hxE r hr hrR
    have ht : Tendsto (fun r : ℝ => (ENNReal.ofReal r)^a) (𝓝[>] (diam A))
        (𝓝 ((ediam A)^a)) := by
      have he : ENNReal.ofReal (diam A)=ediam A := ENNReal.ofReal_toReal hAtop
      rw [← he]
      exact ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto _).mono_left
        nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (isOpen_Iio.mem_nhds hdiam)] with r hdr hrR
    exact hh r hdr hrR
  · have he : closure A ∩ E=∅ := Set.not_nonempty_iff_eq_empty.mp hE
    calc
      (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
      _ = 0 := by rw [Measure.restrict_apply isClosed_closure.measurableSet,he,measure_empty]
      _ ≤ _ := bot_le

theorem positive_set_dim_ge (μ : Measure ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a)
    {B : Set ℝ} (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ENNReal.ofReal a ≤ dimH B := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ r : ℝ, 0 < r → r < 1/((n : ℝ)+1) →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a}
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun r hr hrn => hRx r hr (hrn.trans hn)⟩
  have hex : ∃ n, 0 < μ (B ∩ E n) := by
    by_contra! hn
    have hzero : μ (⋃ n, B ∩ E n)=0 := measure_iUnion_null (fun n => by simpa using hn n)
    have hsub : B ≤ᵐ[μ] ⋃ n, B ∩ E n := by
      filter_upwards [hae] with x hx hxB
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n,hxB,hn⟩
    have := measure_mono_ae hsub
    rw [hzero] at this
    exact (not_lt_of_ge this) hpos
  obtain ⟨n,hn⟩ := hex
  have hdom := restrict_le_hausdorff μ (E n) ha (by positivity : 0 < 1/((n : ℝ)+1))
    (fun x hx r hr hrR => hx r hr hrR)
  have hmass : 0 < Measure.hausdorffMeasure a B := by
    have hh := hdom B
    rw [Measure.restrict_apply hB] at hh
    exact hn.trans_le hh
  have hh := le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨a,ha⟩) hmass.ne'
  convert hh using 1
  exact (ENNReal.coe_nnreal_eq ⟨a,ha⟩).symm

theorem eventual_upper_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x a d : ℝ}
    (hx : x ∈ μ.support) (had : a < d)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a := by
  have hev := hlim.eventually (lt_mem_nhds had)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : a < -Real.log (μ.real (closedBall x r)) / -Real.log r :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hlogr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr hr1)
  have hh := (lt_div_iff₀ hlogr).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  have hle : μ.real (closedBall x r) ≤ r^a := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_log hmass]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [ENNReal.ofReal_rpow_of_pos hr,← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal hle

theorem lower_dim_ge_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by
  unfold lowerHausdorffDimension
  apply le_iInf
  intro B
  apply le_iInf
  intro hB
  apply le_iInf
  intro hpos
  by_cases htop : dimH B=⊤
  · rw [htop]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply le_of_forall_lt_imp_le_of_dense
  intro a had
  by_cases ha : 0 ≤ a
  · have hh := positive_set_dim_ge μ ha (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_upper_of_limit μ hs had hx) hB hpos
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hh
  · exact (le_of_not_ge ha).trans ENNReal.toReal_nonneg

end LocalMass
end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.LocalMass
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit := @_root_.OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit
