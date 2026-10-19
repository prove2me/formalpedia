-- Prove2me | solution 2 for OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:12:12.163832+00:00
-- url     : https://prove2.me/submissions/6d14a720-2a31-417d-96bc-b7d026e6933c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean:L161-L206
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set. The node keeps its source
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

theorem large_uniform_mass_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ q : ℚ, 0 < (q : ℝ) →
    (q : ℝ) < 1/((n : ℝ)+1) → (q : ℝ)^e ≤ μ.real (closedBall x q)}
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    simp only [E,Set.ofPred_forall]
    apply MeasurableSet.iInter fun q : ℚ => ?_
    apply MeasurableSet.iInter fun _ : 0 < (q : ℝ) => ?_
    apply MeasurableSet.iInter fun _ : (q : ℝ) < 1/((n : ℝ)+1) => ?_
    have hm := measurable_measure_prodMk_left (ν := μ)
      (measurableSet_le (measurable_snd.dist measurable_fst) (measurable_const (a := (q : ℝ))))
    exact measurableSet_le measurable_const hm.ennreal_toReal
  have hmono : Monotone E := by
    intro n m hnm x hx q hq hqm
    apply hx q hq
    exact hqm.trans_le (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun q hq hqn => hRx q hq (hqn.trans hn)⟩
  have hzero : μ (⋂ n, (E n)ᶜ)=0 := by
    rw [← compl_iUnion]
    exact ae_iff.mp hae
  have ht : Tendsto (fun n => μ ((E n)ᶜ)) atTop (𝓝 0) := by
    rw [← hzero]
    exact tendsto_measure_iInter_atTop (fun n => (hE n).compl.nullMeasurableSet)
      (fun n m hnm => compl_subset_compl.mpr (hmono hnm)) ⟨0,measure_ne_top μ _⟩
  have htR : Tendsto (fun n => μ.real ((E n)ᶜ)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real] using (ENNReal.continuousAt_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp ht
  obtain ⟨n,hn⟩ := (htR.eventually (gt_mem_nhds hη)).exists
  refine ⟨E n,hE n,hn.le,1/((n : ℝ)+1),by positivity,?_⟩
  intro x hx r hr hrR
  obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (by linarith : r/2 < r)
  have hmass := hx q (lt_trans (by positivity) hq1) (hq2.trans hrR)
  have hsub : closedBall x (q : ℝ) ⊆ ball x r := fun y hy =>
    mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hq2)
  exact (Real.rpow_le_rpow (by positivity) hq1.le he).trans
    (hmass.trans (measureReal_mono hsub))

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


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set := @_root_.OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set
