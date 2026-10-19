-- Prove2me | solution 2 for OAI.EntropyRateDimension.LocalMass.lower_dim_eq_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:17:37.509172+00:00
-- url     : https://prove2.me/submissions/8cac9e2e-a05c-454d-8e11-164a0866d47c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MassDimension.lean:L92-L128
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.LocalMass.lower_dim_eq_of_limit. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_dim_le_of_uniform_lower_mass
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_eventual_lower_of_limit
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_large_uniform_mass_set
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_lower_dim_ge_of_limit

-- ---- from OAI.MeasureTheory.SelfSimilar.MassDimension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension.LocalMass
open MeasureEntropy

theorem lower_dim_eq_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d : ℝ} (hd : 0 ≤ d)
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    lowerHausdorffDimension μ = ENNReal.ofReal d := by
  apply le_antisymm _ (lower_dim_ge_of_limit μ hlim)
  have hub : ∀ e : ℝ, d < e → lowerHausdorffDimension μ ≤ ENNReal.ofReal e := by
    intro e hde
    have he := hd.trans hde.le
    obtain ⟨E,hE,hEc,R,hR,hball⟩ := large_uniform_mass_set μ he (by norm_num : (0 : ℝ)<1/2) (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_lower_of_limit μ hs hde hx)
    obtain ⟨B,_,hB⟩ := hc
    let F := E ∩ Icc (-B) B
    have hF : MeasurableSet F := hE.inter measurableSet_Icc
    have hpos : 0 < μ F := by
      by_contra hn
      have hz : μ F=0 := le_antisymm (le_of_not_gt hn) bot_le
      have hEF : E =ᵐ[μ] F := by
        filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hB] with x hx
        apply propext
        exact ⟨fun h => ⟨h,hx⟩,fun h => h.1⟩
      have hez : μ E=0 := (measure_congr hEF).trans hz
      have hec : μ.real Eᶜ=1 := by simp [Measure.real,measure_compl hE (measure_ne_top μ E),hez]
      linarith
    calc
      lowerHausdorffDimension μ ≤ dimH F :=
        iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le hpos le_rfl))
      _ ≤ ENNReal.ofReal e := dim_le_of_uniform_lower_mass μ F he hR inter_subset_right
        (fun x hx r hr hrR => hball x hx.1 r hr hrR)
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (d+1/((n : ℝ)+1))) atTop
      (𝓝 (ENNReal.ofReal d)) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [add_zero] using (tendsto_const_nhds (x := d)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall (fun n => hub _ (by
    have : 0 < 1/((n : ℝ)+1) := by positivity
    linarith)))

end EntropyRateDimension.LocalMass

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.LocalMass
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureEntropy


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.LocalMass.lower_dim_eq_of_limit := @_root_.OAI.EntropyRateDimension.LocalMass.lower_dim_eq_of_limit
