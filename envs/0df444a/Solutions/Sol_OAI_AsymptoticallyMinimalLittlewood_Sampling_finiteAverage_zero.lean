-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:56:00.58168+00:00
-- url     : https://prove2.me/submissions/63f13317-8f69-49bf-88b8-a651b620d6fe

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean:L223-L239
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_curved_average_zero
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_linear_average_error
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sampled_support_zero
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_tsum_eq_sum_fin

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma linear_average_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (b : ℝ)
    (hb : ∀ l : ℤ, (l : ℝ)≠b) :
    Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase 0 (-b) k)‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := linear_average_error hg hgs hA hsupp b ∅ (fun l _ ↦ hb l)
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hh := h N hN0
  simp only [Finset.sum_empty,sub_zero] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_left hC hN0 (by nlinarith)

lemma finiteAverage_eq {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) (β b : ℝ) :
    finiteAverage g N β b=(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k) := by
  rw [tsum_eq_sum_fin _ (fun k hk ↦ by rw [sampled_support_zero hg hN hk,zero_mul])]
  rfl

lemma finiteAverage_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hsupp : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {D β b : ℝ} (hD : 0≤D) (hbound : ∀ x, ‖g x‖≤D)
    (hfreq : β≠0 ∨ ∀ l : ℤ, (l : ℝ)≠b) :
    Tendsto (fun N : ℕ ↦ ‖finiteAverage g N β b‖) atTop (𝓝 0) := by
  have hs : tsupport g⊆Set.Icc (-1:ℝ) 1 := fun x hx ↦
    ⟨by linarith [(hsupp hx).1],(hsupp hx).2.le⟩
  have ht : Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase (β/N) (-b) k)‖) atTop (𝓝 0) := by
    by_cases hβ : β=0
    · rw [hβ]
      simpa only [zero_div] using linear_average_zero hg hgs (by norm_num : (0:ℝ)≤1) hs b
        (hfreq.resolve_left (not_not.mpr hβ))
    · exact curved_average_zero hg hgs (by norm_num : (0:ℝ)≤1) hD hs hbound hβ b
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [finiteAverage_eq hsupp (by omega)]

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero
