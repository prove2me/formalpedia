-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:04:59.346237+00:00
-- url     : https://prove2.me/submissions/7d0af2be-1268-491c-be64-d0708aafe1d9

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L705-L719
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem CompactlyCarried.mixture {ι : Type uι} [Fintype ι]
    (ν : ι → Measure ℝ) (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) :
    CompactlyCarried (∑ i, ENNReal.ofReal (w i) • ν i) := by
  classical
  choose C hC hCi using hν
  let B := ∑ i, C i
  have hi : ∀ i, C i ≤ B := fun i => Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨B, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hz : ν i (Set.Icc (-B) B)ᶜ = 0 := measure_mono_null (by
    intro x hx hxin
    exact hx ⟨by linarith [hxin.1,hi i],by linarith [hxin.2,hi i]⟩) (hCi i)
  rw [hz, mul_zero]

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture.{uι} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture.{uι}
