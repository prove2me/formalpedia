-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:26:41.88663+00:00
-- url     : https://prove2.me/submissions/479cc306-61ba-40da-9047-1495e1e3967e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L121-L143
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem entropy_scale {α : Type uα} (s : Finset α) (p : α → ℝ) (c : ℝ) :
    entropy s (fun a => c * p a) =
      (∑ a ∈ s, p a) * Real.negMulLog c + c * entropy s p := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem entropy_normalize {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * entropy s (fun a => p a / ∑ b ∈ s, p b) := by
  let P := ∑ a ∈ s, p a
  by_cases hP : P = 0
  · have hz : ∀ a ∈ s, p a = 0 := by
      intro a ha
      have ha' := Finset.single_le_sum hp ha
      change p a ≤ P at ha'
      rw [hP] at ha'
      exact le_antisymm ha' (hp a ha)
    change entropy s p = Real.negMulLog P + P * _
    simp only [hP, Real.negMulLog_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero (fun a ha => by rw [hz a ha, Real.negMulLog_zero])
  · have heq : entropy s p = entropy s (fun a => P * (p a / P)) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      rw [mul_div_cancel₀ _ hP]
    rw [heq, entropy_scale]
    have hsum : (∑ a ∈ s, p a / P) = 1 := by rw [← Finset.sum_div]; exact div_self hP
    rw [hsum, one_mul]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize.{uα} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize.{uα}
