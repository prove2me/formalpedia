-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:25:06.467898+00:00
-- url     : https://prove2.me/submissions/1feed423-ad2c-4661-8b72-29731a893f57

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L85-L107
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card. The node keeps its source
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

theorem entropy_le_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    entropy s p ≤ Real.log s.card := by
  classical
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hs
    norm_num at hs
  have hn : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hterm : ∀ a ∈ s, (s.card : ℝ) * Real.negMulLog (p a) ≤
      1 - (s.card : ℝ) * p a - p a * Real.negMulLog s.card := by
    intro a ha
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hn.le (hp a ha))
    rw [Real.negMulLog_mul] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hs, mul_one, one_mul, Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) * entropy s p ≤ _ at hsum
  have hneg : Real.negMulLog (s.card : ℝ) = -(s.card : ℝ) * Real.log s.card := rfl
  rw [hneg] at hsum
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card.{uα} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card.{uα}
