-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.neg_log_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:27:52.219809+00:00
-- url     : https://prove2.me/submissions/dc6a573e-0334-4b7b-a329-d1d4faa5259d

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/EntropyBounds.lean:L62-L81
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.neg_log_mean_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, P.total]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul_const (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.mean (fun a => f a * c) = P.mean f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma mean_mono_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.mean f ≤ P.mean g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha)))
      (P.nonneg a)

lemma neg_log_mean_le (P : Law α) (f : α → ℝ)
    (hf : ∀ a, 0 < P.mass a → 0 < f a) (hmean : 0 < P.mean f) :
    -Real.log (P.mean f) ≤ P.mean (fun a => -Real.log (f a)) := by
  have ht (a : α) (ha : 0 < P.mass a) :
      Real.log (f a) ≤ Real.log (P.mean f) + f a / P.mean f - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hf a ha) hmean)
    rw [Real.log_div (hf a ha).ne' hmean.ne'] at h
    linarith
  have hm := P.mean_mono_support ht
  have he : P.mean (fun a => Real.log (P.mean f) + f a / P.mean f - 1) =
      Real.log (P.mean f) := by
    rw [P.mean_sub, P.mean_add, P.mean_const, P.mean_const]
    simp only [div_eq_mul_inv]
    rw [P.mean_mul_const, mul_inv_cancel₀ hmean.ne']
    ring
  rw [he] at hm
  have hn : P.mean (fun a => -Real.log (f a)) = -P.mean (fun a => Real.log (f a)) := by
    simp [mean, mul_neg, Finset.sum_neg_distrib]
  rw [hn]
  linarith

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem solution (P : Law α) (f : α → ℝ)
    (hf : ∀ a, 0 < P.mass a → 0 < f a) (hmean : 0 < P.mean f) :
    -Real.log (P.mean f) ≤ P.mean (fun a => -Real.log (f a)) := by
  first
    | exact OAI.ThorpCompatibility.Law.neg_log_mean_le P f hf hmean
    | exact OAI.ThorpCompatibility.Law.neg_log_mean_le
    | (apply OAI.ThorpCompatibility.Law.neg_log_mean_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.neg_log_mean_le <;> assumption)
