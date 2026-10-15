-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.condEntropy_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:21:26.614946+00:00
-- url     : https://prove2.me/submissions/50875bcb-2993-48e4-a895-51686d82fe18

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Entropy.lean:L115-L127
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.condEntropy_eq_mean. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy

-- ---- from OAI.Probability.ThorpCompatibility.FiniteLaw ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (g ∘ f) := by
  classical
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

lemma condEntropy_eq_mean (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y = -P.mean (fun a => Real.log (P.condMass X Y a)) := by
  have hm : P.mean (fun a => Real.log (P.condMass X Y a)) =
      P.mean (fun a => Real.log ((P.map (fun b => (X b, Y b))).mass (X a, Y a)) -
        Real.log ((P.map Y).mass (Y a))) := by
    apply P.mean_congr_support
    intro a ha
    exact Real.log_div (P.map_mass_pos _ ha).ne' (P.map_mass_pos _ ha).ne'
  rw [hm, P.mean_sub]
  unfold condEntropy entropy
  rw [P.mean_map, P.mean_map]
  simp only [Function.comp_def]
  ring

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem solution (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y = -P.mean (fun a => Real.log (P.condMass X Y a)) := by
  first
    | exact OAI.ThorpCompatibility.Law.condEntropy_eq_mean P X Y
    | exact OAI.ThorpCompatibility.Law.condEntropy_eq_mean
    | (apply OAI.ThorpCompatibility.Law.condEntropy_eq_mean <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.condEntropy_eq_mean <;> assumption)
