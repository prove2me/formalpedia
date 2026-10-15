-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.mean_predict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:32:44.73498+00:00
-- url     : https://prove2.me/submissions/3ee2374c-be6c-421b-85a7-9838c87625cc

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Prediction.lean:L74-L106
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.mean_predict. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Theorems.Thm_OAI_ThorpCompatibility_Law_map_mass_pos_iff

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

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Prediction ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma restrict_mass (P : Law α) (S : α → Prop) (h : 0 < P.prob S) (a : α) :
    (P.restrict S).mass a = (if S a then P.mass a else 0) / P.prob S := by
  simp [restrict, h]

lemma prob_eq_map_mass (P : Law α) (Y : α → γ) (y : γ) :
    P.prob (fun a => Y a = y) = (P.map Y).mass y := by rfl

lemma predict_mass (P : Law α) (X : α → β) (Y : α → γ) (y : γ)
    (hy : 0 < (P.map Y).mass y) (x : β) :
    (P.predict X Y y).mass x =
      (P.map (fun a => (X a, Y a))).mass (x, y) / (P.map Y).mass y := by
  have hp : 0 < P.prob (fun a => Y a = y) := hy
  simp only [predict, map, P.restrict_mass _ hp, prob_eq_map_mass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : X a = x <;> by_cases hy' : Y a = y <;> simp [hx, hy']

lemma mean_predict (P : Law α) (X : α → β) (Y : α → γ) (f : γ → β → ℝ) :
    P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      P.mean (fun a => f (Y a) (X a)) := by
  have he : P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      (P.map Y).mean (fun y => (P.predict X Y y).mean (f y)) := by
    rw [P.mean_map]
    rfl
  rw [he]
  have hsum : (P.map Y).mean (fun y => (P.predict X Y y).mean (f y)) =
      ∑ y, ∑ x, (P.map (fun a => (X a, Y a))).mass (x, y) * f y x := by
    unfold mean
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hy : (P.map Y).mass y = 0
    · have hz : (P.map (fun a => (X a, Y a))).mass (x, y) = 0 := by
        by_contra hn
        obtain ⟨a, he, ha⟩ := (P.map_mass_pos_iff _ _).mp
          (lt_of_le_of_ne ((P.map _).nonneg _) (Ne.symm hn))
        have hpos := P.map_mass_pos Y ha
        have hya : Y a = y := congrArg Prod.snd he
        rw [hya, hy] at hpos
        exact lt_irrefl _ hpos
      simp [hy, hz]
    · rw [P.predict_mass X Y y (lt_of_le_of_ne ((P.map Y).nonneg _) (Ne.symm hy)) x]
      field_simp
  rw [hsum, Finset.sum_comm]
  calc
    _ = (P.map (fun a => (X a, Y a))).mean (fun b => f b.2 b.1) := by
      rw [mean, Fintype.sum_prod_type]
    _ = _ := P.mean_map _ _

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem solution (P : Law α) (X : α → β) (Y : α → γ) (f : γ → β → ℝ) :
    P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      P.mean (fun a => f (Y a) (X a)) := by
  first
    | exact OAI.ThorpCompatibility.Law.mean_predict P X Y f
    | exact OAI.ThorpCompatibility.Law.mean_predict
    | (apply OAI.ThorpCompatibility.Law.mean_predict <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.mean_predict <;> assumption)
