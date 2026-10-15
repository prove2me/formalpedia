-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.condEntropy_light_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:25:08.855132+00:00
-- url     : https://prove2.me/submissions/2ddc06b9-ea6c-43a4-8834-3364a0fafa80

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/LightRescaling.lean:L126-L148
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.condEntropy_light_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_le_prediction

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.LightRescaling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma mass_le_prob (P : Law α) (S : α → Prop) {a : α} (ha : S a) :
    P.mass a ≤ P.prob S := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if S b then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [ha, prob] using h

lemma lightRescale_mass_of_not (P : Law α) (L S : α → Prop) {a : α} (ha : ¬L a) :
    (P.lightRescale L S).mass a = P.mass a := by
  unfold lightRescale
  split_ifs <;> simp [ha]

lemma lightRescale_mass_of_mem (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hL : L a) (hS : S a) :
    (P.lightRescale L S).mass a = P.mass a * P.prob L / P.prob (fun a => L a ∧ S a) := by
  have hA : 0 < P.prob (fun a => L a ∧ S a) :=
    lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩)
  simp [lightRescale, hA, hL, hS, mul_div_assoc]

lemma lightRescale_pos (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hS : S a) : 0 < (P.lightRescale L S).mass a := by
  by_cases hL : L a
  · rw [P.lightRescale_mass_of_mem L S hp hL hS]
    exact div_pos (mul_pos hp (lt_of_lt_of_le hp (P.mass_le_prob L hL)))
      (lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩))
  · simpa [P.lightRescale_mass_of_not L S hL] using hp

lemma lightRescale_log (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hS : S a) :
    Real.log ((P.lightRescale L S).mass a) = Real.log (P.mass a) -
      (if L a then Real.log (P.prob (fun b => L b ∧ S b) / P.prob L) else 0) := by
  by_cases hL : L a
  · have hA : 0 < P.prob (fun b => L b ∧ S b) :=
      lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩)
    have hB : 0 < P.prob L := lt_of_lt_of_le hp (P.mass_le_prob L hL)
    rw [P.lightRescale_mass_of_mem L S hp hL hS, ite_eq_left hL,
      Real.log_div (mul_pos hp hB).ne' hA.ne', Real.log_mul hp.ne' hB.ne',
      Real.log_div hA.ne' hB.ne']
    ring
  · rw [P.lightRescale_mass_of_not L S hL, ite_eq_right hL, sub_zero]

lemma condEntropy_light_comparison (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (L S : γ → β → Prop)
    (hK : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a))
    (hS : ∀ a, 0 < P.mass a → S (Y a) (X a)) :
    P.mean (fun a => if L (Y a) (X a) then
      -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
        (K (Y a)).prob (L (Y a))) else 0) ≤
      -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) - P.condEntropy X Y := by
  have h := P.condEntropy_le_prediction X Y
    (fun y => (K y).lightRescale (L y) (S y))
    (fun a ha => (K (Y a)).lightRescale_pos (L (Y a)) (S (Y a)) (hK a ha) (hS a ha))
  have he : P.mean (fun a => Real.log (((K (Y a)).lightRescale (L (Y a)) (S (Y a))).mass (X a))) =
      P.mean (fun a => Real.log ((K (Y a)).mass (X a))) +
        P.mean (fun a => if L (Y a) (X a) then
          -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
            (K (Y a)).prob (L (Y a))) else 0) := by
    rw [← P.mean_add]
    apply P.mean_congr_support
    intro a ha
    rw [(K (Y a)).lightRescale_log _ _ (hK a ha) (hS a ha)]
    split_ifs <;> ring
  rw [he] at h
  linarith

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem solution (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (L S : γ → β → Prop)
    (hK : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a))
    (hS : ∀ a, 0 < P.mass a → S (Y a) (X a)) :
    P.mean (fun a => if L (Y a) (X a) then
      -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
        (K (Y a)).prob (L (Y a))) else 0) ≤
      -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) - P.condEntropy X Y := by
  first
    | exact OAI.ThorpCompatibility.Law.condEntropy_light_comparison P X Y K L S hK hS
    | exact OAI.ThorpCompatibility.Law.condEntropy_light_comparison
    | (apply OAI.ThorpCompatibility.Law.condEntropy_light_comparison <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.condEntropy_light_comparison <;> assumption)
