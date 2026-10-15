-- Prove2me | solution 1 for OAI.ThorpCompatibility.rankLaw_allowed_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:36:41.144134+00:00
-- url     : https://prove2.me/submissions/9d552da5-b6ab-4e32-90db-379950e93370

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/RankAverages.lean:L120-L138
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.rankLaw_allowed_mean_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Theorems.Thm_OAI_ThorpCompatibility_prescribed_function_card_le
import Theorems.Thm_OAI_ThorpCompatibility_uniform_rank_prob

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

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, P.total]

lemma mean_mono (P : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.mean f ≤ P.mean g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

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
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma prob_eq_mean (P : Law α) (S : α → Prop) [DecidablePred S] :
    P.prob S = P.mean (fun a => if S a then 1 else 0) := by
  unfold prob mean
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

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

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RankLaw ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α] [Nonempty α]

lemma uniform_prob_card (S : α → Prop) [DecidablePred S] :
    (uniform : Law α).prob S =
      ((Finset.univ.filter S).card : ℝ) / Fintype.card α := by
  calc
    _ = ∑ _a ∈ Finset.univ.filter S, (1 / (Fintype.card α : ℝ)) := by
      rw [Finset.sum_filter]
      unfold prob uniform
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : S a <;> simp [ha]
    _ = _ := by simp [div_eq_mul_inv]

omit [Nonempty α] in
lemma restrict_prob (P : Law α) (S T : α → Prop) (hS : 0 < P.prob S) :
    (P.restrict S).prob T = P.prob (fun a => S a ∧ T a) / P.prob S := by
  simp only [prob, P.restrict_mass S hS, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : S a <;> by_cases ht : T a <;> simp [hs, ht]

end Law
open Finset

lemma uniform_two_rank_prob_le {D : ℕ} (hD : 2 ≤ D) (k l t s : Fin D) (hkl : k ≠ l) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t ∧ e l = s) ≤
      1 / ((D : ℝ) * (D - 1 : ℕ)) := by
  rw [Law.uniform_prob_card]
  have hc := prescribed_function_card_le {k,l} (fun x : Fin D => if x = k then t else s)
  have hs : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) =>
      ∀ x ∈ ({k,l} : Finset (Fin D)), e x = if x = k then t else s)) =
      Finset.univ.filter (fun e => e k = t ∧ e l = s) := by
    ext e
    simp [Ne.symm hkl]
  have hc' : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) => e k = t ∧ e l = s)).card ≤
      (D - 2).factorial := by
    convert hc using 2
    · ext e
      simp [Ne.symm hkl]
    · simp [hkl]
  have hp : (0 : ℝ) < D.factorial := by positivity
  rw [Fintype.card_perm, Fintype.card_fin]
  calc
    _ ≤ ((D - 2).factorial : ℝ) / D.factorial :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc') hp.le
    _ = _ := by
      have hf' : ((D-2).factorial : ℝ) * ((D:ℝ) * (D-1:ℕ)) = D.factorial := by
        exact_mod_cast (by simpa [Nat.descFactorial_succ, mul_comm] using
          Nat.factorial_mul_descFactorial hD)
      have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      have hD1 : (0 : ℝ) < (D-1:ℕ) := by exact_mod_cast (by omega : 0 < D-1)
      apply (div_eq_div_iff hp.ne' (mul_pos hD0 hD1).ne').mpr
      simpa using hf'

lemma rankLaw_mass_pos_iff {D : ℕ} (k t : Fin D) (e : Equiv.Perm (Fin D)) :
    0 < (rankLaw k t).mass e ↔ e k = t := by
  have hD : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin D)) := by positivity
  have hp : 0 < (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) := by
    rw [uniform_rank_prob]; positivity
  rw [rankLaw, Law.restrict_mass _ _ hp, uniform_rank_prob]
  by_cases he : e k = t <;> simp [he, Law.uniform, hD, hc]

lemma rankLaw_other_prob_le {D : ℕ} (hD : 2 ≤ D) (k l t s : Fin D) (hkl : k ≠ l) :
    (rankLaw k t).prob (fun e => e l = s) ≤ 1 / (D - 1 : ℕ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hp : 0 < (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) := by
    rw [uniform_rank_prob]; positivity
  rw [rankLaw, Law.restrict_prob _ _ _ hp, uniform_rank_prob]
  calc
    _ ≤ (1 / ((D : ℝ) * (D - 1 : ℕ))) / (1 / (D : ℝ)) :=
      div_le_div_of_nonneg_right (uniform_two_rank_prob_le hD k l t s hkl) (by positivity)
    _ = _ := by field_simp

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RankAverages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_comm (P : Law α) (Q : Law β) (f : α → β → ℝ) :
    P.mean (fun a => Q.mean (f a)) = Q.mean (fun b => P.mean (fun a => f a b)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma prob_congr_support (P : Law α) {S T : α → Prop}
    (h : ∀ a, 0 < P.mass a → (S a ↔ T a)) : P.prob S = P.prob T := by
  rw [P.prob_eq_mean, P.prob_eq_mean]
  apply P.mean_congr_support
  intro a ha
  rw [h a ha]

lemma prob_map (P : Law α) (f : α → β) (S : β → Prop) :
    (P.map f).prob S = P.prob (fun a => S (f a)) := by
  rw [P.prob_eq_mean, prob_eq_mean, P.mean_map]
  rfl

lemma prob_eq_sum_filter (P : Law α) (S : α → Prop) [DecidablePred S] :
    P.prob S = ∑ a ∈ Finset.univ.filter S, P.mass a := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

lemma prob_le_card_mul (P : Law α) (S : α → Prop) [DecidablePred S]
    (c : ℝ) (hc : ∀ a, S a → P.mass a ≤ c) :
    P.prob S ≤ ((Finset.univ.filter S).card : ℝ) * c := by
  rw [P.prob_eq_sum_filter S]
  calc
    _ ≤ ∑ _a ∈ Finset.univ.filter S, c :=
      Finset.sum_le_sum (fun a ha => hc a (Finset.mem_filter.mp ha).2)
    _ = _ := by simp

lemma mean_ite_const (P : Law α) (S : α → Prop) [DecidablePred S] (x y : ℝ) :
    P.mean (fun a => if S a then x else y) =
      P.prob S * x + (1 - P.prob S) * y := by
  rw [← P.prob_not S]
  simp only [mean, prob, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

end Law
open Finset

lemma rankLaw_later_le {D : ℕ} (hD : 2 ≤ D) (k l t : Fin D) (hkl : k ≠ l) :
    (rankLaw k t).prob (fun e => e k ≤ e l) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) := by
  have he : (rankLaw k t).prob (fun e => e k ≤ e l) =
      ((rankLaw k t).map (fun e => e l)).prob (fun s => t < s) := by
    rw [Law.prob_map]
    apply Law.prob_congr_support
    intro e he
    have hk := (rankLaw_mass_pos_iff k t e).mp he
    have hn : e l ≠ e k := fun h => hkl (e.injective h).symm
    rw [hk] at hn ⊢
    constructor
    · intro h
      exact lt_of_le_of_ne h (Ne.symm hn)
    · exact le_of_lt
  rw [he]
  have hb := Law.prob_le_card_mul ((rankLaw k t).map (fun e => e l)) (fun s => t < s)
    (1 / ((D - 1 : ℕ) : ℝ)) (by
      intro s _
      rw [← Law.prob_eq_map_mass]
      exact rankLaw_other_prob_le hD k l t s hkl)
  have hc : (Finset.univ.filter (fun s : Fin D => t < s)).card = D - 1 - (t : ℕ) := by
    have he : Finset.univ.filter (fun s : Fin D => t < s) = Finset.Ioi t := by ext s; simp
    rw [he, Fin.card_Ioi]
  rw [hc] at hb
  refine le_trans hb ?_
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have ht0 : (t : ℕ) ≤ D - 1 := by omega
  have hDt : (t : ℕ) ≤ D := Nat.le_of_lt t.isLt
  have hD1 : (0 : ℝ) < (D : ℝ) - 1 := by
    have h : (1 : ℝ) < D := by exact_mod_cast (by omega : 1 < D)
    linarith
  rw [Nat.cast_sub ht0, Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_sub hDt, Nat.cast_one]
  rw [mul_one_div]
  apply (div_le_div_iff₀ hD1 hD0).mpr
  have htpos : (0 : ℝ) ≤ (t : ℕ) := Nat.cast_nonneg _
  nlinarith

lemma rankLaw_allowed_mean_le {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k t : Fin D) :
    (rankLaw k t).mean (fun e => B.prob (fun b => e k ≤ e (f b))) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) + B.prob (fun b => f b = k) := by
  simp_rw [Law.prob_eq_mean]
  rw [Law.mean_comm]
  have hprob (b : β) : (rankLaw k t).mean (fun e => if e k ≤ e (f b) then 1 else 0) ≤
      (if f b = k then 1 else ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) := by
    by_cases hb : f b = k
    · simp [hb, Law.mean_const]
    · rw [ite_eq_right hb, ← Law.prob_eq_mean]
      exact rankLaw_later_le hD k (f b) t (Ne.symm hb)
  have h := B.mean_mono hprob
  rw [B.mean_ite_const] at h
  rw [← B.prob_eq_mean]
  refine le_trans h ?_
  have hα := B.prob_nonneg (fun b => f b = k)
  have hb : 0 ≤ ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) := by positivity
  nlinarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k t : Fin D) :
    (rankLaw k t).mean (fun e => B.prob (fun b => e k ≤ e (f b))) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) + B.prob (fun b => f b = k) := by
  first
    | exact OAI.ThorpCompatibility.rankLaw_allowed_mean_le hD B f k t
    | exact OAI.ThorpCompatibility.rankLaw_allowed_mean_le
    | (apply OAI.ThorpCompatibility.rankLaw_allowed_mean_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.rankLaw_allowed_mean_le <;> assumption)
