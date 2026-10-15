-- Prove2me | solution 1 for OAI.ThorpCompatibility.uniform_rank_prob
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:34:06.856985+00:00
-- url     : https://prove2.me/submissions/a1bed613-f6c9-4a6a-b658-906a3e7cf2e3

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/RankLaw.lean:L37-L51
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.uniform_rank_prob. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_prescribed_permutation_card

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

end Law
open Finset

lemma uniform_rank_prob {D : ℕ} (k t : Fin D) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) = 1 / (D : ℝ) := by
  rw [Law.uniform_prob_card]
  have hc := prescribed_permutation_card {k} (Equiv.swap k t)
  simp only [Finset.mem_singleton, forall_eq, Equiv.swap_apply_left,
    Fintype.card_fin, Finset.card_singleton] at hc
  have he : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) => e k = t)).card =
      (D - 1).factorial := by convert hc using 2
  rw [he, Fintype.card_perm, Fintype.card_fin]
  have hD : 0 < D := k.pos
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  simp

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {D : ℕ} (k t : Fin D) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) = 1 / (D : ℝ) := by
  first
    | exact OAI.ThorpCompatibility.uniform_rank_prob k t
    | exact OAI.ThorpCompatibility.uniform_rank_prob
    | (apply OAI.ThorpCompatibility.uniform_rank_prob <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.uniform_rank_prob <;> assumption)
