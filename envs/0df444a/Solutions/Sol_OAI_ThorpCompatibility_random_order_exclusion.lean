-- Prove2me | solution 1 for OAI.ThorpCompatibility.random_order_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:38:02.544998+00:00
-- url     : https://prove2.me/submissions/f0c61faf-daae-4cdd-8f24-d90f9faeced2

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/RandomExclusion.lean:L11-L48
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.random_order_exclusion. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_neg_log_mean_le
import Theorems.Thm_OAI_ThorpCompatibility_average_log_rank_lower
import Theorems.Thm_OAI_ThorpCompatibility_rankLaw_allowed_mean_le
import Theorems.Thm_OAI_ThorpCompatibility_rankLaw_mean_average

-- ---- from OAI.Probability.ThorpCompatibility.LogEstimates ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

lemma sum_reverse_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ t : Fin n, f (n - (t : ℕ))) = ∑ t : Fin n, f ((t : ℕ) + 1) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro t
  congr 1
  change n - (t : ℕ) = n - ((t : ℕ) + 1) + 1
  omega

lemma sum_inv_sub (n : ℕ) :
    (∑ t : Fin n, 1 / ((n - (t : ℕ) : ℕ) : ℝ)) = (harmonic n : ℝ) := by
  rw [sum_reverse_succ n (fun k => 1 / (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => 1 / ((k + 1 : ℕ) : ℝ))]
  simp [harmonic, one_div]

lemma neg_log_add_lower {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    -Real.log b - a / b ≤ -Real.log (b + a) := by
  have hba : 0 < b + a := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hba hb)
  rw [Real.log_div hba.ne' hb.ne'] at h
  have hr : (b + a) / b - 1 = a / b := by field_simp; ring
  rw [hr] at h
  linarith

lemma average_inverse_rank {D : ℕ} (hD : 0 < D) (a : ℝ) :
    (∑ t : Fin D, a / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)))) / D =
      a * (harmonic D : ℝ) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have he (t : Fin D) : a / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) =
      a * (1 / ((D - (t : ℕ) : ℕ) : ℝ)) * D := by field_simp
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_inv_sub, mul_div_cancel_right₀ _ hD0]

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

lemma prob_mono (P : Law α) {S T : α → Prop} (h : ∀ a, S a → T a) :
    P.prob S ≤ P.prob T := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hs : S a
  · simp [hs, h a hs]
  · simp [hs]
    split_ifs <;> simp_all [P.nonneg]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RandomExclusion ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma random_order_exclusion {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k : Fin D)
    (hα : 0 < B.prob (fun b => f b = k)) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) -
        B.prob (fun b => f b = k) * (1 + Real.log (D : ℝ)) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean
        (fun e => -Real.log (B.prob (fun b => e k ≤ e (f b)))) := by
  let α := B.prob (fun b => f b = k)
  let F : Equiv.Perm (Fin D) → ℝ := fun e => B.prob (fun b => e k ≤ e (f b))
  have hF (e : Equiv.Perm (Fin D)) : α ≤ F e :=
    B.prob_mono (fun b hb => by simp [hb])
  have hD0 : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hstep (t : Fin D) :
      -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) -
        α / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) ≤
          (rankLaw k t).mean (fun e => -Real.log (F e)) := by
    have hb : 0 < (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) :=
      div_pos (by exact_mod_cast Nat.sub_pos_of_lt t.isLt) hD0
    have hm : α ≤ (rankLaw k t).mean F := by
      calc
        α = (rankLaw k t).mean (fun _ => α) := (Law.mean_const _ _).symm
        _ ≤ _ := Law.mean_mono _ hF
    have hpos : 0 < (rankLaw k t).mean F := lt_of_lt_of_le hα hm
    calc
      _ ≤ -Real.log ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) + α) :=
        neg_log_add_lower hb hα.le
      _ ≤ -Real.log ((rankLaw k t).mean F) := neg_le_neg
        (Real.log_le_log hpos (rankLaw_allowed_mean_le hD B f k t))
      _ ≤ _ := Law.neg_log_mean_le _ F (fun e _ => lt_of_lt_of_le hα (hF e)) hpos
  rw [← rankLaw_mean_average k]
  have hsim := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hstep t)) hD0.le
  rw [Finset.sum_sub_distrib, sub_div,
    average_inverse_rank k.pos] at hsim
  have hbase := average_log_rank_lower k.pos
  have hharm := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) hα.le
  dsimp [α, F] at *
  linarith

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k : Fin D)
    (hα : 0 < B.prob (fun b => f b = k)) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) -
        B.prob (fun b => f b = k) * (1 + Real.log (D : ℝ)) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean
        (fun e => -Real.log (B.prob (fun b => e k ≤ e (f b)))) := by
  first
    | exact OAI.ThorpCompatibility.random_order_exclusion hD B f k hα
    | exact OAI.ThorpCompatibility.random_order_exclusion
    | (apply OAI.ThorpCompatibility.random_order_exclusion <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.random_order_exclusion <;> assumption)
