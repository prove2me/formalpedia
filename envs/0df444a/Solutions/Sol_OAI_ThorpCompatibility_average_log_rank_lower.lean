-- Prove2me | solution 1 for OAI.ThorpCompatibility.average_log_rank_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:19:05.688048+00:00
-- url     : https://prove2.me/submissions/fde97633-dba4-4b09-bc63-396c4f2fd991

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/LogEstimates.lean:L67-L83
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.average_log_rank_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Theorems.Thm_OAI_ThorpCompatibility_log_factorial_upper

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

lemma sum_log_sub (n : ℕ) :
    (∑ t : Fin n, Real.log ((n - (t : ℕ) : ℕ) : ℝ)) = Real.log (n.factorial : ℝ) := by
  rw [sum_reverse_succ n (fun k => Real.log (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => Real.log ((k + 1 : ℕ) : ℝ)),
    Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  exact (Real.log_prod (fun i _ => by positivity)).symm

lemma average_log_rank_lower {D : ℕ} (hD : 0 < D) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) ≤
      (∑ t : Fin D, -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) / D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have he (t : Fin D) : -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) =
      Real.log (D : ℝ) - Real.log ((D - (t : ℕ) : ℕ) : ℝ) := by
    rw [Real.log_div (by exact_mod_cast (Nat.sub_pos_of_lt t.isLt).ne') hD0.ne']
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, sum_log_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := log_factorial_upper D hD
  apply (le_div_iff₀ hD0).mpr
  have he : (1 - (1 + Real.log (D : ℝ)) / (D : ℝ)) * D =
      (D : ℝ) - (1 + Real.log (D : ℝ)) := by field_simp
  rw [he]
  linarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {D : ℕ} (hD : 0 < D) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) ≤
      (∑ t : Fin D, -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) / D := by
  first
    | exact OAI.ThorpCompatibility.average_log_rank_lower hD
    | exact OAI.ThorpCompatibility.average_log_rank_lower
    | (apply OAI.ThorpCompatibility.average_log_rank_lower <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.average_log_rank_lower <;> assumption)
