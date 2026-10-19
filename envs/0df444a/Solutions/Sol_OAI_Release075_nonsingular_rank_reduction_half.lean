-- Prove2me | solution 1 for OAI.Release075.nonsingular_rank_reduction_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:45:01.603983+00:00
-- url     : https://prove2.me/submissions/1b68927e-e8cc-4935-9626-4c8ce31acfd3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L177-L206
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.nonsingular_rank_reduction_half. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_det_sq_le_pow_of_row_sq_le
import Theorems.Thm_OAI_Release075_pow_card_sub_rank_dvd_det

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- A nonsingular integer matrix loses less than half its rank modulo a prime
larger than the common squared row-norm bound. -/
theorem nonsingular_rank_reduction_half {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (A i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    n ≤ 2 * (A.map (Int.cast : ℤ → ZMod q)).rank := by
  let AR : Matrix (Fin n) (Fin n) ℝ := A.map Int.cast
  let d := (A.map (Int.cast : ℤ → ZMod q)).rank
  have hcastdet : AR.det = (A.det : ℝ) := by
    simpa [AR] using (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hbound : AR.det ^ 2 ≤ r ^ n := det_sq_le_pow_of_row_sq_le AR r hrow
  have hdiv : (q : ℤ) ^ (n - d) ∣ A.det := by
    simpa only [Fintype.card_fin] using pow_card_sub_rank_dvd_det A q
  have hleI : (q : ℤ) ^ (n - d) ≤ |A.det| :=
    Int.le_of_dvd (abs_pos.mpr hdet) ((dvd_abs _ _).mpr hdiv)
  have hleR : (q : ℝ) ^ (n - d) ≤ |AR.det| := by
    rw [hcastdet]
    exact_mod_cast hleI
  have hsq := pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg q) (n - d)) hleR 2
  rw [sq_abs, ← pow_mul] at hsq
  by_cases hn : n = 0
  · simp [hn]
  have hrnonneg : 0 ≤ r := le_trans zero_le_one hr
  have hstrict : (q : ℝ) ^ ((n - d) * 2) < (q : ℝ) ^ n :=
    (hsq.trans hbound).trans_lt (pow_lt_pow_left₀ hqr hrnonneg hn)
  have hexp : (n - d) * 2 < n :=
    (pow_lt_pow_iff_right₀ (lt_of_le_of_lt hr hqr)).mp hstrict
  change n ≤ 2 * d
  omega

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.nonsingular_rank_reduction_half := @_root_.OAI.Release075.nonsingular_rank_reduction_half
