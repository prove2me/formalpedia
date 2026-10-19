-- Prove2me | solution 1 for OAI.Release075.pow_card_sub_rank_dvd_det
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:40:37.289631+00:00
-- url     : https://prove2.me/submissions/9f755544-b275-4600-a517-ef4a062039d5

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L90-L133
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.pow_card_sub_rank_dvd_det. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_exists_row_basis
import Theorems.Thm_OAI_Release075_pow_sub_card_dvd_det

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- The integral determinant detects the rank lost in reduction modulo a prime. -/
theorem pow_card_sub_rank_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (q : ℕ) [Fact q.Prime] :
    (q : ℤ) ^ (Fintype.card ι - (A.map (Int.cast : ℤ → ZMod q)).rank) ∣ A.det := by
  classical
  let M : Matrix ι ι (ZMod q) := A.map Int.cast
  obtain ⟨S, hScard, _, hspan⟩ := exists_row_basis M
  choose c hc using hspan
  let C : Matrix ι ι ℤ := fun i j =>
    if i ∈ S then 0 else if hj : j ∈ S then (c i ⟨j, hj⟩).cast else 0
  have hCC : C * C = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ∈ S
    · simp [C, hk]
    · by_cases hi : i ∈ S <;> simp [C, hi, hk]
  have hunit : IsUnit (1 - C).det := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨(1 + C).det, ?_⟩
    rw [← Matrix.det_mul]
    have hinv : (1 - C) * (1 + C) = 1 := by
      simp [mul_add, sub_mul, hCC]
    rw [hinv, Matrix.det_one]
  have hdiv : ∀ i, i ∉ S → ∀ j, (q : ℤ) ∣ ((1 - C) * A) i j := by
    intro i hi j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    rw [sub_mul, one_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Int.cast_sub, Int.cast_sum, Int.cast_mul]
    apply sub_eq_zero.mpr
    have hrestrict : (∑ k : ι, (C i k : ZMod q) * (A k j : ZMod q)) =
        ∑ k ∈ S, (C i k : ZMod q) * (A k j : ZMod q) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      simp [C, hi, hk]
    rw [hrestrict, ← Finset.sum_coe_sort]
    have heval := congrArg (fun v : ι → ZMod q => v j) (hc i)
    simpa [C, hi, M, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
  have hd := pow_sub_card_dvd_det ((1 - C) * A) S (q : ℤ) hdiv
  rw [Matrix.det_mul] at hd
  rw [← hScard]
  exact hunit.dvd_mul_left.mp hd

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.pow_card_sub_rank_dvd_det := @_root_.OAI.Release075.pow_card_sub_rank_dvd_det
