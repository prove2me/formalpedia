-- Prove2me | solution 1 for OAI.Release075.pow_sub_card_dvd_det
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:39:12.19638+00:00
-- url     : https://prove2.me/submissions/91cf07da-8014-4d5c-b7a7-c287e7595b18

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L63-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.pow_sub_card_dvd_det. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- Factoring a common divisor from all rows outside a specified set. -/
theorem pow_sub_card_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (S : Finset ι) (q : ℤ)
    (h : ∀ i, i ∉ S → ∀ j, q ∣ A i j) :
    q ^ (Fintype.card ι - S.card) ∣ A.det := by
  classical
  have hd : ∀ i j, (if i ∈ S then (1 : ℤ) else q) ∣ A i j := by
    intro i j
    split_ifs with hi
    · exact one_dvd _
    · exact h i hi j
  choose B hB using hd
  have hA : A = Matrix.of (fun i j => (if i ∈ S then (1 : ℤ) else q) * B i j) := by
    ext i j
    exact hB i j
  have hprod : (∏ i : ι, if i ∈ S then (1 : ℤ) else q) =
      q ^ (Fintype.card ι - S.card) := by
    simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ S)
    have hfilter : Finset.univ.filter (· ∈ S) = S := by ext; simp
    rw [hfilter, Finset.card_univ] at hcard
    omega
  refine ⟨Matrix.det (Matrix.of B), ?_⟩
  rw [hA]
  simpa only [hprod, Matrix.of_apply] using Matrix.det_mul_column (fun i => if i ∈ S then (1 : ℤ) else q) (Matrix.of B)

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.pow_sub_card_dvd_det := @_root_.OAI.Release075.pow_sub_card_dvd_det
