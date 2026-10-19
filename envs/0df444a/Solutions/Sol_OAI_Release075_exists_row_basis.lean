-- Prove2me | solution 1 for OAI.Release075.exists_row_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:37:59.975974+00:00
-- url     : https://prove2.me/submissions/87f49f22-0704-4740-a7ba-7db45b25f4bf

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L30-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.exists_row_basis. The node keeps its source
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

/-- A matrix has a spanning independent subset of its rows, with the expected size. -/
theorem exists_row_basis {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ S : Finset ι, S.card = M.rank ∧
      LinearIndependent K (fun i : S => M i.val) ∧
      ∀ i, ∃ c : S → K, M i = ∑ j : S, c j • M j.val := by
  classical
  obtain ⟨T, _, _, hspan, hlin⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K M.row) (Set.empty_subset (Set.univ : Set ι))
  let S := T.toFinset
  have hS : (S : Set ι) = T := Set.coe_toFinset T
  have hlinS : LinearIndepOn K M.row (S : Set ι) := by rw [hS]; exact hlin
  have hrange : Set.range (fun i : S => M.row i.val) = M.row '' (S : Set ι) := by
    ext x
    simp
  have hsp : Submodule.span K (Set.range (fun i : S => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    rw [hrange]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · apply Submodule.span_le.mpr
      rw [hS]
      simpa only [Set.image_univ] using hspan
  refine ⟨S, ?_, hlinS, ?_⟩
  · rw [M.rank_eq_finrank_span_row, ← hsp]
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using (finrank_span_eq_card hlinS).symm
  · intro i
    have hi : M.row i ∈ Submodule.span K (Set.range (fun j : S => M.row j.val)) := by
      rw [hsp]
      exact Submodule.subset_span (Set.mem_range_self i)
    rcases (Submodule.mem_span_range_iff_exists_fun K).mp hi with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.exists_row_basis := @_root_.OAI.Release075.exists_row_basis
