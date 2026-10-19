-- Prove2me | solution 1 for OAI.Release075.exists_full_rank_minor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:42:08.265323+00:00
-- url     : https://prove2.me/submissions/4f07d0a3-82d7-4c49-a5e0-6bc69cb9e786

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L135-L157
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.exists_full_rank_minor. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_exists_row_basis

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- A full-rank minor exists over a field; both index maps are injective. -/
theorem exists_full_rank_minor {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ (f : Fin M.rank → ι) (g : Fin M.rank → κ),
      Function.Injective f ∧ Function.Injective g ∧ (M.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨S, hScard, hSlin, _⟩ := exists_row_basis M
  have hScard' : Fintype.card S = M.rank := by simpa using hScard
  let eS : Fin M.rank ≃ S := (Fintype.equivFinOfCardEq hScard').symm
  let f : Fin M.rank → ι := fun i => (eS i).val
  let R : Matrix (Fin M.rank) κ K := M.submatrix f id
  have hRlin : LinearIndependent K R.row := hSlin.comp eS eS.injective
  have hRrank : R.rank = M.rank := by
    simpa only [Fintype.card_fin] using hRlin.rank_matrix
  obtain ⟨T, hTcard, hTlin, _⟩ := exists_row_basis R.transpose
  have hTcard' : Fintype.card T = M.rank := by
    simpa only [Fintype.card_coe, Matrix.rank_transpose, hRrank] using hTcard
  let eT : Fin M.rank ≃ T := (Fintype.equivFinOfCardEq hTcard').symm
  let g : Fin M.rank → κ := fun i => (eT i).val
  have hBlin : LinearIndependent K (M.submatrix f g).col := hTlin.comp eT eT.injective
  refine ⟨f, g, Subtype.val_injective.comp eS.injective,
    Subtype.val_injective.comp eT.injective, ?_⟩
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hBlin)

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.exists_full_rank_minor := @_root_.OAI.Release075.exists_full_rank_minor
