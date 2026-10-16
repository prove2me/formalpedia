-- Prove2me | solution 1 for OAI.TreeEdit.Alignment.le_lcs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:33:33.477546+00:00
-- url     : https://prove2.me/submissions/c4085ff1-c438-44b9-99ca-da6049ece87f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Alignments.lean:L23-L36
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.Alignment.le_lcs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

theorem le_lcs (a : Alignment x y n) : n ≤ lcs x y := by
  let z := List.ofFn (fun i => x.get (a.left i))
  have hz : z.length = n := List.length_ofFn
  have hl : z.Sublist x := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨(Fin.castOrderIso hz).toOrderEmbedding.comp a.left, ?_⟩
    intro i
    simp [z, Fin.cast]
  have hr : z.Sublist y := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨(Fin.castOrderIso hz).toOrderEmbedding.comp a.right, ?_⟩
    intro i
    simpa [z, Fin.cast] using a.agree (Fin.cast hz i)
  exact hz ▸ length_le_lcs hl hr

end Alignment

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.Alignment


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.Alignment.le_lcs.{u} := @_root_.OAI.TreeEdit.Alignment.le_lcs.{u}
