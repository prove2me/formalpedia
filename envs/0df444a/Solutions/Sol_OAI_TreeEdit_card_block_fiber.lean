-- Prove2me | solution 1 for OAI.TreeEdit.card_block_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:39:45.504899+00:00
-- url     : https://prove2.me/submissions/f0dd944c-b19c-405c-b45f-b0dd2ef766ae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CycleCharging.lean:L87-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.card_block_fiber. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

-- ---- from OAI.Combinatorics.TreeEdit.CycleCharging ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma card_block_fiber {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) (a : Fin M) :
    (Finset.univ.filter (fun i => blockIndex hP (f i) = a)).card ≤ P := by
  classical
  let r : Fin N → Fin P := fun i => ⟨(f i).val % P, Nat.mod_lt _ hP⟩
  have hi : Set.InjOn r ↑(Finset.univ.filter (fun i => blockIndex hP (f i) = a)) := by
    intro i hi j hj he
    have hi' := congrArg Fin.val (Finset.mem_filter.mp hi).2
    have hj' := congrArg Fin.val (Finset.mem_filter.mp hj).2
    have hr := congrArg Fin.val he
    apply f.injective
    apply Fin.ext
    dsimp [blockIndex] at hi' hj'
    dsimp [r] at hr
    have hx := Nat.div_add_mod (f i).val P
    have hy := Nat.div_add_mod (f j).val P
    rw [hi'] at hx
    rw [hj'] at hy
    omega
  simpa using Finset.card_le_card_of_injOn r (fun _ _ => Finset.mem_univ _) hi

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.card_block_fiber := @_root_.OAI.TreeEdit.card_block_fiber
