-- Prove2me | solution 1 for OAI.FiniteCircle.halfHamming_translate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:43:18.448747+00:00
-- url     : https://prove2.me/submissions/430b5bc7-2b12-421d-939a-bacd4071e115

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L287-L304
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.halfHamming_translate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem halfHamming_translate {M : ℕ} [NeZero M] (v w a : ZMod M) :
    halfHamming (v+a) (w+a) = halfHamming v w := by
  classical
  unfold halfHamming
  apply Finset.card_bij (fun b _ => b-a)
  · intro b hb
    have hb := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [halfBit, sub_add_eq_sub_sub, sub_right_comm] using hb
  · intro b _ c _ hbc
    exact sub_left_injective hbc
  · intro b hb
    refine ⟨b+a, ?_, by simp⟩
    have hb := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [halfBit, add_sub_add_right_eq_sub] using hb

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.halfHamming_translate := @_root_.OAI.FiniteCircle.halfHamming_translate
