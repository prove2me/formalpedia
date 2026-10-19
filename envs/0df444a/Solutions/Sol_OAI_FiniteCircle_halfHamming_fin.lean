-- Prove2me | solution 1 for OAI.FiniteCircle.halfHamming_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:49:05.401577+00:00
-- url     : https://prove2.me/submissions/924230c6-5e6c-4f1d-b0ff-f62f382f8c35

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L378-L393
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.halfHamming_fin. The node keeps its source
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

 theorem halfHamming_fin {M : ℕ} [NeZero M] (v w : ZMod M) :
    (Finset.univ.filter (fun i : Fin M => halfBit v (i.val : ZMod M) ≠
      halfBit w (i.val : ZMod M))).card = halfHamming v w := by
  classical
  unfold halfHamming
  apply Finset.card_bij (fun b _ => (b.val : ZMod M))
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · intro b _ c _ hbc
    have hh := congrArg ZMod.val hbc
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt] at hh
    exact Fin.ext hh
  · intro b hb
    refine ⟨⟨b.val,b.val_lt⟩, ?_, ZMod.natCast_zmod_val b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa only [ZMod.natCast_zmod_val] using hb

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.halfHamming_fin := @_root_.OAI.FiniteCircle.halfHamming_fin
