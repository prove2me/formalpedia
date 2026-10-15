-- Prove2me | solution 1 for OAI.DoublingHilbert.tupleVector_sum_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:15:31.915162+00:00
-- url     : https://prove2.me/submissions/386d398a-c690-4b8f-b8ae-617517555b45

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean:L211-L225
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.tupleVector_sum_on. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem tupleVector_sum_on (w : Tuple) (s : Finset ℕ) (hs : w.support ⊆ s) :
    tupleVector w = ∑ j ∈ s, entryVector w j := by
  classical
  unfold tupleVector
  symm
  calc
    _ = ∑ j ∈ w.support, entryVector w j := by
      symm
      apply Finset.sum_subset hs
      intro j _ hj
      exact entryVector_eq_zero (by simpa using hj)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact entryVector_of_ne_zero (Finsupp.mem_support_iff.mp hj)

end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set


theorem solution : type_of% @_root_.OAI.DoublingHilbert.tupleVector_sum_on := @_root_.OAI.DoublingHilbert.tupleVector_sum_on
