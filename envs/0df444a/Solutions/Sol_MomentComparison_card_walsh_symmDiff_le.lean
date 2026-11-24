-- Prove2me | solution 1 for MomentComparison.card_walsh_symmDiff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:06:01.787608+00:00
-- url     : https://prove2.me/submissions/52f4ab4a-0ebe-4cce-a9ea-63c3d14e8398

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (s t : Finset (Fin n)) :
    (s ∆ t).card ≤ s.card + t.card := by
  exact (card_le_card (symmDiff_le_sup : s ∆ t ⊆ s ∪ t)).trans (card_union_le s t)
end MomentComparison
