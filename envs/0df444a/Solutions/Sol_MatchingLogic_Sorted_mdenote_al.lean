-- Prove2me | solution 1 for MatchingLogic.Sorted.mdenote_al
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:57.605289+00:00
-- url     : https://prove2.me/submissions/d4afb6ea-2545-44aa-b57d-51e7c4a20c06

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}
namespace MatchingLogic.Sorted
theorem _root_.solution (M : MModel S) (ρ : MVal M Var) {s : S.Srt}
    (x : Var) (s' : S.Srt) (φ : MPattern S Var s) :
    mdenote M ρ (MPattern.al x s' φ) =
      ⋂ a : M.carrier s', mdenote M (mupdate M ρ s' x a) φ := by
  classical
  simp [mdenote, Set.compl_iUnion]
end MatchingLogic.Sorted
