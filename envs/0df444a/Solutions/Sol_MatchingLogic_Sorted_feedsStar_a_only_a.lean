-- Prove2me | solution 1 for MatchingLogic.Sorted.feedsStar_a_only_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:59.334024+00:00
-- url     : https://prove2.me/submissions/ffb44eb2-1af8-4e05-a54a-eabe78ac479d

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]
namespace MatchingLogic.Sorted
theorem _root_.solution (t : Srt3) : FeedsStar S3 Srt3.a t → t = Srt3.a := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hfeed ih =>
      rcases hfeed with hsame | ⟨σ, i, harg, _⟩
      · exact hsame ▸ ih
      · rw [ih] at harg
        cases σ <;> cases harg
end MatchingLogic.Sorted
