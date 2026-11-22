-- Prove2me | solution 1 for MatchingLogic.Sorted.mprovable_empty_of_not_feeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:00.383569+00:00
-- url     : https://prove2.me/submissions/740de7de-44fe-4dda-911a-37ba9fb75c5d

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
theorem _root_.solution {sΓ s : S.Srt}
    (Γ : Set (MPattern S Var sΓ)) (φ : MPattern S Var s)
    (hfeed : ¬ FeedsStar S sΓ s) (h : MProvable Γ φ) :
    MProvable (∅ : Set (MPattern S Var sΓ)) φ := by
  revert hfeed
  induction h with
  | hyp hφ =>
      intro hfeed
      exact (hfeed Relation.ReflTransGen.refl).elim
  | taut hp =>
      intro _
      exact .taut hp
  | mp _ _ ih₁ ih₂ =>
      intro hfeed
      exact .mp (ih₁ hfeed) (ih₂ hfeed)
  | exQuant hfree =>
      intro _
      exact .exQuant hfree
  | exGen _ hfree ih =>
      intro hfeed
      exact .exGen (ih hfeed) hfree
  | propBot =>
      intro _
      exact .propBot
  | propOr =>
      intro _
      exact .propOr
  | propEx hfree =>
      intro _
      exact .propEx hfree
  | @framing σ i args φ₁ φ₂ _ ih =>
      intro hfeed
      apply MProvable.framing
      apply ih
      intro hpath
      apply hfeed
      exact hpath.tail (Or.inr ⟨σ, i, rfl, rfl⟩)
  | existence =>
      intro _
      exact .existence
  | singleton C₁ C₂ =>
      intro _
      exact .singleton C₁ C₂
end MatchingLogic.Sorted
