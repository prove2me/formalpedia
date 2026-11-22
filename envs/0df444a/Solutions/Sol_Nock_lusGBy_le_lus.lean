-- Prove2me | solution 1 for Nock.lusGBy_le_lus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:11.933846+00:00
-- url     : https://prove2.me/submissions/3acdf330-de89-4051-89df-f0eafb49188d

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell



set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : Noun.lus x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [Noun.lus, ← h]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h
end Nock
