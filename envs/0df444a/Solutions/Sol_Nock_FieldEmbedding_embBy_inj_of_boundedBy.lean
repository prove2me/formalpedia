-- Prove2me | solution 1 for Nock.FieldEmbedding.embBy_inj_of_boundedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:58.508595+00:00
-- url     : https://prove2.me/submissions/825e0f18-8b36-4e93-81a9-1c93fe906602

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_FieldEmbedding_embBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
public import Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
public import Theorems.Thm_Nock_FieldEmbedding_zmod_natCast_inj_of_lt
attribute [local simp] Nock.FieldEmbedding.BoundedBy_atom
attribute [local simp] Nock.FieldEmbedding.BoundedBy_cell


attribute [local simp] Nock.FieldEmbedding.embBy_atom

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
open Nock.FieldEmbedding
namespace Nock.FieldEmbedding
theorem _root_.solution {q : Nat} :
    ∀ {a b : Noun}, BoundedBy q a → BoundedBy q b → embBy q a = embBy q b → a = b := by
  intro a
  induction a with
  | atom m =>
      intro b hm hb h
      cases b with
      | atom n =>
          simp only [embBy, FNounBy.atom.injEq] at h
          rw [zmod_natCast_inj_of_lt hm hb h]
      | cell _ _ => simp [embBy] at h
  | cell la ra ihl ihr =>
      intro b ha hb h
      cases b with
      | atom _ => simp [embBy] at h
      | cell lb rb =>
          simp only [embBy, FNounBy.cell.injEq] at h
          rw [ihl ha.1 hb.1 h.1, ihr ha.2 hb.2 h.2]
end Nock.FieldEmbedding
