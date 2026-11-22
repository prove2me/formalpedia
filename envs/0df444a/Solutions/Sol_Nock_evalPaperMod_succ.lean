-- Prove2me | solution 1 for Nock.evalPaperMod_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:04.798893+00:00
-- url     : https://prove2.me/submissions/497a140a-2cd7-42ae-addd-43dac574a2d2

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
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
theorem _root_.solution {q n : Nat} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) : evalPaperMod q (n + 1) s form = some r := by
  induction n, s, form using evalPaperMod.induct q generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalPaperMod, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalPaperMod, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalPaperMod]
end Nock
