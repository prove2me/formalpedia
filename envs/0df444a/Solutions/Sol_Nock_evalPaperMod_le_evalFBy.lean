-- Prove2me | solution 1 for Nock.evalPaperMod_le_evalFBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:34.361173+00:00
-- url     : https://prove2.me/submissions/c7b44d19-dbe7-436b-9c14-c763e9484c42

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
    (h : evalPaperMod q n s form = some r) : FieldEmbedding.evalFBy q n s form = some r := by
  induction n, s, form using evalPaperMod.induct q generalizing r <;>
    simp_all only [evalPaperMod, FieldEmbedding.evalFBy, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind
end Nock
