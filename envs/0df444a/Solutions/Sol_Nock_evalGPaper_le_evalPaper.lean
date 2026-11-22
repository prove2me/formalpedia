-- Prove2me | solution 1 for Nock.evalGPaper_le_evalPaper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:47.733021+00:00
-- url     : https://prove2.me/submissions/625672ef-2831-4e63-8300-07ca36823191

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
public import Theorems.Thm_Nock_lusGBy_le_lus
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
    (h : evalGPaper q n s form = some r) : evalPaper n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, evalPaper, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_le_lus]
end Nock
