-- Prove2me | solution 1 for JinTheorem.jin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:27.546084+00:00
-- url     : https://prove2.me/submissions/10cdec21-83bc-4d81-9e8d-d06c84af9379

module
public import Mathlib
public import Definitions.Def_JinLib_Jin
public import Definitions.Def_JinTriangleFree_Solution
public import Theorems.Thm_DenseTriangleFree_jin


set_option autoImplicit true
@[expose] public section
public section
open JinTheorem
namespace JinTheorem
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 :=
  DenseTriangleFree.jin G h3 hδ
end JinTheorem
