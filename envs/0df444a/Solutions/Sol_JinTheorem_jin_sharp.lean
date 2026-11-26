-- Prove2me | solution 1 for JinTheorem.jin_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:51.257657+00:00
-- url     : https://prove2.me/submissions/88f942d2-c0e6-4ffe-974b-267422ae1467

module
public import Mathlib
public import Definitions.Def_JinLib_Jin
public import Definitions.Def_JinTriangleFree_Solution
public import Theorems.Thm_DenseTriangleFree_jin_sharp


set_option autoImplicit true
@[expose] public section
public section
open JinTheorem
namespace JinTheorem
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 :=
  DenseTriangleFree.jin_sharp m hm
end JinTheorem
