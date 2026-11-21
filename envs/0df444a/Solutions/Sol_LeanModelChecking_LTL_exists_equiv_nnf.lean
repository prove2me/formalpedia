-- Prove2me | solution 1 for LeanModelChecking.LTL.exists_equiv_nnf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:03.538043+00:00
-- url     : https://prove2.me/submissions/6a4e8753-0727-45ab-82f2-3544d4cc33a8

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Theorems.Thm_LeanModelChecking_LTL_toNNFCore_sound

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace LTL
theorem _root_.solution {AP} (ψ : LTL AP) :
    ∃ (nnf : NNF AP), ψ.language = nnf.language := by
  refine ⟨LTL.toNNF ψ, funext ?_⟩
  simpa using (toNNFCore_sound ψ).1
end LTL
end LeanModelChecking
