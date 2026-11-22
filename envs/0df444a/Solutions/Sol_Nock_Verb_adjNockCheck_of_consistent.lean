-- Prove2me | solution 1 for Nock.Verb.adjNockCheck_of_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:31.311709+00:00
-- url     : https://prove2.me/submissions/c045e784-3d41-4546-8542-3d9386c49369

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
public import Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution : ∀ (T : List Verb), Consistent T → AdjNockCheck T
  | [],             _ => trivial
  | [_],            _ => trivial
  | a :: b :: rest, h => by
      obtain ⟨hstep, hcons⟩ := h
      exact ⟨nockCheck_eq_true_iff.mpr (Or.inl ⟨b, rfl, hstep⟩),
        solution (b :: rest) hcons⟩
end Nock.Verb
