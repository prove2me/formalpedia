-- Prove2me | solution 1 for Nock.Verb.slot_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:28.678245+00:00
-- url     : https://prove2.me/submissions/fd7aa3be-cac0-47c6-afe8-df123463c7a1

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (m : Nat) (hm : 2 ≤ m) (n : Noun) :
    Noun.slot m n
      = (match Noun.slot (m / 2) n with
         | some (.cell l r) => some (if m % 2 == 0 then l else r)
         | _ => none) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [Noun.slot]
  rfl
end Nock.Verb
