-- Prove2me | solution 1 for Nock.Verb.slot_edit_sibling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:52.813105+00:00
-- url     : https://prove2.me/submissions/ad6e696b-6c97-4792-8d58-e18232fdf1d4

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_siblingAxis_half
public import Theorems.Thm_Nock_Verb_siblingAxis_parity
public import Theorems.Thm_Nock_Verb_slot_edit_eq
public import Theorems.Thm_Nock_Verb_slot_ge_two
section
@[expose] public section
namespace Nock
namespace Verb
open Noun
private theorem slot_edit_immediate_sibling :
    ∀ (a : Nat) {new old res : Noun},
      Noun.edit (a + 2) new old = some res →
        Noun.slot (siblingAxis (a + 2)) res = Noun.slot (siblingAxis (a + 2)) old := by
  intro a new old res h
  rw [Noun.edit] at h
  simp only at h
  cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some sib =>
      rw [hs] at h
      have hres : Noun.slot ((a + 2) / 2) res
            = some (if (a + 2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new) :=
        slot_edit_eq ((a + 2) / 2) h
      have hsib_old : Noun.slot (siblingAxis (a + 2)) old = some sib := by
        unfold siblingAxis; exact hs
      have hge : 2 ≤ siblingAxis (a + 2) := by
        unfold siblingAxis
        by_cases hb : ((a + 2) % 2 == 0) = true
        · rw [if_pos hb]; omega
        · rw [if_neg hb]
          have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
          omega
      rw [hsib_old, slot_ge_two _ hge, siblingAxis_half, hres, siblingAxis_parity]
      by_cases hb : ((a + 2) % 2 == 0) = true
      · simp only [hb, ite_true, Bool.not_true, ite_false, Bool.false_eq_true]
      · have hbf : ((a + 2) % 2 == 0) = false := by
          cases hh : (a + 2) % 2 == 0 with
          | true => exact absurd hh hb
          | false => rfl
        simp only [hbf, ite_false, Bool.not_false, ite_true, Bool.false_eq_true]
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {ax sib : Nat} (hsib : SiblingOf ax sib) :
    ∀ {new old res : Noun},
      Noun.edit ax new old = some res → Noun.slot sib res = Noun.slot sib old := by
  induction hsib with
  | immediate a =>
      intro new old res h
      exact slot_edit_immediate_sibling a h
  | ancestor a hsib ih =>
      intro new old res h
      rw [Noun.edit] at h
      simp only at h
      cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some sibling =>
          rw [hs] at h
          exact ih h
end Nock.Verb
