-- Prove2me | solution 1 for GwExact.run_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:20.158427+00:00
-- url     : https://prove2.me/submissions/ea67cb5a-b5db-42bb-87ba-dbb895a604dc

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_good_ins
public import Theorems.Thm_GwExact_rup_sound

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {σ : Nat → Bool} {src : Trie → Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ db, Good σ db → ∀ h c, src db h = some c → c.Holds σ) :
    ∀ (steps : List Nat) (db : Trie) (i : Nat), Good σ db → run src w wm db i steps = true → False := by
  intro steps
  induction steps with
  | nil => intro db i _ h; simp [run] at h
  | cons s ss ih =>
    intro db i hdb h
    simp only [run] at h
    generalize hr : readLits (Nat.land s 255) (Nat.shiftRight s 8) 0 0 = res at h
    obtain ⟨cl, rest⟩ := res
    simp only at h
    cases hc : rup (src db) w wm (Nat.land rest 255) (Nat.shiftRight rest 8) cl.n cl.p with
    | false => rw [hc, Bool.cond_false] at h; exact absurd h (by simp)
    | true =>
      rw [hc, Bool.cond_true] at h
      -- the derived clause is true under σ
      have hholds : cl.Holds σ := by
        refine Classical.byContradiction fun hno => ?_
        apply rup_sound (hsrc db hdb) _ _ _ _ hc
        · intro v hv
          cases hσ : σ v
          · exact absurd ⟨v, Or.inr ⟨hv, hσ⟩⟩ hno
          · rfl
        · intro v hv
          cases hσ : σ v
          · rfl
          · exact absurd ⟨v, Or.inl ⟨hv, hσ⟩⟩ hno
      by_cases he : Nat.beq cl.p 0 && Nat.beq cl.n 0
      · obtain ⟨v, hv⟩ := hholds
        simp only [Bool.and_eq_true, Nat.beq_eq] at he
        rw [he.1, he.2] at hv
        simp at hv
      · rw [Bool.not_eq_true] at he
        rw [he, Bool.cond_false] at h
        exact ih _ _ (good_ins hdb 32 i hholds) h
end GwExact
