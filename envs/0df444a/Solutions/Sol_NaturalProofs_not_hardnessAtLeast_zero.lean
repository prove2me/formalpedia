-- Prove2me | solution 1 for NaturalProofs.not_hardnessAtLeast_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:44.681037+00:00
-- url     : https://prove2.me/submissions/c58eadcf-b1c4-4637-bb81-3e0b1797f9bc

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_Sanity
public import Theorems.Thm_NaturalProofs_prob_eq_card_filter
public import Theorems.Thm_NaturalProofs_prob_equiv
public import Theorems.Thm_NaturalProofs_prob_fst


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
namespace NaturalProofs
theorem _root_.solution (k : ℕ) (hk : 0 < k) :
    ¬ HardnessAtLeast (fun _ _ _ => false) k 3 := by
  intro h
  let j0 : Fin (2 * k) := ⟨0, by omega⟩
  let D : Circuit (Fin (2 * k)) := ⟨[], .input j0⟩
  have h1 : prob (fun x : Fin k → Bool => D.eval ((fun _ _ _ => false) k x)) = 0 := by
    simp [prob, ind, D, Circuit.eval, Wire.eval]
  have h2 : prob (fun y : Fin (2 * k) → Bool => D.eval y) = 1 / 2 := by
    have := prob_equiv (Equiv.funSplitAt j0 Bool) (fun p : Bool × ({j // j ≠ j0} → Bool) => p.1)
    simp only [Equiv.funSplitAt_apply] at this
    change prob (fun y : Fin (2 * k) → Bool => y j0) = 1 / 2
    rw [this, prob_fst (fun b : Bool => b)]
    simp [prob, ind]
  have c1 : (((Finset.univ.filter (fun x : Fin k → Bool =>
      D.eval ((fun _ _ _ => false) k x) = true)).card : ℝ) / 2 ^ k) =
      prob (fun x : Fin k → Bool => D.eval ((fun _ _ _ => false) k x)) := by
    rw [prob_eq_card_filter]
    simp
  have c2 : (((Finset.univ.filter (fun y : Fin (2 * k) → Bool => D.eval y = true)).card : ℝ) /
      2 ^ (2 * k)) = prob (fun y : Fin (2 * k) → Bool => D.eval y) := by
    rw [prob_eq_card_filter]
    simp
  have := h 2 D (by norm_num) (by simp [D, Circuit.size]) (by
    rw [c1, c2, h1, h2]
    norm_num)
  norm_num at this
end NaturalProofs
