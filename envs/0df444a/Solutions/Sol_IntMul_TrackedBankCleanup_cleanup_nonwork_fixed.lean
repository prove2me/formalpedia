-- Prove2me | solution 1 for IntMul.TrackedBankCleanup.cleanup_nonwork_fixed
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:58:36.625983+00:00
-- url     : https://prove2.me/submissions/8f3214b3-2edf-4e54-b0f2-a3fccbfc5104

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic

namespace IntMul.TrackedBankCleanup

private theorem raw_nonwork_action (M : MultitapeTM) (q : State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) (i : Fin (M.k+2))
    (nonwork : i.val < 2) : (rawTransition M q a).2 i=(a i,Move.stay) := by
  have hi : ¬2 ≤ i.val := by omega
  cases q
  all_goals simp only [rawTransition]
  all_goals try split_ifs
  all_goals simp [hi]

private theorem nonwork_action (M : MultitapeTM) (q : State)
    (a : Fin (M.k+2) → TrackedBankedSimulation.Sym M) (i : Fin (M.k+2))
    (nonwork : i.val < 2) : (transition M q a).2 i=(a i,Move.stay) := by
  simp only [transition,raw_nonwork_action M q a i nonwork]
  cases a i <;> rfl

/-- Cleanup freezes both caller tapes and their heads at every actual time. -/
private theorem cleanup_nonwork_fixed (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) :
    ∀ t i, i.val < 2 →
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).head i=base.head i ∧
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).cells i=base.cells i := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have hn : ¬2 ≤ i.val := by omega
    simp [rewindFrame,TrackedBankedSimulation.embed,parentBase,hn]
  | succ t ih =>
    intro i hi
    rw [Function.iterate_succ_apply']
    let d := (machine M).step^[t] (rewindFrame M base offset extent c pos)
    have ha := nonwork_action M d.state (fun j => d.cells j (d.head j)) i hi
    change ((machine M).step d).head i=base.head i ∧ ((machine M).step d).cells i=base.cells i
    simp only [MultitapeTM.step,ha]
    rw [Function.update_eq_self]
    exact ih i hi

end IntMul.TrackedBankCleanup


open IntMul IntMul.TrackedBankCleanup

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) :
    ∀ t i, i.val < 2 →
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).head i=base.head i ∧
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).cells i=base.cells i :=
  IntMul.TrackedBankCleanup.cleanup_nonwork_fixed M base offset extent c pos

#print axioms solution
