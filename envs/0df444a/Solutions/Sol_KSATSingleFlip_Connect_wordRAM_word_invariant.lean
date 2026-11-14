-- Prove2me | solution 1 for KSATSingleFlip.Connect.wordRAM_word_invariant
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:12:06.20808+00:00
-- url     : https://prove2.me/submissions/0d013ad9-ca05-48de-a5e3-1421c07b0d36

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

namespace KSATSingleFlip.Connect

/-- Every register and memory cell is a valid unsigned word. -/
def auditWordRAMBounded (w : ℕ) (s : WordRAMState) : Prop :=
  (∀ r, s.registers r < 2^w) ∧ ∀ a, s.memory a < 2^w

theorem audit_wordRAM_start_bounded (w : ℕ) (input : List ℕ)
    (h : ∀ a ∈ input, a < 2^w) : auditWordRAMBounded w (wordRAMStart input) := by
  constructor
  · intro r
    simp [wordRAMStart]
  · intro i
    cases he : input[i]? with
    | none => simp [wordRAMStart, he]
    | some a =>
      have ha := h a (List.mem_of_getElem? he)
      simpa [wordRAMStart, he] using ha

theorem audit_wordRAM_write_bounded_state (w d value : ℕ) (s : WordRAMState)
    (hs : auditWordRAMBounded w s) : auditWordRAMBounded w (s.writeNext w d value) := by
  constructor
  · intro r
    simp only [WordRAMState.writeNext, Function.update_apply]
    split_ifs
    · exact Nat.mod_lt _ (by positivity)
    · exact hs.1 r
  · exact hs.2

theorem audit_wordRAM_step_bounded (program : WordRAMProgram) (w : ℕ) (s : WordRAMState)
    (hs : auditWordRAMBounded w s) : auditWordRAMBounded w (wordRAMStep program w s) := by
  unfold wordRAMStep
  split
  · exact hs
  · rename_i hnot
    cases hp : program[s.pc]? with
    | none => simpa [hp, auditWordRAMBounded] using hs
    | some ins =>
      cases ins <;> simp only [hp]
      all_goals try exact audit_wordRAM_write_bounded_state w _ _ s hs
      all_goals try simpa [auditWordRAMBounded] using hs
      case store a b =>
        constructor
        · exact hs.1
        · intro i
          simp only [Function.update_apply]
          split_ifs
          · exact Nat.mod_lt _ (by positivity)
          · exact hs.2 i

theorem audit_wordRAM_run_bounded (program : WordRAMProgram) (w T : ℕ) (s : WordRAMState)
    (hs : auditWordRAMBounded w s) : auditWordRAMBounded w (wordRAMRun program w T s) := by
  induction T generalizing s with
  | zero => exact hs
  | succ T ih =>
    rw [wordRAMRun]
    exact ih _ (audit_wordRAM_step_bounded program w s hs)

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution (program : WordRAMProgram) (w T : ℕ) (s : WordRAMState)
    (hr : ∀ r, s.registers r < 2^w) (hm : ∀ a, s.memory a < 2^w) :
    (∀ r, (wordRAMRun program w T s).registers r < 2^w) ∧
    ∀ a, (wordRAMRun program w T s).memory a < 2^w := by
  exact audit_wordRAM_run_bounded program w T s ⟨hr, hm⟩

#print axioms solution
