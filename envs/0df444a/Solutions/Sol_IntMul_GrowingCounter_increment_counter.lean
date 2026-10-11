-- Prove2me | solution 1 for IntMul.GrowingCounter.increment_counter
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T14:26:15.255012+00:00
-- url     : https://prove2.me/submissions/40467932-14f6-46f7-be4a-098f1aabbb60

import Definitions.Def_IntMul_GrowingCounter
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.GrowingCounter

private theorem increment_value (bits : List Bool) : BinaryAdder.littleVal (increment bits)=BinaryAdder.littleVal bits+1 := by
  induction bits with
  | nil => simp [increment,BinaryAdder.littleVal]
  | cons b bs ih =>
      cases b <;> simp only [increment,BinaryAdder.littleVal,ih,Bool.toNat_false,Bool.toNat_true] <;> omega

private theorem increment_length (bits : List Bool) : (increment bits).length ≤ bits.length+1 := by
  induction bits with
  | nil => simp [increment]
  | cons b bs ih =>
      cases b <;> simp only [increment,List.length_cons] <;> omega

private theorem increment_credit (bits : List Bool) :
    counterSteps bits+2*potential (increment bits)=4+2*potential bits := by
  induction bits with
  | nil => simp [counterSteps,carryLength,increment,potential]
  | cons b bs ih =>
      cases b <;> simp only [counterSteps,carryLength,increment,potential] at * <;> omega

private theorem total_credit (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits+2*potential (iterateCounter n bits)=4*n+2*potential bits := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps,iterateCounter]
  | succ n ih =>
      have h := ih (increment bits)
      have hi := increment_credit bits
      simp only [totalCounterSteps,iterateCounter]
      omega

private theorem total_steps_bound (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits ≤ 4*n+2*potential bits := by
  have h := total_credit n bits
  omega

private theorem iterate_value (n : ℕ) (bits : List Bool) :
    BinaryAdder.littleVal (iterateCounter n bits)=BinaryAdder.littleVal bits+n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih => rw [iterateCounter,ih,increment_value];omega

private theorem iterate_length (n : ℕ) (bits : List Bool) :
    (iterateCounter n bits).length ≤ bits.length+n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih =>
      have h := ih (increment bits)
      have hi := increment_length bits
      simp only [iterateCounter]
      omega

end IntMul.GrowingCounter



namespace IntMul.GrowingCounter
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem tape_replace_after_prefix (M : MultitapeTM)
    (pre post : List M.Sym) (old new : M.Sym) :
    Function.update (M.tapeOf (pre ++ old :: post)) (pre.length + 1) new =
      M.tapeOf (pre ++ new :: post) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases he : p = pre.length
      · subst p
        simp [MultitapeTM.tapeOf, List.getD_append_right]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ pre.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hl : p < pre.length
        · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
        · have hge : pre.length ≤ p := by omega
          rw [List.getD_append_right _ _ _ _ hge, List.getD_append_right _ _ _ _ hge]
          cases hd : p - pre.length with
          | zero => omega
          | succ d => simp

private theorem tape_append_one (N : MultitapeTM) (w : List N.Sym) (a : N.Sym) :
    Function.update (N.tapeOf w) (w.length + 1) a = N.tapeOf (w ++ [a]) := by
  classical
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ w.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem carry_read (base : machine.Cfg) (done : List Bool) (b : Bool) (bits : List Bool) :
    (carryFrame base done (b::bits)).cells 2 ((carryFrame base done (b::bits)).head 2)=machine.bitSym b := by
  simp [carryFrame,MultitapeTM.tapeOf,List.map_append,List.getD_append_right]

private theorem carry_read_nil (base : machine.Cfg) (done : List Bool) :
    (carryFrame base done []).cells 2 ((carryFrame base done []).head 2)=Sym.blank := by
  simp [carryFrame,MultitapeTM.tapeOf]

private theorem payload_not_start (bits : List Bool) (p : ℕ) : machine.tapeOf (bits.map machine.bitSym) (p+1)≠Sym.start := by
  simp only [MultitapeTM.tapeOf]
  by_cases hp : p < bits.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases bits[p] <;> decide
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    decide

end IntMul.GrowingCounter



namespace IntMul.GrowingCounter
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem carry_one_transition (a : Fin 3 → Sym) (h : a 2=Sym.one) :
    transition .carry a=(.carry,fun i => (if i=2 then Sym.zero else a i,if i=2 then .right else .stay)) := by
  simp only [transition,rawTransition,h,if_true]
  congr 1
  funext i
  by_cases hi : i=2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi,safe_stay]

private theorem carry_stop_transition (a : Fin 3 → Sym) (h : a 2=Sym.zero ∨ a 2=Sym.blank) :
    transition .carry a=(.rewind,fun i => (if i=2 then Sym.one else a i,if i=2 then .left else .stay)) := by
  have hn : a 2≠Sym.one := by rcases h with h|h <;> rw [h] <;> decide
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i=2
  · subst i
    simp only [if_pos rfl]
    rcases h with h|h <;> rw [h] <;> decide
  · simp only [if_neg hi,safe_stay]

private theorem rewind_left_transition (a : Fin 3 → Sym) (h : a 2≠Sym.start) :
    transition .rewind a=(.rewind,fun i => (a i,if i=2 then .left else .stay)) := by
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i=2
  · subst i
    simp [safeStep,h]
  · simp only [if_neg hi,safe_stay]

private theorem rewind_marker_transition (a : Fin 3 → Sym) (h : a 2=Sym.start) :
    transition .rewind a=(.halt,fun i => (a i,if i=2 then .right else .stay)) := by
  simp only [transition,rawTransition,if_pos h]
  congr 1
  funext i
  by_cases hi : i=2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi,safe_stay]

end IntMul.GrowingCounter



namespace IntMul.GrowingCounter
open TapeCopy (Sym)

private theorem carry_one_step (base : machine.Cfg) (done bits : List Bool) :
    machine.step (carryFrame base done (true::bits))=carryFrame base (done++[false]) bits := by
  have hr : (carryFrame base done (true::bits)).cells 2 ((carryFrame base done (true::bits)).head 2)=Sym.one :=
    carry_read base done true bits
  have ht := carry_one_transition
    (fun i => (carryFrame base done (true::bits)).cells i ((carryFrame base done (true::bits)).head i)) hr
  change transition (carryFrame base done (true::bits)).state
    (fun i => (carryFrame base done (true::bits)).cells i ((carryFrame base done (true::bits)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp only [carryFrame,Function.update_self,if_pos rfl]
      have h := tape_replace_after_prefix machine (done.map machine.bitSym) (bits.map machine.bitSym) Sym.one Sym.zero
      simpa [List.map_append,List.map_cons,List.append_assoc,MultitapeTM.bitSym] using h
    · simp only [carryFrame,Function.update_of_ne hi,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp [carryFrame]
    · simp only [carryFrame,Function.update_of_ne hi,if_neg hi]

private theorem carry_zero_step (base : machine.Cfg) (done bits : List Bool) :
    machine.step (carryFrame base done (false::bits))=rewindFrame base (done++true::bits) done.length := by
  have hr : (carryFrame base done (false::bits)).cells 2 ((carryFrame base done (false::bits)).head 2)=Sym.zero :=
    carry_read base done false bits
  have ht := carry_stop_transition
    (fun i => (carryFrame base done (false::bits)).cells i ((carryFrame base done (false::bits)).head i)) (Or.inl hr)
  change transition (carryFrame base done (false::bits)).state
    (fun i => (carryFrame base done (false::bits)).cells i ((carryFrame base done (false::bits)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp only [carryFrame,rewindFrame,Function.update_self,if_pos rfl]
      have h := tape_replace_after_prefix machine (done.map machine.bitSym) (bits.map machine.bitSym) Sym.zero Sym.one
      simpa [List.map_append,List.map_cons,MultitapeTM.bitSym] using h
    · simp only [carryFrame,rewindFrame,Function.update_of_ne hi,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp [carryFrame,rewindFrame]
    · simp only [carryFrame,rewindFrame,Function.update_of_ne hi,if_neg hi]

private theorem carry_nil_step (base : machine.Cfg) (done : List Bool) :
    machine.step (carryFrame base done [])=rewindFrame base (done++[true]) done.length := by
  have hr := carry_read_nil base done
  have ht := carry_stop_transition
    (fun i => (carryFrame base done []).cells i ((carryFrame base done []).head i)) (Or.inr hr)
  change transition (carryFrame base done []).state
    (fun i => (carryFrame base done []).cells i ((carryFrame base done []).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp only [carryFrame,rewindFrame,Function.update_self,if_pos rfl,List.append_nil]
      have h := tape_append_one machine (done.map machine.bitSym) Sym.one
      simpa [List.map_append,MultitapeTM.bitSym] using h
    · simp only [carryFrame,rewindFrame,Function.update_of_ne hi,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      simp [carryFrame,rewindFrame]
    · simp only [carryFrame,rewindFrame,Function.update_of_ne hi,if_neg hi]

private theorem rewind_step (base : machine.Cfg) (bits : List Bool) (p : ℕ) :
    machine.step (rewindFrame base bits (p+1))=rewindFrame base bits p := by
  have hr : (rewindFrame base bits (p+1)).cells 2 ((rewindFrame base bits (p+1)).head 2)≠Sym.start := by
    simpa only [rewindFrame,Function.update_self] using payload_not_start bits p
  have ht := rewind_left_transition
    (fun i => (rewindFrame base bits (p+1)).cells i ((rewindFrame base bits (p+1)).head i)) hr
  change transition (rewindFrame base bits (p+1)).state
    (fun i => (rewindFrame base bits (p+1)).cells i ((rewindFrame base bits (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i;simp [rewindFrame]
    · simp only [rewindFrame,Function.update_of_ne hi,if_neg hi]

private theorem rewind_end (base : machine.Cfg) (bits : List Bool) :
    machine.step (rewindFrame base bits 0)=counterFrame base .halt bits := by
  have hr : (rewindFrame base bits 0).cells 2 ((rewindFrame base bits 0).head 2)=Sym.start := by
    simp [rewindFrame,MultitapeTM.tapeOf]
  have ht := rewind_marker_transition
    (fun i => (rewindFrame base bits 0).cells i ((rewindFrame base bits 0).head i)) hr
  change transition (rewindFrame base bits 0).state
    (fun i => (rewindFrame base bits 0).cells i ((rewindFrame base bits 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i;simp [rewindFrame,counterFrame]
    · simp only [rewindFrame,counterFrame,Function.update_of_ne hi,if_neg hi]

end IntMul.GrowingCounter



namespace IntMul.GrowingCounter

private theorem rewind_run (base : machine.Cfg) (bits : List Bool) (p : ℕ) :
    machine.step^[p+1] (rewindFrame base bits p)=counterFrame base .halt bits := by
  induction p with
  | zero => exact rewind_end base bits
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem carry_run (base : machine.Cfg) (bits done : List Bool) :
    machine.step^[2*carryLength bits+done.length+2] (carryFrame base done bits)=
      counterFrame base .halt (done++increment bits) := by
  induction bits generalizing done with
  | nil =>
      simp only [carryLength,increment,Nat.mul_zero,Nat.zero_add]
      rw [show done.length+2=(done.length+1)+1 by omega,Function.iterate_succ_apply,
        carry_nil_step,rewind_run]
  | cons b bits ih =>
      cases b with
      | false =>
          simp only [carryLength,increment,Nat.mul_zero,Nat.zero_add]
          rw [show done.length+2=(done.length+1)+1 by omega,Function.iterate_succ_apply,
            carry_zero_step,rewind_run]
      | true =>
          rw [show 2*carryLength (true::bits)+done.length+2=
              (2*carryLength bits+(done++[false]).length+2)+1 by simp only [carryLength,List.length_append,List.length_singleton];omega,
            Function.iterate_succ_apply,carry_one_step,ih]
          simp [increment,List.append_assoc]

/-- Full ripple increment with real growth and marker return, exact clock,
retained input/output caller frame and additive binary value. The potential
identity supplies the charged amortized bound for repeated increments. -/
private theorem increment_counter (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits)=counterFrame base .halt (increment bits) ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).state=machine.qHalt ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 0=base.cells 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 0=base.head 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 1=base.cells 1 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 1=base.head 1 ∧
      BinaryAdder.littleVal (increment bits)=BinaryAdder.littleVal bits+1 ∧
      (increment bits).length ≤ bits.length+1 ∧
      counterSteps bits+2*potential (increment bits)=4+2*potential bits ∧
      (∀ n, totalCounterSteps n bits ≤ 4*n+2*potential bits ∧
        BinaryAdder.littleVal (iterateCounter n bits)=BinaryAdder.littleVal bits+n) := by
  have he : machine.step^[counterSteps bits] (counterFrame base .carry bits)=counterFrame base .halt (increment bits) := by
    simpa only [counterSteps,counterFrame,carryFrame,List.length_nil,Nat.add_zero,Nat.zero_add,List.nil_append] using (carry_run base bits [])
  refine ⟨he,?_,?_,?_,?_,?_,increment_value bits,increment_length bits,increment_credit bits,?_⟩
  · rw [he];rfl
  · rw [he];simp [counterFrame]
  · rw [he];simp [counterFrame]
  · rw [he];simp [counterFrame]
  · rw [he];simp [counterFrame]
  · intro n;exact ⟨total_steps_bound n bits,iterate_value n bits⟩

end IntMul.GrowingCounter



open IntMul IntMul.GrowingCounter

theorem solution (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits)=counterFrame base .halt (increment bits) ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).state=machine.qHalt ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 0=base.cells 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 0=base.head 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 1=base.cells 1 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 1=base.head 1 ∧
      BinaryAdder.littleVal (increment bits)=BinaryAdder.littleVal bits+1 ∧
      (increment bits).length ≤ bits.length+1 ∧
      counterSteps bits+2*potential (increment bits)=4+2*potential bits ∧
      (∀ n, totalCounterSteps n bits ≤ 4*n+2*potential bits ∧
        BinaryAdder.littleVal (iterateCounter n bits)=BinaryAdder.littleVal bits+n) :=
  IntMul.GrowingCounter.increment_counter base bits

#print axioms solution
