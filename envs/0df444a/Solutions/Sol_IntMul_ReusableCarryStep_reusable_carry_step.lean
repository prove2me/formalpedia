-- Prove2me | solution 1 for IntMul.ReusableCarryStep.reusable_carry_step
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T12:48:59.597121+00:00
-- url     : https://prove2.me/submissions/b592b68f-3036-4550-ae27-709f31de0b29

import Definitions.Def_IntMul_ReusableCarryStep
import Mathlib.Tactic
import Theorems.Thm_IntMul_TapeBankErase_erase_bank
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_StreamCarryStep_stream_carry_step

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem owned_intmulreusablecarryprograms_safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private abbrev eraseMachine (i : Fin 10) : MultitapeTM :=
  TapeBankErase.machine 13 (eraseBank i) (eraseBank_writable i)

private theorem raw_relay (q : Relay) (a : Fin 15 → Sym) :
    rawTransition (relayState q) a=relayRaw q a := rfl

private noncomputable def calcView  (c : (StreamCarryStep.machine).Cfg) : subroutine.Cfg where
  state := calcState c.state
  cells := c.cells
  head := c.head

private theorem calc_step  (c : (StreamCarryStep.machine).Cfg) :
    subroutine.step (calcView c)=calcView ((StreamCarryStep.machine).step c) := by
  let a : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (calcState c.state) a=
      (calcState ((StreamCarryStep.machine).δ c.state a).1,((StreamCarryStep.machine).δ c.state a).2) := by
    by_cases h : c.state=(StreamCarryStep.machine).qHalt
    · rw [h,(StreamCarryStep.machine).halt_fixed a]
      change ((none : State),fun j => safeStep (a j) (a j) .stay)=(none,fun j => (a j,.stay))
      congr 1
      funext j
      exact safe_stay _
    · conv_lhs => rw [calcState,if_neg h]
      change (calcState ((StreamCarryStep.machine).δ c.state a).1,
        fun j => safeStep (a j) (((StreamCarryStep.machine).δ c.state a).2 j).1
          (((StreamCarryStep.machine).δ c.state a).2 j).2)=_
      congr 1
      funext j
      apply owned_intmulreusablecarryprograms_safe_identity
      · exact (StreamCarryStep.machine).start_preserved c.state a j
      · exact (StreamCarryStep.machine).start_only_at_start c.state a j
  change transition (calcView c).state
    (fun j => (calcView c).cells j ((calcView c).head j))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem calc_run  (c : (StreamCarryStep.machine).Cfg) (t : ℕ) :
    subroutine.step^[t] (calcView c)=calcView ((StreamCarryStep.machine).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,calc_step,Function.iterate_succ_apply']

private noncomputable def eraseView (i : Fin 10) (c : (eraseMachine i).Cfg) : subroutine.Cfg where
  state := eraseState i c.state
  cells := c.cells
  head := c.head

private theorem erase_step (i : Fin 10) (c : (eraseMachine i).Cfg) :
    subroutine.step (eraseView i c)=eraseView i ((eraseMachine i).step c) := by
  let a : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (eraseState i c.state) a=
      (eraseState i ((eraseMachine i).δ c.state a).1,((eraseMachine i).δ c.state a).2) := by
    by_cases h : c.state=(eraseMachine i).qHalt
    · rw [h,(eraseMachine i).halt_fixed a]
      change ((none : State),fun j => safeStep (a j) (a j) .stay)=(none,fun j => (a j,.stay))
      congr 1
      funext j
      exact safe_stay _
    · conv_lhs => rw [eraseState,if_neg h]
      change (eraseState i ((eraseMachine i).δ c.state a).1,
        fun j => safeStep (a j) (((eraseMachine i).δ c.state a).2 j).1
          (((eraseMachine i).δ c.state a).2 j).2)=_
      congr 1
      funext j
      apply owned_intmulreusablecarryprograms_safe_identity
      · exact (eraseMachine i).start_preserved c.state a j
      · exact (eraseMachine i).start_only_at_start c.state a j
  change transition (eraseView i c).state
    (fun j => (eraseView i c).cells j ((eraseView i c).head j))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem erase_run (i : Fin 10) (c : (eraseMachine i).Cfg) (t : ℕ) :
    subroutine.step^[t] (eraseView i c)=eraseView i ((eraseMachine i).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,erase_step,Function.iterate_succ_apply']

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)

private noncomputable def eraseBegin (i : Fin 10) (base : subroutine.Cfg) : subroutine.Cfg :=
  {base with state := eraseState i .rewind}

private noncomputable def eraseDone (i : Fin 10) (base : subroutine.Cfg) : subroutine.Cfg where
  state := none
  cells := Function.update base.cells (eraseBank i) (subroutine.tapeOf [])
  head := Function.update base.head (eraseBank i) 0

/-- Literal selected-bank erasure preserves the entire surrounding frame. -/
private theorem erase_complete (i : Fin 10) (base : subroutine.Cfg) (w : List Sym)
    (hw : TapeBankErase.ValidWord w) (h : ℕ)
    (hc : base.cells (eraseBank i)=subroutine.tapeOf w)
    (hh : base.head (eraseBank i)=h) :
    subroutine.step^[h+2*w.length+3] (eraseBegin i base)=eraseDone i base := by
  let c : (eraseMachine i).Cfg := {state := .halt,cells := base.cells,head := base.head}
  have hci : Function.update base.cells (eraseBank i) (subroutine.tapeOf w)=base.cells := by
    rw [←hc]
    exact Function.update_eq_self _ _
  have hhi : Function.update base.head (eraseBank i) h=base.head := by
    rw [←hh]
    exact Function.update_eq_self _ _
  have hin : eraseView i (TapeBankErase.initialFrame 13 (eraseBank i)
      (eraseBank_writable i) c w h)=eraseBegin i base := by
    apply cfg_ext
    · rfl
    · exact hci
    · exact hhi
  have hout : eraseView i (TapeBankErase.finalFrame 13 (eraseBank i)
      (eraseBank_writable i) c)=eraseDone i base := rfl
  have he := (TapeBankErase.erase_bank 13 (eraseBank i) (eraseBank_writable i) c w hw h).1
  rw [←hin,erase_run,he,hout]

private theorem valid_bits (w : List Bool) : TapeBankErase.ValidWord (w.map subroutine.bitSym) := by
  intro s hs
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  cases b <;> decide

private theorem valid_append (u v : List Sym) (hu : TapeBankErase.ValidWord u)
    (hv : TapeBankErase.ValidWord v) : TapeBankErase.ValidWord (u++v) := by
  intro s hs
  rcases List.mem_append.mp hs with h|h
  · exact hu s h
  · exact hv s h

private theorem valid_sep : TapeBankErase.ValidWord [Sym.sep] := by
  intro s hs
  have h : s=Sym.sep := List.mem_singleton.mp hs
  subst s
  decide

private noncomputable def postCalc (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  calcView (StreamCarryStep.finalFrame pre x tail a y z l)

private noncomputable def postOld (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  eraseDone 0 (postCalc pre x tail a y z l)

private theorem old_complete (pre x tail a y z l : List Bool) (h : x.length=y.length) :
    subroutine.step^[3*x.length+4] (eraseBegin 0 (postCalc pre x tail a y z l))=
      postOld pre x tail a y z l := by
  have he := erase_complete 0 (postCalc pre x tail a y z l) (y.map subroutine.bitSym)
    (valid_bits y) (x.length+1) (by rfl) (by rfl)
  have ht : x.length+1+2*(y.map subroutine.bitSym).length+3=3*x.length+4 := by
    simp only [List.length_map];omega
  simpa only [ht,postOld] using he

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem safe_left (s : Sym) (hs : s≠Sym.start) : safeStep s s .left=(s,.left) := by
  simp [safeStep,hs]

private theorem bit_not_start (b : Bool) : subroutine.bitSym b≠Sym.start := by cases b <;> decide

private theorem bits_read (w : List Bool) (j : ℕ) (hj : j < w.length) :
    subroutine.tapeOf (w.map subroutine.bitSym) (j+1)=subroutine.bitSym w[j] := by
  change (w.map subroutine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem bits_blank (w : List Bool) :
    subroutine.tapeOf (w.map subroutine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map subroutine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)

private theorem tape_not_start (w : List Sym) (hw : ∀ a ∈ w, a≠Sym.start) (j : ℕ) :
    subroutine.tapeOf w (j+1)≠Sym.start := by
  change w.getD j Sym.blank≠Sym.start
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hw _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem tape_append_one (w : List Sym) (a : Sym) :
    Function.update (subroutine.tapeOf w) (w.length+1) a=subroutine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p=w.length
    · subst p
      simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1≠w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp;omega)).symm

private theorem input_not_start (x y : List Bool) (j : ℕ) :
    subroutine.tapeOf (x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym) (j+1)≠Sym.start := by
  apply tape_not_start
  intro a ha
  simp only [List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,hb,rfl⟩|rfl|⟨b,hb,rfl⟩
  · exact bit_not_start b
  · decide
  · exact bit_not_start b


end IntMul.ReusableCarryStep


namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)

private noncomputable def seekCarryFrame (base : subroutine.Cfg) (p : ℕ) : subroutine.Cfg :=
  {base with state := relayState .seekCarry,head := Function.update base.head 11 p}

private noncomputable def copyCarryFrame (base : subroutine.Cfg) (w : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .copyCarry
  cells := Function.update base.cells 12 (subroutine.tapeOf ((w.take j).map subroutine.bitSym))
  head := fun i => if i=11 ∨ i=12 then j+1 else base.head i

private noncomputable def rewindCarryFrame (base : subroutine.Cfg) (w : List Bool) (p : ℕ) : subroutine.Cfg where
  state := relayState .rewindCarry
  cells := Function.update base.cells 12 (subroutine.tapeOf (w.map subroutine.bitSym))
  head := fun i => if i=11 ∨ i=12 then p else base.head i

private noncomputable def returnFinal (base : subroutine.Cfg) (w : List Bool) : subroutine.Cfg :=
  {rewindCarryFrame base w 0 with state := none}

private noncomputable def postReturn (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  returnFinal (postOld pre x tail a y z l) (PaddedCarryStep.nextCarryWord x y z)

end IntMul.ReusableCarryStep


namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem seek_carry_step (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step (seekCarryFrame base (p+1))=seekCarryFrame base p := by
  let c := seekCarryFrame base (p+1)
  let s : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have hi : s 11≠Sym.start := by
    change base.cells 11 (p+1)≠Sym.start
    rw [hc]
    exact tape_not_start _ (by intro a ha;obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha;exact bit_not_start b) p
  have ht : transition (relayState .seekCarry) s=(relayState .seekCarry,
      fun i => (s i,if i=11 then .left else .stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_neg hi]
    congr 1
    funext i
    by_cases h : i=11
    · subst i;simp only [if_true];exact safe_left _ hi
    · simp only [if_neg h];exact safe_stay _
  change transition (seekCarryFrame base (p+1)).state
    (fun i => (seekCarryFrame base (p+1)).cells i ((seekCarryFrame base (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekCarryFrame]

private theorem seek_carry_run (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step^[p] (seekCarryFrame base p)=seekCarryFrame base 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,seek_carry_step base w hc p,ih]

private theorem seek_carry_open (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym))
    (h12 : base.cells 12=subroutine.tapeOf []) (hh : base.head 12=0) :
    subroutine.step (seekCarryFrame base 0)=copyCarryFrame base w 0 := by
  let c := seekCarryFrame base 0
  let s : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have hi : s 11=Sym.start := by change base.cells 11 0=Sym.start;rw [hc];rfl
  have ht : transition (relayState .seekCarry) s=(relayState .copyCarry,
      fun i => (s i,if i=11 ∨ i=12 then .right else .stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_pos hi]
    congr 1
    funext i
    split <;> first | exact safe_right _ | exact safe_stay _
  change transition (seekCarryFrame base 0).state
    (fun i => (seekCarryFrame base 0).cells i ((seekCarryFrame base 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [copyCarryFrame,List.take_zero,List.map_nil]
    rw [←h12]
    exact (congrFun (Function.update_eq_self (12 : Fin 15) base.cells) i).symm
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekCarryFrame,copyCarryFrame,hh]

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulreusablecarryreturncopy_copy_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 11=subroutine.bitSym b) (ho : s 12=Sym.blank) :
    transition (relayState .copyCarry) s=(relayState .copyCarry,
      fun i => (if i=12 then s 11 else s i,if i=11 ∨ i=12 then Move.right else Move.stay)) := by
  have hb : s 11=Sym.zero ∨ s 11=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases hj : i=12
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases hk : i=11
    · simp only [hk,if_true,if_false,true_or]
      exact safe_right _
    · simp only [if_neg hj,if_neg (not_or.mpr ⟨hk,hj⟩)]
      exact safe_stay _

private theorem copy_carry_step (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (j : ℕ)
    (hj : j < w.length) :
    subroutine.step (copyCarryFrame base w j)=copyCarryFrame base w (j+1) := by
  have hi : (copyCarryFrame base w j).cells 11 ((copyCarryFrame base w j).head 11)=
      subroutine.bitSym w[j] := by
    change base.cells 11 (j+1)=_
    rw [hc];exact bits_read w j hj
  let v := (w.take j).map subroutine.bitSym
  have hl : v.length=j := by simp [v,Nat.min_eq_left hj.le]
  have ho : (copyCarryFrame base w j).cells 12 ((copyCarryFrame base w j).head 12)=Sym.blank := by
    change v.getD j Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulreusablecarryreturncopy_copy_transition (fun i => (copyCarryFrame base w j).cells i
    ((copyCarryFrame base w j).head i)) w[j] hi ho
  change transition (copyCarryFrame base w j).state
    (fun i => (copyCarryFrame base w j).cells i ((copyCarryFrame base w j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hk : i=12
    · subst i
      change Function.update (subroutine.tapeOf v) (j+1)
        ((copyCarryFrame base w j).cells 11 ((copyCarryFrame base w j).head 11))=
          subroutine.tapeOf ((w.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hv := tape_append_one v (subroutine.bitSym w[j])
      rw [hl] at hv
      rw [List.take_succ_eq_append_getElem hj,List.map_append]
      exact hv
    · rw [if_neg hk,Function.update_eq_self]
      simp only [copyCarryFrame,Function.update_of_ne hk]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyCarryFrame,Nat.add_assoc]

private theorem copy_carry_run (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (j : ℕ)
    (hj : j ≤ w.length) :
    subroutine.step^[j] (copyCarryFrame base w 0)=copyCarryFrame base w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_carry_step base w hc j (by omega)]

private theorem copy_carry_turn (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) :
    subroutine.step (copyCarryFrame base w w.length)=rewindCarryFrame base w w.length := by
  let s : Fin 15 → Sym := fun i => (copyCarryFrame base w w.length).cells i
    ((copyCarryFrame base w w.length).head i)
  have hi : s 11=Sym.blank := by
    change base.cells 11 (w.length+1)=_
    rw [hc];exact bits_blank w
  have h11 : s 11≠Sym.start := by rw [hi];decide
  have h12 : s 12≠Sym.start := by
    change subroutine.tapeOf ((w.take w.length).map subroutine.bitSym) (w.length+1)≠Sym.start
    rw [List.take_length,bits_blank];decide
  have ht : transition (relayState .copyCarry) s=(relayState .rewindCarry,
      fun i => (s i,if i=11 ∨ i=12 then Move.left else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    by_cases hj : i=11
    · subst i;simp only [true_or,if_true];exact safe_left _ h11
    · by_cases hk : i=12
      · subst i;simp only [or_true,if_true];exact safe_left _ h12
      · simp only [if_neg (not_or.mpr ⟨hj,hk⟩)];exact safe_stay _
  change transition (copyCarryFrame base w w.length).state
    (fun i => (copyCarryFrame base w w.length).cells i ((copyCarryFrame base w w.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [copyCarryFrame,rewindCarryFrame,List.take_length]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyCarryFrame,rewindCarryFrame]

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem rewind_carry_step (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step (rewindCarryFrame base w (p+1))=rewindCarryFrame base w p := by
  let s : Fin 15 → Sym := fun i => (rewindCarryFrame base w (p+1)).cells i
    ((rewindCarryFrame base w (p+1)).head i)
  have h11 : s 11≠Sym.start := by
    change base.cells 11 (p+1)≠Sym.start
    rw [hc]
    exact tape_not_start _ (by intro a ha;obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha;exact bit_not_start b) p
  have h12 : s 12≠Sym.start :=
    tape_not_start _ (by intro a ha;obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha;exact bit_not_start b) p
  have ht : transition (relayState .rewindCarry) s=(relayState .rewindCarry,
      fun i => (s i,if i=11 ∨ i=12 then Move.left else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_neg h12]
    congr 1
    funext i
    by_cases hj : i=11
    · subst i;simp only [true_or,if_true];exact safe_left _ h11
    · by_cases hk : i=12
      · subst i;simp only [or_true,if_true];exact safe_left _ h12
      · simp only [if_neg (not_or.mpr ⟨hj,hk⟩)];exact safe_stay _
  change transition (rewindCarryFrame base w (p+1)).state
    (fun i => (rewindCarryFrame base w (p+1)).cells i ((rewindCarryFrame base w (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindCarryFrame]

private theorem rewind_carry_run (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step^[p] (rewindCarryFrame base w p)=rewindCarryFrame base w 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,rewind_carry_step base w hc p,ih]

private theorem rewind_carry_halt (base : subroutine.Cfg) (w : List Bool) :
    subroutine.step (rewindCarryFrame base w 0)=returnFinal base w := by
  let s : Fin 15 → Sym := fun i => (rewindCarryFrame base w 0).cells i
    ((rewindCarryFrame base w 0).head i)
  have hi : s 12=Sym.start := rfl
  have ht : transition (relayState .rewindCarry) s=(none,fun i => (s i,Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_pos hi,safe_stay]
  change transition (rewindCarryFrame base w 0).state
    (fun i => (rewindCarryFrame base w 0).cells i ((rewindCarryFrame base w 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

/-- Every seek, open, copy, turn, rewind and halt transition is charged. -/
private theorem return_complete (base : subroutine.Cfg) (w : List Bool)
    (hc : base.cells 11=subroutine.tapeOf (w.map subroutine.bitSym))
    (h12 : base.cells 12=subroutine.tapeOf []) (hh : base.head 12=0) :
    subroutine.step^[3*w.length+4] (seekCarryFrame base (w.length+1))=returnFinal base w := by
  have hseek : subroutine.step^[w.length+2] (seekCarryFrame base (w.length+1))=
      copyCarryFrame base w 0 := by
    rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',
      seek_carry_run base w hc,seek_carry_open base w hc h12 hh]
  have hcopy : subroutine.step^[w.length+1] (copyCarryFrame base w 0)=
      rewindCarryFrame base w w.length := by
    rw [Function.iterate_succ_apply',copy_carry_run base w hc w.length (by omega),copy_carry_turn base w hc]
  have hrewind : subroutine.step^[w.length+1] (rewindCarryFrame base w w.length)=returnFinal base w := by
    rw [Function.iterate_succ_apply',rewind_carry_run base w hc,rewind_carry_halt]
  have hfirst : subroutine.step^[(w.length+1)+(w.length+2)]
      (seekCarryFrame base (w.length+1))=rewindCarryFrame base w w.length := by
    rw [Function.iterate_add_apply,hseek,hcopy]
  rw [show 3*w.length+4=(w.length+1)+((w.length+1)+(w.length+2)) by omega,
    Function.iterate_add_apply,hfirst,hrewind]

private theorem carry_return_complete (pre x tail a y z l : List Bool) :
    subroutine.step^[3*x.length+4]
      (seekCarryFrame (postOld pre x tail a y z l) (x.length+1))=postReturn pre x tail a y z l := by
  have hn : (PaddedCarryStep.nextCarryWord x y z).length=x.length := by simp [PaddedCarryStep.nextCarryWord,bin]
  have he := return_complete (postOld pre x tail a y z l) (PaddedCarryStep.nextCarryWord x y z)
    (by rfl) (by rfl) (by rfl)
  simpa only [hn,postReturn] using he

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)

/-- Proof frame recording completed real erasures. This predicate is not read
by the finite machine. Tags and selected banks in its table are fixed. -/
private def Cleared (j : ℕ) (i : Fin 15) : Prop :=
  ∃ k : Fin 10, 0 < k.val ∧ k.val ≤ j ∧ eraseBank k=i

private noncomputable def clearFrame (base : subroutine.Cfg) (j : ℕ) : subroutine.Cfg := by
  classical
  exact {
    state := none
    cells := fun i => if Cleared j i then subroutine.tapeOf [] else base.cells i
    head := fun i => if Cleared j i then 0 else base.head i}

private theorem eraseBank_injective : Function.Injective eraseBank := by decide

private theorem cleared_zero (i : Fin 15) : ¬Cleared 0 i := by
  rintro ⟨k,hk,hj,hi⟩;omega

private theorem cleared_next (k : Fin 10) (hk : 0 < k.val) (i : Fin 15) :
    Cleared k.val i ↔ Cleared (k.val-1) i ∨ i=eraseBank k := by
  constructor
  · rintro ⟨v,hv,hj,hi⟩
    by_cases h : v.val ≤ k.val-1
    · exact Or.inl ⟨v,hv,h,hi⟩
    · have hval : v.val=k.val := by omega
      have hvk : v=k := Fin.ext hval
      exact Or.inr (by simpa only [hvk] using hi.symm)
  · rintro (⟨v,hv,hj,hi⟩|hi)
    · exact ⟨v,hv,by omega,hi⟩
    · exact ⟨k,hk,by omega,hi.symm⟩

private theorem selected_fresh (k : Fin 10) (hk : 0 < k.val) :
    ¬Cleared (k.val-1) (eraseBank k) := by
  rintro ⟨v,hv,hj,hi⟩
  have he := eraseBank_injective hi
  subst v
  omega

private theorem clear_zero (base : subroutine.Cfg) : clearFrame base 0={base with state := none} := by
  apply cfg_ext
  · rfl
  · funext i;simp [clearFrame,cleared_zero]
  · funext i;simp [clearFrame,cleared_zero]

private theorem clear_next_frame (base : subroutine.Cfg) (k : Fin 10) (hk : 0 < k.val) :
    eraseDone k (clearFrame base (k.val-1))=clearFrame base k.val := by
  have hclear : Cleared k.val (eraseBank k) := ⟨k,hk,by omega,rfl⟩
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i=eraseBank k
    · subst i
      simp only [eraseDone,Function.update_self,clearFrame,if_pos hclear]
    · simp only [eraseDone,Function.update_of_ne hi,clearFrame]
      have he : Cleared k.val i ↔ Cleared (k.val-1) i := by
        constructor
        · intro h
          rcases (cleared_next k hk i).mp h with h|h
          · exact h
          · exact (hi h).elim
        · intro h;exact (cleared_next k hk i).mpr (Or.inl h)
      rw [he]
  · funext i
    by_cases hi : i=eraseBank k
    · subst i
      simp only [eraseDone,Function.update_self,clearFrame,if_pos hclear]
    · simp only [eraseDone,Function.update_of_ne hi,clearFrame]
      have he : Cleared k.val i ↔ Cleared (k.val-1) i := by
        constructor
        · intro h
          rcases (cleared_next k hk i).mp h with h|h
          · exact h
          · exact (hi h).elim
        · intro h;exact (cleared_next k hk i).mpr (Or.inl h)
      rw [he]

private theorem clear_native (base : subroutine.Cfg) (k : Fin 10) (hk : 0 < k.val)
    (w : List Sym) (hw : TapeBankErase.ValidWord w) (h : ℕ)
    (hc : base.cells (eraseBank k)=subroutine.tapeOf w) (hh : base.head (eraseBank k)=h) :
    subroutine.step^[h+2*w.length+3]
      (eraseBegin k (clearFrame base (k.val-1)))=clearFrame base k.val := by
  rw [erase_complete k (clearFrame base (k.val-1)) w hw h
    (by simp only [clearFrame,if_neg (selected_fresh k hk)];exact hc)
    (by simp only [clearFrame,if_neg (selected_fresh k hk)];exact hh),clear_next_frame base k hk]

/-- Exact physical words retained after arithmetic and carry return. -/
private noncomputable def workWord (k : Fin 10) (x y z : List Bool) : List Sym :=
  if k=0 then y.map subroutine.bitSym
  else if k=1 then x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym
  else if k=2 then (CarryStep.digitWord x y z).map subroutine.bitSym
  else if k=3 then (CarryStep.sumWord x y).map subroutine.bitSym
  else if k=4 then x.map subroutine.bitSym
  else if k=5 then (CarryStep.sumWord x y).reverse.map subroutine.bitSym++Sym.sep::z.map subroutine.bitSym
  else if k=8 then (CarryStep.carryWord x y z).map subroutine.bitSym
  else if k=9 then (PaddedCarryStep.nextCarryWord x y z).map subroutine.bitSym
  else Sym.sep::(z.map subroutine.bitSym++[Sym.sep])

private def workHead (k : Fin 10) (x z : List Bool) : ℕ :=
  if k=0 ∨ k=1 then x.length+1
  else if k=2 then CarryStep.blockSize z+1
  else if k=5 then x.length+2
  else if k=6 ∨ k=7 then z.length+1 else 0

private theorem work_valid (k : Fin 10) (x y z : List Bool) : TapeBankErase.ValidWord (workWord k x y z) := by
  have hb := valid_bits
  have hsep := valid_sep
  have hv (w : List Bool) : TapeBankErase.ValidWord (Sym.sep::w.map subroutine.bitSym) :=
    valid_append [Sym.sep] _ hsep (valid_bits w)
  have hd : TapeBankErase.ValidWord (Sym.sep::(z.map subroutine.bitSym++[Sym.sep])) :=
    valid_append [Sym.sep] _ hsep (valid_append _ _ (valid_bits z) hsep)
  fin_cases k <;> simp only [workWord,if_true,if_false]
  all_goals first | exact valid_bits _ | exact valid_append _ _ (valid_bits _) (hv _) | exact hd

private theorem work_cells (pre x tail a y z l : List Bool) (k : Fin 10) (hk : 0 < k.val) :
    (postReturn pre x tail a y z l).cells (eraseBank k)=subroutine.tapeOf (workWord k x y z) := by
  fin_cases k <;> simp_all only [Fin.val_zero,Fin.val_one,Nat.lt_irrefl]
  all_goals rfl

private theorem work_heads (pre x tail a y z l : List Bool) (k : Fin 10) (hk : 0 < k.val) :
    (postReturn pre x tail a y z l).head (eraseBank k)=workHead k x z := by
  fin_cases k <;> simp_all only [Fin.val_zero,Fin.val_one,Nat.lt_irrefl]
  all_goals rfl

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)

private noncomputable def clearEntry (base : subroutine.Cfg) (k : Fin 10) : machine.Cfg :=
  FiniteCaller.embed subroutine Phase .calc (.erase k) dispatch
    (eraseBegin k (clearFrame base (k.val-1)))

private noncomputable def descriptorBegin (base : subroutine.Cfg) : subroutine.Cfg :=
  {clearFrame base 9 with state := relayState .seekDescriptor}

private noncomputable def clearTarget (base : subroutine.Cfg) (k : Fin 10) : machine.Cfg :=
  if h : k.val < 9 then
    clearEntry base ⟨k.val+1,by omega⟩
  else FiniteCaller.embed subroutine Phase .calc .descriptor dispatch (descriptorBegin base)

private theorem clear_returned (base : subroutine.Cfg) (k : Fin 10) (hk : 0 < k.val) :
    FiniteCaller.returned subroutine Phase .calc (.erase k) dispatch (clearFrame base k.val)=
      clearTarget base k := by
  have hzero : k≠0 := by intro h;subst k;omega
  by_cases h : k.val < 9
  · apply cfg_ext
    · simp [FiniteCaller.returned,dispatch,hzero,h,clearTarget,clearEntry,FiniteCaller.embed,eraseBegin]
    · simp [FiniteCaller.returned,clearTarget,h,clearEntry,FiniteCaller.embed,eraseBegin]
    · simp [FiniteCaller.returned,clearTarget,h,clearEntry,FiniteCaller.embed,eraseBegin]
  · have hn : k.val=9 := by omega
    apply cfg_ext
    · simp [FiniteCaller.returned,dispatch,hzero,h,clearTarget,FiniteCaller.embed,descriptorBegin]
    · simp [FiniteCaller.returned,clearTarget,h,FiniteCaller.embed,descriptorBegin,hn]
    · simp [FiniteCaller.returned,clearTarget,h,FiniteCaller.embed,descriptorBegin,hn]

private noncomputable def clearCost (k : Fin 10) (x y z : List Bool) : ℕ :=
  workHead k x z+2*(workWord k x y z).length+4

private theorem clear_call (pre x tail a y z l : List Bool) (k : Fin 10) (hk : 0 < k.val) :
    ∃ t : ℕ, t ≤ clearCost k x y z ∧
      machine.step^[t] (clearEntry (postReturn pre x tail a y z l) k)=
        clearTarget (postReturn pre x tail a y z l) k := by
  let base := postReturn pre x tail a y z l
  let u := workHead k x z+2*(workWord k x y z).length+3
  have hn : subroutine.step^[u] (eraseBegin k (clearFrame base (k.val-1)))=clearFrame base k.val :=
    clear_native base k hk _ (work_valid k x y z) _ (work_cells pre x tail a y z l k hk)
      (work_heads pre x tail a y z l k hk)
  obtain ⟨t,ht,he⟩ := (FiniteCaller.simulate_run subroutine Phase .calc (.erase k) dispatch
    (eraseBegin k (clearFrame base (k.val-1))) u).2 (by rw [hn];rfl)
  rw [hn,clear_returned base k hk] at he
  refine ⟨t,?_,he⟩
  change t ≤ workHead k x z+2*(workWord k x y z).length+4
  dsimp only [u] at ht
  omega

private theorem clear_total_cost (x y z : List Bool) (h : x.length=y.length)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    clearCost 1 x y z+clearCost 2 x y z+clearCost 3 x y z+
      clearCost 4 x y z+clearCost 5 x y z+clearCost 6 x y z+
      clearCost 7 x y z+clearCost 8 x y z+clearCost 9 x y z=
        16*x.length+CarryStep.blockSize z+8*z.length+60 := by
  have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
    simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left hB]
  have hc : (CarryStep.carryWord x y z).length=x.length+1-CarryStep.blockSize z := by
    simp [CarryStep.carryWord,CarryStep.sumWord,bin]
  simp [clearCost,workHead,workWord,hd,hc,PaddedCarryStep.nextCarryWord,
    CarryStep.sumWord,bin,h.symm] <;> omega

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep

private theorem clear_group_complete (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 16*x.length+CarryStep.blockSize z+8*z.length+60 ∧
      machine.step^[t] (clearEntry (postReturn pre x tail a y z l) 1)=
        FiniteCaller.embed subroutine Phase .calc .descriptor dispatch
          (descriptorBegin (postReturn pre x tail a y z l)) := by
  obtain ⟨c1,hc1,he1⟩ := clear_call pre x tail a y z l 1 (by decide)
  simp only [clearTarget,dif_pos (show (1 : Fin 10).val < 9 by decide)] at he1
  change machine.step^[c1] (clearEntry (postReturn pre x tail a y z l) 1)=clearEntry (postReturn pre x tail a y z l) 2 at he1
  obtain ⟨c2,hc2,he2⟩ := clear_call pre x tail a y z l 2 (by decide)
  simp only [clearTarget,dif_pos (show (2 : Fin 10).val < 9 by decide)] at he2
  change machine.step^[c2] (clearEntry (postReturn pre x tail a y z l) 2)=clearEntry (postReturn pre x tail a y z l) 3 at he2
  obtain ⟨c3,hc3,he3⟩ := clear_call pre x tail a y z l 3 (by decide)
  simp only [clearTarget,dif_pos (show (3 : Fin 10).val < 9 by decide)] at he3
  change machine.step^[c3] (clearEntry (postReturn pre x tail a y z l) 3)=clearEntry (postReturn pre x tail a y z l) 4 at he3
  obtain ⟨c4,hc4,he4⟩ := clear_call pre x tail a y z l 4 (by decide)
  simp only [clearTarget,dif_pos (show (4 : Fin 10).val < 9 by decide)] at he4
  change machine.step^[c4] (clearEntry (postReturn pre x tail a y z l) 4)=clearEntry (postReturn pre x tail a y z l) 5 at he4
  obtain ⟨c5,hc5,he5⟩ := clear_call pre x tail a y z l 5 (by decide)
  simp only [clearTarget,dif_pos (show (5 : Fin 10).val < 9 by decide)] at he5
  change machine.step^[c5] (clearEntry (postReturn pre x tail a y z l) 5)=clearEntry (postReturn pre x tail a y z l) 6 at he5
  obtain ⟨c6,hc6,he6⟩ := clear_call pre x tail a y z l 6 (by decide)
  simp only [clearTarget,dif_pos (show (6 : Fin 10).val < 9 by decide)] at he6
  change machine.step^[c6] (clearEntry (postReturn pre x tail a y z l) 6)=clearEntry (postReturn pre x tail a y z l) 7 at he6
  obtain ⟨c7,hc7,he7⟩ := clear_call pre x tail a y z l 7 (by decide)
  simp only [clearTarget,dif_pos (show (7 : Fin 10).val < 9 by decide)] at he7
  change machine.step^[c7] (clearEntry (postReturn pre x tail a y z l) 7)=clearEntry (postReturn pre x tail a y z l) 8 at he7
  obtain ⟨c8,hc8,he8⟩ := clear_call pre x tail a y z l 8 (by decide)
  simp only [clearTarget,dif_pos (show (8 : Fin 10).val < 9 by decide)] at he8
  change machine.step^[c8] (clearEntry (postReturn pre x tail a y z l) 8)=clearEntry (postReturn pre x tail a y z l) 9 at he8
  obtain ⟨c9,hc9,he9⟩ := clear_call pre x tail a y z l 9 (by decide)
  simp only [clearTarget,dif_neg (show ¬((9 : Fin 10).val < 9) by decide)] at he9
  have he : machine.step^[c9+(c8+(c7+(c6+(c5+(c4+(c3+(c2+(c1))))))))] (clearEntry (postReturn pre x tail a y z l) 1)=
      FiniteCaller.embed subroutine Phase .calc .descriptor dispatch
        (descriptorBegin (postReturn pre x tail a y z l)) := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      he1,he2,he3,he4,he5,he6,he7,he8,he9]
  refine ⟨c9+(c8+(c7+(c6+(c5+(c4+(c3+(c2+(c1)))))))),?_,he⟩
  have ht := clear_total_cost x y z h hB
  omega

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem descriptor_not_cleared (j : ℕ) : ¬Cleared j 6 := by
  rintro ⟨k,hk,hj,hi⟩
  have hn : ∀ k : Fin 10, eraseBank k≠6 := by decide
  exact hn k hi

private noncomputable def descriptorFrame (base : subroutine.Cfg) (p : ℕ) : subroutine.Cfg :=
  {clearFrame base 9 with
    state := relayState .seekDescriptor
    head := Function.update (clearFrame base 9).head 6 p}

private noncomputable def descriptorFinal (base : subroutine.Cfg) : subroutine.Cfg :=
  {descriptorFrame base 0 with state := none}

private theorem descriptor_step (base : subroutine.Cfg) (z : List Bool)
    (hc : base.cells 6=subroutine.tapeOf (z.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step (descriptorFrame base (p+1))=descriptorFrame base p := by
  let s : Fin 15 → Sym := fun i => (descriptorFrame base (p+1)).cells i
    ((descriptorFrame base (p+1)).head i)
  have hi : s 6≠Sym.start := by
    change (clearFrame base 9).cells 6 (p+1)≠Sym.start
    simp only [clearFrame,if_neg (descriptor_not_cleared 9)]
    rw [hc]
    exact tape_not_start _ (by intro a ha;obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha;exact bit_not_start b) p
  have ht : transition (relayState .seekDescriptor) s=(relayState .seekDescriptor,
      fun i => (s i,if i=6 then Move.left else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_neg hi]
    congr 1
    funext i
    by_cases h : i=6
    · subst i;simp only [if_true];exact safe_left _ hi
    · simp only [if_neg h];exact safe_stay _
  change transition (descriptorFrame base (p+1)).state
    (fun i => (descriptorFrame base (p+1)).cells i ((descriptorFrame base (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [descriptorFrame]

private theorem descriptor_run (base : subroutine.Cfg) (z : List Bool)
    (hc : base.cells 6=subroutine.tapeOf (z.map subroutine.bitSym)) (p : ℕ) :
    subroutine.step^[p] (descriptorFrame base p)=descriptorFrame base 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,descriptor_step base z hc p,ih]

private theorem descriptor_halt (base : subroutine.Cfg) (z : List Bool)
    (hc : base.cells 6=subroutine.tapeOf (z.map subroutine.bitSym)) :
    subroutine.step (descriptorFrame base 0)=descriptorFinal base := by
  let s : Fin 15 → Sym := fun i => (descriptorFrame base 0).cells i ((descriptorFrame base 0).head i)
  have hi : s 6=Sym.start := by
    change (clearFrame base 9).cells 6 0=Sym.start
    simp only [clearFrame,if_neg (descriptor_not_cleared 9)]
    rw [hc];rfl
  have ht : transition (relayState .seekDescriptor) s=(none,fun i => (s i,Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_pos hi,safe_stay]
  change transition (descriptorFrame base 0).state
    (fun i => (descriptorFrame base 0).cells i ((descriptorFrame base 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem descriptor_complete (pre x tail a y z l : List Bool) :
    subroutine.step^[z.length+2] (descriptorBegin (postReturn pre x tail a y z l))=
      descriptorFinal (postReturn pre x tail a y z l) := by
  let base := postReturn pre x tail a y z l
  have hc : base.cells 6=subroutine.tapeOf (z.map subroutine.bitSym) := rfl
  have hh : base.head 6=z.length+1 := rfl
  have hin : descriptorBegin base=descriptorFrame base (z.length+1) := by
    apply cfg_ext
    · rfl
    · rfl
    · have h6 : (clearFrame base 9).head 6=z.length+1 := by
        simp only [clearFrame,if_neg (descriptor_not_cleared 9)];exact hh
      change (clearFrame base 9).head=Function.update (clearFrame base 9).head 6 (z.length+1)
      rw [←h6,Function.update_eq_self]
  rw [hin,show z.length+2=(z.length+1)+1 by omega,Function.iterate_succ_apply',
    descriptor_run base z hc,descriptor_halt base z hc]

private theorem final_handoff (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .calc .descriptor dispatch
      (descriptorFinal (postReturn pre x tail a y z l))=finalFrame pre x tail a y z l := by
  have hclear (i : Fin 15) : Cleared 9 i ↔
      i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 := by
    unfold Cleared
    fin_cases i <;> decide
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,descriptorFinal,descriptorFrame,clearFrame,hclear,
      postReturn,returnFinal,rewindCarryFrame,postOld,eraseDone,eraseBank,postCalc,calcView,
      StreamCarryStep.finalFrame,PaddedCarryStep.finalFrame,CarryStep.finalFrame,finalFrame]
    all_goals rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,descriptorFinal,descriptorFrame,clearFrame,hclear,
      postReturn,returnFinal,rewindCarryFrame,postOld,eraseDone,eraseBank,postCalc,calcView,
      StreamCarryStep.finalFrame,PaddedCarryStep.finalFrame,CarryStep.finalFrame,finalFrame]

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep

/-- State-only initial embedding, with every real cell and head retained. -/
private theorem calc_initial (pre x tail a y z l : List Bool) :
    initialFrame pre x tail a y z l=
      FiniteCaller.embed subroutine Phase .calc .calc dispatch
        (calcView (StreamCarryStep.initialFrame pre x tail a y z l)) := rfl

private theorem after_calc (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .calc .calc dispatch (postCalc pre x tail a y z l)=
      FiniteCaller.embed subroutine Phase .calc (.erase 0) dispatch
        (eraseBegin 0 (postCalc pre x tail a y z l)) := rfl

private theorem after_old (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .calc (.erase 0) dispatch (postOld pre x tail a y z l)=
      FiniteCaller.embed subroutine Phase .calc .returnCarry dispatch
        (seekCarryFrame (postOld pre x tail a y z l) (x.length+1)) := by
  apply cfg_ext
  · rfl
  · rfl
  · have hh : (postOld pre x tail a y z l).head 11=x.length+1 := rfl
    change (postOld pre x tail a y z l).head=
      Function.update (postOld pre x tail a y z l).head 11 (x.length+1)
    rw [←hh,Function.update_eq_self]

private theorem after_return (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .calc .returnCarry dispatch (postReturn pre x tail a y z l)=
      clearEntry (postReturn pre x tail a y z l) 1 := by
  apply cfg_ext
  · rfl
  · funext i
    simp [FiniteCaller.returned,clearEntry,FiniteCaller.embed,eraseBegin,clearFrame,cleared_zero]
  · funext i
    simp [FiniteCaller.returned,clearEntry,FiniteCaller.embed,eraseBegin,clearFrame,cleared_zero]

/-- At a charged caller restart, the exact retained cells and heads have the
next incoming frame. This lemma asserts no free transition or data loading. -/
private theorem next_frame (pre x xNext tailNext a y z l : List Bool)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    (finalFrame pre x (xNext++tailNext) a y z l).cells=
      (initialFrame (pre++x) xNext tailNext (a++CarryStep.digitWord x y z)
        (PaddedCarryStep.nextCarryWord x y z) z l).cells ∧
    (finalFrame pre x (xNext++tailNext) a y z l).head=
      (initialFrame (pre++x) xNext tailNext (a++CarryStep.digitWord x y z)
        (PaddedCarryStep.nextCarryWord x y z) z l).head := by
  have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
    simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left hB]
  constructor
  · funext i
    fin_cases i <;> simp [finalFrame,initialFrame,StreamCarryStep.initialFrame,
      StreamCarryStep.rootTape,List.append_assoc] <;> rfl
  · funext i
    fin_cases i <;> simp [finalFrame,initialFrame,StreamCarryStep.initialFrame,hd,Nat.add_assoc]

end IntMul.ReusableCarryStep



namespace IntMul.ReusableCarryStep

/-- Complete actual reusable streaming carry update, including carry return,
nine physical work-bank erasures, descriptor rewind and thirteen caller returns. -/
private theorem reusable_carry_step (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 41*x.length+13*CarryStep.blockSize z+21*z.length+4*l.length+125 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by
  obtain ⟨u,hu,hcalc,hhcalc,hd,hc⟩ := StreamCarryStep.stream_carry_step pre x tail a y z l h hn hB
  have hncalc : subroutine.step^[u] (calcView (StreamCarryStep.initialFrame pre x tail a y z l))=
      postCalc pre x tail a y z l := by rw [calc_run,hcalc];rfl
  obtain ⟨a₁,ha₁,he₁⟩ := (FiniteCaller.simulate_run subroutine Phase .calc .calc dispatch
    (calcView (StreamCarryStep.initialFrame pre x tail a y z l)) u).2 (by rw [hncalc];rfl)
  rw [hncalc,after_calc] at he₁
  obtain ⟨a₂,ha₂,he₂⟩ := (FiniteCaller.simulate_run subroutine Phase .calc (.erase 0) dispatch
    (eraseBegin 0 (postCalc pre x tail a y z l)) (3*x.length+4)).2
      (by rw [old_complete pre x tail a y z l h];rfl)
  rw [old_complete pre x tail a y z l h,after_old] at he₂
  obtain ⟨a₃,ha₃,he₃⟩ := (FiniteCaller.simulate_run subroutine Phase .calc .returnCarry dispatch
    (seekCarryFrame (postOld pre x tail a y z l) (x.length+1)) (3*x.length+4)).2
      (by rw [carry_return_complete];rfl)
  rw [carry_return_complete,after_return] at he₃
  obtain ⟨a₄,ha₄,he₄⟩ := clear_group_complete pre x tail a y z l h hB
  obtain ⟨a₅,ha₅,he₅⟩ := (FiniteCaller.simulate_run subroutine Phase .calc .descriptor dispatch
    (descriptorBegin (postReturn pre x tail a y z l)) (z.length+2)).2
      (by rw [descriptor_complete];rfl)
  rw [descriptor_complete,final_handoff] at he₅
  have he : machine.step^[a₅+(a₄+(a₃+(a₂+a₁)))] (initialFrame pre x tail a y z l)=
      finalFrame pre x tail a y z l := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      Function.iterate_add_apply,calc_initial,he₁,he₂,he₃,he₄,he₅]
  refine ⟨a₅+(a₄+(a₃+(a₂+a₁))),by omega,he,?_,hd,hc⟩
  rw [he];rfl

end IntMul.ReusableCarryStep



open IntMul IntMul.ReusableCarryStep

theorem solution (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 41*x.length+13*CarryStep.blockSize z+21*z.length+4*l.length+125 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) :=
  IntMul.ReusableCarryStep.reusable_carry_step pre x tail a y z l h hn hB

#print axioms solution
