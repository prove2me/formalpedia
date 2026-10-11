-- Prove2me | solution 1 for IntMul.StreamCarryStep.stream_carry_step
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T11:57:18.305384+00:00
-- url     : https://prove2.me/submissions/45e776d0-85e9-418b-b1cf-b299402b12ca

import Definitions.Def_IntMul_StreamCarryStep
import Mathlib.Tactic
import Theorems.Thm_IntMul_FramedBlockRead_read_block
import Theorems.Thm_IntMul_PaddedCarryStep_padded_carry_step
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.StreamCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem owned_intmulstreamcarryprograms_safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private theorem owned_intmulstreamcarryprograms_safe_main (q : PaddedCarryStep.machine.K) (a : Fin 10 → Sym) (j : Fin 10) :
    safeStep (a j) ((PaddedCarryStep.machine.δ q a).2 j).1 ((PaddedCarryStep.machine.δ q a).2 j).2=
      (PaddedCarryStep.machine.δ q a).2 j := by
  apply owned_intmulstreamcarryprograms_safe_identity
  · exact PaddedCarryStep.machine.start_preserved q a j
  · exact PaddedCarryStep.machine.start_only_at_start q a j

private theorem owned_intmulstreamcarryprograms_safe_read (q : CountedStream.machine.K) (a : Fin 4 → Sym) (j : Fin 4) :
    safeStep (a j) ((CountedStream.machine.δ q a).2 j).1 ((CountedStream.machine.δ q a).2 j).2=
      (CountedStream.machine.δ q a).2 j := by
  apply owned_intmulstreamcarryprograms_safe_identity
  · exact CountedStream.machine.start_preserved q a j
  · exact CountedStream.machine.start_only_at_start q a j

private noncomputable def mainView (base : subroutine.Cfg) (c : PaddedCarryStep.machine.Cfg) : subroutine.Cfg where
  state := mainState c.state
  cells := fun i => if h : 2 ≤ i.val ∧ i.val < 12 then c.cells ⟨i.val-2,by change i.val-2 < 10; omega⟩ else base.cells i
  head := fun i => if h : 2 ≤ i.val ∧ i.val < 12 then c.head ⟨i.val-2,by change i.val-2 < 10; omega⟩ else base.head i

private noncomputable def readView (base : subroutine.Cfg) (c : CountedStream.machine.Cfg) : subroutine.Cfg where
  state := readState c.state
  cells := fun i => if i=0 then c.cells 0 else if i=2 then c.cells 1
    else if i=13 then c.cells 2 else if i=14 then c.cells 3 else base.cells i
  head := fun i => if i=0 then c.head 0 else if i=2 then c.head 1
    else if i=13 then c.head 2 else if i=14 then c.head 3 else base.head i

private theorem main_step (base : subroutine.Cfg) (c : PaddedCarryStep.machine.Cfg) :
    subroutine.step (mainView base c)=mainView base (PaddedCarryStep.machine.step c) := by
  let a : Fin 15 → Sym := fun i => (mainView base c).cells i ((mainView base c).head i)
  let b : Fin 10 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (mainTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (mainState c.state) a=(mainState (PaddedCarryStep.machine.δ c.state b).1,
      mainAction a (PaddedCarryStep.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,PaddedCarryStep.machine.halt_fixed b]
      simp only [mainState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [mainState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_stay _
      · exact safe_stay _
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 0
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 1
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 2
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 3
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 4
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 5
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 6
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 7
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 8
      · exact owned_intmulstreamcarryprograms_safe_main c.state b 9
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
  change transition (mainView base c).state
    (fun i => (mainView base c).cells i ((mainView base c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem main_run (base : subroutine.Cfg) (c : PaddedCarryStep.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (mainView base c)=mainView base (PaddedCarryStep.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,main_step,Function.iterate_succ_apply']

private theorem read_step (base : subroutine.Cfg) (c : CountedStream.machine.Cfg) :
    subroutine.step (readView base c)=readView base (CountedStream.machine.step c) := by
  let a : Fin 15 → Sym := fun i => (readView base c).cells i ((readView base c).head i)
  let b : Fin 4 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (readTape j))=b := by funext j;fin_cases j <;> rfl
  have ht : transition (readState c.state) a=(readState (CountedStream.machine.δ c.state b).1,
      readAction a (CountedStream.machine.δ c.state b).2) := by
    by_cases h : c.state=.halt
    · rw [h,CountedStream.machine.halt_fixed b]
      simp only [readState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [readState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact owned_intmulstreamcarryprograms_safe_read c.state b 0
      · exact safe_stay _
      · exact owned_intmulstreamcarryprograms_safe_read c.state b 1
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
      · exact owned_intmulstreamcarryprograms_safe_read c.state b 2
      · exact owned_intmulstreamcarryprograms_safe_read c.state b 3
  change transition (readView base c).state
    (fun i => (readView base c).cells i ((readView base c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rfl
    · exact Function.update_eq_self _ _
    · rfl
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · rfl
    · rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem read_run (base : subroutine.Cfg) (c : CountedStream.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (readView base c)=readView base (CountedStream.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,read_step,Function.iterate_succ_apply']

end IntMul.StreamCarryStep



namespace IntMul.StreamCarryStep
open TapeCopy (Sym)

private noncomputable def incoming (pre x tail a y z l : List Bool) : subroutine.Cfg where
  state := subroutine.qStart
  cells := (initialFrame pre x tail a y z l).cells
  head := (initialFrame pre x tail a y z l).head

private noncomputable def readReady (pre x tail a y z l : List Bool) (j : ℕ) (q : CountedStream.State) : subroutine.Cfg :=
  readView (incoming pre x tail a y z l) (FramedBlockRead.ready pre x tail [] l j q)

private noncomputable def readBegin (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  {readReady pre x tail a y z l 0 .emit with
    state := relayState .openRead
    head := Function.update (readReady pre x tail a y z l 0 .emit).head 2 0}

/-- The five caller-owned banks frozen throughout native arithmetic. -/
private noncomputable def mainBase (pre x tail a y z l : List Bool) : subroutine.Cfg where
  state := none
  cells := (initialFrame pre x tail a y z l).cells
  head := fun i => if i=0 then pre.length+x.length+1 else if i=12 then y.length+1
    else (initialFrame pre x tail a y z l).head i

private noncomputable def arithmeticInitial (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  mainView (mainBase pre x tail a y z l) (PaddedCarryStep.initialFrame x y z)

private noncomputable def arithmeticFinal (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  mainView (mainBase pre x tail a y z l) (PaddedCarryStep.finalFrame x y z)

private noncomputable def openCarryFrame (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  {readReady pre x tail a y z l x.length .halt with
    state := relayState .openCarry}

private noncomputable def carryFrame (pre x tail a y z l : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .copyCarry
  cells := fun i => if i=2 then subroutine.tapeOf
      (x.map subroutine.bitSym++Sym.sep::(y.take j).map subroutine.bitSym)
    else (mainBase pre x tail a y z l).cells i
  head := fun i => if i=2 then x.length+j+2 else if i=12 then j+1
    else (mainBase pre x tail a y z l).head i

private noncomputable def rewindFrame (pre x tail a y z l : List Bool) (p : ℕ) : subroutine.Cfg :=
  {arithmeticInitial pre x tail a y z l with
    state := relayState .rewindRequest
    head := Function.update (arithmeticInitial pre x tail a y z l).head 2 p}

private noncomputable def prepareFinal (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  {arithmeticInitial pre x tail a y z l with state := none}

private noncomputable def seekFrame (pre x tail a y z l : List Bool) (p : ℕ) : subroutine.Cfg :=
  {arithmeticFinal pre x tail a y z l with
    state := relayState .seekDigitStart
    head := Function.update (arithmeticFinal pre x tail a y z l).head 3 p}

private noncomputable def outputFrame (pre x tail a y z l : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .copyDigit
  cells := fun i => if i=1 then subroutine.tapeOf
      ((a++(CarryStep.digitWord x y z).take j).map subroutine.bitSym)
    else (arithmeticFinal pre x tail a y z l).cells i
  head := fun i => if i=1 then a.length+j+1 else if i=3 then j+1
    else (arithmeticFinal pre x tail a y z l).head i

private noncomputable def outputFinal (pre x tail a y z l : List Bool) : subroutine.Cfg :=
  {outputFrame pre x tail a y z l (CarryStep.digitWord x y z).length with state := none}

private theorem read_initial (pre x tail a y z l : List Bool) :
    initialFrame pre x tail a y z l=
      FiniteCaller.embed subroutine Phase .read .read dispatch (readBegin pre x tail a y z l) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.embed,readBegin,readReady,readView,incoming,initialFrame,
      FramedBlockRead.ready,FramedBlockRead.frame,descriptorTape,rootTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.embed,readBegin,readReady,readView,incoming,initialFrame,
      FramedBlockRead.ready,FramedBlockRead.frame]

private theorem output_to_final (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hB : CarryStep.blockSize z ≤ x.length+1) :
    FiniteCaller.returned subroutine Phase .read .output dispatch (outputFinal pre x tail a y z l)=
      finalFrame pre x tail a y z l := by
  have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
    simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left hB]
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,outputFinal,outputFrame,arithmeticFinal,mainView,mainBase,initialFrame,finalFrame] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,outputFinal,outputFrame,arithmeticFinal,mainView,mainBase,initialFrame,finalFrame,
      PaddedCarryStep.finalFrame,CarryStep.finalFrame,h,hd]

end IntMul.StreamCarryStep


namespace IntMul.StreamCarryStep
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


end IntMul.StreamCarryStep


namespace IntMul.StreamCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulstreamcarryread_safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem owned_intmulstreamcarryread_open_read_transition (a : Fin 15 → Sym) :
    transition (relayState .openRead) a=
      (readState .emit,fun i => (a i,if i=2 then .right else .stay)) := by
  simp only [transition,rawTransition,relayState,relayRaw]
  congr 1
  funext i
  by_cases hi : i=2
  · simp only [hi,if_true]
    exact owned_intmulstreamcarryread_safe_right _
  · simp only [if_neg hi]
    exact safe_stay _

private theorem open_read_step (pre x tail a y z l : List Bool) :
    subroutine.step (readBegin pre x tail a y z l)=
      readReady pre x tail a y z l 0 .emit := by
  have ht := owned_intmulstreamcarryread_open_read_transition
    (fun i => (readBegin pre x tail a y z l).cells i ((readBegin pre x tail a y z l).head i))
  change transition (readBegin pre x tail a y z l).state
    (fun i => (readBegin pre x tail a y z l).cells i ((readBegin pre x tail a y z l).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [readBegin,readReady,readView,FramedBlockRead.ready,FramedBlockRead.frame]

private theorem read_complete (pre x tail a y z l : List Bool)
    (hn : x.length=val l+1) :
    ∃ t : ℕ, t ≤ 6*x.length+4*l.length+3 ∧
      subroutine.step^[t] (readBegin pre x tail a y z l)=
        readReady pre x tail a y z l x.length .halt := by
  obtain ⟨t,ht,he⟩ := FramedBlockRead.read_block pre x tail [] l (by omega)
  rw [←hn] at he ht
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,open_read_step]
  unfold readReady
  rw [read_run,he]

private theorem after_read (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .read .read dispatch
      (readReady pre x tail a y z l x.length .halt)=
      FiniteCaller.embed subroutine Phase .read .prepare dispatch
        (openCarryFrame pre x tail a y z l) := by
  apply cfg_ext
  · rfl
  · rfl
  · rfl

end IntMul.StreamCarryStep



namespace IntMul.StreamCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem open_carry_step (pre x tail a y z l : List Bool) :
    subroutine.step (openCarryFrame pre x tail a y z l)=carryFrame pre x tail a y z l 0 := by
  let c := openCarryFrame pre x tail a y z l
  let s : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ho : s 2=Sym.blank := by
    have hb : FramedBlockRead.machine.tapeOf (x.map FramedBlockRead.machine.bitSym) (x.length+1)=Sym.blank := by
      change (x.map FramedBlockRead.machine.bitSym).getD x.length Sym.blank=Sym.blank
      exact List.getD_eq_default _ _ (by simp)
    simpa [s,c,openCarryFrame,readReady,readView,FramedBlockRead.ready,FramedBlockRead.frame] using hb
  have ht : transition (relayState .openCarry) s=(relayState .copyCarry,
      fun i => (if i=2 then Sym.sep else s i,if i=2 ∨ i=12 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    congr 1
    funext i
    by_cases hi : i=2
    · subst i
      simp [ho,safeStep]
    · by_cases hj : i=12
      · simp only [hj,if_true,if_false,or_true]
        exact safe_right _
      · simp only [if_neg hi,if_neg (not_or.mpr ⟨hi,hj⟩)]
        exact safe_stay _
  change transition (openCarryFrame pre x tail a y z l).state
    (fun i => (openCarryFrame pre x tail a y z l).cells i
      ((openCarryFrame pre x tail a y z l).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=2
    · subst i
      change Function.update (subroutine.tapeOf ((x.take x.length).map subroutine.bitSym))
        (0+x.length+1) Sym.sep=subroutine.tapeOf (x.map subroutine.bitSym++[Sym.sep])
      simpa only [List.take_length,List.length_map,Nat.zero_add] using tape_append_one (x.map subroutine.bitSym) Sym.sep
    · rw [if_neg hi,Function.update_eq_self]
      fin_cases i
      all_goals first | exact False.elim (hi rfl) | simp [c,openCarryFrame,readReady,readView,incoming,carryFrame,mainBase,
        initialFrame,FramedBlockRead.ready,FramedBlockRead.frame,descriptorTape,rootTape] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,openCarryFrame,readReady,readView,incoming,carryFrame,mainBase,
      initialFrame,FramedBlockRead.ready,FramedBlockRead.frame]

private theorem owned_intmulstreamcarryrequest_carry_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 12=subroutine.bitSym b) (ho : s 2=Sym.blank) :
    transition (relayState .copyCarry) s=(relayState .copyCarry,
      fun i => (if i=2 then s 12 else s i,if i=2 ∨ i=12 then Move.right else Move.stay)) := by
  have hb : s 12=Sym.zero ∨ s 12=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases hj : i=2
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases hk : i=12
    · simp only [hk,if_true,if_false,or_true]
      exact safe_right _
    · simp only [if_neg hj,if_neg (not_or.mpr ⟨hj,hk⟩)]
      exact safe_stay _

private theorem carry_step (pre x tail a y z l : List Bool) (j : ℕ) (hj : j < y.length) :
    subroutine.step (carryFrame pre x tail a y z l j)=carryFrame pre x tail a y z l (j+1) := by
  have hi : (carryFrame pre x tail a y z l j).cells 12
      ((carryFrame pre x tail a y z l j).head 12)=subroutine.bitSym y[j] := bits_read y j hj
  let w := x.map subroutine.bitSym++Sym.sep::(y.take j).map subroutine.bitSym
  have hl : w.length=x.length+j+1 := by simp [w,Nat.min_eq_left hj.le];omega
  have ho : (carryFrame pre x tail a y z l j).cells 2
      ((carryFrame pre x tail a y z l j).head 2)=Sym.blank := by
    change subroutine.tapeOf w (x.length+j+2)=Sym.blank
    rw [show x.length+j+2=(x.length+j+1)+1 by omega]
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulstreamcarryrequest_carry_transition (fun i => (carryFrame pre x tail a y z l j).cells i
    ((carryFrame pre x tail a y z l j).head i)) y[j] hi ho
  change transition (carryFrame pre x tail a y z l j).state
    (fun i => (carryFrame pre x tail a y z l j).cells i
      ((carryFrame pre x tail a y z l j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hk : i=2
    · subst i
      change Function.update (subroutine.tapeOf w) (x.length+j+2)
        ((carryFrame pre x tail a y z l j).cells 12 ((carryFrame pre x tail a y z l j).head 12))=
          subroutine.tapeOf (x.map subroutine.bitSym++Sym.sep::(y.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one w (subroutine.bitSym y[j])
      rw [hl,show x.length+j+1+1=x.length+j+2 by omega] at hw
      rw [List.take_succ_eq_append_getElem hj,List.map_append,List.map_singleton]
      simpa only [w,List.append_assoc,List.cons_append] using hw
    · rw [if_neg hk,Function.update_eq_self]
      simp only [carryFrame,if_neg hk]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [carryFrame,mainBase] <;> omega

private theorem carry_run (pre x tail a y z l : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    subroutine.step^[j] (carryFrame pre x tail a y z l 0)=carryFrame pre x tail a y z l j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),carry_step pre x tail a y z l j (by omega)]

private theorem carry_to_rewind (pre x tail a y z l : List Bool) :
    subroutine.step (carryFrame pre x tail a y z l y.length)=
      rewindFrame pre x tail a y z l (x.length+y.length+1) := by
  let c := carryFrame pre x tail a y z l y.length
  let s : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have hi : s 12=Sym.blank := bits_blank y
  have ho : s 2≠Sym.start := by
    change subroutine.tapeOf (x.map subroutine.bitSym++Sym.sep::(y.take y.length).map subroutine.bitSym)
      (x.length+y.length+2)≠Sym.start
    simpa only [List.take_length] using input_not_start x y (x.length+y.length+1)
  have ht : transition (relayState .copyCarry) s=(relayState .rewindRequest,
      fun i => (s i,if i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    by_cases hj : i=2
    · simp only [hj,if_true]
      exact safe_left _ ho
    · simp only [if_neg hj]
      exact safe_stay _
  change transition (carryFrame pre x tail a y z l y.length).state
    (fun i => (carryFrame pre x tail a y z l y.length).cells i
      ((carryFrame pre x tail a y z l y.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [c,carryFrame,rewindFrame,arithmeticInitial,mainView,mainBase,
      initialFrame,PaddedCarryStep.initialFrame,CarryStep.initialFrame] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,carryFrame,rewindFrame,arithmeticInitial,mainView,mainBase,
      initialFrame,PaddedCarryStep.initialFrame,CarryStep.initialFrame] <;> omega

end IntMul.StreamCarryStep



namespace IntMul.StreamCarryStep

open TapeCopy (Sym)
open TapeAdder (safe_stay)

private theorem rewind_step (pre x tail a y z l : List Bool) (j : ℕ) :
    subroutine.step (rewindFrame pre x tail a y z l (j+1))=rewindFrame pre x tail a y z l j := by
  let s : Fin 15 → Sym := fun i => (rewindFrame pre x tail a y z l (j+1)).cells i
    ((rewindFrame pre x tail a y z l (j+1)).head i)
  have ho : s 2≠Sym.start := by
    change subroutine.tapeOf (x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym) (j+1)≠Sym.start
    exact input_not_start x y j
  have ht : transition (relayState .rewindRequest) s=(relayState .rewindRequest,
      fun i => (s i,if i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    rw [if_neg ho]
    congr 1
    funext i
    by_cases hi : i=2
    · simp only [hi,if_true]
      exact safe_left _ ho
    · simp only [if_neg hi]
      exact safe_stay _
  change transition (rewindFrame pre x tail a y z l (j+1)).state
    (fun i => (rewindFrame pre x tail a y z l (j+1)).cells i ((rewindFrame pre x tail a y z l (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame]

private theorem rewind_run (pre x tail a y z l : List Bool) (j : ℕ) :
    subroutine.step^[j] (rewindFrame pre x tail a y z l j)=rewindFrame pre x tail a y z l 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem rewind_halt_step (pre x tail a y z l : List Bool) :
    subroutine.step (rewindFrame pre x tail a y z l 0)=prepareFinal pre x tail a y z l := by
  let s : Fin 15 → Sym := fun i => (rewindFrame pre x tail a y z l 0).cells i ((rewindFrame pre x tail a y z l 0).head i)
  have ho : s 2=Sym.start := rfl
  have ht : transition (relayState .rewindRequest) s=(none,fun i => (s i,Move.stay)) := by
    simp [transition,rawTransition,relayState,relayRaw,ho,safe_stay]
  change transition (rewindFrame pre x tail a y z l 0).state
    (fun i => (rewindFrame pre x tail a y z l 0).cells i ((rewindFrame pre x tail a y z l 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame,prepareFinal,arithmeticInitial,mainView,PaddedCarryStep.initialFrame]

private theorem rewind_complete (pre x tail a y z l : List Bool) (j : ℕ) :
    subroutine.step^[j+1] (rewindFrame pre x tail a y z l j)=prepareFinal pre x tail a y z l := by
  rw [Function.iterate_succ_apply',rewind_run,rewind_halt_step]


private theorem prepare_complete (pre x tail a y z l : List Bool) (h : x.length=y.length) :
    subroutine.step^[3*x.length+4] (openCarryFrame pre x tail a y z l)=
      prepareFinal pre x tail a y z l := by
  have h₁ : subroutine.step^[y.length+1] (openCarryFrame pre x tail a y z l)=
      carryFrame pre x tail a y z l y.length := by
    rw [Function.iterate_succ_apply,open_carry_step,carry_run pre x tail a y z l y.length le_rfl]
  have h₂ : subroutine.step^[x.length+y.length+3] (carryFrame pre x tail a y z l y.length)=
      prepareFinal pre x tail a y z l := by
    rw [show x.length+y.length+3=(x.length+y.length+1+1)+1 by omega,
      Function.iterate_succ_apply,carry_to_rewind,rewind_complete]
  rw [show 3*x.length+4=(x.length+y.length+3)+(y.length+1) by omega,
    Function.iterate_add_apply,h₁,h₂]

private theorem after_prepare (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .read .prepare dispatch (prepareFinal pre x tail a y z l)=
      FiniteCaller.embed subroutine Phase .read .arithmetic dispatch (arithmeticInitial pre x tail a y z l) := by
  apply cfg_ext
  · rfl
  · rfl
  · rfl

end IntMul.StreamCarryStep



namespace IntMul.StreamCarryStep
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem seek_step (pre x tail a y z l : List Bool) (j : ℕ) :
    subroutine.step (seekFrame pre x tail a y z l (j+1))=seekFrame pre x tail a y z l j := by
  let s : Fin 15 → Sym := fun i => (seekFrame pre x tail a y z l (j+1)).cells i
    ((seekFrame pre x tail a y z l (j+1)).head i)
  have ho : s 3≠Sym.start := by
    change subroutine.tapeOf ((CarryStep.digitWord x y z).map subroutine.bitSym) (j+1)≠Sym.start
    apply tape_not_start
    intro b hb
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
    exact bit_not_start v
  have ht : transition (relayState .seekDigitStart) s=(relayState .seekDigitStart,
      fun i => (s i,if i=3 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,if_neg ho]
    congr 1
    funext i
    by_cases hi : i=3
    · simp only [hi,if_true]
      exact safe_left _ ho
    · simp only [if_neg hi]
      exact safe_stay _
  change transition (seekFrame pre x tail a y z l (j+1)).state
    (fun i => (seekFrame pre x tail a y z l (j+1)).cells i
      ((seekFrame pre x tail a y z l (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame]

private theorem seek_run (pre x tail a y z l : List Bool) (j : ℕ) :
    subroutine.step^[j] (seekFrame pre x tail a y z l j)=seekFrame pre x tail a y z l 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,seek_step,ih]

private theorem seek_open_step (pre x tail a y z l : List Bool) :
    subroutine.step (seekFrame pre x tail a y z l 0)=outputFrame pre x tail a y z l 0 := by
  let s : Fin 15 → Sym := fun i => (seekFrame pre x tail a y z l 0).cells i
    ((seekFrame pre x tail a y z l 0).head i)
  have ho : s 3=Sym.start := rfl
  have ht : transition (relayState .seekDigitStart) s=(relayState .copyDigit,
      fun i => (s i,if i=3 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,if_pos ho]
    congr 1
    funext i
    by_cases hi : i=3
    · simp only [hi,if_true]
      exact safe_right _
    · simp only [if_neg hi]
      exact safe_stay _
  change transition (seekFrame pre x tail a y z l 0).state
    (fun i => (seekFrame pre x tail a y z l 0).cells i
      ((seekFrame pre x tail a y z l 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,outputFrame,arithmeticFinal,mainView,mainBase,initialFrame] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,outputFrame,arithmeticFinal,mainView,mainBase,initialFrame]

private theorem owned_intmulstreamcarryoutput_output_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 3=subroutine.bitSym b) (ho : s 1=Sym.blank) :
    transition (relayState .copyDigit) s=(relayState .copyDigit,
      fun i => (if i=1 then s 3 else s i,if i=1 ∨ i=3 then Move.right else Move.stay)) := by
  have hb : s 3=Sym.zero ∨ s 3=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases hj : i=1
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases hk : i=3
    · simp only [hk,if_true,if_false,or_true]
      exact safe_right _
    · simp only [if_neg hj,if_neg (not_or.mpr ⟨hj,hk⟩)]
      exact safe_stay _

private theorem output_step (pre x tail a y z l : List Bool) (j : ℕ)
    (hj : j < (CarryStep.digitWord x y z).length) :
    subroutine.step (outputFrame pre x tail a y z l j)=outputFrame pre x tail a y z l (j+1) := by
  let d := CarryStep.digitWord x y z
  have hi : (outputFrame pre x tail a y z l j).cells 3
      ((outputFrame pre x tail a y z l j).head 3)=subroutine.bitSym d[j] := bits_read d j hj
  let w := (a++d.take j).map subroutine.bitSym
  have hl : w.length=a.length+j := by simp [w,d,Nat.min_eq_left hj.le]
  have ho : (outputFrame pre x tail a y z l j).cells 1
      ((outputFrame pre x tail a y z l j).head 1)=Sym.blank := by
    change w.getD (a.length+j) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulstreamcarryoutput_output_transition (fun i => (outputFrame pre x tail a y z l j).cells i
    ((outputFrame pre x tail a y z l j).head i)) d[j] hi ho
  change transition (outputFrame pre x tail a y z l j).state
    (fun i => (outputFrame pre x tail a y z l j).cells i
      ((outputFrame pre x tail a y z l j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hk : i=1
    · subst i
      change Function.update (subroutine.tapeOf w) (a.length+j+1)
        ((outputFrame pre x tail a y z l j).cells 3 ((outputFrame pre x tail a y z l j).head 3))=
          subroutine.tapeOf ((a++d.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one w (subroutine.bitSym d[j])
      rw [hl] at hw
      rw [List.take_succ_eq_append_getElem hj,←List.append_assoc,List.map_append]
      exact hw
    · rw [if_neg hk,Function.update_eq_self]
      simp only [outputFrame,if_neg hk]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [outputFrame,Nat.add_assoc]

private theorem output_run (pre x tail a y z l : List Bool) (j : ℕ)
    (hj : j ≤ (CarryStep.digitWord x y z).length) :
    subroutine.step^[j] (outputFrame pre x tail a y z l 0)=outputFrame pre x tail a y z l j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),output_step pre x tail a y z l j (by omega)]

private theorem output_halt_step (pre x tail a y z l : List Bool) :
    subroutine.step (outputFrame pre x tail a y z l (CarryStep.digitWord x y z).length)=
      outputFinal pre x tail a y z l := by
  let d := CarryStep.digitWord x y z
  let s : Fin 15 → Sym := fun i => (outputFrame pre x tail a y z l d.length).cells i
    ((outputFrame pre x tail a y z l d.length).head i)
  have ho : s 3=Sym.blank := bits_blank d
  have ht : transition (relayState .copyDigit) s=(none,fun i => (s i,Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,ho]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    simp only [safe_stay]
  change transition (outputFrame pre x tail a y z l (CarryStep.digitWord x y z).length).state
    (fun i => (outputFrame pre x tail a y z l (CarryStep.digitWord x y z).length).cells i
      ((outputFrame pre x tail a y z l (CarryStep.digitWord x y z).length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem output_complete (pre x tail a y z l : List Bool)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    subroutine.step^[2*CarryStep.blockSize z+3]
      (seekFrame pre x tail a y z l (CarryStep.blockSize z+1))=outputFinal pre x tail a y z l := by
  have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
    simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left hB]
  have h₁ : subroutine.step^[CarryStep.blockSize z+2]
      (seekFrame pre x tail a y z l (CarryStep.blockSize z+1))=outputFrame pre x tail a y z l 0 := by
    rw [show CarryStep.blockSize z+2=CarryStep.blockSize z+1+1 by omega,
      Function.iterate_succ_apply',seek_run,seek_open_step]
  have h₂ : subroutine.step^[CarryStep.blockSize z+1] (outputFrame pre x tail a y z l 0)=
      outputFinal pre x tail a y z l := by
    rw [←hd,Function.iterate_succ_apply',output_run pre x tail a y z l _ le_rfl,output_halt_step]
  rw [show 2*CarryStep.blockSize z+3=(CarryStep.blockSize z+1)+(CarryStep.blockSize z+2) by omega,
    Function.iterate_add_apply,h₁,h₂]

private theorem after_arithmetic (pre x tail a y z l : List Bool) :
    FiniteCaller.returned subroutine Phase .read .arithmetic dispatch
      (arithmeticFinal pre x tail a y z l)=
      FiniteCaller.embed subroutine Phase .read .output dispatch
        (seekFrame pre x tail a y z l (CarryStep.blockSize z+1)) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,seekFrame,
      arithmeticFinal,mainView,PaddedCarryStep.finalFrame,CarryStep.finalFrame]

end IntMul.StreamCarryStep



namespace IntMul.StreamCarryStep

/-- One complete physical streaming coefficient/carry update. The earlier
input and output prefixes are retained without rescanning; all fifteen banks,
heads and actual phase-return transitions are included in the bound. -/
private theorem stream_carry_step (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 19*x.length+12*CarryStep.blockSize z+12*z.length+4*l.length+50 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by
  obtain ⟨u,hu,hread⟩ := read_complete pre x tail a y z l hn
  obtain ⟨a₁,ha₁,he₁⟩ := (FiniteCaller.simulate_run subroutine Phase .read .read dispatch
    (readBegin pre x tail a y z l) u).2 (by rw [hread];rfl)
  rw [hread,after_read] at he₁
  obtain ⟨a₂,ha₂,he₂⟩ := (FiniteCaller.simulate_run subroutine Phase .read .prepare dispatch
    (openCarryFrame pre x tail a y z l) (3*x.length+4)).2
      (by rw [prepare_complete pre x tail a y z l h];rfl)
  rw [prepare_complete pre x tail a y z l h,after_prepare] at he₂
  obtain ⟨v,hv,hmain,hhalt,hd,hc⟩ := PaddedCarryStep.padded_carry_step x y z h hB
  have hnative : subroutine.step^[v] (arithmeticInitial pre x tail a y z l)=
      arithmeticFinal pre x tail a y z l := by
    unfold arithmeticInitial arithmeticFinal
    rw [main_run,hmain]
  obtain ⟨a₃,ha₃,he₃⟩ := (FiniteCaller.simulate_run subroutine Phase .read .arithmetic dispatch
    (arithmeticInitial pre x tail a y z l) v).2 (by rw [hnative];rfl)
  rw [hnative,after_arithmetic] at he₃
  obtain ⟨a₄,ha₄,he₄⟩ := (FiniteCaller.simulate_run subroutine Phase .read .output dispatch
    (seekFrame pre x tail a y z l (CarryStep.blockSize z+1)) (2*CarryStep.blockSize z+3)).2
      (by rw [output_complete pre x tail a y z l hB];rfl)
  rw [output_complete pre x tail a y z l hB,output_to_final pre x tail a y z l h hB] at he₄
  have hfinal : machine.step^[a₄+(a₃+(a₂+a₁))] (initialFrame pre x tail a y z l)=
      finalFrame pre x tail a y z l := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      read_initial,he₁,he₂,he₃,he₄]
  refine ⟨a₄+(a₃+(a₂+a₁)),by omega,hfinal,?_,hd,hc⟩
  rw [hfinal]
  rfl

end IntMul.StreamCarryStep



open IntMul IntMul.StreamCarryStep

theorem solution (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 19*x.length+12*CarryStep.blockSize z+12*z.length+4*l.length+50 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) :=
  IntMul.StreamCarryStep.stream_carry_step pre x tail a y z l h hn hB

#print axioms solution
