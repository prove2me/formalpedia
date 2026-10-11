-- Prove2me | solution 1 for IntMul.InputWidthCounter.input_width_counter
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T14:50:10.581057+00:00
-- url     : https://prove2.me/submissions/31fb3016-e85b-4c79-b5c3-7cbd0be4b23d

import Definitions.Def_IntMul_InputWidthCounter
import Mathlib.Tactic
import Theorems.Thm_IntMul_GrowingCounter_increment_counter
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem counter_step (c : GrowingCounter.machine.Cfg) :
    subroutine.step (counterView c)=counterView (GrowingCounter.machine.step c) := by
  let a : Fin 3 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (counterState c.state) a=
      (counterState (GrowingCounter.machine.δ c.state a).1,(GrowingCounter.machine.δ c.state a).2) := by
    by_cases h : c.state=GrowingCounter.machine.qHalt
    · rw [h,GrowingCounter.machine.halt_fixed a];rfl
    · conv_lhs => rw [counterState,if_neg h]
      rfl
  change transition (counterView c).state
    (fun i => (counterView c).cells i ((counterView c).head i))=_ at ht
  apply cfg_ext <;> simp only [MultitapeTM.step,ht] <;> rfl

private theorem counter_run (c : GrowingCounter.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (counterView c)=counterView (GrowingCounter.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,counter_step,Function.iterate_succ_apply']

private theorem source_read (q : Reader) (pre tail : List Sym) (bits : List Bool) (a : Sym) :
    (readerFrame q pre (a::tail) bits).cells 0 ((readerFrame q pre (a::tail) bits).head 0)=a := by
  simp [readerFrame,MultitapeTM.tapeOf,List.getD_append_right]

private theorem source_nil (q : Reader) (pre : List Sym) (bits : List Bool) :
    (readerFrame q pre [] bits).cells 0 ((readerFrame q pre [] bits).head 0)=Sym.blank := by
  simp [readerFrame,MultitapeTM.tapeOf]

private theorem counter_ready (pre tail : List Sym) (bits : List Bool) (q : GrowingCounter.State) :
    (GrowingCounter.counterFrame (counterBase pre tail bits) q bits).cells=(readerFrame .scan pre tail bits).cells ∧
    (GrowingCounter.counterFrame (counterBase pre tail bits) q bits).head=(readerFrame .scan pre tail bits).head := by
  constructor <;> funext i <;> fin_cases i <;> simp [GrowingCounter.counterFrame,counterBase,readerFrame]
  all_goals rfl

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem after_counter (pre tail : List Sym) (bits : List Bool)
    (hw : ∀ a ∈ tail, a≠Sym.blank) :
    FiniteCaller.returned subroutine Unit () () dispatch
      (counterView (GrowingCounter.counterFrame (counterBase pre tail bits) .halt (GrowingCounter.increment bits)))=
    loopFrame pre tail (GrowingCounter.increment bits) := by
  apply cfg_ext
  · cases tail with
    | nil => simp [FiniteCaller.returned,dispatch,counterView,GrowingCounter.counterFrame,
        counterBase,readerFrame,loopFrame,MultitapeTM.tapeOf]
    | cons a tail =>
        have ha := hw a (by simp)
        simp [FiniteCaller.returned,dispatch,counterView,GrowingCounter.counterFrame,
          counterBase,readerFrame,loopFrame,MultitapeTM.tapeOf,ha]
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,counterView,GrowingCounter.counterFrame,
      counterBase,readerFrame,loopFrame]
    all_goals rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,counterView,GrowingCounter.counterFrame,
      counterBase,readerFrame,loopFrame]

private theorem caller_reader_transition (q : Reader) (a : Fin 3 → Sym) :
    machine.δ (some ((),readerState q)) a=
      (some ((),(transition (readerState q) a).1),(transition (readerState q) a).2) := by
  simp [FiniteCaller.transition,readerState]

private theorem scan_bit_transition (a : Fin 3 → Sym) (b : Bool) (h : a 0=subroutine.bitSym b) :
    transition (readerState .scan) a=
      (counterState .carry,fun i => (a i,if i=0 then .right else .stay)) := by
  have hb : a 0=Sym.zero ∨ a 0=Sym.one := by rw [h];cases b <;> simp [MultitapeTM.bitSym]
  simp only [readerState,transition,if_pos hb]

private theorem scan_bit_step (pre tail : List Sym) (bits : List Bool) (b : Bool) :
    machine.step (loopFrame pre (subroutine.bitSym b::tail) bits)=
      FiniteCaller.embed subroutine Unit () () dispatch
        (counterView (GrowingCounter.counterFrame (counterBase (pre++[subroutine.bitSym b]) tail bits) .carry bits)) := by
  have hs := source_read .scan pre tail bits (subroutine.bitSym b)
  change (loopFrame pre (subroutine.bitSym b::tail) bits).cells 0
    ((loopFrame pre (subroutine.bitSym b::tail) bits).head 0)=_ at hs
  have ht := caller_reader_transition .scan
    (fun i => (loopFrame pre (subroutine.bitSym b::tail) bits).cells i
      ((loopFrame pre (subroutine.bitSym b::tail) bits).head i))
  rw [scan_bit_transition _ b hs] at ht
  change machine.δ (loopFrame pre (subroutine.bitSym b::tail) bits).state
    (fun i => (loopFrame pre (subroutine.bitSym b::tail) bits).cells i
      ((loopFrame pre (subroutine.bitSym b::tail) bits).head i))=_ at ht
  change FiniteCaller.transition subroutine Unit dispatch
    (loopFrame pre (subroutine.bitSym b::tail) bits).state
    (fun i => (loopFrame pre (subroutine.bitSym b::tail) bits).cells i
      ((loopFrame pre (subroutine.bitSym b::tail) bits).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [loopFrame,readerFrame,FiniteCaller.embed,counterView,
      GrowingCounter.counterFrame,counterBase,List.append_assoc]
    all_goals rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [loopFrame,readerFrame,FiniteCaller.embed,counterView,
      GrowingCounter.counterFrame,counterBase]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem count_bit (pre tail : List Sym) (bits : List Bool) (b : Bool)
    (hw : ∀ a ∈ tail, a≠Sym.blank) :
    ∃ t : ℕ, t ≤ GrowingCounter.counterSteps bits+2 ∧
      machine.step^[t] (loopFrame pre (subroutine.bitSym b::tail) bits)=
        loopFrame (pre++[subroutine.bitSym b]) tail (GrowingCounter.increment bits) := by
  let base := counterBase (pre++[subroutine.bitSym b]) tail bits
  have ec := (GrowingCounter.increment_counter base bits).1
  have en : subroutine.step^[GrowingCounter.counterSteps bits]
      (counterView (GrowingCounter.counterFrame base .carry bits))=
      counterView (GrowingCounter.counterFrame base .halt (GrowingCounter.increment bits)) := by
    rw [counter_run,ec]
  obtain ⟨r,hr,her⟩ := (FiniteCaller.simulate_run subroutine Unit () () dispatch
    (counterView (GrowingCounter.counterFrame base .carry bits)) (GrowingCounter.counterSteps bits)).2
      (by rw [en];rfl)
  rw [en] at her
  change machine.step^[r] (FiniteCaller.embed subroutine Unit () () dispatch
    (counterView (GrowingCounter.counterFrame (counterBase (pre++[subroutine.bitSym b]) tail bits) .carry bits)))=_ at her
  rw [after_counter (pre++[subroutine.bitSym b]) tail bits hw] at her
  refine ⟨r+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,scan_bit_step,her]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private def emptyBoundaryFrame (pre : List Sym) (bits : List Bool) : machine.Cfg where
  state := some ((),none)
  cells := (readerFrame .scan pre [] bits).cells
  head := (readerFrame .scan pre [] bits).head

private theorem reader_blank_transition (q : Reader) (hq : q=.first ∨ q=.scan)
    (a : Fin 3 → Sym) (h : a 0=Sym.blank) :
    transition (readerState q) a=(none,fun i => (a i,.stay)) := by
  rcases hq with hq|hq <;> subst q <;> simp [readerState,transition,h]

private theorem reader_blank_step (q : Reader) (hq : q=.first ∨ q=.scan) (pre : List Sym) (bits : List Bool) :
    machine.step (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre [] bits))=
      emptyBoundaryFrame pre bits := by
  have hs := source_nil q pre bits
  have ht := caller_reader_transition q (fun i => (readerFrame q pre [] bits).cells i ((readerFrame q pre [] bits).head i))
  rw [reader_blank_transition q hq _ hs] at ht
  change FiniteCaller.transition subroutine Unit dispatch
    (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre [] bits)).state
    (fun i => (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre [] bits)).cells i
      ((FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre [] bits)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [FiniteCaller.embed]
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem boundary_blank_step (pre : List Sym) (bits : List Bool) :
    machine.step (emptyBoundaryFrame pre bits)=loopFrame pre [] bits := by
  have hs := source_nil .scan pre bits
  have ht : FiniteCaller.transition subroutine Unit dispatch (emptyBoundaryFrame pre bits).state
      (fun i => (emptyBoundaryFrame pre bits).cells i ((emptyBoundaryFrame pre bits).head i))=
      (none,fun i => ((emptyBoundaryFrame pre bits).cells i ((emptyBoundaryFrame pre bits).head i),.stay)) := by
    simp [emptyBoundaryFrame,FiniteCaller.transition,subroutine,dispatch,hs]
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem reader_blank_run (q : Reader) (hq : q=.first ∨ q=.scan) (pre : List Sym) (bits : List Bool) :
    machine.step^[2] (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre [] bits))=
      loopFrame pre [] bits := by
  rw [show 2=1+1 by rfl,Function.iterate_succ_apply,Function.iterate_one,
    reader_blank_step q hq,boundary_blank_step]

private theorem reader_sep_transition (q : Reader) (hq : q=.first ∨ q=.scan)
    (a : Fin 3 → Sym) (h : a 0=Sym.sep) :
    transition (readerState q) a=(readerState q,fun i => (a i,if i=0 then .right else .stay)) := by
  rcases hq with hq|hq <;> subst q <;> simp [readerState,transition,h]

private theorem reader_sep_step (q : Reader) (hq : q=.first ∨ q=.scan)
    (pre tail : List Sym) (bits : List Bool) :
    machine.step (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre (Sym.sep::tail) bits))=
      FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q (pre++[Sym.sep]) tail bits) := by
  have hs := source_read q pre tail bits Sym.sep
  have ht := caller_reader_transition q (fun i => (readerFrame q pre (Sym.sep::tail) bits).cells i ((readerFrame q pre (Sym.sep::tail) bits).head i))
  rw [reader_sep_transition q hq _ hs] at ht
  change FiniteCaller.transition subroutine Unit dispatch
    (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre (Sym.sep::tail) bits)).state
    (fun i => (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre (Sym.sep::tail) bits)).cells i
      ((FiniteCaller.embed subroutine Unit () () dispatch (readerFrame q pre (Sym.sep::tail) bits)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [FiniteCaller.embed]
    rw [Function.update_eq_self]
    simp [FiniteCaller.embed,readerFrame,List.append_assoc]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [FiniteCaller.embed,readerFrame]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem loop_nonempty (pre tail : List Sym) (bits : List Bool) (h : tail≠[]) :
    FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan pre tail bits)=loopFrame pre tail bits := by
  apply cfg_ext
  · simp [FiniteCaller.embed,loopFrame,readerFrame,h]
  · rfl
  · rfl

private theorem scan_separator (pre tail : List Sym) (bits : List Bool) :
    ∃ t : ℕ, t ≤ 3 ∧ machine.step^[t] (loopFrame pre (Sym.sep::tail) bits)=
      loopFrame (pre++[Sym.sep]) tail bits := by
  cases tail with
  | nil =>
      refine ⟨3,le_refl _,?_⟩
      change machine.step^[3] (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan pre [Sym.sep] bits))=_
      rw [show 3=2+1 by rfl,Function.iterate_succ_apply,reader_sep_step .scan (Or.inr rfl),reader_blank_run .scan (Or.inr rfl)]
  | cons a tail =>
      refine ⟨1,by omega,?_⟩
      rw [Function.iterate_one]
      change machine.step (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan pre (Sym.sep::a::tail) bits))=_
      rw [reader_sep_step .scan (Or.inr rfl),loop_nonempty _ _ _ (by simp)]

private theorem loop_run (pre tail : List Sym) (bits : List Bool)
    (hw : ∀ a ∈ tail, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep) :
    ∃ t : ℕ, t ≤ 2*tail.length+2+GrowingCounter.totalCounterSteps (bitCount tail) bits ∧
      machine.step^[t] (loopFrame pre tail bits)=
        loopFrame (pre++tail) [] (GrowingCounter.iterateCounter (bitCount tail) bits) := by
  induction tail generalizing pre bits with
  | nil =>
      refine ⟨0,by simp [GrowingCounter.totalCounterSteps],?_⟩
      simp [GrowingCounter.iterateCounter,bitCount]
  | cons a tail ih =>
      have hwt : ∀ a ∈ tail, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep := by intro a ha;exact hw a (by simp [ha])
      have hbn : ∀ a ∈ tail, a≠Sym.blank := by
        intro a ha
        rcases hwt a ha with h|h|h <;> subst a <;> decide
      rcases hw a (by simp) with ha|ha|ha
      · subst a
        obtain ⟨r,hr,her⟩ := count_bit pre tail bits false hbn
        change machine.step^[r] (loopFrame pre (Sym.zero::tail) bits)=loopFrame (pre++[Sym.zero]) tail (GrowingCounter.increment bits) at her
        obtain ⟨s,hs,hes⟩ := ih (pre++[Sym.zero]) (GrowingCounter.increment bits) hwt
        have hb : bitCount (Sym.zero::tail)=bitCount tail+1 := by simp [bitCount,Nat.add_comm]
        refine ⟨s+r,?_,?_⟩
        · rw [hb,List.length_cons,GrowingCounter.totalCounterSteps]
          omega
        · rw [Function.iterate_add_apply,her,hes]
          simp only [hb,GrowingCounter.iterateCounter,List.append_assoc,List.singleton_append]
      · subst a
        obtain ⟨r,hr,her⟩ := count_bit pre tail bits true hbn
        change machine.step^[r] (loopFrame pre (Sym.one::tail) bits)=loopFrame (pre++[Sym.one]) tail (GrowingCounter.increment bits) at her
        obtain ⟨s,hs,hes⟩ := ih (pre++[Sym.one]) (GrowingCounter.increment bits) hwt
        have hb : bitCount (Sym.one::tail)=bitCount tail+1 := by simp [bitCount,Nat.add_comm]
        refine ⟨s+r,?_,?_⟩
        · rw [hb,List.length_cons,GrowingCounter.totalCounterSteps]
          omega
        · rw [Function.iterate_add_apply,her,hes]
          simp only [hb,GrowingCounter.iterateCounter,List.append_assoc,List.singleton_append]
      · subst a
        obtain ⟨r,hr,her⟩ := scan_separator pre tail bits
        obtain ⟨s,hs,hes⟩ := ih (pre++[Sym.sep]) bits hwt
        cases tail with
        | nil =>
            refine ⟨r,?_,?_⟩
            · simp [bitCount,GrowingCounter.totalCounterSteps];omega
            · simpa [bitCount,GrowingCounter.iterateCounter] using her
        | cons a tail =>
            have hr1 : ∃ r : ℕ, r ≤ 1 ∧ machine.step^[r] (loopFrame pre (Sym.sep::a::tail) bits)=
                loopFrame (pre++[Sym.sep]) (a::tail) bits := by
              refine ⟨1,le_refl _,?_⟩
              rw [Function.iterate_one]
              change machine.step (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan pre (Sym.sep::a::tail) bits))=_
              rw [reader_sep_step .scan (Or.inr rfl),loop_nonempty _ _ _ (by simp)]
            obtain ⟨r,hr,her⟩ := hr1
            refine ⟨s+r,?_,?_⟩
            · have hb : bitCount (Sym.sep::a::tail)=bitCount (a::tail) := by simp [bitCount]
              rw [hb,List.length_cons]
              omega
            · rw [Function.iterate_add_apply,her,hes]
              simp [bitCount,List.append_assoc]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem first_bit_transition (a : Fin 3 → Sym) (b : Bool) (h : a 0=subroutine.bitSym b) :
    transition (readerState .first) a=(readerState .scan,fun i => (a i,if i=0 then .right else .stay)) := by
  have hb : a 0=Sym.zero ∨ a 0=Sym.one := by rw [h];cases b <;> simp [MultitapeTM.bitSym]
  simp only [readerState,transition,if_pos hb]

private theorem first_bit_step (pre tail : List Sym) (bits : List Bool) (b : Bool) :
    machine.step (FiniteCaller.embed subroutine Unit () () dispatch
      (readerFrame .first pre (subroutine.bitSym b::tail) bits))=
      FiniteCaller.embed subroutine Unit () () dispatch
        (readerFrame .scan (pre++[subroutine.bitSym b]) tail bits) := by
  have hs := source_read .first pre tail bits (subroutine.bitSym b)
  have ht := caller_reader_transition .first
    (fun i => (readerFrame .first pre (subroutine.bitSym b::tail) bits).cells i
      ((readerFrame .first pre (subroutine.bitSym b::tail) bits).head i))
  rw [first_bit_transition _ b hs] at ht
  change FiniteCaller.transition subroutine Unit dispatch
    (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .first pre (subroutine.bitSym b::tail) bits)).state
    (fun i => (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .first pre (subroutine.bitSym b::tail) bits)).cells i
      ((FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .first pre (subroutine.bitSym b::tail) bits)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [FiniteCaller.embed]
    rw [Function.update_eq_self]
    simp [readerFrame,List.append_assoc]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [FiniteCaller.embed,readerFrame]

private theorem opening_step (x y : List Bool) :
    machine.step (initialFrame x y)=FiniteCaller.embed subroutine Unit () () dispatch
      (readerFrame .first [] (x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym) []) := by
  have ht : FiniteCaller.transition subroutine Unit dispatch (initialFrame x y).state
      (fun i => (initialFrame x y).cells i ((initialFrame x y).head i))=
      (some ((),readerState .first),fun i => ((initialFrame x y).cells i ((initialFrame x y).head i),
        if i=0 ∨ i=2 then .right else .stay)) := by
    simp [FiniteCaller.transition,initialFrame,MultitapeTM.initCfg,readerState,transition]
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape,readerFrame,FiniteCaller.embed]
    all_goals rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [initialFrame,MultitapeTM.initCfg,readerFrame,FiniteCaller.embed]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem bitCount_append (u v : List Sym) : bitCount (u++v)=bitCount u+bitCount v := by
  induction u with
  | nil => simp [bitCount]
  | cons a u ih => simp only [List.cons_append,bitCount,ih];omega

private theorem bitCount_bits (x : List Bool) : bitCount (x.map subroutine.bitSym)=x.length := by
  induction x with
  | nil => simp [bitCount]
  | cons b x ih => cases b <;> simp [List.map_cons,MultitapeTM.bitSym,bitCount,ih,Nat.add_comm]

private theorem bits_valid (x : List Bool) :
    ∀ a ∈ x.map subroutine.bitSym, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  cases b <;> simp [MultitapeTM.bitSym]

private theorem zero_counter_facts (n : ℕ) :
    GrowingCounter.totalCounterSteps n [] ≤ 4*n ∧
    BinaryAdder.littleVal (GrowingCounter.iterateCounter n [])=n := by
  obtain ⟨_,_,_,_,_,_,_,_,_,h⟩ := GrowingCounter.increment_counter (counterBase [] [] []) []
  simpa [GrowingCounter.potential,BinaryAdder.littleVal] using h n

private theorem scan_run (pre tail : List Sym) (bits : List Bool)
    (hw : ∀ a ∈ tail, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep) :
    ∃ t : ℕ, t ≤ 2*tail.length+2+GrowingCounter.totalCounterSteps (bitCount tail) bits ∧
      machine.step^[t] (FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan pre tail bits))=
        loopFrame (pre++tail) [] (GrowingCounter.iterateCounter (bitCount tail) bits) := by
  cases tail with
  | nil =>
      refine ⟨2,by simp [bitCount,GrowingCounter.totalCounterSteps],?_⟩
      simpa [bitCount,GrowingCounter.iterateCounter] using reader_blank_run .scan (Or.inr rfl) pre bits
  | cons a tail =>
      obtain ⟨t,ht,he⟩ := loop_run pre (a::tail) bits hw
      refine ⟨t,ht,?_⟩
      rw [loop_nonempty _ _ _ (by simp),he]

private theorem final_ready (x y : List Bool) (pre tail : List Sym)
    (hr : pre++tail=x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym)
    (hn : bitCount tail=x.length+y.length-1) :
    loopFrame (pre++tail) [] (GrowingCounter.iterateCounter (bitCount tail) [])=finalFrame x y := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [loopFrame,readerFrame,finalFrame,hr,hn]
    all_goals rfl
  · funext i
    fin_cases i <;> simp [loopFrame,readerFrame,finalFrame,hr,Nat.add_assoc]

end IntMul.InputWidthCounter



namespace IntMul.InputWidthCounter
open TapeCopy (Sym)

private theorem width_execution (x y : List Bool) (hp : 0 < x.length+y.length) :
    ∃ t : ℕ, t ≤ 6*(x.length+y.length)+4 ∧ machine.step^[t] (initialFrame x y)=finalFrame x y := by
  cases x with
  | cons b x =>
      let tail := x.map subroutine.bitSym++Sym.sep::y.map subroutine.bitSym
      have hw : ∀ a ∈ tail, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep := by
        intro a ha
        rcases List.mem_append.mp ha with ha|ha
        · exact bits_valid x a ha
        · rcases List.mem_cons.mp ha with rfl|ha
          · simp
          · exact bits_valid y a ha
      have hn : bitCount tail=x.length+y.length := by
        simp [tail,bitCount_append,bitCount_bits,bitCount]
      obtain ⟨r,hr,her⟩ := scan_run [subroutine.bitSym b] tail [] hw
      have hs : machine.step^[2] (initialFrame (b::x) y)=
          FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan [subroutine.bitSym b] tail []) := by
        rw [show 2=1+1 by rfl,Function.iterate_succ_apply,Function.iterate_one,opening_step]
        simp only [List.map_cons,List.cons_append]
        rw [first_bit_step]
        rfl
      have hf : loopFrame ([subroutine.bitSym b]++tail) []
          (GrowingCounter.iterateCounter (bitCount tail) [])=finalFrame (b::x) y :=
        final_ready (b::x) y [subroutine.bitSym b] tail (by simp [tail]) (by rw [hn];simp)
      refine ⟨r+2,?_,?_⟩
      · have hc := (zero_counter_facts (bitCount tail)).1
        simp only [hn] at hc hr
        simp only [tail,List.length_append,List.length_map,List.length_cons] at hr
        simp only [List.length_cons]
        omega
      · rw [Function.iterate_add_apply,hs,her,hf]
  | nil =>
      cases y with
      | nil => simp at hp
      | cons b y =>
          let tail := y.map subroutine.bitSym
          have hw : ∀ a ∈ tail, a=Sym.zero ∨ a=Sym.one ∨ a=Sym.sep := bits_valid y
          have hn : bitCount tail=y.length := bitCount_bits y
          obtain ⟨r,hr,her⟩ := scan_run [Sym.sep,subroutine.bitSym b] tail [] hw
          have hs : machine.step^[3] (initialFrame [] (b::y))=
              FiniteCaller.embed subroutine Unit () () dispatch (readerFrame .scan [Sym.sep,subroutine.bitSym b] tail []) := by
            rw [show 3=2+1 by rfl,Function.iterate_succ_apply,opening_step]
            simp only [List.map_nil,List.nil_append,List.map_cons]
            rw [show 2=1+1 by rfl,Function.iterate_succ_apply,Function.iterate_one,
              reader_sep_step .first (Or.inl rfl),first_bit_step]
            rfl
          have hf : loopFrame ([Sym.sep,subroutine.bitSym b]++tail) []
              (GrowingCounter.iterateCounter (bitCount tail) [])=finalFrame [] (b::y) :=
            final_ready [] (b::y) [Sym.sep,subroutine.bitSym b] tail (by simp [tail]) (by rw [hn];simp)
          refine ⟨r+3,?_,?_⟩
          · have hc := (zero_counter_facts (bitCount tail)).1
            simp only [hn] at hc hr
            simp only [tail,List.length_map] at hr
            simp only [List.length_nil,List.length_cons,Nat.zero_add]
            omega
          · rw [Function.iterate_add_apply,hs,her,hf]

/-- Construct the width-minus-one descriptor directly from the original
binary input, with no supplied descriptor or width and a linear real clock. -/
private theorem input_width_counter (x y : List Bool) (hp : 0 < x.length+y.length) :
    ∃ t : ℕ, t ≤ 6*(x.length+y.length)+4 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (GrowingCounter.iterateCounter (x.length+y.length-1) [])+1=x.length+y.length := by
  obtain ⟨t,ht,he⟩ := width_execution x y hp
  refine ⟨t,ht,he,?_,?_,?_,?_⟩
  · rw [he];rfl
  · rw [he]
    simp [finalFrame,initialFrame,MultitapeTM.initCfg,MultitapeTM.inTape]
  · rw [he];simp [finalFrame,MultitapeTM.outTape]
  · rw [(zero_counter_facts (x.length+y.length-1)).2]
    omega

end IntMul.InputWidthCounter



open IntMul IntMul.InputWidthCounter

theorem solution (x y : List Bool) (hp : 0 < x.length+y.length) :
    ∃ t : ℕ, t ≤ 6*(x.length+y.length)+4 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (GrowingCounter.iterateCounter (x.length+y.length-1) [])+1=x.length+y.length :=
  IntMul.InputWidthCounter.input_width_counter x y hp

#print axioms solution
