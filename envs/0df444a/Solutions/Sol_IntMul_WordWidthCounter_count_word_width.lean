-- Prove2me | solution 1 for IntMul.WordWidthCounter.count_word_width
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T15:15:04.425315+00:00
-- url     : https://prove2.me/submissions/c1cca4dc-a275-4384-a2c4-fef84541f072

import Definitions.Def_IntMul_InputWidthCounter
import Mathlib.Tactic
import Theorems.Thm_IntMul_GrowingCounter_increment_counter
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Definitions.Def_IntMul_WordWidthCounter
import Theorems.Thm_IntMul_GrowingCounter_counter_width_logarithmic

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



namespace IntMul.WordWidthCounter
open TapeCopy (Sym)
open IntMul.InputWidthCounter

private theorem owned_intmulwordwidthcounterprimary_opening_word (w : List Bool) :
    machine.step (initialFrame w)=FiniteCaller.embed subroutine Unit () () dispatch
      (readerFrame .first [] (w.map subroutine.bitSym) []) := by
  have ht : FiniteCaller.transition subroutine Unit dispatch (initialFrame w).state
      (fun i => (initialFrame w).cells i ((initialFrame w).head i))=
      (some ((),readerState .first),fun i => ((initialFrame w).cells i ((initialFrame w).head i),
        if i=0 ∨ i=2 then .right else .stay)) := by
    simp [FiniteCaller.transition,initialFrame,readerState,transition]
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [initialFrame,readerFrame,FiniteCaller.embed] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [initialFrame,readerFrame,FiniteCaller.embed]

private theorem owned_intmulwordwidthcounterprimary_word_final (w : List Bool) :
    loopFrame (w.map subroutine.bitSym) [] (counterWord w)=finalFrame w := by
  apply cfg_ext
  · rfl
  · funext i;fin_cases i <;> simp [loopFrame,readerFrame,finalFrame,counterWord] <;> rfl
  · funext i;fin_cases i <;> simp [loopFrame,readerFrame,finalFrame]

private theorem owned_intmulwordwidthcounterprimary_word_execution (w : List Bool) :
    ∃ t : ℕ, t≤ 6*w.length+4 ∧ machine.step^[t] (initialFrame w)=finalFrame w := by
  cases w with
  | nil =>
      refine ⟨3,by simp,?_⟩
      rw [show 3=2+1 by rfl,Function.iterate_add_apply,Function.iterate_one,owned_intmulwordwidthcounterprimary_opening_word]
      simp only [List.map_nil]
      rw [reader_blank_run .first (Or.inl rfl)]
      exact owned_intmulwordwidthcounterprimary_word_final []
  | cons b w =>
      obtain ⟨r,hr,her⟩ := scan_run [subroutine.bitSym b] (w.map subroutine.bitSym) [] (bits_valid w)
      have hn : bitCount (w.map subroutine.bitSym)=w.length := bitCount_bits w
      have hs : machine.step^[2] (initialFrame (b::w))=
          FiniteCaller.embed subroutine Unit () () dispatch
            (readerFrame .scan [subroutine.bitSym b] (w.map subroutine.bitSym) []) := by
        rw [show 2=1+1 by rfl,Function.iterate_succ_apply,Function.iterate_one,owned_intmulwordwidthcounterprimary_opening_word]
        simp only [List.map_cons]
        rw [first_bit_step]
        rfl
      have hf : loopFrame ([subroutine.bitSym b]++w.map subroutine.bitSym) []
          (GrowingCounter.iterateCounter (bitCount (w.map subroutine.bitSym)) [])=finalFrame (b::w) := by
        rw [hn]
        exact owned_intmulwordwidthcounterprimary_word_final (b::w)
      refine ⟨r+2,?_,?_⟩
      · have hc := (zero_counter_facts w.length).1
        simp only [hn,List.length_map] at hr
        simp only [List.length_cons]
        omega
      · rw [Function.iterate_add_apply,hs,her,hf]

/-- Count the length of an actual framed bit word, including the empty word,
without supplying a numerical length to the transition table. -/
private theorem count_word_width (w : List Bool) :
    ∃ t : ℕ, t≤ 6*w.length+4 ∧
      machine.step^[t] (initialFrame w)=finalFrame w ∧
      (machine.step^[t] (initialFrame w)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame w)).cells machine.inTape=(initialFrame w).cells machine.inTape ∧
      (machine.step^[t] (initialFrame w)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (counterWord w)+1=max w.length 1 ∧
      (counterWord w).length=Nat.clog 2 (max w.length 1) := by
  obtain ⟨t,ht,he⟩ := owned_intmulwordwidthcounterprimary_word_execution w
  have hn : w.length-1+1=max w.length 1 := by omega
  obtain ⟨hl,hv,hnil⟩ := GrowingCounter.counter_width_logarithmic (w.length-1)
  refine ⟨t,ht,he,?_,?_,?_,?_,?_⟩
  · rw [he];rfl
  · rw [he];simp [finalFrame,initialFrame,MultitapeTM.inTape]
  · rw [he];simp [finalFrame,MultitapeTM.outTape]
  · change BinaryAdder.littleVal (GrowingCounter.iterateCounter (w.length-1) [])+1=_
    rw [hv,hn]
  · change (GrowingCounter.iterateCounter (w.length-1) []).length=_
    rw [hl,hn]

end IntMul.WordWidthCounter


open IntMul IntMul.WordWidthCounter

theorem solution (w : List Bool) :
    ∃ t : ℕ, t≤ 6*w.length+4 ∧
      machine.step^[t] (initialFrame w)=finalFrame w ∧
      (machine.step^[t] (initialFrame w)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame w)).cells machine.inTape=(initialFrame w).cells machine.inTape ∧
      (machine.step^[t] (initialFrame w)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (counterWord w)+1=max w.length 1 ∧
      (counterWord w).length=Nat.clog 2 (max w.length 1) :=
  IntMul.WordWidthCounter.count_word_width w

#print axioms solution
