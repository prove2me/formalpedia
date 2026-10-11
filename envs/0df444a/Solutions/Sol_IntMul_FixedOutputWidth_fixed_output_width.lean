-- Prove2me | solution 1 for IntMul.FixedOutputWidth.fixed_output_width
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T13:36:55.502552+00:00
-- url     : https://prove2.me/submissions/d6c354be-2bb7-47ed-a9ba-b9631f8d6e89

import Definitions.Def_IntMul_FixedOutputWidth
import Mathlib.Tactic
import Theorems.Thm_IntMul_TapeBankErase_erase_bank
import Theorems.Thm_IntMul_PrefixRead_read_prefix
import Theorems.Thm_IntMul_CanonicalOutput_canonical_output
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fin.Tuple.Take

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private abbrev eraseMachine (i : Fin 2) : MultitapeTM :=
  TapeBankErase.machine 13 (eraseBank i) (eraseBank_writable i)

private noncomputable def eraseView (i : Fin 2) (c : (eraseMachine i).Cfg) : subroutine.Cfg where
  state := eraseState i c.state
  cells := c.cells
  head := c.head

private theorem erase_step (i : Fin 2) (c : (eraseMachine i).Cfg) :
    subroutine.step (eraseView i c)=eraseView i ((eraseMachine i).step c) := by
  let a : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (eraseState i c.state) a=
      (eraseState i ((eraseMachine i).δ c.state a).1,((eraseMachine i).δ c.state a).2) := by
    by_cases h : c.state=(eraseMachine i).qHalt
    · rw [h,(eraseMachine i).halt_fixed a]
      simp only [eraseState,if_true,transition,rawTransition,safe_stay]
    · simp only [eraseState,if_neg h,transition,rawTransition]
      congr 1
      funext j
      apply safe_identity
      · exact (eraseMachine i).start_preserved c.state a j
      · exact (eraseMachine i).start_only_at_start c.state a j
  change transition (eraseView i c).state
    (fun j => (eraseView i c).cells j ((eraseView i c).head j))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem erase_run (i : Fin 2) (c : (eraseMachine i).Cfg) (t : ℕ) :
    subroutine.step^[t] (eraseView i c)=eraseView i ((eraseMachine i).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,erase_step,Function.iterate_succ_apply']

private noncomputable def canonicalView  (c : (CanonicalOutput.machine).Cfg) : subroutine.Cfg where
  state := canonicalState c.state
  cells := c.cells
  head := c.head

private theorem canonical_step  (c : (CanonicalOutput.machine).Cfg) :
    subroutine.step (canonicalView c)=canonicalView ((CanonicalOutput.machine).step c) := by
  let a : Fin 15 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (canonicalState c.state) a=
      (canonicalState ((CanonicalOutput.machine).δ c.state a).1,((CanonicalOutput.machine).δ c.state a).2) := by
    by_cases h : c.state=(CanonicalOutput.machine).qHalt
    · rw [h,(CanonicalOutput.machine).halt_fixed a]
      change ((none : State),fun j => safeStep (a j) (a j) .stay)=(none,fun j => (a j,.stay))
      congr 1
      funext j
      exact safe_stay _
    · conv_lhs => rw [canonicalState,if_neg h]
      change (canonicalState ((CanonicalOutput.machine).δ c.state a).1,
        fun j => safeStep (a j) (((CanonicalOutput.machine).δ c.state a).2 j).1
          (((CanonicalOutput.machine).δ c.state a).2 j).2)=_
      congr 1
      funext j
      apply safe_identity
      · exact (CanonicalOutput.machine).start_preserved c.state a j
      · exact (CanonicalOutput.machine).start_only_at_start c.state a j
  change transition (canonicalView c).state
    (fun j => (canonicalView c).cells j ((canonicalView c).head j))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem canonical_run  (c : (CanonicalOutput.machine).Cfg) (t : ℕ) :
    subroutine.step^[t] (canonicalView c)=canonicalView ((CanonicalOutput.machine).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,canonical_step,Function.iterate_succ_apply']


private theorem raw_relay (q : Relay) (a : Fin 15 → Sym) : rawTransition (relayState q) a=relayRaw q a := rfl

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)

private noncomputable def eraseBegin (i : Fin 2) (base : subroutine.Cfg) : subroutine.Cfg :=
  {base with state := eraseState i .rewind}

private noncomputable def eraseDone (i : Fin 2) (base : subroutine.Cfg) : subroutine.Cfg where
  state := none
  cells := Function.update base.cells (eraseBank i) (subroutine.tapeOf [])
  head := Function.update base.head (eraseBank i) 0

/-- Literal selected-bank erasure preserves the entire surrounding frame. -/
private theorem erase_complete (i : Fin 2) (base : subroutine.Cfg) (w : List Sym)
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

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth
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


end IntMul.FixedOutputWidth


namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulfixedoutputwidthread_safe_read (q : CountedStream.State) (a : Fin 4 → Sym) (j : Fin 4) :
    safeStep (a j) ((CountedStream.machine.δ q a).2 j).1 ((CountedStream.machine.δ q a).2 j).2=
      (CountedStream.machine.δ q a).2 j := by
  apply safe_identity
  · exact CountedStream.machine.start_preserved q a j
  · exact CountedStream.machine.start_only_at_start q a j

private noncomputable def readView (base : subroutine.Cfg) (c : CountedStream.machine.Cfg) : subroutine.Cfg where
  state := readState c.state
  cells := fun i => if i=1 then c.cells 0 else if i=2 then c.cells 1
    else if i=3 then c.cells 2 else if i=4 then c.cells 3 else base.cells i
  head := fun i => if i=1 then c.head 0 else if i=2 then c.head 1
    else if i=3 then c.head 2 else if i=4 then c.head 3 else base.head i

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
    · conv_lhs => rw [readState,if_neg h]
      change (readState (CountedStream.machine.δ c.state (fun j => a (readTape j))).1,
        fun i => safeStep (a i) (readAction a (CountedStream.machine.δ c.state (fun j => a (readTape j))).2 i).1
          (readAction a (CountedStream.machine.δ c.state (fun j => a (readTape j))).2 i).2)=_
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_stay _
      · exact owned_intmulfixedoutputwidthread_safe_read c.state b 0
      · exact owned_intmulfixedoutputwidthread_safe_read c.state b 1
      · exact owned_intmulfixedoutputwidthread_safe_read c.state b 2
      · exact owned_intmulfixedoutputwidthread_safe_read c.state b 3
      all_goals exact safe_stay _
  change transition (readView base c).state
    (fun i => (readView base c).cells i ((readView base c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> first | rfl | exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem read_run (base : subroutine.Cfg) (c : CountedStream.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (readView base c)=readView base (CountedStream.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,read_step,Function.iterate_succ_apply']

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth

private noncomputable def canonicalBase (base : machine.Cfg) (d : List Bool) : CanonicalOutput.machine.Cfg where
  state := none
  cells := Function.update (Function.update base.cells 3 (descriptorTape d)) 4 (descriptorTape d)
  head := Function.update (Function.update base.head 3 (d.length+1)) 4 (d.length+1)

private noncomputable def canonicalIncoming (base : machine.Cfg) (w d : List Bool) : subroutine.Cfg :=
  canonicalView (CanonicalOutput.initialFrame (canonicalBase base d) w)

private noncomputable def canonicalFinal (base : machine.Cfg) (w d : List Bool) : subroutine.Cfg :=
  canonicalView (CanonicalOutput.finalFrame (canonicalBase base d) w)

private noncomputable def seekFrame (base : machine.Cfg) (w d : List Bool) (p : ℕ) : subroutine.Cfg :=
  {canonicalFinal base w d with
    state := relayState .seek
    head := Function.update (canonicalFinal base w d).head 1 p}

private noncomputable def readFrame (base : machine.Cfg) (w d : List Bool) (j : ℕ) (q : CountedStream.State) : subroutine.Cfg :=
  readView (seekFrame base w d 0) (PrefixRead.ready [] w.reverse [] [] d j q)

private noncomputable def seekDone (base : machine.Cfg) (w d : List Bool) : subroutine.Cfg :=
  {readFrame base w d 0 .emit with state := none}

private noncomputable def erasedOutput (base : machine.Cfg) (w d : List Bool) : subroutine.Cfg :=
  eraseDone 0 (readFrame base w d (width d) .halt)

/-- The source on bank 2 is already physically present; the destination has
already been physically erased. Generic frame updates are proved equal to
that retained caller frame at the paid handoff. -/
private noncomputable def reverseIncoming (base : subroutine.Cfg) (w : List Bool) : subroutine.Cfg where
  state := relayState .turn
  cells := Function.update (Function.update base.cells 2 (subroutine.tapeOf (w.map subroutine.bitSym)))
    1 (subroutine.tapeOf [])
  head := Function.update (Function.update base.head 2 (w.length+1)) 1 0

private noncomputable def reverseFrame (base : subroutine.Cfg) (w : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .reverse
  cells := Function.update (Function.update base.cells 2 (subroutine.tapeOf (w.map subroutine.bitSym)))
    1 (subroutine.tapeOf ((w.drop j).reverse.map subroutine.bitSym))
  head := Function.update (Function.update base.head 2 j) 1 (w.length-j+1)

private noncomputable def reverseFinal (base : subroutine.Cfg) (w : List Bool) : subroutine.Cfg :=
  {reverseFrame base w 0 with state := none}

private noncomputable def clearedScratch (base : machine.Cfg) (w d : List Bool) : subroutine.Cfg :=
  eraseDone 1 (reverseFinal (erasedOutput base w d) (w.reverse.take (width d)))

end IntMul.FixedOutputWidth


namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem turn_step (base : subroutine.Cfg) (w : List Bool) :
    subroutine.step (reverseIncoming base w)=reverseFrame base w w.length := by
  let s : Fin 15 → Sym := fun i => (reverseIncoming base w).cells i ((reverseIncoming base w).head i)
  have hi : s 2=Sym.blank := bits_blank w
  have ht : transition (relayState .turn) s=(relayState .reverse,
      fun i => (s i,if i=2 then Move.left else if i=1 then Move.right else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw]
    congr 1
    funext i
    by_cases h : i=2
    · subst i;simp only [if_true];exact safe_left _ (by rw [hi];decide)
    · by_cases h2 : i=1
      · subst i;simp only [if_true,if_false];exact safe_right _
      · simp only [if_neg h,if_neg h2];exact safe_stay _
  change transition (reverseIncoming base w).state
    (fun i => (reverseIncoming base w).cells i ((reverseIncoming base w).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [reverseIncoming,reverseFrame] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [reverseIncoming,reverseFrame]

private theorem owned_intmulfixedoutputwidthreverse_reverse_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 2=subroutine.bitSym b) (ho : s 1=Sym.blank) :
    transition (relayState .reverse) s=(relayState .reverse,
      fun i => (if i=1 then s 2 else s i,if i=2 then Move.left else if i=1 then Move.right else Move.stay)) := by
  have hb : s 2=Sym.zero ∨ s 2=Sym.one := by rw [hi];cases b <;> decide
  unfold transition
  rw [raw_relay]
  simp only [relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases h2 : i=1
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases h1 : i=2
    · subst i
      cases b <;> simp [hi,safeStep,MultitapeTM.bitSym]
    · simp only [if_neg h1,if_neg h2];exact safe_stay _

private theorem reverse_step (base : subroutine.Cfg) (w : List Bool) (j : ℕ) (hj : j+1 ≤ w.length) :
    subroutine.step (reverseFrame base w (j+1))=reverseFrame base w j := by
  have hi : (reverseFrame base w (j+1)).cells 2 ((reverseFrame base w (j+1)).head 2)=
      subroutine.bitSym w[j] := bits_read w j (by omega)
  have hl : ((w.drop (j+1)).reverse.map subroutine.bitSym).length=w.length-(j+1) := by simp
  have ho : (reverseFrame base w (j+1)).cells 1 ((reverseFrame base w (j+1)).head 1)=Sym.blank := by
    change ((w.drop (j+1)).reverse.map subroutine.bitSym).getD (w.length-(j+1)) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulfixedoutputwidthreverse_reverse_transition (fun i => (reverseFrame base w (j+1)).cells i
    ((reverseFrame base w (j+1)).head i)) w[j] hi ho
  change transition (reverseFrame base w (j+1)).state
    (fun i => (reverseFrame base w (j+1)).cells i ((reverseFrame base w (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases h2 : i=1
    · subst i
      change Function.update (subroutine.tapeOf ((w.drop (j+1)).reverse.map subroutine.bitSym))
        (w.length-(j+1)+1)
        ((reverseFrame base w (j+1)).cells 2 ((reverseFrame base w (j+1)).head 2))=
          subroutine.tapeOf ((w.drop j).reverse.map subroutine.bitSym)
      rw [hi]
      have hd : w.drop j=w[j]::w.drop (j+1) := List.drop_eq_getElem_cons (by omega)
      rw [hd,List.reverse_cons,List.map_append,List.map_singleton]
      have hw := tape_append_one ((w.drop (j+1)).reverse.map subroutine.bitSym) (subroutine.bitSym w[j])
      rw [hl] at hw
      exact hw
    · rw [if_neg h2,Function.update_eq_self]
      simp only [reverseFrame,Function.update_of_ne h2]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [reverseFrame] <;> omega

private theorem reverse_run (base : subroutine.Cfg) (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    subroutine.step^[j] (reverseFrame base w j)=reverseFrame base w 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,reverse_step base w j hj,ih (by omega)]

private theorem reverse_halt (base : subroutine.Cfg) (w : List Bool) :
    subroutine.step (reverseFrame base w 0)=reverseFinal base w := by
  let s : Fin 15 → Sym := fun i => (reverseFrame base w 0).cells i ((reverseFrame base w 0).head i)
  have hi : s 2=Sym.start := rfl
  have ht : transition (relayState .reverse) s=(none,fun i => (s i,Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.start=Sym.zero ∨ Sym.start=Sym.one))]
    simp only [safe_stay]
  change transition (reverseFrame base w 0).state
    (fun i => (reverseFrame base w 0).cells i ((reverseFrame base w 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem reverse_complete (base : subroutine.Cfg) (w : List Bool) :
    subroutine.step^[w.length+2] (reverseIncoming base w)=reverseFinal base w := by
  have h1 : subroutine.step^[w.length+1] (reverseIncoming base w)=reverseFrame base w 0 := by
    rw [Function.iterate_succ_apply,turn_step,reverse_run base w w.length (by omega)]
  rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',h1,reverse_halt]

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem canonical_complete (base : machine.Cfg) (w d : List Bool) :
    ∃ t : ℕ, t ≤ 8*w.length+16 ∧
      subroutine.step^[t] (canonicalIncoming base w d)=canonicalFinal base w d := by
  obtain ⟨t,ht,he,hh⟩ := CanonicalOutput.canonical_output (canonicalBase base d) w
  refine ⟨t,ht,?_⟩
  unfold canonicalIncoming canonicalFinal
  rw [canonical_run,he]

private theorem seek_step (base : machine.Cfg) (w d : List Bool) (p : ℕ) :
    subroutine.step (seekFrame base w d (p+1))=seekFrame base w d p := by
  let s : Fin 15 → Sym := fun i => (seekFrame base w d (p+1)).cells i
    ((seekFrame base w d (p+1)).head i)
  have hi : s 1≠Sym.start := by
    change subroutine.tapeOf (w.reverse.map subroutine.bitSym) (p+1)≠Sym.start
    apply tape_not_start
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact bit_not_start b
  have ht : transition (relayState .seek) s=(relayState .seek,
      fun i => (s i,if i=1 then Move.left else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,if_neg hi]
    congr 1
    funext i
    by_cases h : i=1
    · subst i;simp only [if_true];exact safe_left _ hi
    · simp only [if_neg h];exact safe_stay _
  change transition (seekFrame base w d (p+1)).state
    (fun i => (seekFrame base w d (p+1)).cells i ((seekFrame base w d (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame] <;> omega

private theorem seek_run (base : machine.Cfg) (w d : List Bool) (p : ℕ) :
    subroutine.step^[p] (seekFrame base w d p)=seekFrame base w d 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,seek_step,ih]

private theorem seek_open (base : machine.Cfg) (w d : List Bool) :
    subroutine.step (seekFrame base w d 0)=seekDone base w d := by
  let s : Fin 15 → Sym := fun i => (seekFrame base w d 0).cells i ((seekFrame base w d 0).head i)
  have hi : s 1=Sym.start := rfl
  have ht : transition (relayState .seek) s=(none,
      fun i => (s i,if i=1 ∨ i=2 then Move.right else Move.stay)) := by
    unfold transition
    rw [raw_relay]
    simp only [relayRaw,hi,if_true]
    congr 1
    funext i
    by_cases h : i=1 ∨ i=2
    · simp only [if_pos h];exact safe_right _
    · simp only [if_neg h];exact safe_stay _
  change transition (seekFrame base w d 0).state
    (fun i => (seekFrame base w d 0).cells i ((seekFrame base w d 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,canonicalFinal,canonicalView,CanonicalOutput.finalFrame,
      canonicalBase,seekDone,readFrame,readView,PrefixRead.ready,PrefixRead.frame,descriptorTape] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,canonicalFinal,canonicalView,CanonicalOutput.finalFrame,
      canonicalBase,seekDone,readFrame,readView,PrefixRead.ready,PrefixRead.frame]

private theorem seek_complete (base : machine.Cfg) (w d : List Bool) :
    subroutine.step^[w.length+2] (seekFrame base w d (w.length+1))=seekDone base w d := by
  rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',seek_run,seek_open]

private theorem read_complete (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    ∃ t : ℕ, t ≤ 6*width d+4*d.length+2 ∧
      subroutine.step^[t] (readFrame base w d 0 .emit)=readFrame base w d (width d) .halt := by
  obtain ⟨t,ht,he⟩ := PrefixRead.read_prefix [] w.reverse [] [] d
    (by simpa only [width,List.length_reverse] using hW)
  refine ⟨t,ht,?_⟩
  unfold readFrame
  rw [read_run,he]
  rfl

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth

private theorem low_width (w d : List Bool) (hW : width d ≤ w.length) :
    (w.reverse.take (width d)).length=width d := by simp [Nat.min_eq_left hW]

private theorem output_erasure_complete (base : machine.Cfg) (w d : List Bool) :
    subroutine.step^[width d+2*w.length+4]
      (eraseBegin 0 (readFrame base w d (width d) .halt))=erasedOutput base w d := by
  have h := erase_complete 0 (readFrame base w d (width d) .halt)
    (w.reverse.map subroutine.bitSym) (valid_bits w.reverse) (width d+1)
    (by simp [readFrame,readView,PrefixRead.ready,PrefixRead.frame,eraseBank] <;> rfl)
    (by simp [readFrame,readView,PrefixRead.ready,PrefixRead.frame,eraseBank])
  rw [List.length_map,List.length_reverse] at h
  have ht : width d+1+2*w.length+3=width d+2*w.length+4 := by omega
  rw [ht] at h
  simpa only [erasedOutput] using h

private theorem scratch_erasure_complete (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    subroutine.step^[2*width d+3]
      (eraseBegin 1 (reverseFinal (erasedOutput base w d) (w.reverse.take (width d))))=
        clearedScratch base w d := by
  have h := erase_complete 1 (reverseFinal (erasedOutput base w d) (w.reverse.take (width d)))
    ((w.reverse.take (width d)).map subroutine.bitSym) (valid_bits _) 0 rfl rfl
  simpa only [clearedScratch,List.length_map,low_width w d hW,Nat.zero_add] using h

private theorem initial_handoff (base : machine.Cfg) (w d : List Bool) :
    initialFrame base w d=FiniteCaller.embed subroutine Phase .canonical .canonical dispatch
      (canonicalIncoming base w d) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.embed,initialFrame,canonicalIncoming,canonicalView,CanonicalOutput.initialFrame,canonicalBase] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.embed,initialFrame,canonicalIncoming,canonicalView,CanonicalOutput.initialFrame,canonicalBase]

private theorem after_canonical (base : machine.Cfg) (w d : List Bool) :
    FiniteCaller.returned subroutine Phase .canonical .canonical dispatch (canonicalFinal base w d)=
    FiniteCaller.embed subroutine Phase .canonical .seek dispatch (seekFrame base w d (w.length+1)) := by
  apply cfg_ext
  · rfl
  · rfl
  · change (canonicalFinal base w d).head=Function.update (canonicalFinal base w d).head 1 (w.length+1)
    have h : (canonicalFinal base w d).head 1=w.length+1 := rfl
    rw [← h,Function.update_eq_self]

private theorem after_seek (base : machine.Cfg) (w d : List Bool) :
    FiniteCaller.returned subroutine Phase .canonical .seek dispatch (seekDone base w d)=
    FiniteCaller.embed subroutine Phase .canonical .read dispatch (readFrame base w d 0 .emit) := by
  apply cfg_ext <;> rfl

private theorem after_read (base : machine.Cfg) (w d : List Bool) :
    FiniteCaller.returned subroutine Phase .canonical .read dispatch (readFrame base w d (width d) .halt)=
    FiniteCaller.embed subroutine Phase .canonical .eraseOutput dispatch
      (eraseBegin 0 (readFrame base w d (width d) .halt)) := by
  apply cfg_ext <;> rfl

private theorem after_erasure (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    FiniteCaller.returned subroutine Phase .canonical .eraseOutput dispatch (erasedOutput base w d)=
    FiniteCaller.embed subroutine Phase .canonical .reverse dispatch
      (reverseIncoming (erasedOutput base w d) (w.reverse.take (width d))) := by
  have hc1 : (erasedOutput base w d).cells 1=subroutine.tapeOf [] := rfl
  have hc2 : (erasedOutput base w d).cells 2=
      subroutine.tapeOf ((w.reverse.take (width d)).map subroutine.bitSym) := rfl
  have hh1 : (erasedOutput base w d).head 1=0 := rfl
  have hh2 : (erasedOutput base w d).head 2=(w.reverse.take (width d)).length+1 := by
    simp [erasedOutput,eraseDone,eraseBank,readFrame,readView,PrefixRead.ready,PrefixRead.frame,low_width w d hW]
  apply cfg_ext
  · rfl
  · change (erasedOutput base w d).cells=Function.update
      (Function.update (erasedOutput base w d).cells 2 _) 1 _
    rw [← hc2,Function.update_eq_self,← hc1,Function.update_eq_self]
  · change (erasedOutput base w d).head=Function.update
      (Function.update (erasedOutput base w d).head 2 _) 1 _
    rw [← hh2,Function.update_eq_self,← hh1,Function.update_eq_self]

private theorem after_reverse (base : machine.Cfg) (w d : List Bool) :
    FiniteCaller.returned subroutine Phase .canonical .reverse dispatch
      (reverseFinal (erasedOutput base w d) (w.reverse.take (width d)))=
    FiniteCaller.embed subroutine Phase .canonical .eraseScratch dispatch
      (eraseBegin 1 (reverseFinal (erasedOutput base w d) (w.reverse.take (width d)))) := by
  apply cfg_ext <;> rfl

private theorem final_handoff (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    FiniteCaller.returned subroutine Phase .canonical .eraseScratch dispatch (clearedScratch base w d)=
      finalFrame base w d := by
  have hlen := low_width w d hW
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,clearedScratch,eraseDone,eraseBank,reverseFinal,reverseFrame,erasedOutput,
      readFrame,readView,PrefixRead.ready,PrefixRead.frame,seekFrame,canonicalFinal,canonicalView,
      CanonicalOutput.finalFrame,canonicalBase,finalFrame,outputWord,descriptorTape] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,clearedScratch,eraseDone,eraseBank,reverseFinal,reverseFrame,erasedOutput,
      readFrame,readView,PrefixRead.ready,PrefixRead.frame,seekFrame,canonicalFinal,canonicalView,
      CanonicalOutput.finalFrame,canonicalBase,finalFrame,hlen]

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth

/-- Real finite-state output-width return. Every seek, prefix countdown,
erasure, reverse copy and all six finite-caller returns are counted. -/
private theorem width_execution (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    ∃ t : ℕ, t ≤ 11*w.length+10*width d+4*d.length+35 ∧
      machine.step^[t] (initialFrame base w d)=finalFrame base w d ∧
      (machine.step^[t] (initialFrame base w d)).state=machine.qHalt := by
  obtain ⟨u,hu,heu⟩ := canonical_complete base w d
  obtain ⟨a,ha,hea⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .canonical dispatch
    (canonicalIncoming base w d) u).2 (by rw [heu];rfl)
  rw [heu,after_canonical] at hea
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .seek dispatch
    (seekFrame base w d (w.length+1)) (w.length+2)).2 (by rw [seek_complete];rfl)
  rw [seek_complete,after_seek] at heb
  obtain ⟨v,hv,hev⟩ := read_complete base w d hW
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .read dispatch
    (readFrame base w d 0 .emit) v).2 (by rw [hev];rfl)
  rw [hev,after_read] at hec
  obtain ⟨e,he,hee⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .eraseOutput dispatch
    (eraseBegin 0 (readFrame base w d (width d) .halt)) (width d+2*w.length+4)).2
      (by rw [output_erasure_complete];rfl)
  rw [output_erasure_complete,after_erasure base w d hW] at hee
  obtain ⟨f,hf,hef⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .reverse dispatch
    (reverseIncoming (erasedOutput base w d) (w.reverse.take (width d)))
    ((w.reverse.take (width d)).length+2)).2 (by rw [reverse_complete];rfl)
  rw [reverse_complete,after_reverse] at hef
  rw [low_width w d hW] at hf
  obtain ⟨g,hg,heg⟩ := (FiniteCaller.simulate_run subroutine Phase .canonical .eraseScratch dispatch
    (eraseBegin 1 (reverseFinal (erasedOutput base w d) (w.reverse.take (width d))))
    (2*width d+3)).2 (by rw [scratch_erasure_complete base w d hW];rfl)
  rw [scratch_erasure_complete base w d hW,final_handoff base w d hW] at heg
  have hex : machine.step^[g+(f+(e+(c+(b+a))))] (initialFrame base w d)=finalFrame base w d := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      Function.iterate_add_apply,Function.iterate_add_apply,initial_handoff,hea,heb,hec,hee,hef,heg]
  refine ⟨g+(f+(e+(c+(b+a)))),by omega,hex,?_⟩
  rw [hex];rfl

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidthEncoding
open IntMul.BinaryAdder (littleVal)

private theorem owned_intmulfixedoutputwidthencoding_little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem owned_intmulfixedoutputwidthencoding_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) a = 2 ^ x.length * a + IntMul.val x := by
  induction x generalizing a with
  | nil => simp [IntMul.val]
  | cons b xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hv : IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
        simp only [IntMul.val, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        exact ih b.toNat
      rw [hv, pow_succ]
      ring

private theorem owned_intmulfixedoutputwidthencoding_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact owned_intmulfixedoutputwidthencoding_foldl_affine y _

private theorem owned_intmulfixedoutputwidthencoding_val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem owned_intmulfixedoutputwidthencoding_val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, owned_intmulfixedoutputwidthencoding_val_append, owned_intmulfixedoutputwidthencoding_val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring


private theorem owned_intmulfixedoutputwidthencoding_little_value_test_bit (x : List Bool) (i : ℕ) :
    (littleVal x).testBit i = x.getD i false := by
  induction x generalizing i with
  | nil => simp [littleVal]
  | cons b xs ih =>
      have hv : littleVal (b :: xs) = Nat.bit b (littleVal xs) := by
        cases b <;> simp [littleVal, Nat.bit] <;> omega
      rw [hv]
      cases i with
      | zero => cases b <;> simp [Nat.bit, Nat.testBit_zero]
      | succ i => rw [Nat.testBit_bit_succ]; simpa using ih i

/-- The campaign's padded big-endian binary encoding returns every original
word, preserving its declared width and any leading zeroes. -/
private theorem bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← owned_intmulfixedoutputwidthencoding_val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, owned_intmulfixedoutputwidthencoding_little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]


private theorem bin_reverse (B d : ℕ) :
    (bin B d).reverse=List.ofFn (fun i : Fin B => d.testBit i) := by
  apply List.ext_getElem (by simp [bin])
  intro i hi hi'
  simp only [bin,List.getElem_reverse,List.getElem_ofFn]
  congr 1
  simp only [List.length_ofFn] at *
  omega

private theorem bin_value (B d : ℕ) : val (bin B d)=d%2^B := by
  have hv : val (bin B d)=BinaryAdder.littleVal (bin B d).reverse := by
    rw [←owned_intmulfixedoutputwidthencoding_val_reverse_little,List.reverse_reverse]
  rw [hv,bin_reverse]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [owned_intmulfixedoutputwidthencoding_little_value_test_bit,Nat.testBit_mod_two_pow]
  by_cases hj : j < B
  · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
    simp [hj]
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    simp [hj]


end IntMul.FixedOutputWidthEncoding



namespace IntMul.FixedOutputWidth

/-- The physically returned suffix is exactly the campaign model's binary
representation at the supplied width, preserving leading zero padding. -/
private theorem output_binary (w d : List Bool) (hW : width d ≤ w.length) :
    outputWord w d=bin (width d) (val w) := by
  have hw := FixedOutputWidthEncoding.bin_value_roundtrip w
  have hr : w.reverse=List.ofFn (fun i : Fin w.length => (val w).testBit i) := by
    rw [← FixedOutputWidthEncoding.bin_reverse,hw]
  change (w.reverse.take (width d)).reverse=bin (width d) (val w)
  rw [hr,← Fin.ofFn_take_eq_take_ofFn hW]
  change (List.ofFn (fun i : Fin (width d) => (val w).testBit i)).reverse=bin (width d) (val w)
  rw [← FixedOutputWidthEncoding.bin_reverse,List.reverse_reverse]

end IntMul.FixedOutputWidth



namespace IntMul.FixedOutputWidth

/-- The complete paid width conversion returns exactly the binary output at
the requested width, retains the caller frame and globally halts. -/
private theorem fixed_output_width (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    ∃ t : ℕ, t ≤ 11*w.length+10*width d+4*d.length+35 ∧
      machine.step^[t] (initialFrame base w d)=finalFrame base w d ∧
      (machine.step^[t] (initialFrame base w d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base w d)).cells 1=
        machine.tapeOf ((bin (width d) (val w)).map machine.bitSym) := by
  obtain ⟨t,ht,he,hh⟩ := width_execution base w d hW
  refine ⟨t,ht,he,hh,?_⟩
  rw [he]
  simp only [finalFrame,Function.update_of_ne (by decide : (1 : Fin 15)≠4),
    Function.update_of_ne (by decide : (1 : Fin 15)≠3),
    Function.update_of_ne (by decide : (1 : Fin 15)≠2),Function.update_self]
  rw [output_binary w d hW]

end IntMul.FixedOutputWidth



open IntMul IntMul.FixedOutputWidth

theorem solution (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    ∃ t : ℕ, t ≤ 11*w.length+10*width d+4*d.length+35 ∧
      machine.step^[t] (initialFrame base w d)=finalFrame base w d ∧
      (machine.step^[t] (initialFrame base w d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base w d)).cells 1=
        machine.tapeOf ((bin (width d) (val w)).map machine.bitSym) :=
  IntMul.FixedOutputWidth.fixed_output_width base w d hW

#print axioms solution
