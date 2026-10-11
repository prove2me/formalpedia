-- Prove2me | solution 1 for IntMul.CanonicalOutput.canonical_output
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T12:54:51.872037+00:00
-- url     : https://prove2.me/submissions/7c99ec4b-0dea-46f0-848d-32035aa35fca

import Definitions.Def_IntMul_CanonicalOutput
import Mathlib.Tactic
import Theorems.Thm_IntMul_TapeBankErase_erase_bank
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.CanonicalOutput
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem owned_intmulcanonicaloutputprograms_safe_identity (s w : Sym) (d : Move)
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
      apply owned_intmulcanonicaloutputprograms_safe_identity
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

end IntMul.CanonicalOutput




namespace IntMul.CanonicalOutput
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


end IntMul.CanonicalOutput


namespace IntMul.CanonicalOutput
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

end IntMul.CanonicalOutput



namespace IntMul.CanonicalOutput
open TapeCopy (Sym)

private noncomputable def incoming (base : machine.Cfg) (w : List Bool) : subroutine.Cfg where
  state := relayState .turn
  cells := (initialFrame base w).cells
  head := (initialFrame base w).head

private noncomputable def reverseFrame (base : machine.Cfg) (w : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .reverse
  cells := Function.update (Function.update base.cells 1 (subroutine.tapeOf (w.map subroutine.bitSym)))
    2 (subroutine.tapeOf ((w.drop j).reverse.map subroutine.bitSym))
  head := Function.update (Function.update base.head 1 j) 2 (w.length-j+1)

private noncomputable def reverseFinal (base : machine.Cfg) (w : List Bool) : subroutine.Cfg :=
  {reverseFrame base w 0 with state := none}

private noncomputable def erasedOutput (base : machine.Cfg) (w : List Bool) : subroutine.Cfg :=
  eraseDone 0 (reverseFinal base w)

private noncomputable def seekFrame (base : machine.Cfg) (w : List Bool) (p : ℕ) : subroutine.Cfg :=
  {erasedOutput base w with state := relayState .seek,head := Function.update (erasedOutput base w).head 2 p}

private noncomputable def copyFrame (base : machine.Cfg) (w : List Bool) (j : ℕ) : subroutine.Cfg where
  state := relayState .copy
  cells := Function.update (erasedOutput base w).cells 1 (subroutine.tapeOf ((w.reverse.take j).map subroutine.bitSym))
  head := fun i => if i=1 ∨ i=2 then j+1 else (erasedOutput base w).head i

private noncomputable def copyFinal (base : machine.Cfg) (w : List Bool) : subroutine.Cfg :=
  {copyFrame base w w.length with state := none}

private noncomputable def clearedScratch (base : machine.Cfg) (w : List Bool) : subroutine.Cfg :=
  eraseDone 1 (copyFinal base w)

end IntMul.CanonicalOutput


namespace IntMul.CanonicalOutput
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem turn_step (base : machine.Cfg) (w : List Bool) :
    subroutine.step (incoming base w)=reverseFrame base w w.length := by
  let s : Fin 15 → Sym := fun i => (incoming base w).cells i ((incoming base w).head i)
  have hi : s 1=Sym.blank := bits_blank w
  have ht : transition (relayState .turn) s=(relayState .reverse,
      fun i => (s i,if i=1 then Move.left else if i=2 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    congr 1
    funext i
    by_cases h : i=1
    · subst i;simp only [if_true];exact safe_left _ (by rw [hi];decide)
    · by_cases h2 : i=2
      · subst i;simp only [if_true,if_false];exact safe_right _
      · simp only [if_neg h,if_neg h2];exact safe_stay _
  change transition (incoming base w).state
    (fun i => (incoming base w).cells i ((incoming base w).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [incoming,initialFrame,reverseFrame] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [incoming,initialFrame,reverseFrame]

private theorem owned_intmulcanonicaloutputreverse_reverse_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 1=subroutine.bitSym b) (ho : s 2=Sym.blank) :
    transition (relayState .reverse) s=(relayState .reverse,
      fun i => (if i=2 then s 1 else s i,if i=1 then Move.left else if i=2 then Move.right else Move.stay)) := by
  have hb : s 1=Sym.zero ∨ s 1=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases h2 : i=2
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases h1 : i=1
    · subst i
      cases b <;> simp [hi,safeStep,MultitapeTM.bitSym]
    · simp only [if_neg h1,if_neg h2];exact safe_stay _

private theorem reverse_step (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j+1 ≤ w.length) :
    subroutine.step (reverseFrame base w (j+1))=reverseFrame base w j := by
  have hi : (reverseFrame base w (j+1)).cells 1 ((reverseFrame base w (j+1)).head 1)=
      subroutine.bitSym w[j] := bits_read w j (by omega)
  have hl : ((w.drop (j+1)).reverse.map subroutine.bitSym).length=w.length-(j+1) := by simp
  have ho : (reverseFrame base w (j+1)).cells 2 ((reverseFrame base w (j+1)).head 2)=Sym.blank := by
    change ((w.drop (j+1)).reverse.map subroutine.bitSym).getD (w.length-(j+1)) Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcanonicaloutputreverse_reverse_transition (fun i => (reverseFrame base w (j+1)).cells i
    ((reverseFrame base w (j+1)).head i)) w[j] hi ho
  change transition (reverseFrame base w (j+1)).state
    (fun i => (reverseFrame base w (j+1)).cells i ((reverseFrame base w (j+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases h2 : i=2
    · subst i
      change Function.update (subroutine.tapeOf ((w.drop (j+1)).reverse.map subroutine.bitSym))
        (w.length-(j+1)+1)
        ((reverseFrame base w (j+1)).cells 1 ((reverseFrame base w (j+1)).head 1))=
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

private theorem reverse_run (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    subroutine.step^[j] (reverseFrame base w j)=reverseFrame base w 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,reverse_step base w j hj,ih (by omega)]

private theorem reverse_halt (base : machine.Cfg) (w : List Bool) :
    subroutine.step (reverseFrame base w 0)=reverseFinal base w := by
  let s : Fin 15 → Sym := fun i => (reverseFrame base w 0).cells i ((reverseFrame base w 0).head i)
  have hi : s 1=Sym.start := rfl
  have ht : transition (relayState .reverse) s=(none,fun i => (s i,Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.start=Sym.zero ∨ Sym.start=Sym.one))]
    simp only [safe_stay]
  change transition (reverseFrame base w 0).state
    (fun i => (reverseFrame base w 0).cells i ((reverseFrame base w 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem reverse_complete (base : machine.Cfg) (w : List Bool) :
    subroutine.step^[w.length+2] (incoming base w)=reverseFinal base w := by
  have h1 : subroutine.step^[w.length+1] (incoming base w)=reverseFrame base w 0 := by
    rw [Function.iterate_succ_apply,turn_step,reverse_run base w w.length (by omega)]
  rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',h1,reverse_halt]

end IntMul.CanonicalOutput



namespace IntMul.CanonicalOutput
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem seek_step (base : machine.Cfg) (w : List Bool) (p : ℕ) :
    subroutine.step (seekFrame base w (p+1))=seekFrame base w p := by
  let s : Fin 15 → Sym := fun i => (seekFrame base w (p+1)).cells i ((seekFrame base w (p+1)).head i)
  have hi : s 2≠Sym.start :=
    tape_not_start _ (by intro a ha;obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha;exact bit_not_start b) p
  have ht : transition (relayState .seek) s=(relayState .seek,
      fun i => (s i,if i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,if_neg hi]
    congr 1
    funext i
    by_cases h : i=2
    · subst i;simp only [if_true];exact safe_left _ hi
    · simp only [if_neg h];exact safe_stay _
  change transition (seekFrame base w (p+1)).state
    (fun i => (seekFrame base w (p+1)).cells i ((seekFrame base w (p+1)).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame]

private theorem seek_run (base : machine.Cfg) (w : List Bool) (p : ℕ) :
    subroutine.step^[p] (seekFrame base w p)=seekFrame base w 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,seek_step base w p,ih]

private theorem seek_open (base : machine.Cfg) (w : List Bool) :
    subroutine.step (seekFrame base w 0)=copyFrame base w 0 := by
  let s : Fin 15 → Sym := fun i => (seekFrame base w 0).cells i ((seekFrame base w 0).head i)
  have hi : s 2=Sym.start := rfl
  have ht : transition (relayState .seek) s=(relayState .copy,
      fun i => (s i,if i=1 ∨ i=2 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,if_pos hi]
    congr 1
    funext i
    split <;> first | exact safe_right _ | exact safe_stay _
  change transition (seekFrame base w 0).state
    (fun i => (seekFrame base w 0).cells i ((seekFrame base w 0).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,copyFrame,erasedOutput,eraseDone,eraseBank] <;> rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [seekFrame,copyFrame,erasedOutput,eraseDone,eraseBank]

private theorem owned_intmulcanonicaloutputcopy_copy_transition (s : Fin 15 → Sym) (b : Bool)
    (hi : s 2=subroutine.bitSym b) (ho : s 1=Sym.blank) :
    transition (relayState .copy) s=(relayState .copy,
      fun i => (if i=1 then s 2 else s i,if i=1 ∨ i=2 then Move.right else Move.stay)) := by
  have hb : s 2=Sym.zero ∨ s 2=Sym.one := by rw [hi];cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  by_cases h1 : i=1
  · subst i
    cases b <;> simp [hi,ho,safeStep,MultitapeTM.bitSym]
  · by_cases h2 : i=2
    · subst i;simp only [or_true,if_true,if_false];exact safe_right _
    · simp only [if_neg h1,if_neg (not_or.mpr ⟨h1,h2⟩)];exact safe_stay _

private theorem copy_step (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    subroutine.step (copyFrame base w j)=copyFrame base w (j+1) := by
  let d := w.reverse
  have hjd : j < d.length := by simpa [d] using hj
  have hi : (copyFrame base w j).cells 2 ((copyFrame base w j).head 2)=subroutine.bitSym d[j] :=
    bits_read d j hjd
  let v := (d.take j).map subroutine.bitSym
  have hl : v.length=j := by simp [v,Nat.min_eq_left hjd.le]
  have ho : (copyFrame base w j).cells 1 ((copyFrame base w j).head 1)=Sym.blank := by
    change v.getD j Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcanonicaloutputcopy_copy_transition (fun i => (copyFrame base w j).cells i ((copyFrame base w j).head i)) d[j] hi ho
  change transition (copyFrame base w j).state
    (fun i => (copyFrame base w j).cells i ((copyFrame base w j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases h1 : i=1
    · subst i
      change Function.update (subroutine.tapeOf v) (j+1)
        ((copyFrame base w j).cells 2 ((copyFrame base w j).head 2))=
          subroutine.tapeOf ((d.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hv := tape_append_one v (subroutine.bitSym d[j])
      rw [hl] at hv
      rw [List.take_succ_eq_append_getElem hjd,List.map_append]
      exact hv
    · rw [if_neg h1,Function.update_eq_self]
      simp only [copyFrame,Function.update_of_ne h1]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyFrame,Nat.add_assoc]

private theorem copy_run (base : machine.Cfg) (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    subroutine.step^[j] (copyFrame base w 0)=copyFrame base w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_step base w j (by omega)]

private theorem copy_halt (base : machine.Cfg) (w : List Bool) :
    subroutine.step (copyFrame base w w.length)=copyFinal base w := by
  let s : Fin 15 → Sym := fun i => (copyFrame base w w.length).cells i ((copyFrame base w w.length).head i)
  have hi : s 2=Sym.blank := by
    change subroutine.tapeOf (w.reverse.map subroutine.bitSym) (w.length+1)=Sym.blank
    simpa only [List.length_reverse] using bits_blank w.reverse
  have ht : transition (relayState .copy) s=(none,fun i => (s i,Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    simp only [safe_stay]
  change transition (copyFrame base w w.length).state
    (fun i => (copyFrame base w w.length).cells i ((copyFrame base w w.length).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem copy_complete (base : machine.Cfg) (w : List Bool) :
    subroutine.step^[2*w.length+3] (seekFrame base w (w.length+1))=copyFinal base w := by
  have hseek : subroutine.step^[w.length+2] (seekFrame base w (w.length+1))=copyFrame base w 0 := by
    rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply',seek_run,seek_open]
  have hcopy : subroutine.step^[w.length+1] (copyFrame base w 0)=copyFinal base w := by
    rw [Function.iterate_succ_apply',copy_run base w w.length (by omega),copy_halt]
  rw [show 2*w.length+3=(w.length+1)+(w.length+2) by omega,Function.iterate_add_apply,hseek,hcopy]

end IntMul.CanonicalOutput



namespace IntMul.CanonicalOutput
open TapeCopy (Sym)

private theorem output_erasure_complete (base : machine.Cfg) (w : List Bool) :
    subroutine.step^[2*w.length+3] (eraseBegin 0 (reverseFinal base w))=erasedOutput base w := by
  have he := erase_complete 0 (reverseFinal base w) (w.map subroutine.bitSym) (valid_bits w) 0 (by rfl) (by rfl)
  simpa only [List.length_map,Nat.zero_add,erasedOutput] using he

private theorem scratch_erasure_complete (base : machine.Cfg) (w : List Bool) :
    subroutine.step^[3*w.length+4] (eraseBegin 1 (copyFinal base w))=clearedScratch base w := by
  have hc : (copyFinal base w).cells 2=subroutine.tapeOf (w.reverse.map subroutine.bitSym) := rfl
  have hh : (copyFinal base w).head 2=w.length+1 := rfl
  have he := erase_complete 1 (copyFinal base w) (w.reverse.map subroutine.bitSym)
    (valid_bits w.reverse) (w.length+1) hc hh
  have ht : w.length+1+2*(w.reverse.map subroutine.bitSym).length+3=3*w.length+4 := by simp;omega
  simpa only [ht,clearedScratch] using he

private theorem initial_handoff (base : machine.Cfg) (w : List Bool) :
    initialFrame base w=FiniteCaller.embed subroutine Phase .reverse .reverse dispatch (incoming base w) := rfl

private theorem after_reverse (base : machine.Cfg) (w : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .reverse dispatch (reverseFinal base w)=
      FiniteCaller.embed subroutine Phase .reverse .eraseOutput dispatch (eraseBegin 0 (reverseFinal base w)) := rfl

private theorem after_output_erasure (base : machine.Cfg) (w : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .eraseOutput dispatch (erasedOutput base w)=
      FiniteCaller.embed subroutine Phase .reverse .copy dispatch (seekFrame base w (w.length+1)) := by
  apply cfg_ext
  · rfl
  · rfl
  · have hh : (erasedOutput base w).head 2=w.length+1 := rfl
    change (erasedOutput base w).head=Function.update (erasedOutput base w).head 2 (w.length+1)
    rw [←hh,Function.update_eq_self]

private theorem after_copy (base : machine.Cfg) (w : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .copy dispatch (copyFinal base w)=
      FiniteCaller.embed subroutine Phase .reverse .eraseScratch dispatch (eraseBegin 1 (copyFinal base w)) := rfl

private theorem final_handoff (base : machine.Cfg) (w : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .eraseScratch dispatch (clearedScratch base w)=finalFrame base w := by
  have hlen : ((w.map subroutine.bitSym).reverse).length=w.length := by simp
  have htake : ((w.map subroutine.bitSym).reverse).take w.length=(w.map subroutine.bitSym).reverse := by
    rw [←hlen,List.take_length]
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,clearedScratch,eraseDone,eraseBank,copyFinal,copyFrame,
      erasedOutput,reverseFinal,reverseFrame,finalFrame,htake] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,clearedScratch,eraseDone,eraseBank,copyFinal,copyFrame,
      erasedOutput,reverseFinal,reverseFrame,finalFrame,htake]

end IntMul.CanonicalOutput



namespace IntMul.CanonicalOutput

/-- Physical canonical output repair with an exact retained surrounding caller
frame and fully charged linear transition bound, including empty output. -/
private theorem canonical_output (base : machine.Cfg) (w : List Bool) :
    ∃ t : ℕ, t ≤ 8*w.length+16 ∧
      machine.step^[t] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[t] (initialFrame base w)).state=machine.qHalt := by
  obtain ⟨a,ha,hea⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .reverse dispatch
    (incoming base w) (w.length+2)).2 (by rw [reverse_complete];rfl)
  rw [reverse_complete,after_reverse] at hea
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .eraseOutput dispatch
    (eraseBegin 0 (reverseFinal base w)) (2*w.length+3)).2 (by rw [output_erasure_complete];rfl)
  rw [output_erasure_complete,after_output_erasure] at heb
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .copy dispatch
    (seekFrame base w (w.length+1)) (2*w.length+3)).2 (by rw [copy_complete];rfl)
  rw [copy_complete,after_copy] at hec
  obtain ⟨d,hd,hed⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .eraseScratch dispatch
    (eraseBegin 1 (copyFinal base w)) (3*w.length+4)).2 (by rw [scratch_erasure_complete];rfl)
  rw [scratch_erasure_complete,final_handoff] at hed
  have he : machine.step^[d+(c+(b+a))] (initialFrame base w)=finalFrame base w := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
      initial_handoff,hea,heb,hec,hed]
  refine ⟨d+(c+(b+a)),by omega,he,?_⟩
  rw [he];rfl

end IntMul.CanonicalOutput



open IntMul IntMul.CanonicalOutput

theorem solution (base : machine.Cfg) (w : List Bool) :
    ∃ t : ℕ, t ≤ 8*w.length+16 ∧
      machine.step^[t] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[t] (initialFrame base w)).state=machine.qHalt :=
  IntMul.CanonicalOutput.canonical_output base w

#print axioms solution
