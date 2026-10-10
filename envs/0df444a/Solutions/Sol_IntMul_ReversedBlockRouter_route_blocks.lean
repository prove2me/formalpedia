-- Prove2me | solution 1 for IntMul.ReversedBlockRouter.route_blocks
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T09:36:25.13664+00:00
-- url     : https://prove2.me/submissions/8817b29a-2c5c-4b4d-a6f9-7d90ed22917b

import Definitions.Def_IntMul_ReversedBlockRouter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Theorems.Thm_IntMul_TapeReverse_reverse_first_operand
import Theorems.Thm_IntMul_CountedBlockSplitter_split_blocks
import Theorems.Thm_IntMul_FiniteCaller_simulate_run


namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem safe_identity (s w : Sym) (d : Move)
    (hs : s=Sym.start → w=Sym.start ∧ d≠Move.left)
    (hw : s≠Sym.start → w≠Sym.start) : safeStep s w d=(w,d) := by
  by_cases h : s=Sym.start
  · obtain ⟨h₁,h₂⟩ := hs h
    simp [safeStep,h,h₁,h₂]
  · simp [safeStep,h,hw h]

private theorem safe_reverse (q : TapeReverse.State) (a : Fin 2 → Sym) (j : Fin 2) :
    safeStep (a j) (TapeReverse.machine.δ q a |>.2 j).1
      (TapeReverse.machine.δ q a |>.2 j).2=(TapeReverse.machine.δ q a).2 j := by
  apply safe_identity
  · exact TapeReverse.machine.start_preserved q a j
  · exact TapeReverse.machine.start_only_at_start q a j

private theorem safe_split (q : CountedBlockSplitter.machine.K) (a : Fin 4 → Sym) (j : Fin 4) :
    safeStep (a j) (CountedBlockSplitter.machine.δ q a |>.2 j).1
      (CountedBlockSplitter.machine.δ q a |>.2 j).2=(CountedBlockSplitter.machine.δ q a).2 j := by
  apply safe_identity
  · exact CountedBlockSplitter.machine.start_preserved q a j
  · exact CountedBlockSplitter.machine.start_only_at_start q a j

private noncomputable def reverseView (c : TapeReverse.machine.Cfg) : subroutine.Cfg where
  state := reverseState c.state
  cells := fun i => if i=0 then c.cells 0 else if i=2 then c.cells 1 else subroutine.tapeOf []
  head := fun i => if i=0 then c.head 0 else if i=2 then c.head 1 else 0

private noncomputable def splitView (x y : List Bool) (c : CountedBlockSplitter.machine.Cfg) : subroutine.Cfg where
  state := splitState c.state
  cells := fun i =>
    if i=0 then subroutine.tapeOf (x.map subroutine.bitSym ++ Sym.sep :: y.map subroutine.bitSym)
    else if i=1 then c.cells 1
    else if i=2 then subroutine.tapeOf (x.reverse.map subroutine.bitSym)
    else if i=3 then c.cells 0
    else if i=4 then c.cells 2
    else c.cells 3
  head := fun i => if i=0 then x.length+y.length+2 else if i=1 then c.head 1
    else if i=2 then x.length+1 else if i=3 then c.head 0 else if i=4 then c.head 2 else c.head 3

private theorem reverse_step (c : TapeReverse.machine.Cfg) :
    subroutine.step (reverseView c)=reverseView (TapeReverse.machine.step c) := by
  let a : Fin 6 → Sym := fun i => (reverseView c).cells i ((reverseView c).head i)
  let b : Fin 2 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (reverseTape j))=b := by
    funext j
    fin_cases j <;> rfl
  have ht : transition (reverseState c.state) a=
      (reverseState (TapeReverse.machine.δ c.state b).1,
        reverseAction a (TapeReverse.machine.δ c.state b).2) := by
    by_cases h : c.state=.halt
    · rw [h,TapeReverse.machine.halt_fixed b]
      simp only [reverseState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [reverseState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_reverse c.state b 0
      · exact safe_stay _
      · exact safe_reverse c.state b 1
      · exact safe_stay _
      · exact safe_stay _
      · exact safe_stay _
  change transition (reverseView c).state
    (fun i => (reverseView c).cells i ((reverseView c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rfl
    · exact Function.update_eq_self _ _
    · rfl
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem reverse_run (c : TapeReverse.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (reverseView c)=reverseView (TapeReverse.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,reverse_step,Function.iterate_succ_apply']

private theorem split_step (x y : List Bool) (c : CountedBlockSplitter.machine.Cfg) :
    subroutine.step (splitView x y c)=splitView x y (CountedBlockSplitter.machine.step c) := by
  let a : Fin 6 → Sym := fun i => (splitView x y c).cells i ((splitView x y c).head i)
  let b : Fin 4 → Sym := fun j => c.cells j (c.head j)
  have ha : (fun j => a (splitTape j))=b := by
    funext j
    fin_cases j <;> rfl
  have ht : transition (splitState c.state) a=
      (splitState (CountedBlockSplitter.machine.δ c.state b).1,
        splitAction a (CountedBlockSplitter.machine.δ c.state b).2) := by
    by_cases h : c.state=none
    · rw [h,CountedBlockSplitter.machine.halt_fixed b]
      simp only [splitState,if_true,transition,rawTransition,safe_stay]
      congr 1
      funext i
      fin_cases i <;> rfl
    · simp only [splitState,if_neg h,transition,rawTransition]
      rw [ha]
      congr 1
      funext i
      fin_cases i
      · exact safe_stay _
      · exact safe_split c.state b 1
      · exact safe_stay _
      · exact safe_split c.state b 0
      · exact safe_split c.state b 2
      · exact safe_split c.state b 3
  change transition (splitView x y c).state
    (fun i => (splitView x y c).cells i ((splitView x y c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · rfl
    · exact Function.update_eq_self _ _
    · rfl
    · rfl
    · rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> rfl

private theorem split_run (x y : List Bool) (c : CountedBlockSplitter.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (splitView x y c)=splitView x y (CountedBlockSplitter.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,split_step,Function.iterate_succ_apply']

private theorem reverse_init (x y : List Bool) :
    subroutine.initCfg x y=reverseView (TapeReverse.machine.initCfg x y) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)

private noncomputable def inputWord (x y : List Bool) : List Sym :=
  x.map subroutine.bitSym ++ Sym.sep :: y.map subroutine.bitSym

private noncomputable def reverseWord (x : List Bool) : List Sym := x.reverse.map subroutine.bitSym

private noncomputable def requestWord (x y : List Bool) : List Sym :=
  reverseWord x ++ Sym.sep :: y.map subroutine.bitSym

private noncomputable def relayFrame (x y : List Bool) (q : Relay) (w : List Sym)
    (h₀ h₂ h₃ : ℕ) : subroutine.Cfg where
  state := relayState q
  cells := fun i => if i=0 then subroutine.tapeOf (inputWord x y)
    else if i=2 then subroutine.tapeOf (reverseWord x)
    else if i=3 then subroutine.tapeOf w else subroutine.tapeOf []
  head := fun i => if i=0 then h₀ else if i=2 then h₂ else if i=3 then h₃ else 0

private noncomputable def alignFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  relayFrame x y .align [] j (x.length+1-j) 0

private noncomputable def copyReverseFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  relayFrame x y .copyReverse ((x.reverse.take j).map subroutine.bitSym) (x.length+1) (j+1) (j+1)

private noncomputable def descriptorFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  relayFrame x y .copyDescriptor
    (reverseWord x ++ Sym.sep :: (y.take j).map subroutine.bitSym)
    (x.length+j+2) (x.length+1) (x.length+j+2)

private noncomputable def rewindFrame (x y : List Bool) (j : ℕ) : subroutine.Cfg :=
  relayFrame x y .rewind (requestWord x y) (x.length+y.length+2) (x.length+1) j

private noncomputable def relayFinal (x y : List Bool) : subroutine.Cfg :=
  {rewindFrame x y 0 with state := none}

private theorem bit_not_start (b : Bool) : subroutine.bitSym b≠Sym.start := by
  cases b <;> decide

private theorem bit_not_sep (b : Bool) : subroutine.bitSym b≠Sym.sep := by
  cases b <;> decide

private theorem input_length (x y : List Bool) : (inputWord x y).length=x.length+y.length+1 := by
  simp [inputWord]
  omega

private theorem request_length (x y : List Bool) : (requestWord x y).length=x.length+y.length+1 := by
  simp [requestWord,reverseWord]
  omega

private theorem input_read (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    subroutine.tapeOf (inputWord x y) (j+1)=subroutine.bitSym x[j] := by
  change (inputWord x y).getD j Sym.blank=_
  rw [inputWord,List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem input_sep (x y : List Bool) :
    subroutine.tapeOf (inputWord x y) (x.length+1)=Sym.sep := by
  change (inputWord x y).getD x.length Sym.blank=_
  rw [inputWord,List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem input_descriptor (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    subroutine.tapeOf (inputWord x y) (x.length+j+2)=subroutine.bitSym y[j] := by
  have he : x.length+j+2=(x.length+(j+1))+1 := by omega
  rw [he]
  change (inputWord x y).getD (x.length+(j+1)) Sym.blank=_
  rw [inputWord,List.getD_append_right _ _ _ _ (by simp <;> omega)]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem input_blank (x y : List Bool) :
    subroutine.tapeOf (inputWord x y) (x.length+y.length+2)=Sym.blank := by
  have he : x.length+y.length+2=(x.length+y.length+1)+1 := by omega
  rw [he]
  change (inputWord x y).getD (x.length+y.length+1) Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by rw [input_length])

private theorem reverse_read (x : List Bool) (j : ℕ) (hj : j < x.length) :
    subroutine.tapeOf (reverseWord x) (j+1)=subroutine.bitSym ((x.reverse)[j]'(by simpa using hj)) := by
  change (reverseWord x).getD j Sym.blank=_
  rw [reverseWord,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem reverse_blank (x : List Bool) :
    subroutine.tapeOf (reverseWord x) (x.length+1)=Sym.blank := by
  change (reverseWord x).getD x.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp [reverseWord])

private theorem tape_not_start (w : List Sym) (hw : ∀ a ∈ w, a≠Sym.start) (j : ℕ) :
    subroutine.tapeOf w (j+1)≠Sym.start := by
  change w.getD j Sym.blank≠Sym.start
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hw _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem reverse_not_start (x : List Bool) (j : ℕ) (hj : 0 < j) :
    subroutine.tapeOf (reverseWord x) j≠Sym.start := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  apply tape_not_start
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact bit_not_start b

private theorem request_not_start (x y : List Bool) (j : ℕ) (hj : 0 < j) :
    subroutine.tapeOf (requestWord x y) j≠Sym.start := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  apply tape_not_start
  intro a ha
  simp only [requestWord,reverseWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,hb,rfl⟩|rfl|⟨b,hb,rfl⟩
  · exact bit_not_start b
  · decide
  · exact bit_not_start b

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

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem relay_cfg_ext (c d : subroutine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem relay_safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases h : s=Sym.start <;> simp [safeStep,h]

private theorem relay_safe_left (s : Sym) (h : s≠Sym.start) : safeStep s s .left=(s,.left) := by
  simp [safeStep,h]

private theorem align_input_not_sep (x y : List Bool) (j : ℕ) (hj : j < x.length+1) :
    (alignFrame x y j).cells 0 ((alignFrame x y j).head 0)≠Sym.sep := by
  change subroutine.tapeOf (inputWord x y) j≠Sym.sep
  cases j with
  | zero => change Sym.start≠Sym.sep; decide
  | succ j => rw [input_read x y j (by omega)]; exact bit_not_sep _

private theorem align_step (x y : List Bool) (j : ℕ) (hj : j < x.length+1) :
    subroutine.step (alignFrame x y j)=alignFrame x y (j+1) := by
  let a : Fin 6 → Sym := fun i => (alignFrame x y j).cells i ((alignFrame x y j).head i)
  have h₀ : a 0≠Sym.sep := align_input_not_sep x y j hj
  have h₂ : a 2≠Sym.start := reverse_not_start x (x.length+1-j) (by omega)
  have ht : transition (relayState .align) a=(relayState .align,
      fun i => (a i,if i=0 then Move.right else if i=2 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    rw [if_neg (by exact fun h => h₀ h.1)]
    congr 1
    funext i
    fin_cases i
    · exact relay_safe_right _
    · exact safe_stay _
    · exact relay_safe_left _ h₂
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
  change transition (alignFrame x y j).state
    (fun i => (alignFrame x y j).cells i ((alignFrame x y j).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [alignFrame,relayFrame] <;> omega

private theorem align_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length+1) :
    subroutine.step^[j] (alignFrame x y 0)=alignFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),align_step x y j (by omega)]

private theorem align_turn (x y : List Bool) :
    subroutine.step (alignFrame x y (x.length+1))=copyReverseFrame x y 0 := by
  let a : Fin 6 → Sym := fun i => (alignFrame x y (x.length+1)).cells i
    ((alignFrame x y (x.length+1)).head i)
  have h₀ : a 0=Sym.sep := input_sep x y
  have h₂ : a 2=Sym.start := by simp [a,alignFrame,relayFrame,MultitapeTM.tapeOf]
  have ht : transition (relayState .align) a=(relayState .copyReverse,
      fun i => (a i,if i=2 ∨ i=3 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    rw [if_pos ⟨h₀,h₂⟩]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact relay_safe_right _
    · exact relay_safe_right _
    · exact safe_stay _
    · exact safe_stay _
  change transition (alignFrame x y (x.length+1)).state
    (fun i => (alignFrame x y (x.length+1)).cells i
      ((alignFrame x y (x.length+1)).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [alignFrame,copyReverseFrame,relayFrame]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [alignFrame,copyReverseFrame,relayFrame]

private theorem align_complete (x y : List Bool) :
    subroutine.step^[x.length+2] (alignFrame x y 0)=copyReverseFrame x y 0 := by
  rw [show x.length+2=(x.length+1)+1 by omega,Function.iterate_succ_apply',
    align_run x y (x.length+1) le_rfl,align_turn]

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem copy_reverse_transition (a : Fin 6 → Sym) (b : Bool)
    (hi : a 2=subroutine.bitSym b) (ho : a 3=Sym.blank) :
    transition (relayState .copyReverse) a=(relayState .copyReverse,
      fun i => (if i=3 then a 2 else a i,if i=2 ∨ i=3 then Move.right else Move.stay)) := by
  have hb : a 2=Sym.zero ∨ a 2=Sym.one := by rw [hi]; cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · exact relay_safe_right _
  · cases b <;> simp [ho,hi,safeStep,MultitapeTM.bitSym]
  · exact safe_stay _
  · exact safe_stay _

private theorem copy_reverse_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    subroutine.step (copyReverseFrame x y j)=copyReverseFrame x y (j+1) := by
  let b := (x.reverse)[j]'(by simpa using hj)
  have hi : (copyReverseFrame x y j).cells 2 ((copyReverseFrame x y j).head 2)=
      subroutine.bitSym b := reverse_read x j hj
  have hl : ((x.reverse.take j).map subroutine.bitSym).length=j := by simp;omega
  have ho : (copyReverseFrame x y j).cells 3 ((copyReverseFrame x y j).head 3)=Sym.blank := by
    change ((x.reverse.take j).map subroutine.bitSym).getD j Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ hl.le
  have ht := copy_reverse_transition (fun i => (copyReverseFrame x y j).cells i
    ((copyReverseFrame x y j).head i)) b hi ho
  change transition (copyReverseFrame x y j).state
    (fun i => (copyReverseFrame x y j).cells i ((copyReverseFrame x y j).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf ((x.reverse.take j).map subroutine.bitSym))
        (j+1) ((copyReverseFrame x y j).cells 2 ((copyReverseFrame x y j).head 2))=
          subroutine.tapeOf ((x.reverse.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one ((x.reverse.take j).map subroutine.bitSym) (subroutine.bitSym b)
      rw [hl] at hw
      rw [List.take_succ_eq_append_getElem (by simpa using hj),List.map_append,List.map_singleton]
      exact hw
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyReverseFrame,relayFrame] <;> omega

private theorem copy_reverse_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    subroutine.step^[j] (copyReverseFrame x y 0)=copyReverseFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_reverse_step x y j (by omega)]

private theorem reverse_separator_step (x y : List Bool) :
    subroutine.step (copyReverseFrame x y x.length)=descriptorFrame x y 0 := by
  let a : Fin 6 → Sym := fun i => (copyReverseFrame x y x.length).cells i
    ((copyReverseFrame x y x.length).head i)
  have hi : a 2=Sym.blank := reverse_blank x
  have ho : a 3=Sym.blank := by
    change ((x.reverse.take x.length).map subroutine.bitSym).getD x.length Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ (by simp)
  have ht : transition (relayState .copyReverse) a=(relayState .copyDescriptor,
      fun i => (if i=3 then Sym.sep else a i,if i=0 ∨ i=3 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    fin_cases i
    · exact relay_safe_right _
    · exact safe_stay _
    · exact safe_stay _
    · simp [ho,safeStep]
    · exact safe_stay _
    · exact safe_stay _
  change transition (copyReverseFrame x y x.length).state
    (fun i => (copyReverseFrame x y x.length).cells i
      ((copyReverseFrame x y x.length).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf ((x.reverse.take x.length).map subroutine.bitSym))
        (x.length+1) Sym.sep=subroutine.tapeOf (reverseWord x++[Sym.sep])
      rw [List.take_of_length_le (by simp)]
      have hw := tape_append_one (reverseWord x) Sym.sep
      simpa only [reverseWord,List.length_map,List.length_reverse] using hw
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [copyReverseFrame,descriptorFrame,relayFrame] <;> omega

private theorem copy_descriptor_transition (a : Fin 6 → Sym) (b : Bool)
    (hi : a 0=subroutine.bitSym b) (ho : a 3=Sym.blank) :
    transition (relayState .copyDescriptor) a=(relayState .copyDescriptor,
      fun i => (if i=3 then a 0 else a i,if i=0 ∨ i=3 then Move.right else Move.stay)) := by
  have hb : a 0=Sym.zero ∨ a 0=Sym.one := by rw [hi]; cases b <;> decide
  simp only [transition,rawTransition,relayState,relayRaw,if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact relay_safe_right _
  · exact safe_stay _
  · exact safe_stay _
  · cases b <;> simp [ho,hi,safeStep,MultitapeTM.bitSym]
  · exact safe_stay _
  · exact safe_stay _

private theorem copy_descriptor_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    subroutine.step (descriptorFrame x y j)=descriptorFrame x y (j+1) := by
  have hi : (descriptorFrame x y j).cells 0 ((descriptorFrame x y j).head 0)=
      subroutine.bitSym y[j] := input_descriptor x y j hj
  let w := reverseWord x++Sym.sep::(y.take j).map subroutine.bitSym
  have hl : w.length=x.length+j+1 := by simp [w,reverseWord];omega
  have ho : (descriptorFrame x y j).cells 3 ((descriptorFrame x y j).head 3)=Sym.blank := by
    change subroutine.tapeOf w (x.length+j+2)=Sym.blank
    rw [show x.length+j+2=(x.length+j+1)+1 by omega]
    exact List.getD_eq_default _ _ hl.le
  have ht := copy_descriptor_transition (fun i => (descriptorFrame x y j).cells i
    ((descriptorFrame x y j).head i)) y[j] hi ho
  change transition (descriptorFrame x y j).state
    (fun i => (descriptorFrame x y j).cells i ((descriptorFrame x y j).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · change Function.update (subroutine.tapeOf w) (x.length+j+2)
        ((descriptorFrame x y j).cells 0 ((descriptorFrame x y j).head 0))=
        subroutine.tapeOf (reverseWord x++Sym.sep::(y.take (j+1)).map subroutine.bitSym)
      rw [hi]
      have hw := tape_append_one w (subroutine.bitSym y[j])
      rw [hl,show x.length+j+1+1=x.length+j+2 by omega] at hw
      rw [List.take_succ_eq_append_getElem hj,List.map_append,List.map_singleton]
      simpa only [w,List.append_assoc,List.cons_append] using hw
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [descriptorFrame,relayFrame] <;> omega

private theorem copy_descriptor_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    subroutine.step^[j] (descriptorFrame x y 0)=descriptorFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),copy_descriptor_step x y j (by omega)]

private theorem descriptor_rewind_step (x y : List Bool) :
    subroutine.step (descriptorFrame x y y.length)=rewindFrame x y (x.length+y.length+1) := by
  let a : Fin 6 → Sym := fun i => (descriptorFrame x y y.length).cells i
    ((descriptorFrame x y y.length).head i)
  have hi : a 0=Sym.blank := input_blank x y
  have ho : a 3≠Sym.start := by
    change subroutine.tapeOf (reverseWord x++Sym.sep::(y.take y.length).map subroutine.bitSym)
      (x.length+y.length+2)≠Sym.start
    simpa [requestWord] using request_not_start x y (x.length+y.length+2) (by omega)
  have ht : transition (relayState .copyDescriptor) a=(relayState .rewind,
      fun i => (a i,if i=3 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw,hi]
    rw [if_neg (by decide : ¬(Sym.blank=Sym.zero ∨ Sym.blank=Sym.one))]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact relay_safe_left _ ho
    · exact safe_stay _
    · exact safe_stay _
  change transition (descriptorFrame x y y.length).state
    (fun i => (descriptorFrame x y y.length).cells i
      ((descriptorFrame x y y.length).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [descriptorFrame,rewindFrame,relayFrame,requestWord]
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [descriptorFrame,rewindFrame,relayFrame] <;> omega

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

open TapeCopy (Sym)
open TapeAdder (safe_stay)

private theorem rewind_step (x y : List Bool) (j : ℕ) :
    subroutine.step (rewindFrame x y (j+1))=rewindFrame x y j := by
  let a : Fin 6 → Sym := fun i => (rewindFrame x y (j+1)).cells i
    ((rewindFrame x y (j+1)).head i)
  have ho : a 3≠Sym.start := request_not_start x y (j+1) (by omega)
  have ht : transition (relayState .rewind) a=(relayState .rewind,
      fun i => (a i,if i=3 then Move.left else Move.stay)) := by
    simp only [transition,rawTransition,relayState,relayRaw]
    rw [if_neg ho]
    congr 1
    funext i
    fin_cases i
    · exact safe_stay _
    · exact safe_stay _
    · exact safe_stay _
    · exact relay_safe_left _ ho
    · exact safe_stay _
    · exact safe_stay _
  change transition (rewindFrame x y (j+1)).state
    (fun i => (rewindFrame x y (j+1)).cells i ((rewindFrame x y (j+1)).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [rewindFrame,relayFrame]

private theorem rewind_run (x y : List Bool) (j : ℕ) :
    subroutine.step^[j] (rewindFrame x y j)=rewindFrame x y 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply,rewind_step,ih]

private theorem rewind_halt_step (x y : List Bool) :
    subroutine.step (rewindFrame x y 0)=relayFinal x y := by
  let a : Fin 6 → Sym := fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i)
  have ho : a 3=Sym.start := rfl
  have ht : transition (relayState .rewind) a=(none,fun i => (a i,Move.stay)) := by
    simp [transition,rawTransition,relayState,relayRaw,ho,safe_stay]
  change transition (rewindFrame x y 0).state
    (fun i => (rewindFrame x y 0).cells i ((rewindFrame x y 0).head i))=_ at ht
  apply relay_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]; rfl

private theorem rewind_complete (x y : List Bool) (j : ℕ) :
    subroutine.step^[j+1] (rewindFrame x y j)=relayFinal x y := by
  rw [Function.iterate_succ_apply',rewind_run,rewind_halt_step]

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

private theorem copy_reverse_complete (x y : List Bool) :
    subroutine.step^[x.length+1] (copyReverseFrame x y 0)=descriptorFrame x y 0 := by
  rw [Function.iterate_succ_apply',copy_reverse_run x y x.length le_rfl,reverse_separator_step]

private theorem copy_descriptor_complete (x y : List Bool) :
    subroutine.step^[y.length+1] (descriptorFrame x y 0)=rewindFrame x y (x.length+y.length+1) := by
  rw [Function.iterate_succ_apply',copy_descriptor_run x y y.length le_rfl,descriptor_rewind_step]

/-- All real relay transitions, including delimiter writing and complete
rewinding of the routed request, are charged. -/
private theorem relay_complete (x y : List Bool) :
    subroutine.step^[3*x.length+2*y.length+6] (alignFrame x y 0)=relayFinal x y := by
  have h₂ : subroutine.step^[(x.length+1)+(x.length+2)] (alignFrame x y 0)=
      descriptorFrame x y 0 := by
    rw [Function.iterate_add_apply,align_complete,copy_reverse_complete]
  have h₃ : subroutine.step^[(y.length+1)+((x.length+1)+(x.length+2))] (alignFrame x y 0)=
      rewindFrame x y (x.length+y.length+1) := by
    rw [Function.iterate_add_apply,h₂,copy_descriptor_complete]
  rw [show 3*x.length+2*y.length+6=
    (x.length+y.length+2)+((y.length+1)+((x.length+1)+(x.length+2))) by omega,
    Function.iterate_add_apply,h₃]
  exact rewind_complete x y (x.length+y.length+1)

private theorem reverse_to_relay (x y : List Bool) :
    {reverseView (TapeReverse.frame x y 0 .halt) with state := relayState .align}=
      alignFrame x y 0 := by
  apply relay_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [reverseView,TapeReverse.frame,alignFrame,relayFrame,inputWord,reverseWord] <;> rfl
  · funext i
    fin_cases i <;> simp [reverseView,TapeReverse.frame,alignFrame,relayFrame]

private theorem relay_to_split (x y : List Bool) :
    {relayFinal x y with state := splitState CountedBlockSplitter.machine.qStart}=
      splitView x y (CountedBlockSplitter.machine.initCfg x.reverse y) := by
  apply relay_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [relayFinal,rewindFrame,relayFrame,splitView,MultitapeTM.initCfg,
      MultitapeTM.inTape,inputWord,reverseWord,requestWord] <;> rfl
  · funext i
    fin_cases i <;> simp [relayFinal,rewindFrame,relayFrame,splitView,MultitapeTM.initCfg]

end IntMul.ReversedBlockRouter



namespace IntMul.ReversedBlockRouter

private theorem outer_cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem outer_init (x y : List Bool) :
    machine.initCfg x y=FiniteCaller.embed subroutine Phase .reverse .reverse dispatch
      (reverseView (TapeReverse.machine.initCfg x y)) := by
  rw [←reverse_init]
  rfl

private theorem after_reverse (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .reverse dispatch
      (reverseView (TapeReverse.frame x y 0 .halt))=
    FiniteCaller.embed subroutine Phase .reverse .transfer dispatch (alignFrame x y 0) := by
  have h := reverse_to_relay x y
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply outer_cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem after_transfer (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .transfer dispatch (relayFinal x y)=
    FiniteCaller.embed subroutine Phase .reverse .split dispatch
      (splitView x y (CountedBlockSplitter.machine.initCfg x.reverse y)) := by
  have h := relay_to_split x y
  have hc := congrArg (fun c : subroutine.Cfg => c.cells) h
  have hh := congrArg (fun c : subroutine.Cfg => c.head) h
  apply outer_cfg_ext
  · rfl
  · exact hc
  · exact hh

private theorem after_split (x y : List Bool) :
    FiniteCaller.returned subroutine Phase .reverse .split dispatch
      (splitView x y (CountedBlockSplitter.frame x.reverse y x.reverse.length none))=
    finalFrame x y := by
  apply outer_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,splitView,CountedBlockSplitter.frame,finalFrame] <;> rfl
  · funext i
    fin_cases i <;> simp [FiniteCaller.returned,splitView,CountedBlockSplitter.frame,finalFrame]

/-- One actual fixed six-tape machine reverses, physically routes and splits
the first operand into low-significance-first blocks. All three returns and
every relay, descriptor copy and rewind transition are charged. -/
private theorem route_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 13*x.length+((x.length-1)/CountedBlockSplitter.blockSize y)*(4*y.length+4)+
        10*y.length+23 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt := by
  have hr : subroutine.step^[2*x.length+3]
      (reverseView (TapeReverse.machine.initCfg x y))=
      reverseView (TapeReverse.frame x y 0 .halt) := by
    rw [reverse_run,(TapeReverse.reverse_first_operand x y).2]
  obtain ⟨a,ha,hea⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .reverse dispatch
    (reverseView (TapeReverse.machine.initCfg x y)) (2*x.length+3)).2 (by rw [hr]; rfl)
  rw [hr,after_reverse] at hea
  obtain ⟨b,hb,heb⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .transfer dispatch
    (alignFrame x y 0) (3*x.length+2*y.length+6)).2 (by rw [relay_complete]; rfl)
  rw [relay_complete,after_transfer] at heb
  obtain ⟨s,hs,hes,hh⟩ := CountedBlockSplitter.split_blocks x.reverse y
  have hsplit : subroutine.step^[s]
      (splitView x y (CountedBlockSplitter.machine.initCfg x.reverse y))=
      splitView x y (CountedBlockSplitter.frame x.reverse y x.reverse.length none) := by
    rw [split_run,hes]
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Phase .reverse .split dispatch
    (splitView x y (CountedBlockSplitter.machine.initCfg x.reverse y)) s).2
      (by rw [hsplit]; rfl)
  rw [hsplit,after_split] at hec
  have he : machine.step^[c+(b+a)] (machine.initCfg x y)=finalFrame x y := by
    rw [Function.iterate_add_apply,Function.iterate_add_apply,outer_init,hea,heb,hec]
  refine ⟨c+(b+a),?_,he,?_⟩
  · simp only [List.length_reverse] at hs
    omega
  · rw [he]; rfl

end IntMul.ReversedBlockRouter



open IntMul IntMul.ReversedBlockRouter

theorem solution (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 13*x.length+((x.length-1)/CountedBlockSplitter.blockSize y)*(4*y.length+4)+
        10*y.length+23 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt :=
  IntMul.ReversedBlockRouter.route_blocks x y

#print axioms solution
