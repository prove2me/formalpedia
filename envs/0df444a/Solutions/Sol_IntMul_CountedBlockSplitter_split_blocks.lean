-- Prove2me | solution 1 for IntMul.CountedBlockSplitter.split_blocks
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T08:38:31.019486+00:00
-- url     : https://prove2.me/submissions/64e9611b-feb3-473e-82ae-93afd39fb1d9

import Definitions.Def_IntMul_CountedBlockSplitter
import Definitions.Def_IntMul_BinaryAdder
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic


namespace IntMul.AllWindowRelocation

/-- Proof-only relocation of every tape, including a moving read-only input.
Each protected prefix remains supplied by the saved target configuration. -/
private def frame (N : MultitapeTM) (base : N.Cfg) (shift lower : Fin N.k → ℕ) (c : N.Cfg) : N.Cfg where
  state := c.state
  cells := fun i p => if p < shift i+lower i then base.cells i p else c.cells i (p-shift i)
  head := fun i => shift i+c.head i

private theorem owned_intmulallwindowrelocation_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem relocate_step (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (positive : ∀ i, shift i≠0 → 1 ≤ lower i) (inside : ∀ i, lower i ≤ c.head i) :
    N.step (frame N base shift lower c)=frame N base shift lower (N.step c) := by
  have hread : (fun i => (frame N base shift lower c).cells i
      ((frame N base shift lower c).head i))=(fun i => c.cells i (c.head i)) := by
    funext i
    have hwindow : ¬shift i+c.head i < shift i+lower i := by have := inside i; omega
    simp only [frame,if_neg hwindow,Nat.add_sub_cancel_left]
  have hdelta : N.δ (frame N base shift lower c).state
      (fun i => (frame N base shift lower c).cells i ((frame N base shift lower c).head i))=
      N.δ c.state (fun i => c.cells i (c.head i)) := by
    change N.δ c.state _=N.δ c.state _
    rw [hread]
  apply owned_intmulallwindowrelocation_cfg_ext
  · change (N.δ (frame N base shift lower c).state _).1=(N.δ c.state _).1
    rw [hdelta]
  · funext i p
    change Function.update ((frame N base shift lower c).cells i)
      ((frame N base shift lower c).head i)
      ((N.δ (frame N base shift lower c).state _).2 i).1 p=_
    rw [hdelta]
    simp only [frame]
    change Function.update
      (fun p => if p < shift i+lower i then base.cells i p else c.cells i (p-shift i))
      (shift i+c.head i) ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).1 p=
      (if p < shift i+lower i then base.cells i p else
        Function.update (c.cells i) (c.head i)
          ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).1 (p-shift i))
    by_cases hp : p < shift i+lower i
    · have hne : p≠shift i+c.head i := by have := inside i; omega
      simp only [Function.update_of_ne hne,if_pos hp]
    · by_cases heq : p=shift i+c.head i
      · subst p
        rw [Function.update_self,if_neg hp,Nat.add_sub_cancel_left,Function.update_self]
      · have hne : p-shift i≠c.head i := by omega
        simp only [Function.update_of_ne heq,if_neg hp,Function.update_of_ne hne]
  · funext i
    change (match ((N.δ (frame N base shift lower c).state _).2 i).2 with
      | Move.left => (frame N base shift lower c).head i-1
      | Move.stay => (frame N base shift lower c).head i
      | Move.right => (frame N base shift lower c).head i+1)=_
    rw [hdelta]
    simp only [frame]
    change (match ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => shift i+c.head i-1
      | Move.stay => shift i+c.head i
      | Move.right => shift i+c.head i+1)=
      shift i+(match ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 with
      | Move.left => c.head i-1
      | Move.stay => c.head i
      | Move.right => c.head i+1)
    have hzero : shift i=0 ∨ 1 ≤ c.head i := by
      by_cases hs : shift i=0
      · exact Or.inl hs
      · have := positive i hs
        have := inside i
        exact Or.inr (by omega)
    cases hmove : ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 <;>
      simp only [hmove] <;> omega

private theorem relocate_run (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (T : ℕ) (positive : ∀ i, shift i≠0 → 1 ≤ lower i)
    (inside : ∀ t, t < T → ∀ i, lower i ≤ (N.step^[t] c).head i) :
    N.step^[T] (frame N base shift lower c)=frame N base shift lower (N.step^[T] c) := by
  have hrun : ∀ t, t ≤ T → N.step^[t] (frame N base shift lower c)=
      frame N base shift lower (N.step^[t] c) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply',ih (by omega),Function.iterate_succ_apply']
      exact relocate_step N base _ shift lower positive (inside t (by omega))
  exact hrun T (by omega)

end IntMul.AllWindowRelocation



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep)

private theorem owned_intmulcountedstreamoutputwindow_safe_no_left (s w : Sym) (d : Move) (h : d≠Move.left) :
    (safeStep s w d).2≠Move.left := by
  cases d with
  | left => exact False.elim (h rfl)
  | stay => by_cases hs : s=Sym.start <;> simp [safeStep,hs]
  | right => by_cases hs : s=Sym.start <;> simp [safeStep,hs]

private theorem owned_intmulcountedstreamoutputwindow_raw_output_no_left (q : State) (a : Fin 4 → Sym) :
    ((rawTransition q a).2 1).2≠Move.left := by
  cases q <;> simp only [rawTransition]
  all_goals try split_ifs
  all_goals simp_all

private theorem owned_intmulcountedstreamoutputwindow_output_no_left (q : State) (a : Fin 4 → Sym) :
    ((transition q a).2 1).2≠Move.left := by
  apply owned_intmulcountedstreamoutputwindow_safe_no_left
  exact owned_intmulcountedstreamoutputwindow_raw_output_no_left q a

private theorem output_head_monotone (c : machine.Cfg) : c.head 1 ≤ (machine.step c).head 1 := by
  change c.head 1 ≤ (match ((transition c.state (fun i => c.cells i (c.head i))).2 1).2 with
    | Move.left => c.head 1-1
    | Move.stay => c.head 1
    | Move.right => c.head 1+1)
  have hn := owned_intmulcountedstreamoutputwindow_output_no_left c.state (fun i => c.cells i (c.head i))
  cases h : ((transition c.state (fun i => c.cells i (c.head i))).2 1).2
  · exact False.elim (hn h)
  · simp
  · simp

private theorem output_run_monotone (c : machine.Cfg) (t : ℕ) :
    c.head 1 ≤ (machine.step^[t] c).head 1 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans ih (output_head_monotone _)

/-- Reuse an actual counted stream trace at a translated output cursor,
retaining arbitrary previous output and moving the input head exactly as before. -/
private theorem output_window_run (base c : machine.Cfg) (shift lower T : ℕ)
    (positive : 1 ≤ lower) (inside : lower ≤ c.head 1) :
    machine.step^[T] (AllWindowRelocation.frame machine base
      (fun i => if i=1 then shift else 0) (fun i => if i=1 then lower else 0) c)=
    AllWindowRelocation.frame machine base
      (fun i => if i=1 then shift else 0) (fun i => if i=1 then lower else 0)
      (machine.step^[T] c) := by
  apply AllWindowRelocation.relocate_run
  · intro i hi
    by_cases h : i=1
    · simpa only [if_pos h] using positive
    · simp only [if_neg h] at hi
      contradiction
  · intro t ht i
    by_cases h : i=1
    · subst i
      simp only [if_true]
      exact le_trans inside (output_run_monotone c t)
    · simp only [if_neg h]
      exact Nat.zero_le _

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

/-- Full live stream configuration, including emitted prefix and saved template. -/
private def streamFrame (x y bits : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((x.take j).map machine.bitSym)
    else if i = 2 then machine.tapeOf (Sym.sep :: (bits.reverse.map machine.bitSym ++ [Sym.sep]))
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
  head := fun i => if i = 0 ∨ i = 1 then j + 1 else y.length + 1

private def owned_intmulcountedstreamsetup_scanXFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .scanX
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym) else machine.tapeOf []
  head := fun i => if i = 0 then j + 1 else 1

private def owned_intmulcountedstreamsetup_copyYFrame (x y : List Bool) (j : ℕ) : machine.Cfg where
  state := .copyY
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.take j).map machine.bitSym)
    else machine.tapeOf []
  head := fun i => if i = 0 then x.length + 2 + j else if i = 2 ∨ i = 3 then j + 2 else 1

private def owned_intmulcountedstreamsetup_rewindInputFrame (x y : List Bool) (p : ℕ) : machine.Cfg where
  state := .rewindInput
  cells := fun i => if i = 0 then
    machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 2 ∨ i = 3 then machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
    else machine.tapeOf []
  head := fun i => if i = 0 then p else if i = 2 ∨ i = 3 then y.length + 1 else 1

private theorem owned_intmulcountedstreamsetup_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamsetup_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamsetup_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamsetup_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
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
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem owned_intmulcountedstreamsetup_initial_transition (a : Fin 4 → Sym) :
    transition .start a = (.scanX, fun i => (a i, .right)) := by
  simp [transition, rawTransition, owned_intmulcountedstreamsetup_safe_right]

private theorem owned_intmulcountedstreamsetup_setup_start (x y : List Bool) :
    machine.step (machine.initCfg x y) = owned_intmulcountedstreamsetup_scanXFrame x y 0 := by
  have ht := owned_intmulcountedstreamsetup_initial_transition (fun i => (machine.initCfg x y).cells i 0)
  change transition (machine.initCfg x y).state
    (fun i => (machine.initCfg x y).cells i ((machine.initCfg x y).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update (machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym))
        0 Sym.start = machine.tapeOf (x.map machine.bitSym ++ machine.sep :: y.map machine.bitSym)
      exact Function.update_eq_self 0 _
    all_goals
      change Function.update (machine.tapeOf []) 0 Sym.start = machine.tapeOf []
      exact Function.update_eq_self 0 _
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> rfl

private theorem owned_intmulcountedstreamsetup_scan_bit_transition (a : Fin 4 → Sym)
    (h : a 0 = .zero ∨ a 0 = .one) :
    transition .scanX a = (.scanX, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, owned_intmulcountedstreamsetup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_scan_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (owned_intmulcountedstreamsetup_scanXFrame x y j) = owned_intmulcountedstreamsetup_scanXFrame x y (j + 1) := by
  have hr : (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = Sym.zero ∨
      (owned_intmulcountedstreamsetup_scanXFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y j).head 0) = Sym.one := by
    rw [hr]
    cases x[j] <;> decide
  have ht := owned_intmulcountedstreamsetup_scan_bit_transition
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) hb
  change transition (owned_intmulcountedstreamsetup_scanXFrame x y j).state
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_scanXFrame x y j).cells i) ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)
      ((owned_intmulcountedstreamsetup_scanXFrame x y j).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y j).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [owned_intmulcountedstreamsetup_scanXFrame, hi]

private theorem owned_intmulcountedstreamsetup_scan_run (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    machine.step^[j + 1] (machine.initCfg x y) = owned_intmulcountedstreamsetup_scanXFrame x y j := by
  induction j with
  | zero => simpa using owned_intmulcountedstreamsetup_setup_start x y
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamsetup_scan_step x y j (by omega)]


private theorem owned_intmulcountedstreamsetup_scan_end_transition (a : Fin 4 → Sym) (hs : a 0 = .sep)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .scanX a = (.copyY, fun i =>
      (if i = 2 ∨ i = 3 then .sep else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, hs]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamsetup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .right = (Sym.sep, .right)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .right = (Sym.sep, .right)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem owned_intmulcountedstreamsetup_scan_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_scanXFrame x y x.length) = owned_intmulcountedstreamsetup_copyYFrame x y 0 := by
  have hs : (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp [owned_intmulcountedstreamsetup_scanXFrame, h0, MultitapeTM.tapeOf]
  have ht := owned_intmulcountedstreamsetup_scan_end_transition
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i)) hs hw
  change transition (owned_intmulcountedstreamsetup_scanXFrame x y x.length).state
    (fun i => (owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells i ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0) ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0)
        ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).cells 0 ((owned_intmulcountedstreamsetup_scanXFrame x y x.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf []) 1 Sym.sep = machine.tapeOf [Sym.sep]
      exact owned_intmulcountedstreamsetup_tapeOf_append_one machine [] Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_scanXFrame, owned_intmulcountedstreamsetup_copyYFrame]

private theorem owned_intmulcountedstreamsetup_copy_bit_transition (a : Fin 4 → Sym) (b : Bool) (hb : a 0 = machine.bitSym b)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .copyY a = (.copyY, fun i =>
      (if i = 2 ∨ i = 3 then machine.bitSym b else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamsetup_safe_right _
  · exact safe_stay _
  · change safeStep (a 2) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 2 (Or.inl rfl), hb]
    cases b <;> decide
  · change safeStep (a 3) (a 0) .right = (machine.bitSym b, .right)
    rw [hw 3 (Or.inr rfl), hb]
    cases b <;> decide

private theorem owned_intmulcountedstreamsetup_copy_step (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    machine.step (owned_intmulcountedstreamsetup_copyYFrame x y j) = owned_intmulcountedstreamsetup_copyYFrame x y (j + 1) := by
  have hl : (Sym.sep :: (y.take j).map machine.bitSym).length = j + 1 := by
    simp [Nat.min_eq_left hj.le]
  have hr : (owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0) = machine.bitSym y[j] := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)) (x.length + 2 + j) = _
    rw [show x.length + 2 + j = (x.length + 1 + j) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, show x.length + 1 + j - x.length = j + 1 by omega, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [owned_intmulcountedstreamsetup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take j).map machine.bitSym).getD (j + 1) machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcountedstreamsetup_copy_bit_transition
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i)) y[j] hr hw
  change transition (owned_intmulcountedstreamsetup_copyYFrame x y j).state
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y j).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y j).head i)) = _ at ht
  have hnew : Sym.sep :: (y.take (j + 1)).map machine.bitSym =
      (Sym.sep :: (y.take j).map machine.bitSym) ++ [machine.bitSym y[j]] := by
    rw [List.take_succ_eq_append_getElem hj, List.map_append]
    rfl
  have hwrite := owned_intmulcountedstreamsetup_tapeOf_append_one machine (Sym.sep :: (y.take j).map machine.bitSym) (machine.bitSym y[j])
  rw [hl] at hwrite
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0) ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0)
        ((owned_intmulcountedstreamsetup_copyYFrame x y j).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y j).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf (Sym.sep :: (y.take j).map machine.bitSym)) (j + 2)
        (machine.bitSym y[j]) = machine.tapeOf (Sym.sep :: (y.take (j + 1)).map machine.bitSym)
      rw [hnew]
      exact hwrite
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_copyYFrame] <;> omega

private theorem owned_intmulcountedstreamsetup_copy_run (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    machine.step^[j] (owned_intmulcountedstreamsetup_copyYFrame x y 0) = owned_intmulcountedstreamsetup_copyYFrame x y j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamsetup_copy_step x y j (by omega)]


private theorem owned_intmulcountedstreamsetup_copy_end_transition (a : Fin 4 → Sym) (hs : a 0 = .blank)
    (hw : ∀ i : Fin 4, i = 2 ∨ i = 3 → a i = .blank) :
    transition .copyY a = (.rewindInput, fun i =>
      (if i = 2 ∨ i = 3 then .sep else a i,
        if i = 0 ∨ i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hs]
  rw [if_neg (by decide : ¬(Sym.blank = Sym.zero ∨ Sym.blank = Sym.one))]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .left = (a 0, .left)
    rw [hs]
    exact owned_intmulcountedstreamsetup_safe_left _ (by decide)
  · exact safe_stay _
  · change safeStep (a 2) Sym.sep .left = (Sym.sep, .left)
    rw [hw 2 (Or.inl rfl)]
    decide
  · change safeStep (a 3) Sym.sep .left = (Sym.sep, .left)
    rw [hw 3 (Or.inr rfl)]
    decide

private theorem owned_intmulcountedstreamsetup_copy_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_copyYFrame x y y.length) = owned_intmulcountedstreamsetup_rewindInputFrame x y (x.length + y.length + 1) := by
  have hs : (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0) = Sym.blank := by
    change (machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym))
      (x.length + 2 + y.length) = _
    rw [show x.length + 2 + y.length = (x.length + 1 + y.length) + 1 by omega]
    simp only [MultitapeTM.tapeOf]
    exact List.getD_eq_default _ _ (by simp; omega)
  have hw : ∀ i : Fin 4, i = 2 ∨ i = 3 →
      (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i) = Sym.blank := by
    intro i hi
    have h0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
    simp only [owned_intmulcountedstreamsetup_copyYFrame, if_neg h0, if_pos hi]
    change (Sym.sep :: (y.take y.length).map machine.bitSym).getD (y.length + 1) machine.blank = _
    rw [List.take_length]
    exact List.getD_eq_default _ _ (by simp)
  have ht := owned_intmulcountedstreamsetup_copy_end_transition
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i)) hs hw
  change transition (owned_intmulcountedstreamsetup_copyYFrame x y y.length).state
    (fun i => (owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells i ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0) ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0)
        ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).cells 0 ((owned_intmulcountedstreamsetup_copyYFrame x y y.length).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf []) 1 ((machine.tapeOf []) 1) = machine.tapeOf []
      exact Function.update_eq_self _ _
    all_goals
      change Function.update (machine.tapeOf (Sym.sep :: (y.take y.length).map machine.bitSym))
        (y.length + 2) Sym.sep = machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
      simpa [List.take_length] using owned_intmulcountedstreamsetup_tapeOf_append_one machine (Sym.sep :: y.map machine.bitSym) Sym.sep
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_copyYFrame, owned_intmulcountedstreamsetup_rewindInputFrame] <;> omega

private theorem owned_intmulcountedstreamsetup_input_getD_ne_start (x y : List Bool) (p : ℕ) :
    (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD p machine.blank ≠ Sym.start := by
  let w := x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym
  have hw : ∀ a ∈ w, a ≠ Sym.start := by
    intro a ha
    rcases List.mem_append.mp ha with hx | hy
    · rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
      cases b <;> decide
    · rcases List.mem_cons.mp hy with hs | hy
      · subst a; decide
      · rcases List.mem_map.mp hy with ⟨b, _, rfl⟩
        cases b <;> decide
  change w.getD p machine.blank ≠ Sym.start
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact hw _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

private theorem owned_intmulcountedstreamsetup_rewind_transition (a : Fin 4 → Sym) (h : a 0 ≠ .start) :
    transition .rewindInput a = (.rewindInput, fun i => (a i, if i = 0 then .left else .stay)) := by
  simp only [transition, rawTransition, if_neg h]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    exact owned_intmulcountedstreamsetup_safe_left _ h
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_rewind_step (x y : List Bool) (p : ℕ) :
    machine.step (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)) = owned_intmulcountedstreamsetup_rewindInputFrame x y p := by
  have hn : (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells 0 ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head 0) ≠ Sym.start :=
    owned_intmulcountedstreamsetup_input_getD_ne_start x y p
  have ht := owned_intmulcountedstreamsetup_rewind_transition
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) hn
  change transition (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).state
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i) ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)
      ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y (p + 1)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 0 <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, hi]

private theorem owned_intmulcountedstreamsetup_rewind_run (x y : List Bool) (p : ℕ) :
    machine.step^[p] (owned_intmulcountedstreamsetup_rewindInputFrame x y p) = owned_intmulcountedstreamsetup_rewindInputFrame x y 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply, owned_intmulcountedstreamsetup_rewind_step, ih]

private theorem owned_intmulcountedstreamsetup_rewind_end_transition (a : Fin 4 → Sym) (h : a 0 = .start) :
    transition .rewindInput a = (.emit, fun i => (a i, if i = 0 then .right else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [if_pos hi, owned_intmulcountedstreamsetup_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamsetup_rewind_end (x y : List Bool) :
    machine.step (owned_intmulcountedstreamsetup_rewindInputFrame x y 0) = streamFrame x y y.reverse 0 .emit := by
  have hs : (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells 0 ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head 0) = Sym.start := rfl
  have ht := owned_intmulcountedstreamsetup_rewind_end_transition
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) hs
  change transition (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).state
    (fun i => (owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) = _ at ht
  apply owned_intmulcountedstreamsetup_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i) ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)
      ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).cells i ((owned_intmulcountedstreamsetup_rewindInputFrame x y 0).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, streamFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [owned_intmulcountedstreamsetup_rewindInputFrame, streamFrame]

/-- Exact setup cost includes both operand/descriptor scans, the saved copy,
separator writes, and the input-head return to the first payload bit. -/
private theorem setup_correct (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      streamFrame x y y.reverse 0 .emit := by
  have hscan : machine.step^[x.length + 2] (machine.initCfg x y) = owned_intmulcountedstreamsetup_copyYFrame x y 0 := by
    rw [show x.length + 2 = (x.length + 1) + 1 by omega,
      Function.iterate_succ_apply', owned_intmulcountedstreamsetup_scan_run x y x.length le_rfl, owned_intmulcountedstreamsetup_scan_end]
  have hcopy : machine.step^[x.length + y.length + 3] (machine.initCfg x y) =
      owned_intmulcountedstreamsetup_rewindInputFrame x y (x.length + y.length + 1) := by
    rw [show x.length + y.length + 3 = (y.length + (x.length + 2)) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_add_apply, hscan,
      owned_intmulcountedstreamsetup_copy_run x y y.length le_rfl, owned_intmulcountedstreamsetup_copy_end]
  rw [show 2 * x.length + 2 * y.length + 5 =
      ((x.length + y.length + 1) + (x.length + y.length + 3)) + 1 by omega,
    Function.iterate_succ_apply', Function.iterate_add_apply, hcopy, owned_intmulcountedstreamsetup_rewind_run, owned_intmulcountedstreamsetup_rewind_end]

end IntMul.CountedStream



/-! Decrement arithmetic adapted from the frozen public CounterArithmetic
module, with Boolean direction fixed to decrement and the campaign word value.
The integrated controller and actual campaign-machine trace are separate. -/
namespace IntMul.CountedStream

open IntMul.BinaryAdder (littleVal)

private theorem updated_nil : updated [] = [] := rfl

private theorem updated_zero (bs : List Bool) : updated (false :: bs) = true :: updated bs := by
  simp [updated, carryLength, stopTail, List.replicate_succ]

private theorem updated_one (bs : List Bool) : updated (true :: bs) = false :: bs := by
  simp [updated, carryLength, stopTail]

private theorem updated_length (bits : List Bool) : (updated bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]; simp [ih]
      · rw [updated_one]; rfl

private theorem carry_length_le (bits : List Bool) : carryLength bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [carryLength, List.length_cons]; split_ifs <;> omega

private theorem potential_le (bits : List Bool) : potential bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [potential, List.length_cons]; split_ifs <;> omega

private theorem potential_accounting (bits : List Bool) :
    carryLength bits + potential (updated bits) ≤ potential bits + 1 := by
  induction bits with
  | nil => simp [carryLength, potential, updated_nil]
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [carryLength, potential, if_true, Bool.true_eq_false, if_false]
        omega
      · rw [updated_one]
        simp [carryLength, potential, Nat.add_comm]

private theorem amortized_step (bits : List Bool) :
    counterSteps bits + 2 * potential (updated bits) ≤ 4 + 2 * potential bits := by
  have h := potential_accounting bits
  unfold counterSteps
  omega

private theorem iterate_counter_length (n : ℕ) (bits : List Bool) :
    (iterateCounter n bits).length = bits.length := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => rw [iterateCounter, ih, updated_length]

private theorem amortized_total (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits + 2 * potential (iterateCounter n bits) ≤ 4 * n + 2 * potential bits := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have h := amortized_step bits
      have hn := ih (updated bits)
      simp only [totalCounterSteps, iterateCounter]
      omega

private theorem total_counter_steps_bound (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits ≤ 4 * n + 2 * bits.length := by
  have h := amortized_total n bits
  have hp := potential_le bits
  omega

/-- Exact decrement, including the fixed-width wrap term on underflow. -/
private theorem decrement_value (bits : List Bool) :
    value bits + (if underflow bits then 2 ^ bits.length else 0) = value (updated bits) + 1 := by
  induction bits with
  | nil => simp [updated_nil, value, littleVal, underflow]
  | cons b bs ih =>
      simp only [value] at ih
      cases b
      · rw [updated_zero]
        simp only [value, littleVal, underflow, Bool.toNat_false, Bool.toNat_true,
          if_true, List.length_cons, pow_succ]
        cases ho : underflow bs <;> simp [ho] at ih ⊢ <;> omega
      · simp [updated_one, value, littleVal, underflow, Nat.add_comm]

private theorem underflow_iff_zero (bits : List Bool) : underflow bits = true ↔ value bits = 0 := by
  induction bits with
  | nil => simp [underflow, value, littleVal]
  | cons b bs ih => cases b <;> simp [underflow, value, littleVal, ih]

private theorem underflow_all_ones (bits : List Bool) (h : underflow bits = true) :
    updated bits = List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [underflow, if_true] at h
        rw [ih h, List.length_cons, List.replicate_succ]
      · simp [underflow] at h

private theorem decrement_positive (bits : List Bool) (h : 0 < value bits) :
    underflow bits = false ∧ value (updated bits) + 1 = value bits := by
  have hn : underflow bits ≠ true := by
    intro hflag
    have := (underflow_iff_zero bits).mp hflag
    omega
  have hf : underflow bits = false := by cases hflag : underflow bits <;> simp_all
  refine ⟨hf, ?_⟩
  have hv := decrement_value bits
  simpa [hf] using hv.symm

private theorem countdown_value (bits : List Bool) (n : ℕ) (hn : n ≤ value bits) :
    value (iterateCounter n bits) = value bits - n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hv := (decrement_positive bits hp).2
      have hnext : n ≤ value (updated bits) := by omega
      rw [iterateCounter, ih (updated bits) hnext]
      omega

private theorem countdown_not_finished (bits : List Bool) (n : ℕ) (hn : n < value bits) :
    underflow (iterateCounter n bits) = false := by
  have hv := countdown_value bits n hn.le
  exact (decrement_positive _ (by omega)).1

private theorem countdown_final_underflow (bits : List Bool) :
    underflow (iterateCounter (value bits) bits) = true := by
  apply (underflow_iff_zero _).mpr
  rw [countdown_value bits (value bits) le_rfl]
  omega


private theorem total_counter_steps_succ (n : ℕ) (bits : List Bool) :
    totalCounterSteps (n + 1) bits = totalCounterSteps n bits + counterSteps (iterateCounter n bits) := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      change counterSteps bits + totalCounterSteps (n + 1) (updated bits) =
        (counterSteps bits + totalCounterSteps n (updated bits)) + counterSteps (iterateCounter n (updated bits))
      rw [ih (updated bits)]
      omega

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem owned_intmulcountedstreamcounter_tape_replace_after_prefix (M : MultitapeTM)
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

private theorem owned_intmulcountedstreamcounter_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamcounter_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem owned_intmulcountedstreamcounter_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamcounter_carry_zero_transition (a : Fin 4 → Sym) (h : a 2 = .zero) :
    transition .carry a = (.carry, fun i =>
      (if i = 2 then .one else a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_carry_one_transition (a : Fin 4 → Sym) (h : a 2 = .one) :
    transition .carry a = (.rewind false, fun i =>
      (if i = 2 then .zero else a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.one = Sym.zero)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_carry_sep_transition (a : Fin 4 → Sym) (h : a 2 = .sep) :
    transition .carry a = (.rewind true, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.sep = Sym.zero),
    if_neg (by decide : ¬Sym.sep = Sym.one)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, owned_intmulcountedstreamcounter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_rewind_bit_transition (a : Fin 4 → Sym) (f : Bool)
    (h : a 2 = .zero ∨ a 2 = .one) :
    transition (.rewind f) a = (.rewind f, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, owned_intmulcountedstreamcounter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_rewind_sep_transition (a : Fin 4 → Sym) (f : Bool) (h : a 2 = .sep) :
    transition (.rewind f) a = (.done f, fun i => (a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    exact owned_intmulcountedstreamcounter_safe_left _ (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamcounter_bit_mem (b : Bool) : machine.bitSym b = Sym.zero ∨ machine.bitSym b = Sym.one := by
  cases b <;> decide

/-- Reading the least significant remaining bit after the left delimiter. -/
private theorem owned_intmulcountedstreamcounter_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamcounter_carry_read (base : machine.Cfg) (b : Bool) (bs done : List Bool) :
    (carryFrame base (b :: bs) done).cells 2 ((carryFrame base (b :: bs) done).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
    (bs.length + 2) = machine.bitSym b
  rw [show bs.length + 2 = (bs.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  exact owned_intmulcountedstreamcounter_reverse_last b bs done

private theorem owned_intmulcountedstreamcounter_carry_zero_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (false :: bs) done) = carryFrame base bs (true :: done) := by
  have hz : (carryFrame base (false :: bs) done).cells 2
      ((carryFrame base (false :: bs) done).head 2) = Sym.zero := owned_intmulcountedstreamcounter_carry_read base false bs done
  have ht := owned_intmulcountedstreamcounter_carry_zero_transition
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) hz
  change transition (carryFrame base (false :: bs) done).state
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.one =
          machine.tapeOf (Sym.sep :: ((bs.reverse ++ true :: done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        owned_intmulcountedstreamcounter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.zero Sym.one
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (false :: bs) done).cells i)
        ((carryFrame base (false :: bs) done).head i)
        ((carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame]
    · simp [carryFrame, hi]


private theorem owned_intmulcountedstreamcounter_carry_one_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (true :: bs) done) = rewindFrame base false (false :: bs).reverse done := by
  have ho : (carryFrame base (true :: bs) done).cells 2
      ((carryFrame base (true :: bs) done).head 2) = Sym.one := owned_intmulcountedstreamcounter_carry_read base true bs done
  have ht := owned_intmulcountedstreamcounter_carry_one_transition
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) ho
  change transition (carryFrame base (true :: bs) done).state
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((true :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.zero =
          machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        owned_intmulcountedstreamcounter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.one Sym.zero
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (true :: bs) done).cells i)
        ((carryFrame base (true :: bs) done).head i)
        ((carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, rewindFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame, rewindFrame]
    · simp [carryFrame, rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_carry_nil_step (base : machine.Cfg) (done : List Bool) :
    machine.step (carryFrame base [] done) = rewindFrame base true [] done := by
  have hm : (carryFrame base [] done).cells 2 ((carryFrame base [] done).head 2) = Sym.sep := rfl
  have ht := owned_intmulcountedstreamcounter_carry_sep_transition
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) hm
  change transition (carryFrame base [] done).state
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((carryFrame base [] done).cells i) ((carryFrame base [] done).head i)
      ((carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _
    rw [Function.update_eq_self]
    simp [carryFrame, rewindFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [carryFrame, rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_read (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep])))
    (pre.length + 2) = machine.bitSym b
  rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamcounter_rewind_step (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    machine.step (rewindFrame base f pre (b :: bs)) = rewindFrame base f (pre ++ [b]) bs := by
  have hb : (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.zero ∨
      (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.one := by
    rw [owned_intmulcountedstreamcounter_rewind_read]
    exact owned_intmulcountedstreamcounter_bit_mem b
  have ht := owned_intmulcountedstreamcounter_rewind_bit_transition
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) f hb
  change transition (rewindFrame base f pre (b :: bs)).state
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre (b :: bs)).cells i) ((rewindFrame base f pre (b :: bs)).head i)
      ((rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_end (base : machine.Cfg) (f : Bool) (pre : List Bool) :
    machine.step (rewindFrame base f pre []) = counterFrame base (.done f) pre.reverse := by
  have hs : (rewindFrame base f pre []).cells 2 ((rewindFrame base f pre []).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: ((pre ++ []).map machine.bitSym ++ [Sym.sep])))
      (pre.length + 2) = Sym.sep
    rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ, List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamcounter_rewind_sep_transition
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) f hs
  change transition (rewindFrame base f pre []).state
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _ at ht
  apply owned_intmulcountedstreamcounter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre []).cells i) ((rewindFrame base f pre []).head i)
      ((rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, counterFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, counterFrame, hi]

private theorem owned_intmulcountedstreamcounter_rewind_run (base : machine.Cfg) (f : Bool) (pre right : List Bool) :
    machine.step^[right.length + 1] (rewindFrame base f pre right) =
      counterFrame base (.done f) (pre ++ right).reverse := by
  induction right generalizing pre with
  | nil => simpa using owned_intmulcountedstreamcounter_rewind_end base f pre
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp,
        Function.iterate_succ_apply, owned_intmulcountedstreamcounter_rewind_step, ih]
      simp [List.append_assoc]

private theorem owned_intmulcountedstreamcounter_carry_run (base : machine.Cfg) (bits done : List Bool) :
    machine.step^[carryLength bits + 1] (carryFrame base bits done) =
      rewindFrame base (underflow bits) (stopTail bits).reverse
        (List.replicate (carryLength bits) true ++ done) := by
  induction bits generalizing done with
  | nil => simpa [carryLength, underflow, stopTail] using owned_intmulcountedstreamcounter_carry_nil_step base done
  | cons b bs ih =>
      cases b
      · simp only [carryLength, underflow, stopTail, if_true]
        rw [Function.iterate_succ_apply, owned_intmulcountedstreamcounter_carry_zero_step, ih]
        simp [List.replicate_succ', List.append_assoc]
      · simpa [carryLength, underflow, stopTail] using owned_intmulcountedstreamcounter_carry_one_step base bs done

/-- The actual decrement table restores the head and preserves all other tapes.
Its exact count includes propagation, resolution, and the full head return. -/
private theorem counter_correct (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits) =
      counterFrame base (.done (underflow bits)) (updated bits) := by
  have hc : counterFrame base .carry bits = carryFrame base bits [] := by
    apply owned_intmulcountedstreamcounter_cfg_ext <;> simp [counterFrame, carryFrame]
  have ht : counterSteps bits = (carryLength bits + 1) + (carryLength bits + 1) := by
    unfold counterSteps
    omega
  rw [hc, ht, Function.iterate_add_apply, owned_intmulcountedstreamcounter_carry_run]
  simp only [List.append_nil]
  have hr := owned_intmulcountedstreamcounter_rewind_run base (underflow bits) (stopTail bits).reverse (List.replicate (carryLength bits) true)
  simpa [updated, List.reverse_append, List.reverse_replicate] using hr

end IntMul.CountedStream




namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem owned_intmulcountedstreamreset_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamreset_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamreset_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem owned_intmulcountedstreamreset_bit_ne_start (b : Bool) : machine.bitSym b ≠ Sym.start := by
  cases b <;> decide

private theorem owned_intmulcountedstreamreset_reset_left_transition (a : Fin 4 → Sym) (x y : Bool)
    (hx : a 2 = machine.bitSym x) (hy : a 3 = machine.bitSym y) :
    transition .resetLeft a = (.resetLeft, fun i =>
      (if i = 2 then a 3 else a i, if i = 2 ∨ i = 3 then .left else .stay)) := by
  have hb : a 2 = Sym.zero ∨ a 2 = Sym.one := by rw [hx]; cases x <;> decide
  simp only [transition, rawTransition, if_pos hb]
  congr 1
  funext i
  fin_cases i
  · exact safe_stay _
  · exact safe_stay _
  · change safeStep (a 2) (a 3) .left = (a 3, .left)
    rw [hx, hy]
    cases x <;> cases y <;> decide
  · change safeStep (a 3) (a 3) .left = (a 3, .left)
    rw [hy]
    exact owned_intmulcountedstreamreset_safe_left _ (owned_intmulcountedstreamreset_bit_ne_start y)

private theorem owned_intmulcountedstreamreset_reset_left_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) : transition .resetLeft a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, owned_intmulcountedstreamreset_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamreset_reset_right_bit_transition (a : Fin 4 → Sym)
    (hx : a 2 = .zero ∨ a 2 = .one) : transition .resetRight a =
      (.resetRight, fun i => (a i, if i = 2 ∨ i = 3 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos hx]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi, owned_intmulcountedstreamreset_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem owned_intmulcountedstreamreset_reset_right_sep_transition (a : Fin 4 → Sym)
    (hx : a 2 = .sep) (hy : a 3 = .sep) : transition .resetRight a =
      (.halt, fun i => (a i, if i = 2 ∨ i = 3 then .left else .stay)) := by
  simp only [transition, rawTransition, hx]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2 ∨ i = 3
  · simp only [if_pos hi]
    apply owned_intmulcountedstreamreset_safe_left
    rcases hi with rfl | rfl
    · rw [hx]; decide
    · rw [hy]; decide
  · simp only [if_neg hi, safe_stay]
/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem owned_intmulcountedstreamreset_tape_replace_after_prefix (M : MultitapeTM)
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



private theorem owned_intmulcountedstreamreset_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedstreamreset_reset_left_read (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
    (h : xs.length = ys.length) :
    (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells 2 (xs.length + 2) = machine.bitSym a ∧
    (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells 3 (xs.length + 2) = machine.bitSym b := by
  constructor
  · change (machine.tapeOf (Sym.sep :: (((a :: xs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
      (xs.length + 2) = _
    rw [show xs.length + 2 = (xs.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    exact owned_intmulcountedstreamreset_reverse_last a xs done
  · change (machine.tapeOf (Sym.sep :: (((b :: ys).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
      (xs.length + 2) = _
    rw [h, show ys.length + 2 = (ys.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    exact owned_intmulcountedstreamreset_reverse_last b ys done

private theorem owned_intmulcountedstreamreset_reset_left_step (base : machine.Cfg) (a b : Bool) (xs ys done : List Bool)
    (h : xs.length = ys.length) :
    machine.step (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)) =
        resetFrame base .resetLeft (xs.reverse ++ b :: done) (ys.reverse ++ b :: done) (xs.length + 1) := by
  let f := resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done) (xs.length + 2)
  have hx : f.cells 2 (f.head 2) = machine.bitSym a := (owned_intmulcountedstreamreset_reset_left_read base a b xs ys done h).1
  have hy : f.cells 3 (f.head 3) = machine.bitSym b := (owned_intmulcountedstreamreset_reset_left_read base a b xs ys done h).2
  have ht := owned_intmulcountedstreamreset_reset_left_transition (fun i => f.cells i (f.head i)) a b hx hy
  change transition (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).state
    (fun i => (resetFrame base .resetLeft ((a :: xs).reverse ++ done) ((b :: ys).reverse ++ done)
      (xs.length + 2)).cells i ((resetFrame base .resetLeft ((a :: xs).reverse ++ done)
        ((b :: ys).reverse ++ done) (xs.length + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht, hy]
    funext i
    fin_cases i
    · change Function.update (f.cells 0) (f.head 0) (f.cells 0 (f.head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (f.cells 1) (f.head 1) (f.cells 1 (f.head 1)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update
        (machine.tapeOf (Sym.sep :: (((a :: xs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (xs.length + 2) (machine.bitSym b) =
          machine.tapeOf (Sym.sep :: ((xs.reverse ++ b :: done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse, List.map_nil, List.nil_append] using
        owned_intmulcountedstreamreset_tape_replace_after_prefix machine (Sym.sep :: xs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) (machine.bitSym a) (machine.bitSym b)
    · change Function.update (f.cells 3) (f.head 3) (f.cells 3 (f.head 3)) = _
      rw [Function.update_eq_self]
      simp [f, resetFrame, List.reverse_cons, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [resetFrame]

private theorem owned_intmulcountedstreamreset_reset_left_run (base : machine.Cfg) (xs ys done : List Bool) (h : xs.length = ys.length) :
    machine.step^[xs.length]
      (resetFrame base .resetLeft (xs.reverse ++ done) (ys.reverse ++ done) (xs.length + 1)) =
        resetFrame base .resetLeft (ys.reverse ++ done) (ys.reverse ++ done) 1 := by
  induction xs generalizing ys done with
  | nil =>
      cases ys with
      | nil => simp
      | cons b ys => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          rw [List.length_cons, Function.iterate_succ_apply]
          change machine.step^[xs.length]
            (machine.step (resetFrame base .resetLeft ((a :: xs).reverse ++ done)
              ((b :: ys).reverse ++ done) (xs.length + 2))) = _
          rw [owned_intmulcountedstreamreset_reset_left_step base a b xs ys done ht, ih ys (b :: done) ht]
          simp [List.reverse_cons, List.append_assoc]


private theorem owned_intmulcountedstreamreset_reset_left_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetLeft word word 1) = resetFrame base .resetRight word word 2 := by
  have hs : (resetFrame base .resetLeft word word 1).cells 2
      ((resetFrame base .resetLeft word word 1).head 2) = Sym.sep := rfl
  have ht := owned_intmulcountedstreamreset_reset_left_sep_transition
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) hs
  change transition (resetFrame base .resetLeft word word 1).state
    (fun i => (resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetLeft word word 1).cells i)
      ((resetFrame base .resetLeft word word 1).head i)
      ((resetFrame base .resetLeft word word 1).cells i ((resetFrame base .resetLeft word word 1).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi]

private theorem owned_intmulcountedstreamreset_reset_right_step (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j < word.length) :
    machine.step (resetFrame base .resetRight word word (j + 2)) =
      resetFrame base .resetRight word word ((j + 1) + 2) := by
  have hr : (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = machine.bitSym word[j] := by
    change (machine.tapeOf (Sym.sep :: (word.map machine.bitSym ++ [Sym.sep]))) (j + 2) = _
    rw [show j + 2 = (j + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hb : (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = Sym.zero ∨
      (resetFrame base .resetRight word word (j + 2)).cells 2
      ((resetFrame base .resetRight word word (j + 2)).head 2) = Sym.one := by
    rw [hr]
    cases word[j] <;> decide
  have ht := owned_intmulcountedstreamreset_reset_right_bit_transition
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) hb
  change transition (resetFrame base .resetRight word word (j + 2)).state
    (fun i => (resetFrame base .resetRight word word (j + 2)).cells i
      ((resetFrame base .resetRight word word (j + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetRight word word (j + 2)).cells i)
      ((resetFrame base .resetRight word word (j + 2)).head i)
      ((resetFrame base .resetRight word word (j + 2)).cells i
        ((resetFrame base .resetRight word word (j + 2)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi] <;> omega

private theorem owned_intmulcountedstreamreset_reset_right_run (base : machine.Cfg) (word : List Bool) (j : ℕ) (hj : j ≤ word.length) :
    machine.step^[j] (resetFrame base .resetRight word word 2) = resetFrame base .resetRight word word (j + 2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), owned_intmulcountedstreamreset_reset_right_step base word j (by omega)]

private theorem owned_intmulcountedstreamreset_reset_right_end (base : machine.Cfg) (word : List Bool) :
    machine.step (resetFrame base .resetRight word word (word.length + 2)) =
      resetFrame base .halt word word (word.length + 1) := by
  have hs : (resetFrame base .resetRight word word (word.length + 2)).cells 2
      ((resetFrame base .resetRight word word (word.length + 2)).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: (word.map machine.bitSym ++ [Sym.sep]))) (word.length + 2) = _
    rw [show word.length + 2 = (word.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamreset_reset_right_sep_transition
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) hs hs
  change transition (resetFrame base .resetRight word word (word.length + 2)).state
    (fun i => (resetFrame base .resetRight word word (word.length + 2)).cells i
      ((resetFrame base .resetRight word word (word.length + 2)).head i)) = _ at ht
  apply owned_intmulcountedstreamreset_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((resetFrame base .resetRight word word (word.length + 2)).cells i)
      ((resetFrame base .resetRight word word (word.length + 2)).head i)
      ((resetFrame base .resetRight word word (word.length + 2)).cells i
        ((resetFrame base .resetRight word word (word.length + 2)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 ∨ i = 3 <;> simp [resetFrame, hi]

/-- Literal saved-template reset, including restoration of BOTH work heads.
The arbitrary input/output tapes and their heads remain exactly unchanged. -/
private theorem template_reset_correct (base : machine.Cfg) (bits template : List Bool)
    (h : bits.length = template.length) :
    machine.step^[2 * bits.length + 2]
      (resetFrame base .resetLeft bits template (bits.length + 1)) =
        resetFrame base .halt template template (template.length + 1) := by
  have hf : resetFrame base .resetLeft bits template (bits.length + 1) =
      resetFrame base .resetLeft (bits.reverse.reverse ++ []) (template.reverse.reverse ++ [])
        (bits.reverse.length + 1) := by simp
  rw [hf]
  have hl : machine.step^[bits.length + 1]
      (resetFrame base .resetLeft (bits.reverse.reverse ++ []) (template.reverse.reverse ++ [])
        (bits.reverse.length + 1)) = resetFrame base .resetRight template template 2 := by
    rw [Function.iterate_succ_apply']
    have he := owned_intmulcountedstreamreset_reset_left_run base bits.reverse template.reverse [] (by simpa using h)
    simp only [List.length_reverse] at he ⊢
    rw [he]
    simp only [List.reverse_reverse, List.append_nil]
    exact owned_intmulcountedstreamreset_reset_left_end base template
  rw [show 2 * bits.length + 2 = (template.length + 1) + (bits.length + 1) by omega,
    Function.iterate_add_apply, hl, Function.iterate_succ_apply',
    owned_intmulcountedstreamreset_reset_right_run base template template.length le_rfl, owned_intmulcountedstreamreset_reset_right_end]

end IntMul.CountedStream



namespace IntMul.BinaryAdder

private theorem full_adder_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem add_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addLittle x y c).length = x.length + 1 := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => rfl
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, List.length_cons, ih ys _ ht]

private theorem add_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addLittle x y c) = littleVal x + littleVal y + c.toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [addLittle, littleVal]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, littleVal, ih ys _ ht]
          have hv := full_adder_value a b c
          omega

private theorem little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem foldl_affine (x : List Bool) (a : ℕ) :
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

private theorem val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact foldl_affine y _

private theorem val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, val_append, val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring

/-- Ripple-carry addition computes the ordinary campaign-model value, preserving
all leading zeroes and adding exactly one final carry position. -/
private theorem ripple_sum_spec (x y : List Bool) (h : x.length = y.length) :
    ((addLittle x.reverse y.reverse false).reverse).length = x.length + 1 ∧
    IntMul.val ((addLittle x.reverse y.reverse false).reverse) = IntMul.val x + IntMul.val y := by
  have hl : x.reverse.length = y.reverse.length := by simpa using h
  constructor
  · simpa using add_little_length x.reverse y.reverse false hl
  · rw [val_reverse_little, add_little_value _ _ _ hl]
    have hx : littleVal x.reverse = IntMul.val x := by
      rw [← val_reverse_little, List.reverse_reverse]
    have hy : littleVal y.reverse = IntMul.val y := by
      rw [← val_reverse_little, List.reverse_reverse]
    simp [hx, hy]

/-- Every little-endian word has exactly its specified binary digits, including
trailing zeroes; no normalization assumption is needed. -/
private theorem little_value_test_bit (x : List Bool) (i : ℕ) :
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
    rw [← val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]

/-- The ripple adder produces exactly the canonical output word demanded by the
linear-time addition milestone, rather than merely a word of the same value. -/
private theorem ripple_sum_bin (x y : List Bool) (h : x.length = y.length) :
    (addLittle x.reverse y.reverse false).reverse =
      IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y) := by
  have hs := ripple_sum_spec x y h
  have hr := bin_value_roundtrip ((addLittle x.reverse y.reverse false).reverse)
  rw [hs.1, hs.2] at hr
  exact hr.symm

end IntMul.BinaryAdder




namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

private theorem owned_intmulcountedstreamblocks_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulcountedstreamblocks_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem owned_intmulcountedstreamblocks_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
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
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem owned_intmulcountedstreamblocks_counter_frame_from_stream (x y old bits : List Bool) (j : ℕ) (q₀ q : State)
    (h : bits.length = y.length) :
    counterFrame (streamFrame x y old j q₀) q bits = streamFrame x y bits j q := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame, h]

private theorem owned_intmulcountedstreamblocks_stream_counter (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step^[counterSteps bits] (streamFrame x y bits j .carry) =
      streamFrame x y (updated bits) j (.done (underflow bits)) := by
  have hf := owned_intmulcountedstreamblocks_counter_frame_from_stream x y bits bits j .carry .carry h
  rw [← hf, counter_correct]
  exact owned_intmulcountedstreamblocks_counter_frame_from_stream x y bits (updated bits) j .carry (.done (underflow bits))
    (by rw [updated_length]; exact h)

private theorem owned_intmulcountedstreamblocks_emit_transition (a : Fin 4 → Sym) (b : Bool)
    (hb : a 0 = machine.bitSym b) (ho : a 1 = .blank) :
    transition .emit a = (.carry, fun i =>
      (if i = 1 then machine.bitSym b else a i, if i = 0 ∨ i = 1 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact owned_intmulcountedstreamblocks_safe_right _
  · change safeStep (a 1) (a 0) .right = (machine.bitSym b, .right)
    rw [ho, hb]
    cases b <;> decide
  · exact safe_stay _
  · exact safe_stay _

private theorem owned_intmulcountedstreamblocks_emit_step (x y bits : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (streamFrame x y bits j .emit) = streamFrame x y bits (j + 1) .carry := by
  have hl : ((x.take j).map machine.bitSym).length = j := by simp [Nat.min_eq_left hj.le]
  have hr : (streamFrame x y bits j .emit).cells 0 ((streamFrame x y bits j .emit).head 0) = machine.bitSym x[j] := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank = _
    rw [List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have ho : (streamFrame x y bits j .emit).cells 1 ((streamFrame x y bits j .emit).head 1) = Sym.blank := by
    change ((x.take j).map machine.bitSym).getD j machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := owned_intmulcountedstreamblocks_emit_transition
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) x[j] hr ho
  change transition (streamFrame x y bits j .emit).state
    (fun i => (streamFrame x y bits j .emit).cells i ((streamFrame x y bits j .emit).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i
    · change Function.update ((streamFrame x y bits j .emit).cells 0) ((streamFrame x y bits j .emit).head 0)
        ((streamFrame x y bits j .emit).cells 0 ((streamFrame x y bits j .emit).head 0)) = _
      rw [Function.update_eq_self]
      rfl
    · change Function.update (machine.tapeOf ((x.take j).map machine.bitSym)) (j + 1)
        (machine.bitSym x[j]) = machine.tapeOf ((x.take (j + 1)).map machine.bitSym)
      have hnew : (x.take (j + 1)).map machine.bitSym =
          (x.take j).map machine.bitSym ++ [machine.bitSym x[j]] := by
        rw [List.take_succ_eq_append_getElem hj, List.map_append]
        rfl
      rw [hnew]
      have hw := owned_intmulcountedstreamblocks_tapeOf_append_one machine ((x.take j).map machine.bitSym) (machine.bitSym x[j])
      rw [hl] at hw
      exact hw
    all_goals
      change Function.update ((streamFrame x y bits j .emit).cells _) ((streamFrame x y bits j .emit).head _)
        ((streamFrame x y bits j .emit).cells _ ((streamFrame x y bits j .emit).head _)) = _
      rw [Function.update_eq_self]
      rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [streamFrame]

private theorem owned_intmulcountedstreamblocks_done_transition (a : Fin 4 → Sym) (f : Bool) :
    transition (.done f) a = (if f then .resetLeft else .emit, fun i => (a i, .stay)) := by
  simp [transition, rawTransition, safe_stay]

private theorem owned_intmulcountedstreamblocks_done_false_step (x y bits : List Bool) (j : ℕ) :
    machine.step (streamFrame x y bits j (.done false)) = streamFrame x y bits j .emit := by
  have ht := owned_intmulcountedstreamblocks_done_transition (fun i => (streamFrame x y bits j (.done false)).cells i
    ((streamFrame x y bits j (.done false)).head i)) false
  change transition (streamFrame x y bits j (.done false)).state
    (fun i => (streamFrame x y bits j (.done false)).cells i
      ((streamFrame x y bits j (.done false)).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame x y bits j (.done false)).cells i)
      ((streamFrame x y bits j (.done false)).head i)
      ((streamFrame x y bits j (.done false)).cells i ((streamFrame x y bits j (.done false)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulcountedstreamblocks_done_true_step (x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step (streamFrame x y bits j (.done true)) =
      resetFrame (streamFrame x y bits j (.done true)) .resetLeft bits.reverse y (y.length + 1) := by
  have ht := owned_intmulcountedstreamblocks_done_transition (fun i => (streamFrame x y bits j (.done true)).cells i
    ((streamFrame x y bits j (.done true)).head i)) true
  change transition (streamFrame x y bits j (.done true)).state
    (fun i => (streamFrame x y bits j (.done true)).cells i
      ((streamFrame x y bits j (.done true)).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame x y bits j (.done true)).cells i)
      ((streamFrame x y bits j (.done true)).head i)
      ((streamFrame x y bits j (.done true)).cells i ((streamFrame x y bits j (.done true)).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [streamFrame, resetFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [streamFrame, resetFrame]


private theorem owned_intmulcountedstreamblocks_nonterminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hp : 0 < value bits) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      streamFrame x y (updated bits) (j + 1) .emit := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulcountedstreamblocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', owned_intmulcountedstreamblocks_stream_counter x y bits (j + 1) hw,
    (decrement_positive bits hp).1, owned_intmulcountedstreamblocks_done_false_step]

private theorem owned_intmulcountedstreamblocks_loop_run (x y : List Bool) (n : ℕ) (bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hv : n ≤ value bits) (hx : j + n ≤ x.length) :
    machine.step^[2 * n + totalCounterSteps n bits] (streamFrame x y bits j .emit) =
      streamFrame x y (iterateCounter n bits) (j + n) .emit := by
  induction n generalizing bits j with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hval := (decrement_positive bits hp).2
      have htime : 2 * (n + 1) + totalCounterSteps (n + 1) bits =
          (2 * n + totalCounterSteps n (updated bits)) + (counterSteps bits + 2) := by
        rw [totalCounterSteps]
        omega
      rw [htime, Function.iterate_add_apply,
        owned_intmulcountedstreamblocks_nonterminal_cycle x y bits j (by omega) hw hp]
      have hr := ih (updated bits) (j + 1) (by rw [updated_length]; exact hw) (by omega) (by omega)
      simpa only [iterateCounter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private theorem owned_intmulcountedstreamblocks_terminal_cycle (x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hz : value bits = 0) :
    machine.step^[counterSteps bits + 2] (streamFrame x y bits j .emit) =
      resetFrame (streamFrame x y (updated bits) (j + 1) (.done true))
        .resetLeft (updated bits).reverse y (y.length + 1) := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, owned_intmulcountedstreamblocks_emit_step x y bits j hj,
    Function.iterate_succ_apply', owned_intmulcountedstreamblocks_stream_counter x y bits (j + 1) hw,
    (underflow_iff_zero bits).mpr hz]
  exact owned_intmulcountedstreamblocks_done_true_step x y (updated bits) (j + 1) (by rw [updated_length]; exact hw)

/-- The last (B-th) emission detects underflow, then takes its actual dispatch
transition into reset. All previous emissions remain in the same finite loop. -/
private theorem owned_intmulcountedstreamblocks_block_run (x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits]
      (streamFrame x y bits j .emit) =
        resetFrame (streamFrame x y last (j + (value bits + 1)) (.done true))
          .resetLeft last.reverse y (y.length + 1) := by
  dsimp only
  have hn : (iterateCounter (value bits) bits).length = y.length := by
    rw [iterate_counter_length]
    exact hw
  have hz : value (iterateCounter (value bits) bits) = 0 := by
    rw [countdown_value bits (value bits) le_rfl]
    omega
  have ht : 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits =
      (counterSteps (iterateCounter (value bits) bits) + 2) +
        (2 * value bits + totalCounterSteps (value bits) bits) := by
    rw [total_counter_steps_succ]
    omega
  rw [ht, Function.iterate_add_apply, owned_intmulcountedstreamblocks_loop_run x y (value bits) bits j hw le_rfl (by omega),
    owned_intmulcountedstreamblocks_terminal_cycle x y (iterateCounter (value bits) bits) (j + value bits) (by omega) hn hz]
  simp only [Nat.add_assoc]

/-- Complete live block, including every payload, counter, dispatch, and reset
transition. The final full configuration also records both returned work heads. -/
private theorem owned_intmulcountedstreamblocks_block_reset_run (x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2)]
      (streamFrame x y bits j .emit) =
        resetFrame (streamFrame x y last (j + (value bits + 1)) (.done true))
          .halt y y (y.length + 1) := by
  dsimp only
  have hl : (updated (iterateCounter (value bits) bits)).reverse.length = y.length := by
    rw [List.length_reverse, updated_length, iterate_counter_length]
    exact hw
  rw [show 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2) =
      (2 * y.length + 2) + (2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits) by omega,
    Function.iterate_add_apply, owned_intmulcountedstreamblocks_block_run x y bits j hw hx]
  have hr := template_reset_correct
    (streamFrame x y (updated (iterateCounter (value bits) bits)) (j + (value bits + 1)) (.done true))
      (updated (iterateCounter (value bits) bits)).reverse y hl
  rw [hl] at hr
  exact hr


private theorem owned_intmulcountedstreamblocks_ready_matches_stream (x y : List Bool) (j : ℕ) (q : State) :
    readyFrame x y j q = streamFrame x y y.reverse j q := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame]

private theorem owned_intmulcountedstreamblocks_reset_matches_ready (x y old : List Bool) (j : ℕ) :
    resetFrame (streamFrame x y old j (.done true)) .halt y y (y.length + 1) =
      readyFrame x y j .halt := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]
  · funext i
    fin_cases i <;> simp [readyFrame, streamFrame, resetFrame]

/-- Initialization is paid only once; the full boundary configuration is public. -/
private theorem setup_ready (x y : List Bool) :
    machine.step^[2 * x.length + 2 * y.length + 5] (machine.initCfg x y) =
      readyFrame x y 0 .emit := by
  rw [setup_correct, owned_intmulcountedstreamblocks_ready_matches_stream]

/-- One already initialized block returns all physical heads and restores its
descriptor, so a finite caller can reuse it without scanning the whole input. -/
private theorem initialized_block (x y : List Bool) (j : ℕ)
    (hx : j + (IntMul.val y + 1) ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (readyFrame x y j .emit) =
        readyFrame x y (j + (IntMul.val y + 1)) .halt := by
  have hv : value y.reverse = IntMul.val y := by
    change IntMul.BinaryAdder.littleVal y.reverse = IntMul.val y
    rw [← IntMul.BinaryAdder.val_reverse_little, List.reverse_reverse]
  let clock := 2 * (value y.reverse + 1) +
    totalCounterSteps (value y.reverse + 1) y.reverse + (2 * y.length + 2)
  refine ⟨clock, ?_, ?_⟩
  · have hc := total_counter_steps_bound (value y.reverse + 1) y.reverse
    rw [List.length_reverse, hv] at hc
    dsimp only [clock]
    rw [hv]
    omega
  · rw [owned_intmulcountedstreamblocks_ready_matches_stream]
    have hr := owned_intmulcountedstreamblocks_block_reset_run x y y.reverse j (by simp) (by simpa [hv] using hx)
    simpa only [clock, hv, owned_intmulcountedstreamblocks_reset_matches_ready] using hr

private theorem owned_intmulcountedstreamblocks_end_emit_transition (a : Fin 4 → Sym) (h : a 0 = .sep) :
    transition .emit a = (.halt, fun i => (a i,.stay)) := by
  simp [transition, rawTransition, h, safe_stay]

private theorem owned_intmulcountedstreamblocks_end_emit_step (x y bits : List Bool) :
    machine.step (streamFrame x y bits x.length .emit) =
      streamFrame x y bits x.length .halt := by
  have hr : (streamFrame x y bits x.length .emit).cells 0
      ((streamFrame x y bits x.length .emit).head 0) = Sym.sep := by
    change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := owned_intmulcountedstreamblocks_end_emit_transition (fun i => (streamFrame x y bits x.length .emit).cells i
    ((streamFrame x y bits x.length .emit).head i)) hr
  change transition (streamFrame x y bits x.length .emit).state
    (fun i => (streamFrame x y bits x.length .emit).cells i
      ((streamFrame x y bits x.length .emit).head i)) = _ at ht
  apply owned_intmulcountedstreamblocks_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem owned_intmulcountedstreamblocks_tail_matches_reset (x y bits : List Bool) (h : bits.length = y.length) :
    streamFrame x y bits x.length .halt =
      resetFrame (readyFrame x y x.length .halt) .halt bits.reverse y (y.length + 1) := by
  apply owned_intmulcountedstreamblocks_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [streamFrame, resetFrame, readyFrame]
  · funext i
    fin_cases i <;> simp [streamFrame, resetFrame, readyFrame, h]

/-- A final short block stops at the input separator. Its counter is left in an
explicit fixed-width frame for the caller's separately charged cleanup. -/
private theorem initialized_tail (x y : List Bool) (j r : ℕ)
    (hr : r ≤ IntMul.val y) (hx : j + r = x.length) :
    ∃ t : ℕ, t ≤ 6 * r + 2 * y.length + 1 ∧
      machine.step^[t] (readyFrame x y j .emit) =
        resetFrame (readyFrame x y x.length .halt) .halt
          (iterateCounter r y.reverse).reverse y (y.length + 1) := by
  have hv : value y.reverse = IntMul.val y := by
    change IntMul.BinaryAdder.littleVal y.reverse = IntMul.val y
    rw [← IntMul.BinaryAdder.val_reverse_little, List.reverse_reverse]
  let clock := 2 * r + totalCounterSteps r y.reverse + 1
  refine ⟨clock, ?_, ?_⟩
  · have hc := total_counter_steps_bound r y.reverse
    rw [List.length_reverse] at hc
    dsimp only [clock]
    omega
  · dsimp only [clock]
    rw [Function.iterate_succ_apply', owned_intmulcountedstreamblocks_ready_matches_stream,
      owned_intmulcountedstreamblocks_loop_run x y r y.reverse j (by simp) (by simpa [hv] using hr) (by omega), hx,
      owned_intmulcountedstreamblocks_end_emit_step, owned_intmulcountedstreamblocks_tail_matches_reset]
    rw [iterate_counter_length]
    simp

end IntMul.CountedStream



namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)

private noncomputable def windowFrame (x y : List Bool) (j : ℕ) (preWord : List Sym)
    (q : CountedStream.State) : CountedStream.machine.Cfg where
  state := q
  cells := fun i =>
    if i=0 then CountedStream.machine.tapeOf (x.map CountedStream.machine.bitSym ++ Sym.sep :: y.map CountedStream.machine.bitSym)
    else if i=1 then CountedStream.machine.tapeOf preWord
    else CountedStream.machine.tapeOf (Sym.sep :: (y.map CountedStream.machine.bitSym ++ [Sym.sep]))
  head := fun i => if i=0 then j+1 else if i=1 then preWord.length+1 else y.length+1

private noncomputable def bitSegment (x : List Bool) (j r : ℕ) : List Sym :=
  ((x.drop j).take r).map CountedStream.machine.bitSym

private theorem owned_intmulcountedblocksplitterwindows_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem segment_length (x : List Bool) (j r : ℕ) (hx : j+r ≤ x.length) :
    (bitSegment x j r).length=r := by
  simp only [bitSegment,List.length_map,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

private theorem owned_intmulcountedblocksplitterwindows_shifted_payload (x : List Bool) (j r i : ℕ) (hx : j+r ≤ x.length) :
    ((x.take (j+r)).map CountedStream.machine.bitSym).getD (j+i) Sym.blank=
      (bitSegment x j r).getD i Sym.blank := by
  have hwhole : ((x.take (j+r)).map CountedStream.machine.bitSym).length=j+r := by
    simp [Nat.min_eq_left hx]
  have hpart := segment_length x j r hx
  by_cases hi : i < r
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
    simp only [bitSegment,List.getElem_map,List.getElem_take,List.getElem_drop]
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

private theorem owned_intmulcountedblocksplitterwindows_spliced_output (x : List Bool) (j r : ℕ) (preWord : List Sym)
    (hl : j ≤ preWord.length) (hx : j+r ≤ x.length) :
    (fun p => if p < (preWord.length-j)+(j+1) then CountedStream.machine.tapeOf preWord p
      else CountedStream.machine.tapeOf ((x.take (j+r)).map CountedStream.machine.bitSym)
        (p-(preWord.length-j)))=
      CountedStream.machine.tapeOf (preWord++bitSegment x j r) := by
  funext p
  have hbound : (preWord.length-j)+(j+1)=preWord.length+1 := by omega
  rw [hbound]
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p < preWord.length
    · rw [if_pos (by omega)]
      simp only [MultitapeTM.tapeOf]
      exact (List.getD_append _ _ _ _ hp).symm
    · rw [if_neg (by omega)]
      have hind : p+1-(preWord.length-j)=j+(p-preWord.length)+1 := by omega
      rw [hind]
      simp only [MultitapeTM.tapeOf]
      rw [List.getD_append_right _ _ _ _ (by omega),owned_intmulcountedblocksplitterwindows_shifted_payload x j r (p-preWord.length) hx]

private theorem window_frame (x y : List Bool) (j r : ℕ) (preWord : List Sym)
    (q : CountedStream.State) (hl : j ≤ preWord.length) (hx : j+r ≤ x.length) :
    AllWindowRelocation.frame CountedStream.machine (windowFrame x y j preWord q)
      (fun i => if i=1 then preWord.length-j else 0) (fun i => if i=1 then j+1 else 0)
      (CountedStream.readyFrame x y (j+r) q)=
      windowFrame x y (j+r) (preWord++bitSegment x j r) q := by
  apply owned_intmulcountedblocksplitterwindows_cfg_ext
  · rfl
  · funext i p
    fin_cases i
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame]
    · change (if p < (preWord.length-j)+(j+1) then CountedStream.machine.tapeOf preWord p
        else CountedStream.machine.tapeOf ((x.take (j+r)).map CountedStream.machine.bitSym)
          (p-(preWord.length-j)))=_
      exact congrFun (owned_intmulcountedblocksplitterwindows_spliced_output x j r preWord hl hx) p
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame]
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame]
  · funext i
    have hlen := segment_length x j r hx
    fin_cases i <;> simp only [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame,
      List.length_append,hlen]
    all_goals simp
    omega

/-- An actual full counted block appends bits to an arbitrary preserved
output preWord, with unchanged service clock and both descriptors restored. -/
private theorem window_block (x y : List Bool) (j : ℕ) (preWord : List Sym)
    (hl : j ≤ preWord.length) (hx : j+blockSize y ≤ x.length) :
    ∃ t, t ≤ 6*blockSize y+4*y.length+2 ∧
      CountedStream.machine.step^[t] (windowFrame x y j preWord .emit)=
        windowFrame x y (j+blockSize y) (preWord++bitSegment x j (blockSize y)) .halt := by
  obtain ⟨t,ht,hr⟩ := CountedStream.initialized_block x y j hx
  have hstart := window_frame x y j 0 preWord .emit hl (by omega)
  simp only [Nat.add_zero,bitSegment,List.take_zero,List.map_nil,List.append_nil] at hstart
  have hend := window_frame x y j (blockSize y) preWord .halt hl hx
  refine ⟨t,ht,?_⟩
  rw [←hstart,CountedStream.output_window_run _ _ (preWord.length-j) (j+1) t (by omega) (by
    change j+1 ≤ j+1
    exact le_rfl),hr]
  exact hend

private theorem reset_window_frame (x y bits : List Bool) (j r : ℕ) (preWord : List Sym)
    (q : CountedStream.State) (hl : j ≤ preWord.length) (hx : j+r ≤ x.length) :
    AllWindowRelocation.frame CountedStream.machine (windowFrame x y j preWord .emit)
      (fun i => if i=1 then preWord.length-j else 0) (fun i => if i=1 then j+1 else 0)
      (CountedStream.resetFrame (CountedStream.readyFrame x y (j+r) .halt)
        q bits y (y.length+1))=
      CountedStream.resetFrame
        (windowFrame x y (j+r) (preWord++bitSegment x j r) .halt)
        q bits y (y.length+1) := by
  apply owned_intmulcountedblocksplitterwindows_cfg_ext
  · rfl
  · funext i p
    fin_cases i
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame,CountedStream.resetFrame]
    · change (if p < (preWord.length-j)+(j+1) then CountedStream.machine.tapeOf preWord p
        else CountedStream.machine.tapeOf ((x.take (j+r)).map CountedStream.machine.bitSym)
          (p-(preWord.length-j)))=_
      exact congrFun (owned_intmulcountedblocksplitterwindows_spliced_output x j r preWord hl hx) p
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame,CountedStream.resetFrame]
    · simp [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame,CountedStream.resetFrame]
  · funext i
    have hlen := segment_length x j r hx
    fin_cases i <;> simp only [AllWindowRelocation.frame,windowFrame,CountedStream.readyFrame,
      CountedStream.resetFrame,List.length_append,hlen]
    all_goals simp
    omega

/-- The final short block preserves earlier separated output. Its remaining
counter is explicit and has the descriptor's original width. -/
private theorem window_tail (x y : List Bool) (j r : ℕ) (preWord : List Sym)
    (hl : j ≤ preWord.length) (hr : r ≤ IntMul.val y) (hx : j+r=x.length) :
    ∃ t, t ≤ 6*r+2*y.length+1 ∧
      CountedStream.machine.step^[t] (windowFrame x y j preWord .emit)=
        CountedStream.resetFrame
          (windowFrame x y (j+r) (preWord++bitSegment x j r) .halt) .halt
          (CountedStream.iterateCounter r y.reverse).reverse y (y.length+1) := by
  obtain ⟨t,ht,he⟩ := CountedStream.initialized_tail x y j r hr hx
  have hstart := window_frame x y j 0 preWord .emit hl (by omega)
  simp only [Nat.add_zero,bitSegment,List.take_zero,List.map_nil,List.append_nil] at hstart
  have hend := reset_window_frame x y (CountedStream.iterateCounter r y.reverse).reverse
    j r preWord .halt hl (by omega)
  refine ⟨t,ht,?_⟩
  rw [←hstart,CountedStream.output_window_run _ _ (preWord.length-j) (j+1) t (by omega)
    (by change j+1 ≤ j+1; exact le_rfl),he,←hx]
  exact hend

private theorem window_reset_identity (x y : List Bool) (j : ℕ) (preWord : List Sym)
    (q : CountedStream.State) :
    CountedStream.resetFrame (windowFrame x y j preWord .halt) q y y (y.length+1)=
      windowFrame x y j preWord q := by
  apply owned_intmulcountedblocksplitterwindows_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame,windowFrame]
  · funext i
    fin_cases i <;> simp [CountedStream.resetFrame,windowFrame]

private theorem window_cleanup (x y bits : List Bool) (j : ℕ) (preWord : List Sym)
    (hw : bits.length=y.length) :
    CountedStream.machine.step^[2*y.length+2]
      (CountedStream.resetFrame (windowFrame x y j preWord .halt)
        .resetLeft bits y (y.length+1))=windowFrame x y j preWord .halt := by
  have h := CountedStream.template_reset_correct (windowFrame x y j preWord .halt) bits y hw
  rw [hw] at h
  rw [h,window_reset_identity]

end IntMul.CountedBlockSplitter



namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)

private def streamLift (c : CountedStream.machine.Cfg) : subroutine.Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

private theorem stream_step (c : CountedStream.machine.Cfg) :
    subroutine.step (streamLift c)=streamLift (CountedStream.machine.step c) := by
  rfl

private theorem stream_run (c : CountedStream.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (streamLift c)=streamLift (CountedStream.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,stream_step,Function.iterate_succ_apply']

private abbrev lift (e : Bool) (c : subroutine.Cfg) : machine.Cfg :=
  FiniteCaller.embed subroutine Bool false e dispatch c

private abbrev after (e : Bool) (c : subroutine.Cfg) : machine.Cfg :=
  FiniteCaller.returned subroutine Bool false e dispatch c

private theorem call (e : Bool) (c : subroutine.Cfg) (T : ℕ)
    (h : (subroutine.step^[T] c).state=subroutine.qHalt) :
    ∃ t : ℕ, t ≤ T+1 ∧ machine.step^[t] (lift e c)=after e (subroutine.step^[T] c) :=
  (FiniteCaller.simulate_run subroutine Bool false e dispatch c T).2 h

private theorem segment (e : Bool) (c : subroutine.Cfg) (T : ℕ)
    (h : (subroutine.step^[T] c).state≠subroutine.qHalt) :
    machine.step^[T] (lift e c)=lift e (subroutine.step^[T] c) :=
  (FiniteCaller.simulate_run subroutine Bool false e dispatch c T).1 h

private theorem owned_intmulcountedblocksplitterprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem after_live (c : subroutine.Cfg)
    (h : c.cells 0 (c.head 0)=Sym.zero ∨ c.cells 0 (c.head 0)=Sym.one) :
    after false c=lift false {c with state := .inr ()} := by
  apply owned_intmulcountedblocksplitterprograms_cfg_ext
  · change dispatch false (fun i => c.cells i (c.head i))=some (false,Sum.inr ())
    simp [dispatch,h]
  · rfl
  · rfl

private theorem after_end (c : subroutine.Cfg) (h : c.cells 0 (c.head 0)=Sym.sep) :
    after false c=lift true {c with state := .inl .resetLeft} := by
  apply owned_intmulcountedblocksplitterprograms_cfg_ext
  · change dispatch false (fun i => c.cells i (c.head i))=some (true,Sum.inl CountedStream.State.resetLeft)
    simp [dispatch,h]
  · rfl
  · rfl

private theorem after_cleanup (c : subroutine.Cfg) :
    (after true c).state=machine.qHalt := by
  rfl

private theorem separator_step (c : subroutine.Cfg) (hs : c.state=.inr ())
    (blank : c.cells 1 (c.head 1)=Sym.blank) :
    subroutine.step c=
      {state := .inl .emit,
       cells := fun i => if i=1 then Function.update (c.cells i) (c.head i) Sym.sep else c.cells i,
       head := fun i => if i=1 then c.head i+1 else c.head i} := by
  apply owned_intmulcountedblocksplitterprograms_cfg_ext
  · simp [MultitapeTM.step,transition,hs]
  · funext i
    by_cases hi : i=1
    · subst i
      simp only [MultitapeTM.step,transition,hs,if_true,blank]
      rfl
    · simp only [MultitapeTM.step,transition,hs,if_neg hi]
      change Function.update (c.cells i) (c.head i)
        (IntMul.TapeAdder.safeStep (c.cells i (c.head i)) (c.cells i (c.head i)) Move.stay).1=c.cells i
      rw [IntMul.TapeAdder.safe_stay]
      exact Function.update_eq_self _ _
  · funext i
    by_cases hi : i=1
    · subst i
      simp only [MultitapeTM.step,transition,hs,if_true,blank]
      rfl
    · simp only [MultitapeTM.step,transition,hs,if_neg hi]
      rw [IntMul.TapeAdder.safe_stay]

end IntMul.CountedBlockSplitter



namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)

private theorem packed_zero (x y : List Bool) : packedPrefix x y 0=[] := by
  simp [packedPrefix]

private theorem packed_step (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    packedPrefix x y (j+1)=packedPrefix x y j ++
      (if 0 < j ∧ j % blockSize y=0 then [Sym.sep] else []) ++
      [machine.bitSym (x.getD j false)] := by
  simp only [packedPrefix,Nat.min_eq_left (by omega : j+1 ≤ x.length),Nat.min_eq_left hj.le,
    List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact (List.append_assoc _ _ _).symm

private theorem packed_length (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    (packedPrefix x y j).length=j+(j-1)/blockSize y := by
  induction j with
  | zero => simp [packed_zero]
  | succ j ih =>
    rw [packed_step x y j (by omega),List.length_append,List.length_append,ih (by omega),List.length_singleton]
    cases j with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel] at *
      by_cases hm : (k+1)%blockSize y=0
      · have hd := Nat.succ_div_of_mod_eq_zero hm
        simp only [show 0 < k+1 by omega,hm,true_and,if_true,List.length_singleton]
        omega
      · have hd := Nat.succ_div_of_mod_ne_zero hm
        simp only [show 0 < k+1 by omega,hm,false_and,and_false,if_false,List.length_nil]
        omega

/-- A block of at most B bits beginning at a multiple of B contains no
internal separator; a positive boundary contributes exactly one prefix separator. -/
private theorem packed_block (x y : List Bool) (j r : ℕ)
    (hj : j % blockSize y=0) (hr : r ≤ blockSize y) (hx : j+r ≤ x.length) :
    packedPrefix x y (j+r)=packedPrefix x y j ++
      (if 0 < j ∧ 0 < r then [Sym.sep] else []) ++
      ((List.range r).map fun p => machine.bitSym (x.getD (j+p) false)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show j+(r+1)=j+r+1 by omega,packed_step x y (j+r) (by omega),ih (by omega) (by omega)]
    rw [List.range_succ,List.map_append,List.map_singleton]
    cases r with
    | zero =>
      simp only [Nat.add_zero,List.range_zero,List.map_nil,List.append_nil,hj]
      by_cases hz : 0 < j <;> simp [hz]
    | succ r =>
      have hmod : (j+(r+1)) % blockSize y=r+1 := by
        rw [Nat.add_mod,hj,Nat.zero_add,Nat.mod_eq_of_lt (by omega : r+1 < blockSize y)]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [hmod,show (r+1:ℕ)≠0 by omega,and_false,if_false,List.append_nil]
      simp only [show 0 < r+1 by omega,show 0 < r+1+1 by omega,and_true]
      simp only [List.append_assoc]

end IntMul.CountedBlockSplitter



namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)

private noncomputable def openWord (x y : List Bool) (j : ℕ) : List Sym :=
  packedPrefix x y j ++ if 0 < j then [Sym.sep] else []

private noncomputable def ready (x y : List Bool) (j : ℕ) : machine.Cfg :=
  lift false (streamLift (windowFrame x y j (openWord x y j) .emit))

private theorem owned_intmulcountedblocksplittercalls_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem open_length (x y : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    j ≤ (openWord x y j).length := by
  rw [openWord,List.length_append]
  apply le_trans (b := (packedPrefix x y j).length)
  · rw [packed_length x y j hj]
    exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _

private theorem segment_as_range (x : List Bool) (j r : ℕ) (hx : j+r ≤ x.length) :
    bitSegment x j r=(List.range r).map fun p => machine.bitSym (x.getD (j+p) false) := by
  apply List.ext_getElem
  · rw [segment_length x j r hx,List.length_map,List.length_range]
  · intro i hi hi'
    have hir : i < r := by simpa using hi'
    simp only [bitSegment,List.getElem_map,List.getElem_take,List.getElem_drop,List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega)]
    rfl

private theorem packed_segment (x y : List Bool) (j r : ℕ)
    (hj : j % blockSize y=0) (hr : 0 < r) (hb : r ≤ blockSize y) (hx : j+r ≤ x.length) :
    openWord x y j ++ bitSegment x j r=packedPrefix x y (j+r) := by
  rw [packed_block x y j r hj hb hx,openWord,segment_as_range x j r hx]
  simp only [hr,and_true]

private theorem window_read (x y : List Bool) (j : ℕ) (preWord : List Sym) (q : CountedStream.State)
    (hj : j < x.length) :
    (windowFrame x y j preWord q).cells 0 ((windowFrame x y j preWord q).head 0)=
      machine.bitSym x[j] := by
  change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD j machine.blank=_
  rw [List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem window_read_end (x y : List Bool) (preWord : List Sym) (q : CountedStream.State) :
    (windowFrame x y x.length preWord q).cells 0
      ((windowFrame x y x.length preWord q).head 0)=Sym.sep := by
  change (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym).getD x.length machine.blank=_
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem owned_intmulcountedblocksplittercalls_tapeOf_append_one (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a=machine.tapeOf (w++[a]) := by
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
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem separator_window (x y : List Bool) (j : ℕ) (preWord : List Sym) :
    subroutine.step {streamLift (windowFrame x y j preWord .halt) with state := .inr ()}=
      streamLift (windowFrame x y j (preWord++[Sym.sep]) .emit) := by
  rw [separator_step _ rfl (by
    change preWord.getD preWord.length Sym.blank=Sym.blank
    exact List.getD_eq_default _ _ le_rfl)]
  apply owned_intmulcountedblocksplittercalls_cfg_ext
  · rfl
  · funext i
    fin_cases i
    · simp [streamLift,windowFrame]
    · change Function.update (machine.tapeOf preWord) (preWord.length+1) Sym.sep=_
      exact owned_intmulcountedblocksplittercalls_tapeOf_append_one _ _
    · simp [streamLift,windowFrame]
    · simp [streamLift,windowFrame]
  · funext i
    fin_cases i <;> simp [streamLift,windowFrame]

/-- A full nonfinal block includes the service return and the actual separator
write. Both descriptor tapes and all boundary heads are restored. -/
private theorem nonfinal_block (x y : List Bool) (j : ℕ)
    (hj : j % blockSize y=0) (hx : j+blockSize y < x.length) :
    ∃ t, t ≤ 6*blockSize y+4*y.length+4 ∧
      machine.step^[t] (ready x y j)=ready x y (j+blockSize y) := by
  have hb : 0 < blockSize y := by unfold blockSize; omega
  obtain ⟨s,hs,he⟩ := window_block x y j (openWord x y j) (open_length x y j (by omega)) hx.le
  rw [packed_segment x y j (blockSize y) hj hb le_rfl hx.le] at he
  have hr := stream_run (windowFrame x y j (openWord x y j) .emit) s
  rw [he] at hr
  obtain ⟨t,ht,htRun⟩ := call false _ s (by rw [hr]; rfl)
  rw [hr,after_live _ (by
    change (windowFrame x y (j+blockSize y) (packedPrefix x y (j+blockSize y)) .halt).cells 0
      ((windowFrame x y (j+blockSize y) (packedPrefix x y (j+blockSize y)) .halt).head 0)=Sym.zero ∨
      (windowFrame x y (j+blockSize y) (packedPrefix x y (j+blockSize y)) .halt).cells 0
      ((windowFrame x y (j+blockSize y) (packedPrefix x y (j+blockSize y)) .halt).head 0)=Sym.one
    rw [window_read _ _ _ _ _ hx]
    cases x[j+blockSize y] <;> decide)] at htRun
  have hsep := separator_window x y (j+blockSize y) (packedPrefix x y (j+blockSize y))
  have hostSep := segment false _ 1 (by
    rw [Function.iterate_one,hsep]
    change Sum.inl CountedStream.State.emit ≠ Sum.inl CountedStream.State.halt
    decide)
  simp only [Function.iterate_one,hsep] at hostSep
  refine ⟨1+t,by omega,?_⟩
  rw [Function.iterate_add_apply]
  change machine.step^[1] (machine.step^[t] (lift false (streamLift
    (windowFrame x y j (openWord x y j) .emit))))=_
  rw [htRun,Function.iterate_one,hostSep]
  simp only [ready,openWord,show 0 < j+blockSize y by omega,if_true]

end IntMul.CountedBlockSplitter



namespace IntMul.CountedBlockSplitter

open IntMul.TapeCopy (Sym)

private theorem owned_intmulcountedblocksplitterexecution_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private abbrev blockCost (y : List Bool) : ℕ := 6*blockSize y+4*y.length+4

private theorem full_blocks (x y : List Bool) (q j : ℕ)
    (hj : j % blockSize y=0) (hx : j+q*blockSize y < x.length) :
    ∃ t, t ≤ q*blockCost y ∧
      machine.step^[t] (ready x y j)=ready x y (j+q*blockSize y) := by
  induction q generalizing j with
  | zero => refine ⟨0,by simp,?_⟩; simp
  | succ q ih =>
    have hx' : j+blockSize y+q*blockSize y < x.length := by
      rw [Nat.succ_mul] at hx
      omega
    obtain ⟨u,hu,he⟩ := nonfinal_block x y j hj (by omega)
    obtain ⟨v,hv,hr⟩ := ih (j+blockSize y) (by simp [Nat.add_mod,hj]) hx'
    refine ⟨v+u,?_,?_⟩
    · rw [Nat.succ_mul]
      dsimp only [blockCost] at hv ⊢
      omega
    · rw [Function.iterate_add_apply,he,hr]
      apply congrArg (ready x y)
      rw [Nat.succ_mul]
      omega

private theorem cleanup (x y bits : List Bool) (hw : bits.length=y.length) :
    ∃ t, t ≤ 2*y.length+3 ∧
      machine.step^[t]
        (lift true (streamLift (CountedStream.resetFrame
          (windowFrame x y x.length (packedPrefix x y x.length) .halt)
          .resetLeft bits y (y.length+1))))=frame x y x.length none := by
  have hr := stream_run (CountedStream.resetFrame
    (windowFrame x y x.length (packedPrefix x y x.length) .halt)
    .resetLeft bits y (y.length+1)) (2*y.length+2)
  rw [window_cleanup _ _ _ _ _ hw] at hr
  obtain ⟨t,ht,he⟩ := call true _ (2*y.length+2) (by rw [hr]; rfl)
  refine ⟨t,by omega,?_⟩
  rw [hr] at he
  exact he

private theorem final_word (x y : List Bool) (j r : ℕ)
    (hj : j % blockSize y=0) (hb : r ≤ blockSize y) (hx : j+r=x.length)
    (hz : r=0 → j=0) :
    openWord x y j++bitSegment x j r=packedPrefix x y x.length := by
  by_cases hr : r=0
  · have h := hz hr
    have hn : x.length=0 := by omega
    rw [h,hr,show x.length=0 from hn]
    simp [openWord,packed_zero,bitSegment]
  · rw [packed_segment x y j r hj (by omega) hb hx.le,hx]

/-- A final full or short block runs cleanup and its actual global-halt
dispatch, with no trailing separator. The empty input is also included. -/
private theorem last_block (x y : List Bool) (j r : ℕ)
    (hj : j % blockSize y=0) (hr : r ≤ blockSize y) (hx : j+r=x.length)
    (hz : r=0 → j=0) :
    ∃ t, t ≤ 6*r+6*y.length+6 ∧
      machine.step^[t] (ready x y j)=frame x y x.length none := by
  have hp := final_word x y j r hj hr hx hz
  have hl := open_length x y j (by omega)
  by_cases hfull : r=blockSize y
  · obtain ⟨s,hs,he⟩ := window_block x y j (openWord x y j) hl (by omega)
    rw [←hfull,hx,hp] at he
    have hsub := stream_run (windowFrame x y j (openWord x y j) .emit) s
    rw [he] at hsub
    obtain ⟨u,hu,huRun⟩ := call false _ s (by rw [hsub]; rfl)
    rw [hsub,after_end _ (window_read_end x y (packedPrefix x y x.length) .halt)] at huRun
    change machine.step^[u] (ready x y j)=
      lift true (streamLift (windowFrame x y x.length (packedPrefix x y x.length) .resetLeft)) at huRun
    rw [←window_reset_identity x y x.length (packedPrefix x y x.length) .resetLeft] at huRun
    obtain ⟨v,hv,hc⟩ := cleanup x y y rfl
    refine ⟨v+u,by omega,?_⟩
    rw [Function.iterate_add_apply,huRun,hc]
  · have hsmall : r ≤ IntMul.val y := by unfold blockSize at hr hfull; omega
    obtain ⟨s,hs,he⟩ := window_tail x y j r (openWord x y j) hl hsmall hx
    rw [hx,hp] at he
    let bits := (CountedStream.iterateCounter r y.reverse).reverse
    have hw : bits.length=y.length := by
      simp only [bits,List.length_reverse,CountedStream.iterate_counter_length]
    have hsub := stream_run (windowFrame x y j (openWord x y j) .emit) s
    rw [he] at hsub
    obtain ⟨u,hu,huRun⟩ := call false _ s (by rw [hsub]; rfl)
    rw [hsub,after_end _ (by
      simpa [streamLift,CountedStream.resetFrame] using
        window_read_end x y (packedPrefix x y x.length) .halt)] at huRun
    change machine.step^[u] (ready x y j)=
      lift true (streamLift (CountedStream.resetFrame
        (windowFrame x y x.length (packedPrefix x y x.length) .halt)
        .resetLeft bits y (y.length+1))) at huRun
    obtain ⟨v,hv,hc⟩ := cleanup x y bits hw
    refine ⟨v+u,by omega,?_⟩
    rw [Function.iterate_add_apply,huRun,hc]

private theorem setup (x y : List Bool) :
    machine.step^[2*x.length+2*y.length+5] (machine.initCfg x y)=ready x y 0 := by
  have hr := stream_run (CountedStream.machine.initCfg x y) (2*x.length+2*y.length+5)
  rw [CountedStream.setup_ready] at hr
  have hi : machine.initCfg x y=lift false (streamLift (CountedStream.machine.initCfg x y)) := rfl
  rw [hi,segment false _ _ (by
    rw [hr]
    change Sum.inl CountedStream.State.emit ≠ Sum.inl CountedStream.State.halt
    decide),hr]
  simp only [ready,openWord,packed_zero,show ¬0 < (0:ℕ) by omega,if_false,List.append_nil]
  have hw : CountedStream.readyFrame x y 0 .emit=windowFrame x y 0 [] .emit := by
    apply owned_intmulcountedblocksplitterexecution_cfg_ext
    · rfl
    · funext i
      fin_cases i <;> simp [CountedStream.readyFrame,windowFrame]
    · funext i
      fin_cases i <;> simp [CountedStream.readyFrame,windowFrame]
  rw [hw]

end IntMul.CountedBlockSplitter



namespace IntMul.CountedBlockSplitter

/-- One fixed four-tape machine writes descriptor-sized separated blocks,
restores both descriptor tapes and their heads, and halts at the exact frame.
Every service return, separator write and final cleanup is charged. -/
private theorem split_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8*x.length+((x.length-1)/blockSize y)*(4*y.length+4)+8*y.length+11 ∧
      machine.step^[t] (machine.initCfg x y)=frame x y x.length none ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt := by
  let q := (x.length-1)/blockSize y
  let j := q*blockSize y
  let r := x.length-j
  have hB : 0 < blockSize y := by unfold blockSize; omega
  have hjle : j ≤ x.length := by
    have hm := Nat.div_mul_le_self (x.length-1) (blockSize y)
    dsimp only [j,q]
    omega
  have hjr : j+r=x.length := by dsimp only [r]; omega
  have hmod : j%blockSize y=0 := by simp [j]
  have hr : r ≤ blockSize y := by
    have hm := Nat.mod_lt (x.length-1) hB
    have he := Nat.div_add_mod (x.length-1) (blockSize y)
    rw [Nat.mul_comm] at he
    dsimp only [j,q,r]
    by_cases hn : x.length=0
    · simp [hn]
    · omega
  have hz : r=0 → j=0 := by
    intro hz
    have hm := Nat.div_mul_le_self (x.length-1) (blockSize y)
    change j ≤ x.length-1 at hm
    omega
  obtain ⟨v,hv,hend⟩ := last_block x y j r hmod hr hjr hz
  have hprefix : ∃ u : ℕ, u ≤ q*blockCost y ∧
      machine.step^[u] (ready x y 0)=ready x y j := by
    by_cases hn : x.length=0
    · refine ⟨0,by omega,?_⟩
      have hj : j=0 := by omega
      simp [hj]
    · have hjlt : j < x.length := by
        have hm := Nat.div_mul_le_self (x.length-1) (blockSize y)
        change j ≤ x.length-1 at hm
        omega
      simpa only [Nat.zero_add,j] using full_blocks x y q 0 (by simp) (by simpa using hjlt)
  obtain ⟨u,hu,hstart⟩ := hprefix
  let initTime := 2*x.length+2*y.length+5
  refine ⟨v+u+initTime,?_,?_,?_⟩
  · have hcost : q*blockCost y=6*j+q*(4*y.length+4) := by
      dsimp only [blockCost,j]
      ring
    rw [hcost] at hu
    change v+u+initTime ≤ 8*x.length+q*(4*y.length+4)+8*y.length+11
    dsimp only [initTime]
    omega
  · rw [Function.iterate_add_apply,setup,Function.iterate_add_apply,hstart,hend]
  · rw [Function.iterate_add_apply,setup,Function.iterate_add_apply,hstart,hend]
    rfl

end IntMul.CountedBlockSplitter


open IntMul.CountedBlockSplitter

theorem solution (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8*x.length+((x.length-1)/blockSize y)*(4*y.length+4)+8*y.length+11 ∧
      machine.step^[t] (machine.initCfg x y)=frame x y x.length none ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt :=
  IntMul.CountedBlockSplitter.split_blocks x y

#print axioms solution
