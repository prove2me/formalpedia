-- Prove2me | solution 1 for IntMul.InteriorBankedCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:43:37.771897+00:00
-- url     : https://prove2.me/submissions/71981cf0-8a83-4c83-aeb4-a8c1eebe00f9

import Definitions.Def_IntMul_InteriorBankedCall
import Theorems.Thm_IntMul_BankedSimulation_simulate_run
import Theorems.Thm_IntMul_InteriorBankedCall_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.InteriorBankedCall

private theorem bank_boundary (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ) (w : List M.Sym) :
    bankTape M base offset w offset = some M.startSym := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem bank_payload (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) :
    bankTape M base offset w (offset + p + 1) = some (w.getD p M.blank) := by
  rw [bankTape,if_neg (by omega),show offset + p + 1 - offset = p + 1 by omega]
  rfl

private theorem bank_append_one (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (a : M.Sym) :
    Function.update (bankTape M base offset w) (offset + w.length + 1) (some a) =
      bankTape M base offset (w ++ [a]) := by
  classical
  funext p
  by_cases hp : p < offset
  · rw [Function.update_of_ne (by omega : p ≠ offset + w.length + 1)]
    simp only [bankTape,if_pos hp]
  · by_cases he : p = offset + w.length + 1
    · subst p
      rw [Function.update_self,bank_payload]
      simp
    · rw [Function.update_of_ne he]
      simp only [bankTape,if_neg hp]
      cases hq : p - offset with
      | zero => rfl
      | succ q =>
          change some (w.getD q M.blank) = some ((w ++ [a]).getD q M.blank)
          by_cases hlt : q < w.length
          · rw [List.getD_append _ _ _ _ hlt]
          · have hge : w.length ≤ q := by omega
            rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge,
              List.getD_eq_default _ _ (by simp; omega)]

private theorem fresh_mark (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ) :
    Function.update (freshTape M base offset) offset (some M.startSym) = bankTape M base offset [] := by
  classical
  funext p
  by_cases he : p = offset
  · subst p
    rw [Function.update_self,bank_boundary]
  · rw [Function.update_of_ne he]
    by_cases hp : p < offset
    · simp only [freshTape,bankTape,if_pos hp]
    · simp only [freshTape,bankTape,if_neg hp]
      have hg : 0 < p - offset := by omega
      cases hq : p - offset with
      | zero => omega
      | succ q => rfl

private theorem source_mark (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ) (w : List M.Sym) :
    Function.update (sourceTape M base sigma w) sigma (some M.startSym) = copyTape M base sigma w 0 := by
  classical
  funext p
  by_cases he : p = sigma
  · subst p
    simp [copyTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp only [sourceTape,copyTape,if_pos hp]
    · simp only [sourceTape,copyTape,if_neg hp,if_neg he,if_neg (by omega : ¬p < sigma + 0 + 1)]

private theorem copy_read (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    copyTape M base sigma w j (sigma + j + 1) = some (w.getD j M.blank) := by
  simp only [copyTape,if_neg (by omega : ¬sigma + j + 1 < sigma),
    if_neg (by omega : sigma + j + 1 ≠ sigma),if_neg (by omega : ¬sigma + j + 1 < sigma + j + 1)]
  congr 2
  omega

private theorem copy_erase (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) (j : ℕ) :
    Function.update (copyTape M base sigma w j) (sigma + j + 1) (some M.blank) =
      copyTape M base sigma w (j + 1) := by
  classical
  funext p
  by_cases he : p = sigma + j + 1
  · subst p
    simp [copyTape,show ¬sigma + j + 1 < sigma by omega,show sigma + j + 1 ≠ sigma by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < sigma
    · simp only [copyTape,if_pos hp]
    · by_cases hs : p = sigma
      · simp only [copyTape,if_neg hp,if_pos hs]
      · simp only [copyTape,if_neg hp,if_neg hs]
        by_cases hj : p < sigma + j + 1
        · simp only [if_pos hj,if_pos (by omega : p < sigma + (j + 1) + 1)]
        · simp only [if_neg hj,if_neg (by omega : ¬p < sigma + (j + 1) + 1)]

private theorem copy_finished (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) : copyTape M base sigma w w.length = bankTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp only [copyTape,bankTape,if_pos hp]
  · by_cases he : p = sigma
    · subst p
      simp [copyTape,bankTape,MultitapeTM.tapeOf]
    · simp only [copyTape,bankTape,if_neg hp,if_neg he]
      have hg : 0 < p - sigma := by omega
      cases hq : p - sigma with
      | zero => omega
      | succ q =>
          simp only [MultitapeTM.tapeOf,List.getD_nil]
          by_cases hw : p < sigma + w.length + 1
          · simp only [if_pos hw]
          · rw [if_neg hw,List.getD_eq_default _ _ (by omega)]

end IntMul.InteriorBankedCall



namespace IntMul.InteriorBankedCall

private theorem run_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def run_lift (M : MultitapeTM) (b : (BankedSimulation.machine M).Cfg) :
    (machine M).Cfg where
  state := .inr b.state
  cells := b.cells
  head := b.head

private theorem run_lift_step (M : MultitapeTM) (b : (BankedSimulation.machine M).Cfg)
    (h : b.state ≠ M.qHalt) :
    (machine M).step (run_lift M b) = run_lift M ((BankedSimulation.machine M).step b) := by
  classical
  apply run_cfg_ext
  · simp [MultitapeTM.step,run_lift,transition,rawTransition,h]
  · simp [MultitapeTM.step,run_lift,transition,rawTransition,h]
  · simp [MultitapeTM.step,run_lift,transition,rawTransition,h]

private theorem run_markers_step (M : MultitapeTM) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) : ∀ j, (M.step c).cells j 0 = M.startSym := by
  classical
  intro j
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 0 = _
  by_cases hh : c.head j = 0
  · rw [hh,Function.update_self]
    exact (M.start_preserved c.state (fun j => c.cells j (c.head j)) j
      (by rw [hh,marker j])).1
  · rw [Function.update_of_ne (by omega : 0 ≠ c.head j)]
    exact marker j

private theorem run_markers_iterate (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    ∀ j, (M.step^[T] c).cells j 0 = M.startSym := by
  induction T with
  | zero => exact marker
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact run_markers_step M _ ih

private theorem run_running_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (c : M.Cfg)
    (h : c.state ≠ M.qHalt) (marker : ∀ j, c.cells j 0 = M.startSym) :
    (machine M).step (runningFrame M base sigma offset x y c) =
      runningFrame M base sigma offset x y (M.step c) := by
  have hs := (BankedSimulation.simulate_run M (callerBase M base sigma x y) offset
    positive c 1 marker).1
  simp only [Function.iterate_one] at hs
  change (machine M).step (run_lift M (BankedSimulation.embed M (callerBase M base sigma x y) offset c)) =
    run_lift M (BankedSimulation.embed M (callerBase M base sigma x y) offset (M.step c))
  rw [run_lift_step M _ h,hs]

private theorem run_running_iterate (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym)
    (h : ∀ s : ℕ, s < T → (M.step^[s] c).state ≠ M.qHalt) :
    (machine M).step^[T] (runningFrame M base sigma offset x y c) =
      runningFrame M base sigma offset x y (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact h s (by omega)),
        run_running_step M base sigma offset positive x y _ (h T (by omega))
          (run_markers_iterate M c T marker),Function.iterate_succ_apply']

private theorem run_child_halted_step (M : MultitapeTM) (c : M.Cfg) (h : c.state = M.qHalt) :
    M.step c = c := by
  apply run_cfg_ext
  · simp [MultitapeTM.step,h,M.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,h,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,h,M.halt_fixed]

private theorem run_child_halted_iterate (M : MultitapeTM) (c : M.Cfg)
    (h : c.state = M.qHalt) (n : ℕ) : M.step^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,run_child_halted_step M c h]

private theorem run_first_halt (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (h : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T ∧ M.step^[t] c = M.step^[T] c ∧
      ∀ s : ℕ, s < t → (M.step^[s] c).state ≠ M.qHalt := by
  classical
  have hex : ∃ t : ℕ, (M.step^[t] c).state = M.qHalt := ⟨T,h⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex h
  have hh : (M.step^[t] c).state = M.qHalt := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T = (T - t) + t by omega,Function.iterate_add_apply,run_child_halted_iterate M _ hh]
  · intro s hs
    exact Nat.find_min hex hs

private theorem run_running_output_head (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M base sigma offset x y c).head i = offset M.outTape + c.head M.outTape := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he]

private theorem run_return_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (h : c.state = M.qHalt) :
    (machine M).step (runningFrame M base sigma offset x y c) =
      returnOutputFrame M base sigma offset x y c ((BankedCall.inputWord M x y).length + 1)
        (c.head M.outTape) := by
  classical
  have ht : transition M (runningFrame M base sigma offset x y c).state
      (fun i => (runningFrame M base sigma offset x y c).cells i
        ((runningFrame M base sigma offset x y c).head i)) =
      (.inl .rewindOutput,fun i => ((runningFrame M base sigma offset x y c).cells i
        ((runningFrame M base sigma offset x y c).head i),.stay)) := by
    simp [runningFrame,transition,rawTransition,h]
  apply run_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,if_pos hi,runningFrame,BankedSimulation.embed,
        dif_neg (by omega : ¬2 ≤ i.val),callerBase,if_pos hi,Nat.add_assoc]
    · by_cases ho : i.val = 3
      · simpa only [returnOutputFrame,if_neg hi,if_pos ho] using
          run_running_output_head M base sigma offset x y c i ho
      · simp only [returnOutputFrame,if_neg hi,if_neg ho]

/-- The child is simulated through its first halt, then one actual transition
enters the two-head return phase, preserving its complete terminal banks. -/
private theorem run_to_return (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) (halt : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T + 1 ∧
      (machine M).step^[t] (runningFrame M base sigma offset x y c) =
        returnOutputFrame M base sigma offset x y (M.step^[T] c)
          ((BankedCall.inputWord M x y).length + 1) ((M.step^[T] c).head M.outTape) := by
  obtain ⟨t,ht,he,hn⟩ := run_first_halt M c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',run_running_iterate M base sigma offset positive x y c t marker hn,
    he,run_return_step M base sigma offset x y _ halt]

end IntMul.InteriorBankedCall



namespace IntMul.InteriorBankedCall

private theorem output_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem output_protect_right (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .right = (a,.right) := by
  cases a <;> rfl

private theorem output_protect_stay (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .stay = (a,.stay) := by
  cases a <;> rfl

private theorem output_protect_left (M : MultitapeTM) (a : Option M.Sym) (h : a ≠ none) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem output_running_output_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym))
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M base sigma offset x y c).cells i =
      bankTape M (base.cells i) (offset M.outTape) (w.map M.bitSym) := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  funext p
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he,out,bankTape]
  by_cases hp : p < offset M.outTape
  · simp only [if_pos hp,callerBase,if_neg (by omega : i.val ≠ 1)]
  · simp only [if_neg hp]

private theorem output_running_buffer_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 1) :
    (runningFrame M base sigma offset x y c).cells i = bankTape M (base.cells i) sigma [] := by
  simp only [runningFrame,BankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),callerBase,if_pos hi]

private theorem output_payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem output_bank_marker_iff (M : MultitapeTM) (base : ℕ → Option M.Sym)
    (offset : ℕ) (w : List Bool) (p : ℕ) :
    bankTape M base offset (w.map M.bitSym) (offset + p) = some M.startSym ↔ p = 0 := by
  cases p with
  | zero => simp only [Nat.add_zero,bank_boundary,iff_true]
  | succ p =>
      rw [show offset + (p + 1) = offset + p + 1 by omega,bank_payload]
      simp only [Option.some.injEq,Nat.succ_ne_zero,iff_false]
      exact output_payload_not_marker M w p

private theorem output_bank_not_none (M : MultitapeTM) (base : ℕ → Option M.Sym)
    (offset : ℕ) (w : List M.Sym) (p : ℕ) :
    bankTape M base offset w (offset + p) ≠ none := by
  simp only [bankTape,if_neg (by omega : ¬offset + p < offset), ]
  exact Option.some_ne_none _

private theorem output_return_scans (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    let f := returnOutputFrame M base sigma offset x y c a b
    (f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.startSym ↔ a = 0) ∧
    (f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym ↔ b = 0) ∧
    f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none ∧
    f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
  dsimp only
  have h₁ : (returnOutputFrame M base sigma offset x y c a b).cells
      ⟨1,by change 1 < M.k + 2; omega⟩
      ((returnOutputFrame M base sigma offset x y c a b).head ⟨1,by change 1 < M.k + 2; omega⟩) =
      bankTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma [] (sigma + a) := by
    change (runningFrame M base sigma offset x y c).cells ⟨1,by change 1 < M.k + 2; omega⟩ (sigma + a) = _
    rw [output_running_buffer_cells M base sigma offset x y c _ rfl]
  have h₃ : (returnOutputFrame M base sigma offset x y c a b).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M base sigma offset x y c a b).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) =
      bankTape M (base.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) (offset M.outTape) (w.map M.bitSym) (offset M.outTape + b) := by
    change (runningFrame M base sigma offset x y c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.outTape + b) = _
    rw [output_running_output_cells M base sigma offset x y c w out _ rfl]
  rw [h₁,h₃]
  exact ⟨output_bank_marker_iff M _ sigma [] a,output_bank_marker_iff M _ _ w b,
    output_bank_not_none M _ _ _ _,output_bank_not_none M _ _ _ _⟩

private theorem output_return_left_transition (M : MultitapeTM) (f : (machine M).Cfg) (a b : ℕ)
    (h₁ : f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.startSym ↔ a = 0)
    (h₃ : f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym ↔ b = 0)
    (n₁ : f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none)
    (n₃ : f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none)
    (hab : ¬(a = 0 ∧ b = 0)) :
    transition M (.inl .rewindOutput) (fun i => f.cells i (f.head i)) =
      (.inl .rewindOutput,fun i => (f.cells i (f.head i),
        if i.val = 1 then (if a = 0 then .stay else .left)
        else if i.val = 3 then (if b = 0 then .stay else .left) else .stay)) := by
  classical
  have hn : ¬(f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.startSym ∧
      f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym) := by
    intro h
    exact hab ⟨h₁.mp h.1,h₃.mp h.2⟩
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
    by_cases ha : a = 0
    · have hm : f.cells i (f.head i) = some M.startSym := by rw [he]; exact h₁.mpr ha
      have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some M.startSym) := by intro h; exact h.2 hm
      simp only [if_neg hd,if_pos hi,if_pos ha,output_protect_stay]
    · have hm : f.cells i (f.head i) ≠ some M.startSym := by rw [he]; exact mt h₁.mp ha
      have hd : (i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some M.startSym := ⟨Or.inl hi,hm⟩
      simp only [if_pos hd,if_pos hi,if_neg ha]
      exact output_protect_left M _ (by rw [he]; exact n₁)
  · by_cases ho : i.val = 3
    · have he : i = ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext ho
      by_cases hb : b = 0
      · have hm : f.cells i (f.head i) = some M.startSym := by rw [he]; exact h₃.mpr hb
        have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some M.startSym) := by intro h; exact h.2 hm
        simp only [if_neg hd,if_neg hi,if_pos ho,if_pos hb,output_protect_stay]
      · have hm : f.cells i (f.head i) ≠ some M.startSym := by rw [he]; exact mt h₃.mp hb
        have hd : (i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some M.startSym := ⟨Or.inr ho,hm⟩
        simp only [if_pos hd,if_neg hi,if_pos ho,if_neg hb]
        exact output_protect_left M _ (by rw [he]; exact n₃)
    · have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some M.startSym) := by tauto
      simp only [if_neg hi,if_neg ho,if_neg hd,output_protect_stay]

private theorem output_return_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ)
    (hab : ¬(a = 0 ∧ b = 0)) :
    (machine M).step (returnOutputFrame M base sigma offset x y c a b) =
      returnOutputFrame M base sigma offset x y c (a - 1) (b - 1) := by
  obtain ⟨h₁,h₃,n₁,n₃⟩ := output_return_scans M base sigma offset x y c w out a b
  have ht := output_return_left_transition M (returnOutputFrame M base sigma offset x y c a b) a b h₁ h₃ n₁ n₃ hab
  change transition M (returnOutputFrame M base sigma offset x y c a b).state
    (fun i => (returnOutputFrame M base sigma offset x y c a b).cells i
      ((returnOutputFrame M base sigma offset x y c a b).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,if_pos hi]
      by_cases ha : a = 0
      · simp only [if_pos ha]
        subst a
        rfl
      · simp only [if_neg ha]
        omega
    · by_cases ho : i.val = 3
      · simp only [returnOutputFrame,if_neg hi,if_pos ho]
        by_cases hb : b = 0
        · simp only [if_pos hb]
          subst b
          rfl
        · simp only [if_neg hb]
          omega
      · simp only [returnOutputFrame,if_neg hi,if_neg ho]

/-- Each return head stops independently at its marker. The exact number of
left transitions is the maximum of the two initial distances. -/
private theorem rewind_pair_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b] (returnOutputFrame M base sigma offset x y c a b) =
      returnOutputFrame M base sigma offset x y c 0 0 := by
  generalize hn : max a b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      by_cases hz : a = 0 ∧ b = 0
      · obtain ⟨rfl,rfl⟩ := hz
        simp only [max_self] at hn
        subst n
        rfl
      · have hm : max (a - 1) (b - 1) < n := by omega
        have he : n = max (a - 1) (b - 1) + 1 := by omega
        rw [he,Function.iterate_succ_apply,output_return_left_step M base sigma offset x y c w out a b hz]
        exact ih _ hm (a - 1) (b - 1) rfl

private theorem output_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h₁ : a ⟨1,by omega⟩ = some M.startSym)
    (h₃ : a ⟨3,by have := M.two_le_k; omega⟩ = some M.startSym) :
    transition M (.inl .rewindOutput) a = (.inl .copyOutput,fun i =>
      (a i,if i.val = 1 ∨ i.val = 3 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos (And.intro h₁ h₃)]
  congr 1
  funext i
  by_cases hi : i.val = 1 ∨ i.val = 3
  · simp only [if_pos hi,output_protect_right]
  · simp only [if_neg hi,output_protect_stay]

private theorem output_return_marker_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (returnOutputFrame M base sigma offset x y c 0 0) =
      copyOutputFrame M base sigma offset x y c w 0 := by
  obtain ⟨h₁,h₃,_,_⟩ := output_return_scans M base sigma offset x y c w out 0 0
  have ht := output_return_marker_transition M
    (fun i => (returnOutputFrame M base sigma offset x y c 0 0).cells i
      ((returnOutputFrame M base sigma offset x y c 0 0).head i)) (h₁.mpr rfl) (h₃.mpr rfl)
  change transition M (returnOutputFrame M base sigma offset x y c 0 0).state
    (fun i => (returnOutputFrame M base sigma offset x y c 0 0).cells i
      ((returnOutputFrame M base sigma offset x y c 0 0).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,List.take_zero,List.map_nil]
      exact output_running_buffer_cells M base sigma offset x y c i hi
    · simp only [returnOutputFrame,copyOutputFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,if_pos (Or.inl hi)]
    · by_cases ho : i.val = 3
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_pos ho,if_pos (Or.inr ho)]
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_neg ho,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3))]

private theorem rewind_output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + 1] (returnOutputFrame M base sigma offset x y c a b) =
      copyOutputFrame M base sigma offset x y c w 0 := by
  rw [Function.iterate_succ_apply',rewind_pair_correct M base sigma offset x y c w out a b,
    output_return_marker_step M base sigma offset x y c w out]

private theorem output_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (b : Bool) (source : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.bitSym b))
    (target : a ⟨1,by omega⟩ = some M.blank) :
    transition M (.inl .copyOutput) a = (.inl .copyOutput,fun i =>
      (if i.val = 1 then some (M.bitSym b) else a i,
        if i.val = 1 ∨ i.val = 3 then .right else .stay)) := by
  classical
  have hb : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.zero ∨
      a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.one := by
    rw [source]
    cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases ht : i.val = 1
  · have he : i = ⟨1,by omega⟩ := Fin.ext ht
    simp only [if_pos ht,if_pos (Or.inl ht)]
    rw [he,target,source]
    cases b <;> rfl
  · simp only [if_neg ht]
    by_cases hs : i.val = 3
    · simp only [if_pos (Or.inr hs),output_protect_right]
    · simp only [if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3)),output_protect_stay]

private theorem output_copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyOutputFrame M base sigma offset x y c w j) =
      copyOutputFrame M base sigma offset x y c w (j + 1) := by
  have hs : (copyOutputFrame M base sigma offset x y c w j).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M base sigma offset x y c w j).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.bitSym w[j]) := by
    change (runningFrame M base sigma offset x y c).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.outTape + j + 1) = _
    rw [output_running_output_cells M base sigma offset x y c w out _ rfl,bank_payload,
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have hb : (copyOutputFrame M base sigma offset x y c w j).cells
      ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyOutputFrame M base sigma offset x y c w j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.blank := by
    change bankTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma
      ((w.take j).map M.bitSym) (sigma + j + 1) = _
    rw [bank_payload,List.getD_eq_default _ _ (by simp [hl])]
  have ht := output_copy_transition M
    (fun i => (copyOutputFrame M base sigma offset x y c w j).cells i
      ((copyOutputFrame M base sigma offset x y c w j).head i)) w[j] hs hb
  change transition M (copyOutputFrame M base sigma offset x y c w j).state
    (fun i => (copyOutputFrame M base sigma offset x y c w j).cells i
      ((copyOutputFrame M base sigma offset x y c w j).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [if_pos hi,copyOutputFrame]
      change Function.update (bankTape M (base.cells i) sigma ((w.take j).map M.bitSym))
        (sigma + j + 1) (some (M.bitSym w[j])) =
          bankTape M (base.cells i) sigma ((w.take (j + 1)).map M.bitSym)
      rw [List.take_succ_eq_append_getElem hj]
      simpa only [hl,List.length_map,List.map_append,List.map_singleton] using
        bank_append_one M (base.cells i) sigma ((w.take j).map M.bitSym) (M.bitSym w[j])
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [copyOutputFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [copyOutputFrame,if_pos hi,if_pos (Or.inl hi),Nat.add_assoc]
    · by_cases ho : i.val = 3
      · simp only [copyOutputFrame,if_neg hi,if_pos ho,if_pos (Or.inr ho),Nat.add_assoc]
      · simp only [copyOutputFrame,if_neg hi,if_neg ho,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3))]

private theorem output_copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyOutputFrame M base sigma offset x y c w 0) =
      copyOutputFrame M base sigma offset x y c w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),
      output_copy_step M base sigma offset x y c w out j (by omega)]

private theorem output_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.blank) :
    transition M (.inl .copyOutput) a = (.inl .halt,fun i => (a i,.stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hn : ¬(a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.zero ∨
      a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.one) := by
    rw [h]
    simp only [Option.some.injEq,not_or]
    aesop
  simp [transition,rawTransition,hn,output_protect_stay]

private theorem output_copy_end_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (copyOutputFrame M base sigma offset x y c w w.length) =
      finalFrame M base sigma offset x y c w := by
  have hr : (copyOutputFrame M base sigma offset x y c w w.length).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M base sigma offset x y c w w.length).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change (runningFrame M base sigma offset x y c).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (offset M.outTape + w.length + 1) = _
    rw [output_running_output_cells M base sigma offset x y c w out _ rfl,bank_payload,
      List.getD_eq_default _ _ (by simp)]
  have ht := output_copy_end_transition M
    (fun i => (copyOutputFrame M base sigma offset x y c w w.length).cells i
      ((copyOutputFrame M base sigma offset x y c w w.length).head i)) hr
  change transition M (copyOutputFrame M base sigma offset x y c w w.length).state
    (fun i => (copyOutputFrame M base sigma offset x y c w w.length).cells i
      ((copyOutputFrame M base sigma offset x y c w w.length).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

/-- Full physical output return: both head rewinds run simultaneously, then
the child output is copied into the erased caller buffer and the caller halts. -/
private theorem output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + w.length + 2] (returnOutputFrame M base sigma offset x y c a b) =
      finalFrame M base sigma offset x y c w := by
  rw [show max a b + w.length + 2 = (w.length + (max a b + 1)) + 1 by omega,
    Function.iterate_succ_apply',Function.iterate_add_apply,
    rewind_output_correct M base sigma offset x y c w out a b,
    output_copy_run M base sigma offset x y c w out w.length le_rfl,output_copy_end_step M base sigma offset x y c w out]

end IntMul.InteriorBankedCall



namespace IntMul.InteriorBankedCall

private theorem main_init_markers (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).cells j 0 = M.startSym := by
  intro j
  simp only [MultitapeTM.initCfg]
  split <;> rfl

/-- Complete physical interior call with exact returned banks and output
buffer, charging setup, child execution, parallel head return and copy-back. -/
private theorem call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (w : List Bool) (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + max ((BankedCall.inputWord M x y).length + 1)
        ((M.step^[T] (M.initCfg x y)).head M.outTape) + w.length +
        2 * (BankedCall.inputWord M x y).length + 6 ∧
      (machine M).step^[t] (inputFrame M base sigma offset x y) =
        finalFrame M base sigma offset x y (M.step^[T] (M.initCfg x y)) w := by
  let c := M.step^[T] (M.initCfg x y)
  let L := (BankedCall.inputWord M x y).length
  obtain ⟨t,ht,hr⟩ := run_to_return M base sigma offset positive x y
    (M.initCfg x y) T (main_init_markers M x y) halts.1
  change (machine M).step^[t] (readyFrame M base sigma offset x y) =
    returnOutputFrame M base sigma offset x y c (L + 1) (c.head M.outTape) at hr
  have ho := output_correct M base sigma offset x y c w halts.2 (L + 1) (c.head M.outTape)
  let clock := 2 * L + 3 + t + (max (L + 1) (c.head M.outTape) + w.length + 2)
  have hp : (machine M).step^[t + (2 * L + 3)] (inputFrame M base sigma offset x y) =
      returnOutputFrame M base sigma offset x y c (L + 1) (c.head M.outTape) := by
    rw [Function.iterate_add_apply,setup_correct,hr]
  have he : (machine M).step^[clock] (inputFrame M base sigma offset x y) =
      finalFrame M base sigma offset x y c w := by
    rw [show clock = (max (L + 1) (c.head M.outTape) + w.length + 2) +
        (t + (2 * L + 3)) by unfold clock; omega,Function.iterate_add_apply,hp,ho]
  refine ⟨clock,?_,he⟩
  change clock ≤ T + max (L + 1) (c.head M.outTape) + w.length + 2 * L + 6
  unfold clock
  omega

private theorem main_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem main_head_run_bound (M : MultitapeTM) (x y : List Bool) (T : ℕ) (j : Fin M.k) :
    (M.step^[T] (M.initCfg x y)).head j ≤ T := by
  induction T with
  | zero => exact le_refl 0
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      have hs := main_head_step_bound M (M.step^[T] (M.initCfg x y)) j
      omega

/-- Arbitrary child terminal head positions give a universal 2T+linear bound. -/
private theorem call_bounded (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (w : List Bool) (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ, t ≤ 2 * T + w.length + 3 * (BankedCall.inputWord M x y).length + 7 ∧
      (machine M).step^[t] (inputFrame M base sigma offset x y) =
        finalFrame M base sigma offset x y (M.step^[T] (M.initCfg x y)) w := by
  obtain ⟨t,ht,he⟩ := call_correct M base sigma offset positive x y T w halts
  refine ⟨t,?_,he⟩
  have hh := main_head_run_bound M x y T M.outTape
  omega

/-- Saved caller prefixes survive the whole call. Global input zero and its
head are unchanged, while the buffer has exactly the returned tagged word. -/
private theorem final_saved_data (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg) (w : List Bool) :
    (finalFrame M base sigma offset x y c w).cells ⟨0,by change 0 < M.k + 2; omega⟩ =
      base.cells ⟨0,by change 0 < M.k + 2; omega⟩ ∧
    (finalFrame M base sigma offset x y c w).head ⟨0,by change 0 < M.k + 2; omega⟩ =
      base.head ⟨0,by change 0 < M.k + 2; omega⟩ ∧
    (finalFrame M base sigma offset x y c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      bankTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (w.map M.bitSym) ∧
    (∀ (p : ℕ), p < sigma →
      (finalFrame M base sigma offset x y c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ p =
        base.cells ⟨1,by change 1 < M.k + 2; omega⟩ p) ∧
    (∀ (i : Fin (M.k + 2)) (hi : 2 ≤ i.val) (p : ℕ),
      p < offset (BankedSimulation.innerTape M i hi) →
      (finalFrame M base sigma offset x y c w).cells i p = base.cells i p) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp only [finalFrame,copyOutputFrame,if_true,List.take_length]
  constructor
  · intro p hp
    simp only [finalFrame,copyOutputFrame,if_true,bankTape,if_pos hp]
  · intro i hi p hp
    have hn : i.val ≠ 1 := by omega
    simp only [finalFrame,copyOutputFrame,if_neg hn,runningFrame,BankedSimulation.embed,
      dif_pos hi,if_pos hp,callerBase,if_neg hn]

end IntMul.InteriorBankedCall


open IntMul IntMul.InteriorBankedCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (w : List Bool) (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + max ((BankedCall.inputWord M x y).length + 1)
        ((M.step^[T] (M.initCfg x y)).head M.outTape) + w.length +
        2 * (BankedCall.inputWord M x y).length + 6 ∧
      (machine M).step^[t] (inputFrame M base sigma offset x y) =
        finalFrame M base sigma offset x y (M.step^[T] (M.initCfg x y)) w :=
  IntMul.InteriorBankedCall.call_correct M base sigma offset positive x y T w halts

#print axioms solution
