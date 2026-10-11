-- Prove2me | solution 1 for IntMul.PreparedBankedCall.call_prepared
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T14:10:28.32016+00:00
-- url     : https://prove2.me/submissions/3e4fddec-c7e0-4fd9-81a7-c662d17f50ca

import Definitions.Def_IntMul_PreparedBankedCall
import Theorems.Thm_IntMul_BankedSimulation_simulate_run
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.PreparedBankedCall
open IntMul.BankedCall (Phase State transition rawTransition)

private theorem owned_intmulpreparedbankedcallrun_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def owned_intmulpreparedbankedcallrun_lift (M : MultitapeTM) (b : (BankedSimulation.machine M).Cfg) :
    (machine M).Cfg where
  state := .inr b.state
  cells := b.cells
  head := b.head

private theorem owned_intmulpreparedbankedcallrun_lift_step (M : MultitapeTM) (b : (BankedSimulation.machine M).Cfg)
    (h : b.state ≠ M.qHalt) :
    (machine M).step (owned_intmulpreparedbankedcallrun_lift M b) = owned_intmulpreparedbankedcallrun_lift M ((BankedSimulation.machine M).step b) := by
  classical
  apply owned_intmulpreparedbankedcallrun_cfg_ext
  · simp [MultitapeTM.step,owned_intmulpreparedbankedcallrun_lift,transition,rawTransition,h]
  · simp [MultitapeTM.step,owned_intmulpreparedbankedcallrun_lift,transition,rawTransition,h]
  · simp [MultitapeTM.step,owned_intmulpreparedbankedcallrun_lift,transition,rawTransition,h]

private theorem owned_intmulpreparedbankedcallrun_markers_step (M : MultitapeTM) (c : M.Cfg)
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

private theorem owned_intmulpreparedbankedcallrun_markers_iterate (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    ∀ j, (M.step^[T] c).cells j 0 = M.startSym := by
  induction T with
  | zero => exact marker
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact owned_intmulpreparedbankedcallrun_markers_step M _ ih

private theorem owned_intmulpreparedbankedcallrun_running_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (h : c.state ≠ M.qHalt) (marker : ∀ j, c.cells j 0 = M.startSym) :
    (machine M).step (runningFrame M base c) = runningFrame M base (M.step c) := by
  have hs := (BankedSimulation.simulate_run M (bankBase M base) (fun _ => 1)
    (by intro j; exact le_refl 1) c 1 marker).1
  simp only [Function.iterate_one] at hs
  change (machine M).step (owned_intmulpreparedbankedcallrun_lift M (BankedSimulation.embed M (bankBase M base) (fun _ => 1) c)) =
    owned_intmulpreparedbankedcallrun_lift M (BankedSimulation.embed M (bankBase M base) (fun _ => 1) (M.step c))
  rw [owned_intmulpreparedbankedcallrun_lift_step M _ h,hs]

private theorem owned_intmulpreparedbankedcallrun_running_iterate (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym)
    (h : ∀ s : ℕ, s < T → (M.step^[s] c).state ≠ M.qHalt) :
    (machine M).step^[T] (runningFrame M base c) = runningFrame M base (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact h s (by omega)),
        owned_intmulpreparedbankedcallrun_running_step M base _ (h T (by omega)) (owned_intmulpreparedbankedcallrun_markers_iterate M c T marker),Function.iterate_succ_apply']

private theorem owned_intmulpreparedbankedcallrun_child_halted_step (M : MultitapeTM) (c : M.Cfg) (h : c.state = M.qHalt) :
    M.step c = c := by
  apply owned_intmulpreparedbankedcallrun_cfg_ext
  · simp [MultitapeTM.step,h,M.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,h,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,h,M.halt_fixed]

private theorem owned_intmulpreparedbankedcallrun_child_halted_iterate (M : MultitapeTM) (c : M.Cfg)
    (h : c.state = M.qHalt) (n : ℕ) : M.step^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,owned_intmulpreparedbankedcallrun_child_halted_step M c h]

private theorem owned_intmulpreparedbankedcallrun_first_halt (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (h : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T ∧ M.step^[t] c = M.step^[T] c ∧
      ∀ s : ℕ, s < t → (M.step^[s] c).state ≠ M.qHalt := by
  classical
  have hex : ∃ t : ℕ, (M.step^[t] c).state = M.qHalt := ⟨T,h⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex h
  have hh : (M.step^[t] c).state = M.qHalt := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T = (T - t) + t by omega,Function.iterate_add_apply,owned_intmulpreparedbankedcallrun_child_halted_iterate M _ hh]
  · intro s hs
    exact Nat.find_min hex hs

private theorem owned_intmulpreparedbankedcallrun_running_output_head (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M base c).head i = 1 + c.head M.outTape := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he]

private theorem owned_intmulpreparedbankedcallrun_return_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (h : c.state = M.qHalt) :
    (machine M).step (runningFrame M base c) =
      returnOutputFrame M base c (1 + c.head M.outTape) := by
  classical
  have ht : transition M (runningFrame M base c).state
      (fun i => (runningFrame M base c).cells i ((runningFrame M base c).head i)) =
      (.inl .rewindOutput,fun i => ((runningFrame M base c).cells i ((runningFrame M base c).head i),.stay)) := by
    simp [runningFrame,transition,rawTransition,h]
  apply owned_intmulpreparedbankedcallrun_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 3
    · simpa only [returnOutputFrame,if_pos hi] using owned_intmulpreparedbankedcallrun_running_output_head M base c i hi
    · simp only [returnOutputFrame,if_neg hi]

/-- A terminating child call is simulated through its first halt, followed
by one actual transition into output return. Its complete final bank contents
and all heads are retained, even if the supplied child clock was padded. -/
private theorem run_to_return (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) (halt : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T + 1 ∧
      (machine M).step^[t] (runningFrame M base c) =
        returnOutputFrame M base (M.step^[T] c) (1 + (M.step^[T] c).head M.outTape) := by
  obtain ⟨t,ht,he,hn⟩ := owned_intmulpreparedbankedcallrun_first_halt M c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',owned_intmulpreparedbankedcallrun_running_iterate M base c t marker hn,he,owned_intmulpreparedbankedcallrun_return_step M base _ halt]

end IntMul.PreparedBankedCall



namespace IntMul.PreparedBankedCall
open IntMul.BankedCall (Phase State transition rawTransition)

private theorem owned_intmulpreparedbankedcalloutput_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulpreparedbankedcalloutput_protect_right (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .right = (a,.right) := by
  cases a <;> rfl

private theorem owned_intmulpreparedbankedcalloutput_protect_stay (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .stay = (a,.stay) := by
  cases a <;> rfl

private theorem owned_intmulpreparedbankedcalloutput_protect_left (M : MultitapeTM) (a : Option M.Sym) (h : a ≠ none) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem owned_intmulpreparedbankedcalloutput_bank_payload (M : MultitapeTM) (saved : ℕ → Option M.Sym) (w : List M.Sym) (p : ℕ) :
    bankTape M saved w (p + 2) = some (w.getD p M.blank) := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem owned_intmulpreparedbankedcalloutput_running_output_cells (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym))
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M base c).cells i = bankTape M (base.cells i) (w.map M.bitSym) := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  funext p
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he,out]
  by_cases hp : p=0
  · subst p
    simp only [bankTape,if_pos rfl,bankBase]
    rw [Function.update_of_ne (by intro h;have e:=congrArg Fin.val h;change i.val=1 at e;omega)]
    simp
  · simp [bankTape,bankBase,hp,show ¬p< 1 by omega,hi]

private theorem owned_intmulpreparedbankedcalloutput_running_global_output_cells (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 1) :
    (runningFrame M base c).cells i = (machine M).tapeOf [] := by
  have e : i=⟨1,by change 1 < M.k+2;omega⟩ := Fin.ext hi
  rw [e]
  simp [runningFrame,BankedSimulation.embed,bankBase]

private theorem owned_intmulpreparedbankedcalloutput_running_global_output_head (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 1) :
    (runningFrame M base c).head i = 1 := by
  have e : i=⟨1,by change 1 < M.k+2;omega⟩ := Fin.ext hi
  rw [e]
  simp [runningFrame,BankedSimulation.embed,bankBase]

private theorem owned_intmulpreparedbankedcalloutput_payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem owned_intmulpreparedbankedcalloutput_return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ ≠ some M.startSym)
    (hn : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ ≠ none) :
    transition M (.inl .rewindOutput) a = (.inl .rewindOutput,fun i =>
      (a i,if i.val = 3 then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg h]
  congr 1
  funext i
  by_cases hi : i.val = 3
  · simp only [if_pos hi]
    have he : i = ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext hi
    rw [he]
    exact owned_intmulpreparedbankedcalloutput_protect_left M _ hn
  · simp only [if_neg hi,owned_intmulpreparedbankedcalloutput_protect_stay]

private theorem owned_intmulpreparedbankedcalloutput_return_left_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step (returnOutputFrame M base c (p + 2)) = returnOutputFrame M base c (p + 1) := by
  have hr : (returnOutputFrame M base c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M base c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) =
          some ((w.map M.bitSym).getD p M.blank) := by
    change (runningFrame M base c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (p + 2) = _
    rw [owned_intmulpreparedbankedcalloutput_running_output_cells M base c w out _ rfl,owned_intmulpreparedbankedcalloutput_bank_payload]
  have hm : (returnOutputFrame M base c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M base c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some M.startSym := by
    rw [hr]
    exact fun he => owned_intmulpreparedbankedcalloutput_payload_not_marker M w p (Option.some.inj he)
  have hn : (returnOutputFrame M base c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M base c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have ht := owned_intmulpreparedbankedcalloutput_return_left_transition M
    (fun i => (returnOutputFrame M base c (p + 2)).cells i ((returnOutputFrame M base c (p + 2)).head i)) hm hn
  change transition M (returnOutputFrame M base c (p + 2)).state
    (fun i => (returnOutputFrame M base c (p + 2)).cells i ((returnOutputFrame M base c (p + 2)).head i)) = _ at ht
  apply owned_intmulpreparedbankedcalloutput_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 3
    · simp only [returnOutputFrame,if_pos hi]
      omega
    · simp only [returnOutputFrame,if_neg hi]

private theorem owned_intmulpreparedbankedcalloutput_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.startSym) :
    transition M (.inl .rewindOutput) a = (.inl .copyOutput,fun i =>
      (a i,if i.val = 3 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos h]
  congr 1
  funext i
  by_cases hi : i.val = 3
  · simp only [if_pos hi,owned_intmulpreparedbankedcalloutput_protect_right]
  · simp only [if_neg hi,owned_intmulpreparedbankedcalloutput_protect_stay]

private theorem owned_intmulpreparedbankedcalloutput_return_marker_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (returnOutputFrame M base c 1) = copyOutputFrame M base c w 0 := by
  have hr : (returnOutputFrame M base c 1).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M base c 1).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym := by
    change (runningFrame M base c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ 1 = _
    rw [owned_intmulpreparedbankedcalloutput_running_output_cells M base c w out _ rfl]
    rfl
  have ht := owned_intmulpreparedbankedcalloutput_return_marker_transition M
    (fun i => (returnOutputFrame M base c 1).cells i ((returnOutputFrame M base c 1).head i)) hr
  change transition M (returnOutputFrame M base c 1).state
    (fun i => (returnOutputFrame M base c 1).cells i ((returnOutputFrame M base c 1).head i)) = _ at ht
  apply owned_intmulpreparedbankedcalloutput_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,List.take_zero,List.map_nil]
      exact owned_intmulpreparedbankedcalloutput_running_global_output_cells M base c i hi
    · simp only [returnOutputFrame,copyOutputFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,if_neg (by omega : i.val ≠ 3)]
      exact owned_intmulpreparedbankedcalloutput_running_global_output_head M base c i hi
    · by_cases h₃ : i.val = 3
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_pos h₃]
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_neg h₃]

private theorem rewind_output_correct (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step^[p + 1] (returnOutputFrame M base c (p + 1)) = copyOutputFrame M base c w 0 := by
  induction p with
  | zero => simpa using owned_intmulpreparedbankedcalloutput_return_marker_step M base c w out
  | succ p ih => rw [Function.iterate_succ_apply,owned_intmulpreparedbankedcalloutput_return_left_step M base c w out p,ih]

private theorem owned_intmulpreparedbankedcalloutput_tape_append_one (N : MultitapeTM) (w : List N.Sym) (a : N.Sym) :
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

private theorem owned_intmulpreparedbankedcalloutput_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (b : Bool) (source : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some (M.bitSym b))
    (target : a ⟨1,by omega⟩ = some M.blank) :
    transition M (.inl .copyOutput) a = (.inl .copyOutput,fun i =>
      (if i.val = 1 then (machine M).bitSym b else a i,
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
    · simp only [if_pos (Or.inr hs),owned_intmulpreparedbankedcalloutput_protect_right]
    · simp only [if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3)),owned_intmulpreparedbankedcalloutput_protect_stay]

private theorem owned_intmulpreparedbankedcalloutput_copy_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyOutputFrame M base c w j) = copyOutputFrame M base c w (j + 1) := by
  have hs : (copyOutputFrame M base c w j).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M base c w j).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.bitSym w[j]) := by
    change (runningFrame M base c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (j + 2) = _
    rw [owned_intmulpreparedbankedcalloutput_running_output_cells M base c w out _ rfl,owned_intmulpreparedbankedcalloutput_bank_payload,
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have hb : (copyOutputFrame M base c w j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyOutputFrame M base c w j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.blank := by
    change ((w.take j).map (machine M).bitSym).getD j (some M.blank) = _
    exact List.getD_eq_default _ _ (by simp [hl])
  have ht := owned_intmulpreparedbankedcalloutput_copy_transition M
    (fun i => (copyOutputFrame M base c w j).cells i ((copyOutputFrame M base c w j).head i)) w[j] hs hb
  change transition M (copyOutputFrame M base c w j).state
    (fun i => (copyOutputFrame M base c w j).cells i ((copyOutputFrame M base c w j).head i)) = _ at ht
  apply owned_intmulpreparedbankedcalloutput_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [if_pos hi,copyOutputFrame]
      change Function.update ((machine M).tapeOf ((w.take j).map (machine M).bitSym))
        (j + 1) ((machine M).bitSym w[j]) =
          (machine M).tapeOf ((w.take (j + 1)).map (machine M).bitSym)
      rw [List.take_succ_eq_append_getElem hj]
      simpa only [hl,List.length_map,List.map_append,List.map_singleton] using
        owned_intmulpreparedbankedcalloutput_tape_append_one (machine M) ((w.take j).map (machine M).bitSym) ((machine M).bitSym w[j])
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [copyOutputFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [copyOutputFrame,if_pos hi,if_pos (Or.inl hi)]
    · by_cases h₃ : i.val = 3
      · simp only [copyOutputFrame,if_neg hi,if_pos h₃,if_pos (Or.inr h₃)]
      · simp only [copyOutputFrame,if_neg hi,if_neg h₃,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3))]

private theorem owned_intmulpreparedbankedcalloutput_copy_run (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyOutputFrame M base c w 0) = copyOutputFrame M base c w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),owned_intmulpreparedbankedcalloutput_copy_step M base c w out j (by omega)]

private theorem owned_intmulpreparedbankedcalloutput_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
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
  simp [transition,rawTransition,hn,owned_intmulpreparedbankedcalloutput_protect_stay]

private theorem owned_intmulpreparedbankedcalloutput_copy_end_step (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (copyOutputFrame M base c w w.length) = finalFrame M base c w := by
  have hr : (copyOutputFrame M base c w w.length).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M base c w w.length).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change (runningFrame M base c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (w.length + 2) = _
    rw [owned_intmulpreparedbankedcalloutput_running_output_cells M base c w out _ rfl,owned_intmulpreparedbankedcalloutput_bank_payload,
      List.getD_eq_default _ _ (by simp)]
  have ht := owned_intmulpreparedbankedcalloutput_copy_end_transition M
    (fun i => (copyOutputFrame M base c w w.length).cells i ((copyOutputFrame M base c w w.length).head i)) hr
  change transition M (copyOutputFrame M base c w w.length).state
    (fun i => (copyOutputFrame M base c w w.length).cells i ((copyOutputFrame M base c w w.length).head i)) = _ at ht
  apply owned_intmulpreparedbankedcalloutput_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

/-- Full physical output return from any distance p to the child marker,
including its head rewind, copied bits, and final blank dispatch. -/
private theorem output_correct (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step^[p + w.length + 2] (returnOutputFrame M base c (p + 1)) = finalFrame M base c w := by
  rw [show p + w.length + 2 = (w.length + (p + 1)) + 1 by omega,
    Function.iterate_succ_apply',Function.iterate_add_apply,rewind_output_correct M base c w out p,
    owned_intmulpreparedbankedcalloutput_copy_run M base c w out w.length le_rfl,owned_intmulpreparedbankedcalloutput_copy_end_step M base c w out]

end IntMul.PreparedBankedCall



namespace IntMul.PreparedBankedCall

/-- The complete prepared child computation and physical global-output
return, retaining the true read-only caller input and each bank prefix. -/
private theorem call_prepared (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym)
    (halt : (M.step^[T] c).state=M.qHalt) (w : List Bool)
    (out : (M.step^[T] c).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T+(M.step^[T] c).head M.outTape+w.length+3 ∧
      (machine M).step^[t] (runningFrame M base c)=finalFrame M base (M.step^[T] c) w ∧
      ((machine M).step^[t] (runningFrame M base c)).state=(machine M).qHalt ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).outTape=
        (machine M).tapeOf (w.map (machine M).bitSym) ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).inTape=base.cells (machine M).inTape ∧
      ((machine M).step^[t] (runningFrame M base c)).head (machine M).inTape=base.head (machine M).inTape ∧
      (∀ j, ((machine M).step^[t] (runningFrame M base c)).cells (BankedSimulation.workTape M j) 0=
        base.cells (BankedSimulation.workTape M j) 0) := by
  obtain ⟨s,hs,hes⟩ := run_to_return M base c T marker halt
  let p := (M.step^[T] c).head M.outTape
  have he : (machine M).step^[p+w.length+2+s] (runningFrame M base c)=
      finalFrame M base (M.step^[T] c) w := by
    rw [Function.iterate_add_apply,hes]
    simpa only [p,Nat.add_comm 1] using output_correct M base (M.step^[T] c) w out p
  refine ⟨p+w.length+2+s,by dsimp only [p];omega,he,?_,?_,?_,?_,?_⟩
  · rw [he];rfl
  · rw [he]
    simp [finalFrame,copyOutputFrame,MultitapeTM.outTape]
  · rw [he]
    simp [finalFrame,copyOutputFrame,runningFrame,BankedSimulation.embed,bankBase,MultitapeTM.inTape]
  · rw [he]
    simp [finalFrame,copyOutputFrame,runningFrame,BankedSimulation.embed,bankBase,MultitapeTM.inTape]
  · intro j
    rw [he]
    have hge : 2 ≤ (BankedSimulation.workTape M j).val := by simp [BankedSimulation.workTape]
    have hn : (BankedSimulation.workTape M j).val≠1 := by omega
    have he : BankedSimulation.workTape M j≠⟨1,by change 1 < M.k+2;omega⟩ := by
      intro h;have hv:=congrArg Fin.val h;change j.val+2=1 at hv;omega
    simp [finalFrame,copyOutputFrame,runningFrame,BankedSimulation.embed,bankBase,hge,hn,
      BankedSimulation.workTape]

end IntMul.PreparedBankedCall



open IntMul IntMul.PreparedBankedCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym)
    (halt : (M.step^[T] c).state=M.qHalt) (w : List Bool)
    (out : (M.step^[T] c).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T+(M.step^[T] c).head M.outTape+w.length+3 ∧
      (machine M).step^[t] (runningFrame M base c)=finalFrame M base (M.step^[T] c) w ∧
      ((machine M).step^[t] (runningFrame M base c)).state=(machine M).qHalt ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).outTape=
        (machine M).tapeOf (w.map (machine M).bitSym) ∧
      ((machine M).step^[t] (runningFrame M base c)).cells (machine M).inTape=base.cells (machine M).inTape ∧
      ((machine M).step^[t] (runningFrame M base c)).head (machine M).inTape=base.head (machine M).inTape ∧
      (∀ j, ((machine M).step^[t] (runningFrame M base c)).cells (BankedSimulation.workTape M j) 0=
        base.cells (BankedSimulation.workTape M j) 0) :=
  IntMul.PreparedBankedCall.call_prepared M base c T marker halt w out

#print axioms solution
