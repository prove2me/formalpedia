-- Prove2me | solution 1 for IntMul.BankedCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T21:12:51.276665+00:00
-- url     : https://prove2.me/submissions/ed4b8de2-47bf-4345-ba97-dd077b5c95ea

import Definitions.Def_IntMul_BankedCall
import Theorems.Thm_IntMul_BankedSimulation_simulate_run
import Theorems.Thm_IntMul_BankedCall_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.BankedCall

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

private theorem run_running_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (h : c.state ≠ M.qHalt) (marker : ∀ j, c.cells j 0 = M.startSym) :
    (machine M).step (runningFrame M x y c) = runningFrame M x y (M.step c) := by
  have hs := (BankedSimulation.simulate_run M (bankBase M x y) (fun _ => 1)
    (by intro j; exact le_refl 1) c 1 marker).1
  simp only [Function.iterate_one] at hs
  change (machine M).step (run_lift M (BankedSimulation.embed M (bankBase M x y) (fun _ => 1) c)) =
    run_lift M (BankedSimulation.embed M (bankBase M x y) (fun _ => 1) (M.step c))
  rw [run_lift_step M _ h,hs]

private theorem run_running_iterate (M : MultitapeTM) (x y : List Bool) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym)
    (h : ∀ s : ℕ, s < T → (M.step^[s] c).state ≠ M.qHalt) :
    (machine M).step^[T] (runningFrame M x y c) = runningFrame M x y (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact h s (by omega)),
        run_running_step M x y _ (h T (by omega)) (run_markers_iterate M c T marker),Function.iterate_succ_apply']

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

private theorem run_running_output_head (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M x y c).head i = 1 + c.head M.outTape := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he]

private theorem run_return_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (h : c.state = M.qHalt) :
    (machine M).step (runningFrame M x y c) =
      returnOutputFrame M x y c (1 + c.head M.outTape) := by
  classical
  have ht : transition M (runningFrame M x y c).state
      (fun i => (runningFrame M x y c).cells i ((runningFrame M x y c).head i)) =
      (.inl .rewindOutput,fun i => ((runningFrame M x y c).cells i ((runningFrame M x y c).head i),.stay)) := by
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
    by_cases hi : i.val = 3
    · simpa only [returnOutputFrame,if_pos hi] using run_running_output_head M x y c i hi
    · simp only [returnOutputFrame,if_neg hi]

/-- A terminating child call is simulated through its first halt, followed
by one actual transition into output return. Its complete final bank contents
and all heads are retained, even if the supplied child clock was padded. -/
private theorem run_to_return (M : MultitapeTM) (x y : List Bool) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) (halt : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T + 1 ∧
      (machine M).step^[t] (runningFrame M x y c) =
        returnOutputFrame M x y (M.step^[T] c) (1 + (M.step^[T] c).head M.outTape) := by
  obtain ⟨t,ht,he,hn⟩ := run_first_halt M c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',run_running_iterate M x y c t marker hn,he,run_return_step M x y _ halt]

/-- The physically prepared ready frame is exactly the child's complete
initial configuration embedded in offset-one banks. -/
private theorem ready_eq_running_init (M : MultitapeTM) (x y : List Bool) :
    readyFrame M x y = runningFrame M x y (M.initCfg x y) := by
  classical
  apply run_cfg_ext
  · rfl
  · funext i p
    by_cases hi : 2 ≤ i.val
    · have hn₀ : i.val ≠ 0 := by omega
      have hn₁ : i.val ≠ 1 := by omega
      have he : BankedSimulation.innerTape M i hi = M.inTape ↔ i.val = 2 := by
        constructor
        · intro h
          have hv := congrArg Fin.val h
          simp only [BankedSimulation.innerTape,MultitapeTM.inTape] at hv
          omega
        · intro h
          apply Fin.ext
          simp only [BankedSimulation.innerTape,MultitapeTM.inTape]
          omega
      simp only [readyFrame,runningFrame,BankedSimulation.embed,dif_pos hi,if_neg hn₀,if_neg hn₁,
        MultitapeTM.initCfg,he]
      by_cases hp : p = 0
      · subst p
        simp only [bankTape,if_pos rfl,show (0:ℕ) < 1 by omega,if_pos,bankBase,readyFrame,
          if_neg hn₀,if_neg hn₁]
      · have hn : ¬p < 1 := by omega
        simp only [bankTape,if_neg hp,if_neg hn]
        by_cases ht : i.val = 2
        · simp only [if_pos ht,inputWord,bankTape,if_neg hp]
        · simp only [if_neg ht,bankTape,if_neg hp]
    · simp only [runningFrame,BankedSimulation.embed,dif_neg hi,bankBase]
  · funext i
    by_cases hi : 2 ≤ i.val
    · simp only [runningFrame,BankedSimulation.embed,dif_pos hi,MultitapeTM.initCfg,Nat.add_zero]
      simp only [readyFrame,if_neg (by omega : i.val ≠ 0)]
    · simp only [runningFrame,BankedSimulation.embed,dif_neg hi,bankBase]

end IntMul.BankedCall



namespace IntMul.BankedCall

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

private theorem output_bank_payload (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    bankTape M w (p + 2) = some (w.getD p M.blank) := by
  simp [bankTape,MultitapeTM.tapeOf]

private theorem output_running_output_cells (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym))
    (i : Fin (M.k + 2)) (hi : i.val = 3) :
    (runningFrame M x y c).cells i = bankTape M (w.map M.bitSym) := by
  have hg : 2 ≤ i.val := by omega
  have he : BankedSimulation.innerTape M i hg = M.outTape := by
    apply Fin.ext
    simp only [BankedSimulation.innerTape,MultitapeTM.outTape]
    omega
  funext p
  simp only [runningFrame,BankedSimulation.embed,dif_pos hg,he,out]
  by_cases hp : p = 0
  · subst p
    simp only [show (0:ℕ) < 1 by omega,if_pos,bankBase,readyFrame,
      if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),if_neg (by omega : i.val ≠ 2),
      bankTape,if_pos rfl]
  · simp only [bankTape,if_neg hp,if_neg (by omega : ¬p < 1)]

private theorem output_running_global_output_cells (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 1) :
    (runningFrame M x y c).cells i = (machine M).tapeOf [] := by
  simp only [runningFrame,BankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),bankBase,
    readyFrame,if_neg (by omega : i.val ≠ 0),if_pos hi]

private theorem output_running_global_output_head (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (i : Fin (M.k + 2)) (hi : i.val = 1) :
    (runningFrame M x y c).head i = 1 := by
  simp only [runningFrame,BankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),bankBase,
    readyFrame,if_neg (by omega : i.val ≠ 0)]

private theorem output_payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem output_return_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
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
    exact output_protect_left M _ hn
  · simp only [if_neg hi,output_protect_stay]

private theorem output_return_left_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step (returnOutputFrame M x y c (p + 2)) = returnOutputFrame M x y c (p + 1) := by
  have hr : (returnOutputFrame M x y c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M x y c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) =
          some ((w.map M.bitSym).getD p M.blank) := by
    change (runningFrame M x y c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (p + 2) = _
    rw [output_running_output_cells M x y c w out _ rfl,output_bank_payload]
  have hm : (returnOutputFrame M x y c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M x y c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ some M.startSym := by
    rw [hr]
    exact fun he => output_payload_not_marker M w p (Option.some.inj he)
  have hn : (returnOutputFrame M x y c (p + 2)).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M x y c (p + 2)).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
    rw [hr]
    exact Option.some_ne_none _
  have ht := output_return_left_transition M
    (fun i => (returnOutputFrame M x y c (p + 2)).cells i ((returnOutputFrame M x y c (p + 2)).head i)) hm hn
  change transition M (returnOutputFrame M x y c (p + 2)).state
    (fun i => (returnOutputFrame M x y c (p + 2)).cells i ((returnOutputFrame M x y c (p + 2)).head i)) = _ at ht
  apply output_cfg_ext
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

private theorem output_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
    (h : a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ = some M.startSym) :
    transition M (.inl .rewindOutput) a = (.inl .copyOutput,fun i =>
      (a i,if i.val = 3 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos h]
  congr 1
  funext i
  by_cases hi : i.val = 3
  · simp only [if_pos hi,output_protect_right]
  · simp only [if_neg hi,output_protect_stay]

private theorem output_return_marker_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (returnOutputFrame M x y c 1) = copyOutputFrame M x y c w 0 := by
  have hr : (returnOutputFrame M x y c 1).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnOutputFrame M x y c 1).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.startSym := by
    change (runningFrame M x y c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ 1 = _
    rw [output_running_output_cells M x y c w out _ rfl]
    rfl
  have ht := output_return_marker_transition M
    (fun i => (returnOutputFrame M x y c 1).cells i ((returnOutputFrame M x y c 1).head i)) hr
  change transition M (returnOutputFrame M x y c 1).state
    (fun i => (returnOutputFrame M x y c 1).cells i ((returnOutputFrame M x y c 1).head i)) = _ at ht
  apply output_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,List.take_zero,List.map_nil]
      exact output_running_global_output_cells M x y c i hi
    · simp only [returnOutputFrame,copyOutputFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnOutputFrame,copyOutputFrame,if_pos hi,if_neg (by omega : i.val ≠ 3)]
      exact output_running_global_output_head M x y c i hi
    · by_cases h₃ : i.val = 3
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_pos h₃]
      · simp only [returnOutputFrame,copyOutputFrame,if_neg hi,if_neg h₃]

private theorem rewind_output_correct (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step^[p + 1] (returnOutputFrame M x y c (p + 1)) = copyOutputFrame M x y c w 0 := by
  induction p with
  | zero => simpa using output_return_marker_step M x y c w out
  | succ p ih => rw [Function.iterate_succ_apply,output_return_left_step M x y c w out p,ih]

private theorem output_tape_append_one (N : MultitapeTM) (w : List N.Sym) (a : N.Sym) :
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

private theorem output_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Option M.Sym)
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
    · simp only [if_pos (Or.inr hs),output_protect_right]
    · simp only [if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3)),output_protect_stay]

private theorem output_copy_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyOutputFrame M x y c w j) = copyOutputFrame M x y c w (j + 1) := by
  have hs : (copyOutputFrame M x y c w j).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M x y c w j).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.bitSym w[j]) := by
    change (runningFrame M x y c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (j + 2) = _
    rw [output_running_output_cells M x y c w out _ rfl,output_bank_payload,
      List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have hb : (copyOutputFrame M x y c w j).cells ⟨1,by change 1 < M.k + 2; omega⟩
      ((copyOutputFrame M x y c w j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some M.blank := by
    change ((w.take j).map (machine M).bitSym).getD j (some M.blank) = _
    exact List.getD_eq_default _ _ (by simp [hl])
  have ht := output_copy_transition M
    (fun i => (copyOutputFrame M x y c w j).cells i ((copyOutputFrame M x y c w j).head i)) w[j] hs hb
  change transition M (copyOutputFrame M x y c w j).state
    (fun i => (copyOutputFrame M x y c w j).cells i ((copyOutputFrame M x y c w j).head i)) = _ at ht
  apply output_cfg_ext
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
        output_tape_append_one (machine M) ((w.take j).map (machine M).bitSym) ((machine M).bitSym w[j])
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

private theorem output_copy_run (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyOutputFrame M x y c w 0) = copyOutputFrame M x y c w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),output_copy_step M x y c w out j (by omega)]

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

private theorem output_copy_end_step (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (copyOutputFrame M x y c w w.length) = finalFrame M x y c w := by
  have hr : (copyOutputFrame M x y c w w.length).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyOutputFrame M x y c w w.length).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some M.blank := by
    change (runningFrame M x y c).cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (w.length + 2) = _
    rw [output_running_output_cells M x y c w out _ rfl,output_bank_payload,
      List.getD_eq_default _ _ (by simp)]
  have ht := output_copy_end_transition M
    (fun i => (copyOutputFrame M x y c w w.length).cells i ((copyOutputFrame M x y c w w.length).head i)) hr
  change transition M (copyOutputFrame M x y c w w.length).state
    (fun i => (copyOutputFrame M x y c w w.length).cells i ((copyOutputFrame M x y c w w.length).head i)) = _ at ht
  apply output_cfg_ext
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
private theorem output_correct (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    (machine M).step^[p + w.length + 2] (returnOutputFrame M x y c (p + 1)) = finalFrame M x y c w := by
  rw [show p + w.length + 2 = (w.length + (p + 1)) + 1 by omega,
    Function.iterate_succ_apply',Function.iterate_add_apply,rewind_output_correct M x y c w out p,
    output_copy_run M x y c w out w.length le_rfl,output_copy_end_step M x y c w out]

end IntMul.BankedCall



namespace IntMul.BankedCall

private theorem main_init_markers (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).cells j 0 = M.startSym := by
  intro j
  simp only [MultitapeTM.initCfg]
  split <;> rfl

/-- The entire literal child call starts in the real initial configuration,
physically builds banks, runs the child, rewinds and copies its output, and
halts with the exact same output. The child's final output-head distance is
explicitly charged rather than treated as a free return. -/
private theorem call_correct (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool)
    (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + (M.step^[T] (M.initCfg x y)).head M.outTape + w.length +
        2 * x.length + 2 * y.length + 9 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (machine M).step^[t] ((machine M).initCfg x y) =
        finalFrame M x y (M.step^[T] (M.initCfg x y)) w := by
  let c := M.step^[T] (M.initCfg x y)
  obtain ⟨t,ht,hr⟩ := run_to_return M x y (M.initCfg x y) T (main_init_markers M x y) halts.1
  change (machine M).step^[t] (runningFrame M x y (M.initCfg x y)) =
    returnOutputFrame M x y c (1 + c.head M.outTape) at hr
  have ho := output_correct M x y c w halts.2 (c.head M.outTape)
  rw [Nat.add_comm (c.head M.outTape) 1] at ho
  let clock := 2 * x.length + 2 * y.length + 6 + t + (c.head M.outTape + w.length + 2)
  have hp : (machine M).step^[t + (2 * x.length + 2 * y.length + 6)] ((machine M).initCfg x y) =
      returnOutputFrame M x y c (1 + c.head M.outTape) := by
    rw [Function.iterate_add_apply,setup_correct,ready_eq_running_init,hr]
  have he : (machine M).step^[clock] ((machine M).initCfg x y) = finalFrame M x y c w := by
    rw [show clock = (c.head M.outTape + w.length + 2) +
        (t + (2 * x.length + 2 * y.length + 6)) by unfold clock; omega,
      Function.iterate_add_apply,hp,ho]
  refine ⟨clock,?_,?_,he⟩
  · change clock ≤ T + c.head M.outTape + w.length + 2 * x.length + 2 * y.length + 9
    unfold clock
    omega
  · unfold MultitapeTM.HaltsWithOutput
    rw [he]
    constructor
    · rfl
    · change (machine M).tapeOf ((w.take w.length).map (machine M).bitSym) =
        (machine M).tapeOf (w.map (machine M).bitSym)
      simp only [List.take_length]

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

/-- No head-position contract is needed for the universal 2T+linear bound. -/
private theorem call_bounded (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool)
    (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ, t ≤ 2 * T + w.length + 2 * x.length + 2 * y.length + 9 ∧
      (machine M).HaltsWithOutput x y t w := by
  obtain ⟨t,ht,ho,_⟩ := call_correct M x y T w halts
  refine ⟨t,?_,ho⟩
  have hh := main_head_run_bound M x y T M.outTape
  omega

end IntMul.BankedCall


open IntMul IntMul.BankedCall

theorem solution (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool)
    (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + (M.step^[T] (M.initCfg x y)).head M.outTape + w.length +
        2 * x.length + 2 * y.length + 9 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (machine M).step^[t] ((machine M).initCfg x y) =
        finalFrame M x y (M.step^[T] (M.initCfg x y)) w :=
  IntMul.BankedCall.call_correct M x y T w halts

#print axioms solution
