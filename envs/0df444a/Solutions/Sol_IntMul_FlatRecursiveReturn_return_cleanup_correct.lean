-- Prove2me | solution 1 for IntMul.FlatRecursiveReturn.return_cleanup_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T02:15:47.359603+00:00
-- url     : https://prove2.me/submissions/c5bf781e-5105-4172-9dd4-25aee50da2b1

import Definitions.Def_IntMul_FlatRecursiveReturn
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.FlatRecursiveScheduler

private theorem flatrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.cells (FixedTapeExtension.oldTape N j)=c.cells j) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.head (FixedTapeExtension.oldTape N j)=c.head j) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply flatrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (canonical : ∀ j p, base.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j))) :
    (TrackedBankedSimulation.embed M base offset extent c).cells=base.cells := by
  funext i p
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    let j := innerTape M i hi
    by_cases hp : p< offset j
    · dsimp only [j] at hp
      simp only [if_pos hp]
    · have hle : offset j≤ p := Nat.le_of_not_gt hp
      dsimp only [j] at hp
      rw [if_neg hp]
      have h := canonical j (p-offset j)
      have hw : workTape M j=i := work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (extents)

noncomputable def bodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)


end IntMul.FlatRecursiveScheduler


namespace IntMul.FlatRecursiveScheduler

private theorem flatrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem flatrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem flatrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem flatrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,flatrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [boot_iterate M n request resume c s hlive,he]

private theorem preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [preparation_iterate M n request resume c s hlive,he]

private theorem body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,if_neg live,no_request]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem body_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bodyMachine M).step^[s] c).state≠(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    (machine M n request resume).step^[T] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)) (by intro s hs; exact no_request s (by omega)),
      body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [input_iterate M n request resume label c s hlive,he]

private theorem reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [reservation_iterate M n request resume c s hlive,he]

private theorem return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [return_iterate M n request resume c s hlive,he]

private theorem cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [cleanup_iterate M n request resume c s hlive,he]

private theorem restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [restore_iterate M n request resume c s hlive,he]

private theorem output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [output_iterate M n request resume label c s hlive,he]

private theorem finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := flatrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem flatrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem flatrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem flatrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) (present : a tape≠none) : moveActions M a tape .left=
      fun i => (a i,if i=tape then .left else .stay) := by
  classical
  funext i
  simp only [moveActions]
  by_cases hi : i=tape
  · subst i
    simp only [eq_self,if_true]
    cases h : a tape with
    | none => exact False.elim (present h)
    | some s => rfl
  · simp only [if_neg hi]
    cases a i <;> rfl

private theorem stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [flatrecursiveschedulerdispatch_right_actions] at ht
  apply flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [flatrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply flatrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,if_pos exit]

private theorem preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,if_pos exit]

private theorem input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,if_pos exit]

private theorem reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,if_pos exit]

private theorem return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,if_pos exit]

private theorem cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,if_pos exit]

private theorem restore_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (exit : c.state=(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=relabel M n request resume (.pop .popStart) (liftRestore M n request resume c) := by
  apply stay_step
  change transition M n request resume (.restore c.state) _=_
  simp only [transition,if_pos exit]

private theorem output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,if_pos exit]

private theorem finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,if_pos exit]

private theorem body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_pos exit]

private theorem body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_neg live,call]

private theorem push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,if_pos exit]

private theorem pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,exit]

private theorem inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply stay_step
  simp only [phase,transition,if_pos root]

private theorem inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  simp only [phase,transition,if_neg parent]

private theorem reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  apply right_step
  simp only [phase,transition,if_pos marker]

private theorem reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  simp only [phase,transition,if_neg marker]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveReturn

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem flatrecursivereturnframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def returnParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) : (TrackedReturnReplacement.machine M).Cfg where
  state := (TrackedReturnReplacement.machine M).qStart
  cells := fun i => base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

noncomputable def returnPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (returnMachine M).Cfg where
  state := (returnMachine M).qStart
  cells := (bodyView M n request resume base rho sigma offset extent c v).cells
  head := (bodyView M n request resume base rho sigma offset extent c v).head

noncomputable def returnStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (returnMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedReturnReplacement.machine M)
    (returnPadBase M n request resume base rho sigma offset extent c v)
    (TrackedReturnReplacement.initialFrame M (returnParent M n request resume base) sigma offset extent c v)

noncomputable def returnFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (returnMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedReturnReplacement.machine M)
    (returnPadBase M n request resume base rho sigma offset extent c v)
    (TrackedReturnReplacement.finalFrame M (returnParent M n request resume base) sigma offset extent c v w)

private theorem flatrecursivereturnframes_word_before_heads (M : MultitapeTM) (base : (TrackedWordInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    (TrackedWordInputBridge.beforeFrame M base sigma offset extent c v 0).head=
      TrackedWordInputBridge.initialHeads M base sigma offset extent c v := by
  funext i
  simp only [TrackedWordInputBridge.beforeFrame,Nat.sub_zero]
  by_cases hb : i=TrackedWordInputBridge.bufferTape M
  · subst i
    simp only [if_true,TrackedWordInputBridge.initialHeads,TrackedBankedSimulation.embed,
      TrackedWordInputBridge.bufferTape,dif_neg (by omega : ¬2 ≤ (1 : ℕ)),
      TrackedWordInputBridge.parentBase,if_true]
    omega
  · simp only [if_neg hb]
    by_cases hp : i=TrackedWordInputBridge.packetTape M
    · subst i
      simp only [if_true]
      exact (embed_work_head M (TrackedWordInputBridge.parentBase M base sigma v)
        offset extent c M.outTape).symm
    · simp only [if_neg hp]

private theorem flatrecursivereturnframes_word_parent_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    TrackedWordInputBridge.parentBase M
      (TrackedReturnReplacement.inputBase M (returnParent M n request resume base)) sigma v=
      parentBase M n request resume base sigma v := by
  apply flatrecursivereturnframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedWordInputBridge.parentBase,TrackedReturnReplacement.inputBase,returnParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]
  · funext i
    simp only [TrackedWordInputBridge.parentBase,TrackedReturnReplacement.inputBase,returnParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]

private theorem body_return_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    relabel M n request resume (.returning (returnMachine M).qStart)
      (bodyFrame M n request resume base rho sigma offset extent c v)=
    liftReturn M n request resume (returnStart M n request resume base rho sigma offset extent c v) := by
  have hc : (TrackedReturnReplacement.initialFrame M (returnParent M n request resume base)
      sigma offset extent c v).cells=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).cells := by
    simp only [TrackedReturnReplacement.initialFrame,TrackedReturnReplacement.liftInput,
      TrackedWordInputBridge.initialFrame,TrackedWordInputBridge.beforeFrame,
      TrackedWordInputBridge.initialCells,flatrecursivereturnframes_word_parent_ready]
  have hh : (TrackedReturnReplacement.initialFrame M (returnParent M n request resume base)
      sigma offset extent c v).head=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).head := by
    simp only [TrackedReturnReplacement.initialFrame,TrackedReturnReplacement.liftInput,
      TrackedWordInputBridge.initialFrame,flatrecursivereturnframes_word_before_heads,
      TrackedWordInputBridge.initialHeads,flatrecursivereturnframes_word_parent_ready]
  apply flatrecursivereturnframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftReturn,returnStart,returnPadBase,bodyView,
      FixedTapeExtension.embed,hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftReturn,returnStart,returnPadBase,bodyView,
      FixedTapeExtension.embed,hh]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.FlatRecursiveReturn



namespace IntMul.FlatRecursiveReturn

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem flatrecursivereturncleanupframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def cleanupParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (TrackedBankCleanup.machine M).Cfg where
  state := .rewind
  cells := (TrackedReturnReplacement.finalFrame M (returnParent M n request resume base)
    sigma offset extent c v w).cells
  head := (TrackedReturnReplacement.finalFrame M (returnParent M n request resume base)
    sigma offset extent c v w).head

noncomputable def cleanupPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg where
  state := .rewind
  cells := (returnFinal M n request resume base rho sigma offset extent c v w).cells
  head := (returnFinal M n request resume base rho sigma offset extent c v w).head

noncomputable def cleanupStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankCleanup.machine M)
    (cleanupPadBase M n request resume base rho sigma offset extent c v w)
    (TrackedBankCleanup.rewindFrame M (cleanupParent M n request resume base sigma offset extent c v w)
      offset extent c (returnedHeads M c))

noncomputable def cleanupFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankCleanup.machine M)
    (cleanupPadBase M n request resume base rho sigma offset extent c v w)
    (TrackedBankCleanup.finalFrame M (cleanupParent M n request resume base sigma offset extent c v w) offset)

private theorem flatrecursivereturncleanupframes_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedWordInputBridge.bufferTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workTape,TrackedWordInputBridge.bufferTape] at hv
  omega

private theorem return_work_canonical (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) (p : ℕ) :
    (cleanupParent M n request resume base sigma offset extent c v w).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (flatrecursivereturncleanupframes_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells]
  exact embed_work M _ offset extent c j p

private theorem return_work_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) :
    (cleanupParent M n request resume base sigma offset extent c v w).head (workTape M j)=
      offset j+returnedHeads M c j := by
  simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (flatrecursivereturncleanupframes_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedWordInputBridge.packetTape,if_true,returnedHeads,Nat.add_zero]
  · have hp : workTape M j≠TrackedWordInputBridge.packetTape M := by
      intro h; exact hj (work_injective M h)
    simp only [if_neg hp,returnedHeads,if_neg hj,TrackedWordInputBridge.initialHeads]
    exact embed_work_head M _ offset extent c j

private theorem return_cleanup_old_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    TrackedBankCleanup.rewindFrame M (cleanupParent M n request resume base sigma offset extent c v w)
      offset extent c (returnedHeads M c)=
      cleanupParent M n request resume base sigma offset extent c v w := by
  apply flatrecursivereturncleanupframes_cfg_ext
  · rfl
  · apply embed_cells_ready
    intro j p
    exact return_work_canonical M n request resume base sigma offset extent c v w j p
  · funext i
    simp only [TrackedBankCleanup.rewindFrame]
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      have h := return_work_heads M n request resume base sigma offset extent c v w (innerTape M i hi)
      rw [work_inner M i hi] at h
      exact h.symm
    · simp only [dif_neg hi]

private theorem return_cleanup_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    relabel M n request resume (.cleanup .rewind)
      (liftReturn M n request resume (returnFinal M n request resume base rho sigma offset extent c v w))=
      liftCleanup M n request resume (cleanupStart M n request resume base rho sigma offset extent c v w) := by
  rw [cleanupStart,return_cleanup_old_ready]
  have hp : FixedTapeExtension.embed (TrackedBankCleanup.machine M)
      (cleanupPadBase M n request resume base rho sigma offset extent c v w)
      (cleanupParent M n request resume base sigma offset extent c v w)=
      cleanupPadBase M n request resume base rho sigma offset extent c v w := by
    apply flatrecursivereturncleanupframes_cfg_ext
    · rfl
    · apply extension_cells_ready
      intro j
      change (FixedTapeExtension.embed (TrackedReturnReplacement.machine M) _ _).cells
        (FixedTapeExtension.oldTape (TrackedReturnReplacement.machine M) j)=_
      rw [extension_old_cells]
      rfl
    · apply extension_heads_ready
      intro j
      change (FixedTapeExtension.embed (TrackedReturnReplacement.machine M) _ _).head
        (FixedTapeExtension.oldTape (TrackedReturnReplacement.machine M) j)=_
      rw [extension_old_heads]
      rfl
  rw [hp]
  rfl

end IntMul.FlatRecursiveReturn



namespace IntMul.FlatRecursiveReturn

open IntMul.FlatRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem flatrecursivereturninspection_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem flatrecursivereturninspection_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedWordInputBridge.bufferTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workTape,TrackedWordInputBridge.bufferTape] at hv
  omega

private theorem return_work_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) (p : ℕ)
    (hp : p < offset j) :
    (cleanupParent M n request resume base sigma offset extent c v w).cells (workTape M j) p=
      base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j)) p := by
  simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (flatrecursivereturninspection_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells]
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp only [innerTape]
    omega
  rw [hi,if_pos hp]
  change (TrackedWordInputBridge.parentBase M
    (TrackedReturnReplacement.inputBase M (returnParent M n request resume base)) sigma v).cells (workTape M j) p=_
  simp only [TrackedWordInputBridge.parentBase,if_neg (flatrecursivereturninspection_work_ne_buffer M j),
    TrackedReturnReplacement.inputBase,returnParent]
  rfl

private theorem return_low (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (i : Fin (M.k+2))
    (hi : i.val < 2) :
    (cleanupParent M n request resume base sigma offset extent c v w).cells i=
      (if i.val=1 then TrackedOutputReturn.bufferTape M
        (base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) sigma w
        else base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) ∧
    (cleanupParent M n request resume base sigma offset extent c v w).head i=
      (if i.val=1 then sigma+w.length+1
        else base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) := by
  by_cases hb : i.val=1
  · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
    constructor
    · simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_pos he,if_pos hb,returnParent]
    · simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_pos he,if_pos hb]
  · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
    have hp : i≠TrackedWordInputBridge.packetTape M := by
      intro h; have hv := congrArg Fin.val h
      simp only [TrackedWordInputBridge.packetTape,workTape,MultitapeTM.outTape] at hv
      omega
    constructor
    · simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_neg he,TrackedWordInputBridge.finalFrame,
        TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),
        TrackedWordInputBridge.parentBase,if_neg he,returnParent,if_neg hb]
    · simp only [cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_neg he,TrackedWordInputBridge.finalFrame,
        TrackedReturnReplacement.inputBase,if_neg hp,TrackedWordInputBridge.initialHeads,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),
        TrackedWordInputBridge.parentBase,if_neg he,returnParent,if_neg hb]

private theorem cleanup_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    (cleanupFinal M n request resume base rho sigma offset extent c v w).head (stackTape M)=rho ∧
    (cleanupFinal M n request resume base rho sigma offset extent c v w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho := by
  have hi : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  constructor
  · simp only [cleanupFinal,FixedTapeExtension.embed,dif_neg hi,cleanupPadBase,returnFinal,
      returnPadBase,bodyView,stackBase,if_true]
  · simp only [cleanupFinal,FixedTapeExtension.embed,dif_neg hi,cleanupPadBase,returnFinal,
      returnPadBase,bodyView,stackBase,if_true]

private theorem cleanup_inspection_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    headFrame M n request resume .inspectStack
      (liftCleanup M n request resume (cleanupFinal M n request resume base rho sigma offset extent c v w))
      (stackTape M) (rho-1)=inspectionFrame M n request resume base rho sigma offset w := by
  apply flatrecursivereturninspection_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,liftCleanup,cleanupFinal,FixedTapeExtension.embed,inspectionFrame]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,TrackedBankCleanup.finalFrame,FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        let j := innerTape M ⟨i.val,hi⟩ hw
        change (if p < offset j then
          (cleanupParent M n request resume base sigma offset extent c v w).cells ⟨i.val,hi⟩ p
          else some (M.blank,false))=(if p < offset j then base.cells i p else some (M.blank,false))
        by_cases hp : p < offset j
        · simp only [TrackedBankCleanup.freshTape,if_pos hp]
          have h := return_work_prefix M n request resume base sigma offset extent c v w j p hp
          have he : workTape M j=⟨i.val,hi⟩ := work_inner M _ hw
          rw [he] at h
          exact h
        · simp only [TrackedBankCleanup.freshTape,if_neg hp]
      · simp only [dif_neg hw]
        have h := (return_low M n request resume base sigma offset extent c v w ⟨i.val,hi⟩ (by change i.val < 2; omega)).1
        exact congrFun h p
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      have h := (cleanup_stack M n request resume base rho sigma offset extent c v w).2
      simpa only [cleanupFinal,FixedTapeExtension.embed,dif_neg hi] using congrFun h p
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,liftCleanup,inspectionFrame]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h; have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      rw [Function.update_of_ne hs]
      simp only [cleanupFinal,FixedTapeExtension.embed,dif_pos hi,TrackedBankCleanup.finalFrame,
        FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
      · simp only [dif_neg hw]
        exact (return_low M n request resume base sigma offset extent c v w ⟨i.val,hi⟩ (by change i.val < 2; omega)).2
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [Function.update_self]

end IntMul.FlatRecursiveReturn



namespace IntMul.FlatRecursiveReturn

open IntMul.FlatRecursiveScheduler
open IntMul.TrackedBankCleanup (span)

/-- The actual flat scheduler returns from one finished body, replaces an
arbitrary older result, clears every current work bank and physically probes
the continuation stack. All three dispatches and every head move are charged. -/
private theorem return_cleanup_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v w : List Bool) (halt : c.state=M.qHalt)
    (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
        span M (returnedHeads M c)+2*span M extent+12 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w := by
  have hbody : (machine M n request resume).step
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftReturn M n request resume (returnStart M n request resume base rho sigma offset extent c v) := by
    change (machine M n request resume).step
      (liftBody M n request resume (bodyView M n request resume base rho sigma offset extent c v))=_
    rw [body_dispatch M n request resume (bodyView M n request resume base rho sigma offset extent c v) halt]
    exact body_return_ready M n request resume base rho sigma offset extent c v
  obtain ⟨r,hrclock,hrrun,hrhalt,hrbuffer,hrbufferhead,hrbanks,hrheads⟩ :=
    TrackedReturnReplacement.return_correct M (returnParent M n request resume base)
      sigma offset extent c v w out
  have hr : (returnMachine M).step^[r] (returnStart M n request resume base rho sigma offset extent c v)=
      returnFinal M n request resume base rho sigma offset extent c v w := by
    have h := (FixedTapeExtension.simulate_run (TrackedReturnReplacement.machine M)
      (returnPadBase M n request resume base rho sigma offset extent c v)
      (TrackedReturnReplacement.initialFrame M (returnParent M n request resume base) sigma offset extent c v) r).1
    rw [hrrun] at h
    exact h
  have hre : ((returnMachine M).step^[r]
      (returnStart M n request resume base rho sigma offset extent c v)).state=(returnMachine M).qHalt := by
    rw [hr]
    exact hrhalt
  obtain ⟨s,hsclock,hsrun⟩ := return_to_halt M n request resume
    (returnStart M n request resume base rho sigma offset extent c v) r hre
  rw [hr] at hsrun
  have hreturn : (machine M n request resume).step^[s+1]
      (liftReturn M n request resume (returnStart M n request resume base rho sigma offset extent c v))=
      liftCleanup M n request resume (cleanupStart M n request resume base rho sigma offset extent c v w) := by
    rw [Function.iterate_succ_apply',hsrun,return_dispatch M n request resume _ hrhalt]
    exact return_cleanup_ready M n request resume base rho sigma offset extent c v w
  let C := span M (returnedHeads M c)+2*span M extent+3
  have hclean : (cleanupMachine M).step^[C] (cleanupStart M n request resume base rho sigma offset extent c v w)=
      cleanupFinal M n request resume base rho sigma offset extent c v w := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankCleanup.machine M)
      (cleanupPadBase M n request resume base rho sigma offset extent c v w)
      (TrackedBankCleanup.rewindFrame M (cleanupParent M n request resume base sigma offset extent c v w)
        offset extent c (returnedHeads M c)) C).1
    rw [(TrackedBankCleanup.cleanup_correct M (cleanupParent M n request resume base sigma offset extent c v w)
      offset extent positive c (returnedHeads M c) unique tail).1] at h
    exact h
  have hce : ((cleanupMachine M).step^[C]
      (cleanupStart M n request resume base rho sigma offset extent c v w)).state=(cleanupMachine M).qHalt := by
    rw [hclean]
    rfl
  obtain ⟨q,hqclock,hqrun⟩ := cleanup_to_halt M n request resume
    (cleanupStart M n request resume base rho sigma offset extent c v w) C hce
  rw [hclean] at hqrun
  have hstack := cleanup_stack M n request resume base rho sigma offset extent c v w
  have hpresent : (cleanupFinal M n request resume base rho sigma offset extent c v w).cells (stackTape M)
      ((cleanupFinal M n request resume base rho sigma offset extent c v w).head (stackTape M))≠none := by
    rw [hstack.1,hstack.2]
    simp [FiniteContinuationStack.freshTape]
  have hcleanup : (machine M n request resume).step^[q+1]
      (liftCleanup M n request resume (cleanupStart M n request resume base rho sigma offset extent c v w))=
      inspectionFrame M n request resume base rho sigma offset w := by
    rw [Function.iterate_succ_apply',hqrun,cleanup_dispatch M n request resume _ rfl hpresent,hstack.1]
    exact cleanup_inspection_ready M n request resume base rho sigma offset extent c v w
  have hstaged : (machine M n request resume).step^[(s+1)+1]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftCleanup M n request resume (cleanupStart M n request resume base rho sigma offset extent c v w) := by
    rw [Function.iterate_succ_apply,hbody,hreturn]
  refine ⟨(q+1)+((s+1)+1),by dsimp only [C] at *; omega,?_⟩
  rw [Function.iterate_add_apply,hstaged,hcleanup]

end IntMul.FlatRecursiveReturn


open IntMul IntMul.FlatRecursiveReturn IntMul.FlatRecursiveScheduler IntMul.TrackedBankCleanup

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v w : List Bool) (halt : c.state=M.qHalt)
    (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
        span M (returnedHeads M c)+2*span M extent+12 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w :=
  IntMul.FlatRecursiveReturn.return_cleanup_correct M n request resume base rho sigma offset extent positive c v w halt out unique tail

#print axioms solution
