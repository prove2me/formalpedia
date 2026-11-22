-- Prove2me | solution 1 for LinearSetReconciliation327.Main.cr23_toggles_within_at
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T09:47:00.516788+00:00
-- url     : https://prove2.me/submissions/9cc9f297-c8f8-4dbc-8e37-3a98b644797b

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23

set_option autoImplicit false
set_option linter.all false
namespace LinearSetReconciliation327.Main
open Finset
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
@[simp] theorem execInstr_halt (E : RAMEnv) (s : RAMState) : execInstr .halt E s = s := rfl
@[simp] theorem execInstr_imm (E : RAMEnv) (s : RAMState) (d : Fin 16) (v : ℕ) :
    execInstr (.imm d v) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_add (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.add d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_sub (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.sub d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + 2 ^ E.W - (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ||| (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bxor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bxor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ^^^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_lt (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.lt d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((if (s.regs a) < (s.regs b) then 1 else 0) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl
@[simp] theorem execInstr_jz (E : RAMEnv) (s : RAMState) (c : Fin 16) (t : ℕ) :
    execInstr (.jz c t) E s = { s with pc := if (s.regs c) = 0 then t else s.pc + 1 } := rfl
@[simp] theorem execInstr_jmp (E : RAMEnv) (s : RAMState) (t : ℕ) :
    execInstr (.jmp t) E s = { s with pc := t } := rfl
@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl
/-- `step` runs the branch of `execInstr` at the current program counter. -/
theorem step_eq_execInstr (P : Program) (E : RAMEnv) (s : RAMState) (i : Instr)
    (h : P[s.pc]? = some i) : step P E s = execInstr i E s := by
  unfold step execInstr
  rw [h]
  cases i <;> rfl
/-- The machine does not move at a `halt`. -/
theorem step_halt (P : Program) (E : RAMEnv) (s : RAMState)
    (h : P[s.pc]? = some .halt) : step P E s = s := by
  rw [step_eq_execInstr P E s .halt h, execInstr_halt]
/-- Unfolding of `Halted`. -/
theorem halted_iff (P : Program) (s : RAMState) : Halted P s ↔ P[s.pc]? = some .halt := by
  unfold Halted
  cases h : P[s.pc]? with
  | none => simp
  | some i => cases i <;> simp
/-- A non-branching, non-halting instruction advances the program counter by one. -/
theorem execInstr_pc (i : Instr) (E : RAMEnv) (s : RAMState) (hno : i.NoBranchI) :
    (execInstr i E s).pc = s.pc + 1 := by
  obtain ⟨h1, h2, h3⟩ := hno
  cases i <;> simp_all [execInstr]
/-- Only `store` touches memory. -/
theorem execInstr_mem (i : Instr) (E : RAMEnv) (s : RAMState)
    (h : ∀ a v, i ≠ .store a v) : (execInstr i E s).mem = s.mem := by
  cases i <;> simp_all [execInstr]
/-- Which register an instruction overwrites, if any. -/
def Instr.dest? : Instr → Option (Fin 16)
  | .imm d _ => some d
  | .add d _ _ => some d
  | .sub d _ _ => some d
  | .mul d _ _ => some d
  | .div d _ _ => some d
  | .mod d _ _ => some d
  | .band d _ _ => some d
  | .bor d _ _ => some d
  | .bxor d _ _ => some d
  | .shl d _ _ => some d
  | .shr d _ _ => some d
  | .lt d _ _ => some d
  | .load d _ => some d
  | .store _ _ => none
  | .jz _ _ => none
  | .jmp _ => none
  | .qDet d _ => some d
  | .qPerm d _ _ => some d
  | .qPermInv d _ _ => some d
  | .qCoeff d _ _ => some d
  | .halt => none
/-- Only the destination register of an instruction changes. -/
theorem execInstr_regs (i : Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : i.dest? ≠ some d) : (execInstr i E s).regs d = s.regs d := by
  cases i <;>
    simp only [execInstr, Instr.dest?] at h ⊢ <;>
    first
      | rfl
      | (rw [Function.update_of_ne (fun he => h (by rw [he]))])
@[simp] theorem noBranch_nil : NoBranch ([] : List Instr) ↔ True := by simp [NoBranch]
@[simp] theorem noBranch_cons (i : Instr) (c : List Instr) :
    NoBranch (i :: c) ↔ i.NoBranchI ∧ NoBranch c := by simp [NoBranch]
@[simp] theorem noBranchI_imm (d : Fin 16) (v : ℕ) : (iImm d v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_add (d a b : Fin 16) : (iAdd d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_sub (d a b : Fin 16) : (iSub d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_bor (d a b : Fin 16) : (iBor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_bxor (d a b : Fin 16) : (iBxor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_lt (d a b : Fin 16) : (iLt d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_load (d a : Fin 16) : (iLd d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_store (a v : Fin 16) : (iSt a v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qDet (d a : Fin 16) : (iTbl d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem runBlock_nil (E : RAMEnv) (s : RAMState) : runBlock [] E s = s := rfl
@[simp] theorem runBlock_cons (i : Instr) (code : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (i :: code) E s = runBlock code E (execInstr i E s) := by
  simp [runBlock, List.foldl_cons]
/-- Concatenation of straight-line blocks. -/
theorem runBlock_append (c₁ c₂ : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (c₁ ++ c₂) E s = runBlock c₂ E (runBlock c₁ E s) := by
  simp [runBlock, List.foldl_append]
/-- A straight-line block advances the program counter by its length. -/
theorem runBlock_pc (code : List Instr) (E : RAMEnv) (s : RAMState) (hno : NoBranch code) :
    (runBlock code E s).pc = s.pc + code.length := by
  induction code generalizing s with
  | nil => simp
  | cons i tl ih =>
      obtain ⟨hi, ht⟩ := hno
      rw [runBlock_cons, ih (s := execInstr i E s) ht, execInstr_pc i E s hi]
      simp only [List.length_cons]
      omega
/-- A block that never writes register `d` leaves register `d` alone. -/
theorem runBlock_regs_frame (code : List Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : ∀ i ∈ code, i.dest? ≠ some d) : (runBlock code E s).regs d = s.regs d := by
  induction code generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (s := execInstr i E s) (fun j hj => h j (by
        simp only [List.mem_cons]; exact Or.inr hj))]
      exact execInstr_regs i E s d (h i (by simp))
/-- A block with no `store` leaves memory alone. -/
theorem runBlock_mem_frame (code : List Instr) (E : RAMEnv) (s : RAMState)
    (h : ∀ i ∈ code, ∀ a v, i ≠ .store a v) : (runBlock code E s).mem = s.mem := by
  induction code generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (s := execInstr i E s) (fun j hj => h j (by
        simp only [List.mem_cons]; exact Or.inr hj))]
      exact execInstr_mem i E s (h i (by simp))
/-- Front peeling of iterates: the first step is applied first. -/
theorem iterate_succ_apply_front {α : Type} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = (f^[n]) (f x) := by
  rw [Function.iterate_add_apply]
  rfl
theorem At.cons {P : Program} {a : ℕ} {i : Instr} {l : List Instr} :
    At P a (i :: l) ↔ P[a]? = some i ∧ At P (a + 1) l := by
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · have h1 := h (r + 1) (by simpa using hr)
      rw [show a + (r + 1) = a + 1 + r from by omega] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ r hr
    cases r with
    | zero => simpa using h1
    | succ r =>
        have h3 := h2 r (by simpa using hr)
        rw [show a + (r + 1) = a + 1 + r from by omega]
        simpa using h3
@[simp] theorem At.nil {P : Program} {a : ℕ} : At P a ([] : List Instr) ↔ True := by
  unfold At
  simp
theorem At.append {P : Program} {a : ℕ} {l₁ l₂ : List Instr} :
    At P a (l₁ ++ l₂) ↔ At P a l₁ ∧ At P (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · have h' := h r (by simp only [List.length_append]; omega)
      rwa [List.getElem?_append_left hr] at h'
    · have h' := h (l₁.length + r) (by simp only [List.length_append]; omega)
      rw [List.getElem?_append_right (by omega : l₁.length ≤ l₁.length + r)] at h'
      rw [show l₁.length + r - l₁.length = r from by omega] at h'
      rwa [show a + (l₁.length + r) = a + l₁.length + r from by omega] at h'
  · intro ⟨h₁, h₂⟩ r hr
    by_cases hlt : r < l₁.length
    · rw [List.getElem?_append_left hlt]
      exact h₁ r hlt
    · rw [List.getElem?_append_right (by omega : l₁.length ≤ r)]
      have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append ..
      rw [hlen] at hr
      have h := h₂ (r - l₁.length) (by omega)
      rwa [show a + l₁.length + (r - l₁.length) = a + r from by omega] at h
/-- A block found by `At` runs exactly as `runBlock` says. -/
theorem iterate_runBlock_of_at (P : Program) (E : RAMEnv) :
    ∀ (l : List Instr) (s : RAMState), At P s.pc l → NoBranch l →
      (step P E)^[l.length] s = runBlock l E s
  | [], s, _, _ => by simp
  | i :: tl, s, ha, hno => by
      obtain ⟨hi, ht⟩ := hno
      have hg : P[s.pc]? = some i := by
        have h := ha 0 (by simp)
        simpa using h
      have hstep : step P E s = execInstr i E s := step_eq_execInstr P E s i hg
      have hpc : (execInstr i E s).pc = s.pc + 1 := execInstr_pc i E s hi
      have ha' : At P (execInstr i E s).pc tl := by
        intro r hr
        rw [hpc]
        have h := ha (r + 1) (by simpa using hr)
        rw [show s.pc + (r + 1) = s.pc + 1 + r from by omega] at h
        simpa using h
      rw [List.length_cons, iterate_succ_apply_front, hstep, runBlock_cons]
      exact iterate_runBlock_of_at P E tl (execInstr i E s) ha' ht
/-- The mathematical meaning of a test. -/
def Cond.eval : Cond → RAMState → Prop
  | .neqz r, s => s.regs r ≠ 0
  | .lt _ a b, s => s.regs a < s.regs b
theorem Cond.noBranch_code (c : Cond) : NoBranch c.code := by
  cases c with
  | neqz r => simp [Cond.code]
  | lt d a b => simp [Cond.code]
/-- A test holds exactly when its test register, after the test code, is nonzero. -/
theorem Cond.eval_iff (c : Cond) (E : RAMEnv) (s : RAMState) (hW : 1 < 2 ^ E.W) :
    c.eval s ↔ (runBlock c.code E s).regs c.test ≠ 0 := by
  cases c with
  | neqz r => simp [Cond.eval, Cond.code, Cond.test]
  | lt d a b =>
      have hcode : Cond.code (Cond.lt d a b) = [iLt d a b] := rfl
      have htest : Cond.test (Cond.lt d a b) = d := rfl
      have hrun : (runBlock (Cond.code (Cond.lt d a b)) E s).regs (Cond.test (Cond.lt d a b))
          = (if s.regs a < s.regs b then 1 else 0) % 2 ^ E.W := by
        rw [hcode, htest, runBlock_cons, runBlock_nil, execInstr_lt]
        simp
      rw [hrun]
      by_cases h : s.regs a < s.regs b
      · rw [if_pos h, Nat.mod_eq_of_lt hW]
        exact ⟨fun _ => one_ne_zero, fun _ => h⟩
      · rw [if_neg h]
        exact ⟨fun hc => absurd hc h, fun hc => absurd hc (by simp)⟩
theorem Stmt.length_compile (s : Stmt) (base : ℕ) : (s.compile base).length = s.len := by
  induction s generalizing base with
  | code l => rfl
  | seq a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append] <;> omega
  | ite c a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega
  | loop c b ih =>
      simp only [Stmt.compile, Stmt.len, ih, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega
theorem at_loop {P : Program} {a : ℕ} {c : Cond} {b : Stmt}
    (h : At P a (Stmt.compile (Stmt.loop c b) a)) :
    At P a c.code ∧ P[a + c.code.length]? = some (iJz c.test (a + c.code.length + b.len + 2)) ∧
      At P (a + c.code.length + 1) (b.compile (a + c.code.length + 1)) ∧
      P[a + c.code.length + 1 + b.len]? = some (iJmp a) := by
  simpa [Stmt.compile, Stmt.length_compile, At.append, At.cons, At.nil] using h
/-- A block runs exactly as `runBlock` says. -/
theorem Sem.block (P : Program) (E : RAMEnv) (a : ℕ) (l : List Instr) (s : RAMState)
    (hAt : At P a l) (hno : NoBranch l) (hpc : s.pc = a) :
    Sem P E a (a + l.length) s (fun k s' => k = l.length ∧ s' = runBlock l E s) := by
  refine ⟨hpc, l.length, runBlock l E s, ?_, ?_, rfl, rfl⟩
  · exact iterate_runBlock_of_at P E l s (hpc.symm ▸ hAt) hno
  · rw [runBlock_pc l E s hno, hpc]
/-- One instruction. -/
theorem Sem.exec (P : Program) (E : RAMEnv) (a b : ℕ) (s : RAMState) (i : Instr)
    (hAt : P[a]? = some i) (hpc : s.pc = a) (hb : (execInstr i E s).pc = b) :
    Sem P E a b s (fun k s' => k = 1 ∧ s' = execInstr i E s) := by
  refine ⟨hpc, 1, execInstr i E s, ?_, hb, rfl, rfl⟩
  rw [Function.iterate_one, step_eq_execInstr P E s i (by rwa [← hpc] at hAt)]
/-- Weakening the postcondition. -/
theorem Sem.mono {P : Program} {E : RAMEnv} {a b : ℕ} {s : RAMState}
    {Q Q' : ℕ → RAMState → Prop} (h : Sem P E a b s Q) (hQ : ∀ k s', Q k s' → Q' k s') :
    Sem P E a b s Q' := by
  obtain ⟨hpc, k, s', hstep, hb, hQ'⟩ := h
  exact ⟨hpc, k, s', hstep, hb, hQ k s' hQ'⟩
/-- A `jz` whose test register is zero takes its target, in one step. -/
theorem Sem.jz_taken (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test = 0) :
    Sem P E a t s (fun k s' => k = 1 ∧ s' = { s with pc := t }) := by
  refine Sem.mono (Sem.exec P E a t s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0]⟩
/-- A `jz` whose test register is nonzero falls through, in one step. -/
theorem Sem.jz_next (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test ≠ 0) :
    Sem P E a (a + 1) s (fun k s' => k = 1 ∧ s' = { s with pc := a + 1 }) := by
  refine Sem.mono (Sem.exec P E a (a + 1) s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0, hpc]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0, hpc]⟩
/-- Two exact runs glue, and the costs add. -/
theorem Sem.trans {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState} {n₁ n₂ : ℕ}
    {s₁ s₂ : RAMState}
    (h₁ : Sem P E a b s (fun k s' => k = n₁ ∧ s' = s₁))
    (h₂ : Sem P E b c s₁ (fun k s' => k = n₂ ∧ s' = s₂)) :
    Sem P E a c s (fun k s' => k = n₁ + n₂ ∧ s' = s₂) := by
  obtain ⟨hpc, k₁, t₁, hs₁, -, hk₁, ht₁⟩ := h₁
  obtain ⟨-, k₂, t₂, hs₂, hc, hk₂, ht₂⟩ := h₂
  refine ⟨hpc, k₁ + k₂, s₂, ?_, ?_, by omega, rfl⟩
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, ht₁, hs₂, ht₂]
  · rw [← ht₂]
    exact hc
/-- Sequential composition: the second run may depend on the cost and the state of the first. -/
theorem Sem.seq {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q₁ : ℕ → RAMState → Prop} {Q₂ : ℕ → ℕ → RAMState → Prop}
    (h₁ : Sem P E a b s Q₁)
    (h₂ : ∀ (k₁ : ℕ) (s₁ : RAMState), Q₁ k₁ s₁ → Sem P E b c s₁ (Q₂ k₁)) :
    Sem P E a c s (fun k s' => ∃ k₁ k₂, k = k₁ + k₂ ∧ Q₂ k₁ k₂ s') := by
  obtain ⟨hpc, k₁, s₁, hs₁, -, hQ₁⟩ := h₁
  obtain ⟨-, k₂, s₂, hs₂, hc, hQ₂⟩ := h₂ k₁ s₁ hQ₁
  refine ⟨hpc, k₁ + k₂, s₂, ?_, hc, k₁, k₂, rfl, hQ₂⟩
  rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, hs₂]
/-- Append a `jmp`: the postcondition sees the state with its program counter already moved. -/
theorem Sem.jmp_append {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} (hAt : P[b]? = some (iJmp c))
    (h : Sem P E a b s (fun t s' => Q (t + 1) { s' with pc := c })) :
    Sem P E a c s Q := by
  obtain ⟨hpc, k, s', hstep, hpb, hQ⟩ := h
  have hstep' : (step P E)^[k + 1] s = { s' with pc := c } := by
    rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      step_eq_execInstr P E s' (iJmp c) (by rw [hpb]; exact hAt), execInstr_jmp]
  exact ⟨hpc, k + 1, { s' with pc := c }, hstep', rfl, hQ⟩
/-- Leaving the loop: the test fails, the `jz` fires, control lands past the statement. -/
theorem Sem.loopExit (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt) (s : RAMState)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) (hpc : s.pc = a)
    (hstop : ¬ c.eval s) :
    Sem P E a (a + c.code.length + b.len + 2) s
      (fun k s' => k = c.code.length + 1 ∧
        s' = { runBlock c.code E s with pc := a + c.code.length + b.len + 2 }) := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have h0 : (runBlock c.code E s).regs c.test = 0 := by
    by_contra hne
    exact hstop ((Cond.eval_iff c E s hW).mpr hne)
  exact Sem.trans htest
    (Sem.jz_taken P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT h0)
/-- A `Sem` run that lands on a `halt` is a `HaltsWithin` run; the `halt` itself costs one more
step.  `Post` is the caller's reading of the final state. -/
theorem halts_of_run (P : Program) (E : RAMEnv) (a e : ℕ) (s : RAMState) (B : ℝ)
    (Q : ℕ → RAMState → Prop) (Post : RAMState → Prop)
    (hAt : P[e]? = some .halt) (h : Sem P E a e s Q)
    (hQ : ∀ t s', Q t s' → (t : ℝ) + 1 ≤ B ∧ Post s') :
    ∃ s' : RAMState, HaltsWithin P E B s s' ∧ Post s' := by
  obtain ⟨-, k, s', hstep, hpe, hQ'⟩ := h
  obtain ⟨hB, hPost⟩ := hQ k s' hQ'
  refine ⟨s', ⟨k + 1, ?_, ?_, ?_⟩, hPost⟩
  · push_cast at hB ⊢
    linarith
  · rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      step_halt P E s' (by rw [hpe]; exact hAt)]
  · rw [halted_iff, hpe]
    exact hAt
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
/-- Column `v` of the sketch is what an update XORs in. -/
theorem cr23Sketch_single (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (v : Fin N) :
    cr23Sketch N t C (Pi.single v 1) = fun p => cr23Matrix N t C p v := by
  funext p
  simp [cr23Sketch]
/-- `clog 2 m ≤ logb 2 m + 1` (copied from the old block, renamed). -/
theorem cr23_clog_le_logb_add_one (m : ℕ) (hm : 1 < m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hm)
  have hlt : (2 : ℕ) ^ (Nat.clog 2 m - 1) < m :=
    Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hm
  have hltR : (2 : ℝ) ^ ((Nat.clog 2 m - 1 : ℕ) : ℝ) < (m : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hlt
  have hlog : ((Nat.clog 2 m - 1 : ℕ) : ℝ) < Real.logb 2 (m : ℝ) :=
    (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hmR).2 hltR
  have hc1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num : 1 < 2) hm
  have hsub : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]
    norm_num
  linarith
/-- `1 ≤ lg(N+2)` for `N ≥ 1` (copied from the old block, renamed). -/
theorem cr23_one_le_lg (N : ℕ) (hN : 1 ≤ N) : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := by
  show (1 : ℝ) ≤ Real.logb 2 ((N : ℝ) + 2)
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos, Real.rpow_one]
  have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith
/-- `N ≤ 2^(log N)`. -/
theorem cr23_le_pow_lb (N : ℕ) : N ≤ 2 ^ cr23Lb N := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) (N + 1)
  simp only [cr23Lb]
  omega
/-- `lg` is `Real.logb 2`, definitionally; the bridge lets `linarith` see through the definition. -/
theorem cr23_lg_eq (x : ℝ) : lg x = Real.logb 2 x := rfl
/-- `log N ≤ lg(N+2) + 1`. -/
theorem cr23_lb_le (N : ℕ) (hN : 1 ≤ N) : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := by
  have hmono : cr23Lb N ≤ Nat.clog 2 (N + 2) := by
    have h2 : Nat.clog 2 (N + 1) ≤ Nat.clog 2 (N + 2) := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
      exact le_trans (by omega : N + 1 ≤ N + 2)
        (Nat.le_pow_clog (by norm_num : 1 < 2) (N + 2))
    simpa only [cr23Lb] using h2
  have hcast : (cr23Lb N : ℝ) ≤ (Nat.clog 2 (N + 2) : ℝ) := by exact_mod_cast hmono
  have h := cr23_clog_le_logb_add_one (N + 2) (by omega : 1 < N + 2)
  push_cast at h
  rw [cr23_lg_eq]
  linarith
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
noncomputable section
theorem cr23Word_pos (N : ℕ) : 0 < cr23Word N := by simp only [cr23Word]; omega
/-- The number whose `b`-th bit (for `b < W`) is `f b`. -/
def ofBits (W : ℕ) (f : ℕ → Bool) : ℕ := ∑ b ∈ Finset.range W, if f b then 2 ^ b else 0
theorem geom_two (W : ℕ) : (∑ b ∈ Finset.range W, 2 ^ b) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
theorem ofBits_lt (W : ℕ) (f : ℕ → Bool) : ofBits W f < 2 ^ W := by
  have h : ofBits W f ≤ ∑ b ∈ Finset.range W, 2 ^ b := by
    refine Finset.sum_le_sum ?_
    intro b _
    split_ifs with hb
    · exact le_rfl
    · exact Nat.zero_le _
  rw [geom_two] at h
  have h2 : 0 < 2 ^ W := Nat.two_pow_pos W
  omega
theorem ofBits_succ (W : ℕ) (f : ℕ → Bool) :
    ofBits (W + 1) f = (if f 0 then 1 else 0) + 2 * ofBits W (fun b => f (b + 1)) := by
  rw [ofBits, ofBits, Finset.sum_range_succ']
  have h2 : (∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ (k + 1) else 0))
      = 2 * ∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ k else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    split_ifs with hk
    · rw [pow_succ]
      ring
    · rfl
  rw [h2]
  by_cases h : f 0 = true
  · simp [h, Nat.add_comm]
  · simp [h, Nat.add_comm]
theorem ofBits_testBit (W : ℕ) (f : ℕ → Bool) (b : ℕ) (hb : b < W) :
    (ofBits W f).testBit b = f b := by
  induction W generalizing b f with
  | zero => omega
  | succ n ih =>
      rw [ofBits_succ]
      cases b with
      | zero =>
          rw [Nat.testBit_zero, Nat.add_mul_mod_self_left]
          by_cases h : f 0 = true <;> simp [h]
      | succ b =>
          rw [Nat.testBit_succ]
          have hdiv : ((if f 0 then 1 else 0) + 2 * ofBits n (fun b => f (b + 1))) / 2
              = ofBits n (fun b => f (b + 1)) := by
            rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
            by_cases h : f 0 = true <;> simp [h]
          rw [hdiv]
          exact ih (fun b => f (b + 1)) b (by omega)
/-- `packMem` is the bit string of the rows `a·W + b < M` that are set. -/
theorem packMem_eq_ofBits (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a = ofBits W (fun b => decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1)) := by
  rw [packMem, ofBits]
  have hR : (∑ b ∈ Finset.range W,
        (if decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) then 2 ^ b else 0))
      = ∑ b ∈ (Finset.range W).filter
          (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1), 2 ^ b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b _
    by_cases h : ∃ p : Fin M, p.val = a * W + b ∧ y p = 1 <;> simp [h]
  rw [hR]
  have hL : (∑ p : Fin M, (if p.val / W = a ∧ y p = 1 then 2 ^ (p.val % W) else 0))
      = ∑ b ∈ (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
          (fun p => p.val % W), 2 ^ b := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
    · intro p hp p' hp' heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp hp'
      have heq' : p.val % W = p'.val % W := heq
      refine Fin.ext ?_
      rw [← Nat.div_add_mod p.val W, hp.1, ← Nat.div_add_mod p'.val W, hp'.1, heq']
  rw [hL]
  have himg : (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
        (fun p => p.val % W)
      = (Finset.range W).filter (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and,
      exists_prop]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨Nat.mod_lt _ hW, p, ?_, hp2⟩
      rw [← hp1, Nat.mul_comm]
      exact (Nat.div_add_mod p.val W).symm
    · rintro ⟨hb, p, hp, hp2⟩
      refine ⟨p, ⟨?_, hp2⟩, ?_⟩
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [himg]
theorem testBit_packMem (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a b : ℕ)
    (hb : b < W) :
    (packMem W y a).testBit b = decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_testBit W _ b hb
theorem packMem_lt (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a < 2 ^ W := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_lt W _
/-- In `ZMod 2`, `a + b = 1` is the exclusive or of `a = 1` and `b = 1`. -/
theorem decide_zmod2_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
/-- The `b`-th bit of a sum of two payloads packed into the same word. -/
theorem decide_row_add {M : ℕ} (q : ℕ) (u z : Fin M → ZMod 2) :
    decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1)
      = (decide (∃ p : Fin M, p.val = q ∧ u p = 1)
          ^^ decide (∃ p : Fin M, p.val = q ∧ z p = 1)) := by
  have hrow : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) → ∀ p' : Fin M,
      p'.val = q → y p' = 1 := by
    intro y hy p' hp'
    obtain ⟨p, hp, hpy⟩ := hy
    have : p' = p := Fin.ext (by rw [hp', hp])
    rwa [this]
  by_cases hex : ∃ p : Fin M, p.val = q
  · obtain ⟨p₀, hp₀⟩ := hex
    have e : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) ↔ y p₀ = 1 := by
      intro y
      exact ⟨fun hy => hrow y hy p₀ hp₀, fun hy => ⟨p₀, hp₀, hy⟩⟩
    have e1 : decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1) = decide ((u + z) p₀ = 1) := by
      by_cases h : (u + z) p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e (u + z)).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e (u + z)).mp hc))]
    have e2 : decide (∃ p : Fin M, p.val = q ∧ u p = 1) = decide (u p₀ = 1) := by
      by_cases h : u p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e u).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e u).mp hc))]
    have e3 : decide (∃ p : Fin M, p.val = q ∧ z p = 1) = decide (z p₀ = 1) := by
      by_cases h : z p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e z).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e z).mp hc))]
    rw [e1, e2, e3]
    show decide (u p₀ + z p₀ = 1) = (decide (u p₀ = 1) ^^ decide (z p₀ = 1))
    exact decide_zmod2_add _ _
  · have h1 : ¬ ∃ p : Fin M, p.val = q ∧ (u + z) p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h2 : ¬ ∃ p : Fin M, p.val = q ∧ u p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h3 : ¬ ∃ p : Fin M, p.val = q ∧ z p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
    rfl
/-- **The packed payload is additive.** Toggling the bits of `z` in a stored payload `y` is the
XOR of the packed words. -/
theorem packMem_add (W : ℕ) (hW : 0 < W) {M : ℕ} (u z : Fin M → ZMod 2) (a : ℕ) :
    packMem W (u + z) a = packMem W u a ^^^ packMem W z a := by
  refine Nat.eq_of_testBit_eq ?_
  intro b
  by_cases hb : b < W
  · rw [testBit_packMem W hW _ a b hb, Nat.testBit_xor, testBit_packMem W hW _ a b hb,
      testBit_packMem W hW _ a b hb, decide_row_add]
  · have hbW : W ≤ b := by omega
    have h1 : packMem W (u + z) a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h2 : packMem W u a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h3 : packMem W z a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_xor, Nat.testBit_lt_two_pow h2,
      Nat.testBit_lt_two_pow h3]
    rfl
/-- The part of column `v` contributed by the seeds `0, …, j-1`. -/
def cr23Delta (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (j : ℕ) (v : Fin N) :
    Fin (cr23R N t) → ZMod 2 :=
  fun p => ∑ s ∈ Finset.range j, cr23Lvl N t C v s p
theorem cr23Lvl_apply (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (p : Fin (cr23R N t)) :
    cr23Lvl N t C v s p
      = if p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) then
          cr23Sketch N t C (Pi.single v 1) p else 0 := by
  simp only [cr23Lvl, dif_pos hs]
theorem cr23Lb_succ_pos (N : ℕ) : 0 < cr23Lb N + 1 := by omega
theorem cr23_one_le_lb (N : ℕ) (hN : 1 ≤ N) : 1 ≤ cr23Lb N :=
  Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < N + 1)
theorem cr23D_pos (N : ℕ) (hN : 1 ≤ N) : 0 < cr23D N := by
  have h := cr23_one_le_lb N hN
  simp only [cr23D]
  omega
/-- A row of the sketch forces `M > 0` (`R = 0` when `t = 0`). -/
theorem cr23M_pos (N t : ℕ) (p : Fin (cr23R N t)) : 0 < cr23M t := by
  rcases Nat.eq_zero_or_pos (cr23M t) with h | h
  · exfalso
    have h0 : cr23R N t = 0 := by simp [cr23R, h]
    have := p.isLt
    omega
  · exact h
/-- The check index of row `p` is below `D·M`. -/
theorem cr23_check_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) < cr23D N * cr23M t := by
  rw [Nat.div_lt_iff_lt_mul (cr23Lb_succ_pos N)]
  simpa only [cr23R] using p.isLt
theorem cr23RowSeedComp_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) / cr23M t < cr23D N :=
  (Nat.div_lt_iff_lt_mul (cr23M_pos N t p)).mpr (cr23_check_lt N t p)
theorem cr23RowBktComp_lt (N t : ℕ) (p : Fin (cr23R N t)) :
    p.val / (cr23Lb N + 1) % cr23M t < cr23M t :=
  Nat.mod_lt _ (cr23M_pos N t p)
/-- The seed of row `p`: the check of `p` is `(seed, bucket)`. -/
def cr23RowSeed (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23D N) :=
  ⟨p.val / (cr23Lb N + 1) / cr23M t, cr23RowSeedComp_lt N t p⟩
/-- The bucket of row `p`. -/
def cr23RowBkt (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23M t) :=
  ⟨p.val / (cr23Lb N + 1) % cr23M t, cr23RowBktComp_lt N t p⟩
/-- The label bit of row `p`. -/
def cr23RowBit (N t : ℕ) (p : Fin (cr23R N t)) : Fin (cr23Lb N + 1) :=
  ⟨p.val % (cr23Lb N + 1), Nat.mod_lt _ (cr23Lb_succ_pos N)⟩
/-- The value of the row-triple equivalence, in terms of the check index. -/
theorem cr23RowEquiv_val (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t))
    (k : Fin (cr23Lb N + 1)) :
    (cr23RowEquiv N t ((s, y), k)).val
      = k.val + (cr23Lb N + 1) * cr23Check N t s y := rfl
/-- Every row is the row of its own check, at its own label bit. -/
theorem cr23Row_mk (N t : ℕ) (p : Fin (cr23R N t)) :
    cr23RowEquiv N t ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) = p := by
  refine Fin.ext ?_
  have hsplit : p.val / (cr23Lb N + 1) % cr23M t
        + cr23M t * (p.val / (cr23Lb N + 1) / cr23M t) = p.val / (cr23Lb N + 1) := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod _ _
  simp only [cr23RowEquiv_val, cr23Check, cr23RowSeed, cr23RowBkt, cr23RowBit, Fin.val_mk]
  rw [hsplit, Nat.mod_add_div]
/-- The sketch value at a row is the entry of the row's own check, bucket and bit. -/
theorem cr23Sketch_entry (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (p : Fin (cr23R N t)) :
    cr23Sketch N t C (Pi.single v 1) p
      = cr23Entry N t C ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) v := by
  have hsymm : (cr23RowEquiv N t).symm p
      = ((cr23RowSeed N t p, cr23RowBkt N t p), cr23RowBit N t p) := by
    rw [Equiv.symm_apply_eq]
    exact (cr23Row_mk N t p).symm
  rw [cr23Sketch_single]
  show cr23Matrix N t C p v = _
  rw [show cr23Matrix N t C p v = cr23Entry N t C ((cr23RowEquiv N t).symm p) v from rfl, hsymm]
theorem cr23Lvl_word (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (p : Fin (cr23R N t)) (h : cr23Lvl N t C v s p = 1) :
    p.val / cr23Word N = cr23Addr N t C ⟨s, hs⟩ v := by
  have hn : 0 < cr23Lb N + 1 := cr23Lb_succ_pos N
  rw [cr23Lvl_apply N t C v s hs] at h
  by_cases hc : p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩)
  · have hp : p.val = p.val % (cr23Lb N + 1)
        + (cr23Lb N + 1) * cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) := by
      rw [← hc, Nat.mod_add_div]
    set cheq := cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) with hcheq
    have hk : p.val % (cr23Lb N + 1) < cr23Lb N + 1 := Nat.mod_lt _ hn
    have hr : cheq % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
    have hq : cheq = 1024 * (cheq / 1024) + cheq % 1024 := (Nat.div_add_mod cheq 1024).symm
    have hsmall : p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024)
        < 1024 * (cr23Lb N + 1) := by
      have h1 : (cr23Lb N + 1) * (cheq % 1024) ≤ (cr23Lb N + 1) * 1023 :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 := Nat.add_lt_add_of_lt_of_le hk h1
      calc p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024)
          < (cr23Lb N + 1) + (cr23Lb N + 1) * 1023 := h2
        _ = 1024 * (cr23Lb N + 1) := by ring
    have hsplit : p.val = (p.val % (cr23Lb N + 1) + (cr23Lb N + 1) * (cheq % 1024))
        + (1024 * (cr23Lb N + 1)) * (cheq / 1024) := by
      conv_lhs => rw [hp]
      conv_lhs => rw [hq]
      ring
    rw [cr23Addr, cr23Word, hsplit,
      Nat.add_mul_div_left _ _ (by positivity : 0 < 1024 * (cr23Lb N + 1)),
      Nat.div_eq_of_lt hsmall, Nat.zero_add]
  · rw [if_neg hc] at h
    exact absurd h (by norm_num)
theorem packMem_cr23Lvl (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) (s : ℕ)
    (hs : s < cr23D N) (a : ℕ) :
    packMem (cr23Word N) (cr23Lvl N t C v s) a
      = if a = cr23Addr N t C ⟨s, hs⟩ v then cr23Mask N t C ⟨s, hs⟩ v else 0 := by
  have hW : 0 < cr23Word N := cr23Word_pos N
  by_cases ha : a = cr23Addr N t C ⟨s, hs⟩ v
  · rw [if_pos ha, ha]
    rfl
  · rw [if_neg ha, packMem]
    refine Finset.sum_eq_zero ?_
    intro p _
    by_cases hp : p.val / cr23Word N = a
    · have h0 : cr23Lvl N t C v s p ≠ 1 := by
        rintro h1
        exact ha (by rw [← hp]; exact cr23Lvl_word N t C v s hs p h1)
      rw [if_neg (by rintro ⟨-, hc⟩; exact h0 hc)]
    · rw [if_neg (by rintro ⟨hc, -⟩; exact hp hc)]
theorem cr23Mask_lt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : Fin (cr23D N))
    (v : Fin N) : cr23Mask N t C s v < 2 ^ cr23Word N :=
  packMem_lt (cr23Word N) (cr23Word_pos N) _ _
theorem cr23Delta_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Delta N t C 0 v = 0 := by
  funext p
  simp only [cr23Delta, Finset.range_zero, Finset.sum_empty, Pi.zero_apply]
theorem cr23Delta_succ (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (j : ℕ)
    (v : Fin N) :
    cr23Delta N t C (j + 1) v = cr23Delta N t C j v + cr23Lvl N t C v j := by
  funext p
  simp only [cr23Delta, Finset.sum_range_succ, Pi.add_apply]
/-- **The column of `v` is the sum of its seed parts.** -/
theorem cr23Delta_full (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Delta N t C (cr23D N) v = cr23Sketch N t C (Pi.single v 1) := by
  funext p
  have hM : 0 < cr23M t := cr23M_pos N t p
  have hval := cr23Sketch_entry N t C v p
  have hcheq : p.val / (cr23Lb N + 1)
      = (cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val := by
    have key : p.val / (cr23Lb N + 1) % cr23M t
        + cr23M t * (p.val / (cr23Lb N + 1) / cr23M t) = p.val / (cr23Lb N + 1) := by
      rw [Nat.add_comm]
      exact Nat.div_add_mod _ _
    simp only [cr23RowSeed, cr23RowBkt]
    exact key.symm
  -- any seed whose check matches row `p` is `p`'s own seed, with `p`'s own bucket
  have hkey : ∀ (s : ℕ) (hs : s < cr23D N),
      p.val / (cr23Lb N + 1) = cr23Check N t ⟨s, hs⟩ (C v ⟨s, hs⟩) →
      s = (cr23RowSeed N t p).val ∧ C v ⟨s, hs⟩ = cr23RowBkt N t p := by
    intro s hs hc
    have h1 : (C v ⟨s, hs⟩).val + cr23M t * s
        = (cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val :=
      hc.symm.trans hcheq
    have e1 : ((C v ⟨s, hs⟩).val + cr23M t * s) % cr23M t = (C v ⟨s, hs⟩).val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (C v ⟨s, hs⟩).isLt]
    have e2 : ((cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val) % cr23M t
        = (cr23RowBkt N t p).val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (cr23RowBkt N t p).isLt]
    rw [h1] at e1
    rw [e2] at e1
    have hbkt : C v ⟨s, hs⟩ = cr23RowBkt N t p := Fin.ext e1.symm
    refine ⟨?_, hbkt⟩
    have e3 : ((C v ⟨s, hs⟩).val + cr23M t * s) / cr23M t = s := by
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (C v ⟨s, hs⟩).isLt, Nat.zero_add]
    have e4 : ((cr23RowBkt N t p).val + cr23M t * (cr23RowSeed N t p).val) / cr23M t
        = (cr23RowSeed N t p).val := by
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (cr23RowBkt N t p).isLt, Nat.zero_add]
    rw [← h1] at e4
    rw [← e3]
    exact e4
  by_cases hcy : C v (cr23RowSeed N t p) = cr23RowBkt N t p
  · have hcond : p.val / (cr23Lb N + 1)
        = cr23Check N t (cr23RowSeed N t p) (C v (cr23RowSeed N t p)) := by
      rw [cr23Check, hcy]
      exact hcheq
    have hterm : cr23Lvl N t C v (cr23RowSeed N t p).val p
        = cr23Sketch N t C (Pi.single v 1) p := by
      rw [cr23Lvl_apply N t C v _ (cr23RowSeed N t p).isLt p, if_pos hcond]
    rw [cr23Delta,
      Finset.sum_eq_single (cr23RowSeed N t p).val, hterm]
    · intro s hsS hne
      have hsD : s < cr23D N := Finset.mem_range.mp hsS
      rw [cr23Lvl_apply N t C v s hsD p, if_neg]
      intro hc
      exact hne (hkey s hsD hc).1
    · intro hmem
      exact absurd (Finset.mem_range.mpr (cr23RowSeed N t p).isLt) hmem
  · have hzero : ∀ s ∈ Finset.range (cr23D N), cr23Lvl N t C v s p = 0 := by
      intro s hsS
      have hsD : s < cr23D N := Finset.mem_range.mp hsS
      rw [cr23Lvl_apply N t C v s hsD p, if_neg]
      intro hc
      obtain ⟨hse, hbk⟩ := hkey s hsD hc
      refine hcy ?_
      have hseed : (⟨s, hsD⟩ : Fin (cr23D N)) = cr23RowSeed N t p := Fin.ext hse
      rw [hseed] at hbk
      exact hbk
    rw [cr23Delta, Finset.sum_eq_zero hzero, hval]
    simp only [cr23Entry, Prod.fst, Prod.snd, if_neg hcy]
theorem cr23UpDet_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    cr23UpDet N t C 0 = cr23D N := by
  rw [cr23UpDet, dif_pos rfl]
theorem cr23UpDet_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23UpDet N t C (1 + v.val) = upBase N v.val := by
  have h0 : ¬ (1 + v.val = 0) := by omega
  have hb : 1 + v.val ≤ N := by omega
  rw [cr23UpDet, dif_neg h0, dif_pos hb, show 1 + v.val - 1 = v.val from by omega]
/-- `(b + c·a) % c = b` for `b < c`. -/
theorem cr23_mod_mul_add (a b c : ℕ) (hb : b < c) : (b + c * a) % c = b := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
/-- `(b + c·a) / c = a` for `b < c`. -/
theorem cr23_div_mul_add (a b c : ℕ) (hc : 0 < c) (hb : b < c) : (b + c * a) / c = a := by
  rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hb, Nat.zero_add]
theorem cr23UpDet_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (s : Fin (cr23D N)) :
    cr23UpDet N t C (upBase N v.val + 2 * s.val) = cr23Addr N t C s v := by
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hD0 : 0 < cr23D N := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  set q := upBase N v.val + 2 * s.val with hqdef
  have hq : q = 1 + N + (2 * (cr23D N * v.val) + 2 * s.val) := by
    rw [hqdef]; simp only [upBase]; ring
  have h0 : ¬ (q = 0) := by omega
  have hb : ¬ q ≤ N := by omega
  have hpair : q < cr23PairEnd N := by
    have hv : v.val + 1 ≤ N := by omega
    have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
    have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
    have hsum : 2 * (cr23D N * v.val) + 2 * s.val < 2 * (cr23D N * N) := by
      calc 2 * (cr23D N * v.val) + 2 * s.val < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
        _ = 2 * (cr23D N * (v.val + 1)) := h1
        _ ≤ 2 * (cr23D N * N) := h2
    simp only [cr23PairEnd]
    omega
  have hr : q - (1 + N) = 2 * (cr23D N * v.val) + 2 * s.val := by omega
  have hpar : (q - (1 + N)) % 2 = 0 := by rw [hr]; omega
  have hhalf : (q - (1 + N)) / 2 = s.val + cr23D N * v.val := by rw [hr]; omega
  have hval1 : (q - (1 + N)) / 2 % cr23D N = s.val := by
    rw [hhalf, cr23_mod_mul_add v.val s.val (cr23D N) s.isLt]
  have hval2 : (q - (1 + N)) / 2 / cr23D N % N = v.val := by
    rw [hhalf, cr23_div_mul_add v.val s.val (cr23D N) hD0 s.isLt, Nat.mod_eq_of_lt v.isLt]
  have hs1 : (⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hD0⟩ : Fin (cr23D N)) = s :=
    Fin.ext hval1
  have hv1 : (⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN0⟩ : Fin N) = v :=
    Fin.ext hval2
  rw [cr23UpDet, dif_neg h0, dif_neg hb, dif_pos (show 0 < N ∧ 0 < cr23D N from ⟨hN0, hD0⟩),
    dif_pos hpair, if_pos hpar, hs1, hv1]
theorem cr23UpDet_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N)
    (s : Fin (cr23D N)) :
    cr23UpDet N t C (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hD0 : 0 < cr23D N := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  set q := upBase N v.val + 2 * s.val + 1 with hqdef
  have hq : q = 1 + N + (2 * (cr23D N * v.val) + 2 * s.val) + 1 := by
    rw [hqdef]; simp only [upBase]; ring
  have h0 : ¬ (q = 0) := by omega
  have hb : ¬ q ≤ N := by omega
  have hpair : q < cr23PairEnd N := by
    have hv : v.val + 1 ≤ N := by omega
    have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
    have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
    have hsum : 2 * (cr23D N * v.val) + 2 * s.val + 1 < 2 * (cr23D N * N) := by
      calc 2 * (cr23D N * v.val) + 2 * s.val + 1
          < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
        _ = 2 * (cr23D N * (v.val + 1)) := h1
        _ ≤ 2 * (cr23D N * N) := h2
    simp only [cr23PairEnd]
    omega
  have hr : q - (1 + N) = 2 * (cr23D N * v.val) + 2 * s.val + 1 := by omega
  have hpar : ¬ (q - (1 + N)) % 2 = 0 := by rw [hr]; omega
  have hhalf : (q - (1 + N)) / 2 = s.val + cr23D N * v.val := by rw [hr]; omega
  have hval1 : (q - (1 + N)) / 2 % cr23D N = s.val := by
    rw [hhalf, cr23_mod_mul_add v.val s.val (cr23D N) s.isLt]
  have hval2 : (q - (1 + N)) / 2 / cr23D N % N = v.val := by
    rw [hhalf, cr23_div_mul_add v.val s.val (cr23D N) hD0 s.isLt, Nat.mod_eq_of_lt v.isLt]
  have hs1 : (⟨(q - (1 + N)) / 2 % cr23D N, Nat.mod_lt _ hD0⟩ : Fin (cr23D N)) = s :=
    Fin.ext hval1
  have hv1 : (⟨(q - (1 + N)) / 2 / cr23D N % N, Nat.mod_lt _ hN0⟩ : Fin N) = v :=
    Fin.ext hval2
  rw [cr23UpDet, dif_neg h0, dif_neg hb, dif_pos (show 0 < N ∧ 0 < cr23D N from ⟨hN0, hD0⟩),
    dif_pos hpair, if_neg hpar, hs1, hv1]
theorem cr23_pow_lt_word (N : ℕ) (hN : 1 ≤ N) :
    2 ^ (2 * cr23Lb N + 20) < 2 ^ cr23Word N := by
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  have h := cr23_one_le_lb N hN
  simp only [cr23Word]
  omega
theorem cr23_lt_word (N : ℕ) (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ 2 ^ (2 * cr23Lb N + 20)) :
    j < 2 ^ cr23Word N := lt_of_le_of_lt hj (cr23_pow_lt_word N hN)
theorem cr23D_lt_word (N : ℕ) (hN : 1 ≤ N) : cr23D N < 2 ^ cr23Word N := by
  apply cr23_lt_word N hN
  calc cr23D N = 2 ^ 10 * cr23Lb N := by
        show 1024 * cr23Lb N = 2 ^ 10 * cr23Lb N
        norm_num
    _ ≤ 2 ^ 10 * 2 ^ cr23Lb N := Nat.mul_le_mul_left _ (le_of_lt Nat.lt_two_pow_self)
    _ = 2 ^ (cr23Lb N + 10) := by
        rw [← pow_add]
        congr 1
        omega
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
theorem cr23_succ_lt_word (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : v.val + 1 < 2 ^ cr23Word N := by
  apply cr23_lt_word N hN
  calc v.val + 1 ≤ N := by omega
    _ ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
theorem cr23_one_lt_word (N : ℕ) (hN : 1 ≤ N) : 1 < 2 ^ cr23Word N := by
  have h := cr23D_lt_word N hN
  have h1 : 0 < cr23D N := cr23D_pos N hN
  omega
theorem cr23_two_lt_word (N : ℕ) (hN : 1 ≤ N) : 2 < 2 ^ cr23Word N := by
  have h1 : 2 ≤ 2 ^ (2 * cr23Lb N + 20) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  exact lt_of_le_of_lt h1 (cr23_pow_lt_word N hN)
theorem upBase_le_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ) (hu : u ≤ 2 ^ cr23Lb N) :
    1 + N + 2 * (cr23D N * u) ≤ 2 ^ (2 * cr23Lb N + 13) := by
  have hLle : cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
  have hone : (1 : ℕ) ≤ 2 ^ cr23Lb N := Nat.one_le_two_pow
  have h1 : 1 + N ≤ 2 ^ (cr23Lb N + 1) := by
    calc 1 + N ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N := Nat.add_le_add hone (cr23_le_pow_lb N)
      _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ]; ring
  have h2 : 2 * (cr23D N * u) ≤ 2 ^ (2 * cr23Lb N + 11) := by
    calc 2 * (cr23D N * u) = 2048 * cr23Lb N * u := by
          show 2 * (1024 * cr23Lb N * u) = 2048 * cr23Lb N * u
          ring
      _ ≤ 2048 * cr23Lb N * 2 ^ cr23Lb N := Nat.mul_le_mul_left _ hu
      _ ≤ 2048 * 2 ^ cr23Lb N * 2 ^ cr23Lb N := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left 2048 hLle
      _ = 2 ^ (2 * cr23Lb N + 11) := by
          rw [show (2048 : ℕ) = 2 ^ 11 by norm_num, ← pow_add, ← pow_add]
          congr 1
          ring
  have h3 : 2 ^ (cr23Lb N + 1) ≤ 2 ^ (2 * cr23Lb N + 12) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have h4 : 2 ^ (2 * cr23Lb N + 11) ≤ 2 ^ (2 * cr23Lb N + 12) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have h5 : 2 ^ (2 * cr23Lb N + 12) + 2 ^ (2 * cr23Lb N + 12) = 2 ^ (2 * cr23Lb N + 13) := by
    rw [show 2 * cr23Lb N + 13 = (2 * cr23Lb N + 12) + 1 from by ring, pow_succ]
    ring
  calc 1 + N + 2 * (cr23D N * u)
      ≤ 2 ^ (cr23Lb N + 1) + 2 ^ (2 * cr23Lb N + 11) := Nat.add_le_add h1 h2
    _ ≤ 2 ^ (2 * cr23Lb N + 12) + 2 ^ (2 * cr23Lb N + 12) := Nat.add_le_add h3 h4
    _ = 2 ^ (2 * cr23Lb N + 13) := h5
theorem upBase_lt_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ) (hu : u ≤ 2 ^ cr23Lb N) :
    1 + N + 2 * (cr23D N * u) < 2 ^ cr23Word N := by
  have h1 := upBase_le_general N hN u hu
  have h2 : 2 ^ (2 * cr23Lb N + 13) ≤ 2 ^ (2 * cr23Lb N + 20) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt h2 (cr23_pow_lt_word N hN))
theorem upBase_succ_lt_general (N : ℕ) (hN : 1 ≤ N) (u : ℕ)
    (hu : u ≤ 2 ^ cr23Lb N) : 2 + N + 2 * (cr23D N * u) < 2 ^ cr23Word N := by
  have h1 := upBase_le_general N hN u hu
  have h2 : 2 + N + 2 * (cr23D N * u) ≤ 2 * (1 + N + 2 * (cr23D N * u)) := by omega
  have h3 : 2 * 2 ^ (2 * cr23Lb N + 13) = 2 ^ (2 * cr23Lb N + 14) := by
    rw [show 2 * cr23Lb N + 14 = (2 * cr23Lb N + 13) + 1 from by ring, pow_succ]
    ring
  have h4 : 2 ^ (2 * cr23Lb N + 14) ≤ 2 ^ (2 * cr23Lb N + 20) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  calc 2 + N + 2 * (cr23D N * u) ≤ 2 * (1 + N + 2 * (cr23D N * u)) := h2
    _ ≤ 2 * 2 ^ (2 * cr23Lb N + 13) := Nat.mul_le_mul_left 2 h1
    _ = 2 ^ (2 * cr23Lb N + 14) := h3
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := h4
    _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
theorem upBase_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : upBase N v.val < 2 ^ cr23Word N :=
  upBase_lt_general N hN v.val (le_trans (le_of_lt v.isLt) (cr23_le_pow_lb N))
theorem upBase_add_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) : upBase N v.val + cr23D N < 2 ^ cr23Word N := by
  have h := upBase_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
  have e1 : 2 * (cr23D N * (v.val + 1)) = 2 * (cr23D N * v.val) + 2 * cr23D N := by ring
  have e : upBase N v.val + cr23D N ≤ 1 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]
    rw [e1]
    omega
  exact lt_of_le_of_lt e h
theorem upBase_end_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val + 2 * cr23D N < 2 ^ cr23Word N := by
  have e : upBase N v.val + 2 * cr23D N = 1 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]; ring
  rw [e]
  exact upBase_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
theorem upBase_end_succ_lt (N : ℕ) (hN : 1 ≤ N) (v : Fin N) :
    upBase N v.val + 1 + 2 * cr23D N < 2 ^ cr23Word N := by
  have h := upBase_succ_lt_general N hN (v.val + 1) (le_trans (by omega) (cr23_le_pow_lb N))
  have e : upBase N v.val + 1 + 2 * cr23D N = 2 + N + 2 * (cr23D N * (v.val + 1)) := by
    simp only [upBase]; ring
  rw [e]
  exact h
theorem cr23Check_lt (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t)) :
    cr23Check N t s y < cr23M t * cr23D N := by
  have h1 : cr23M t * s.val + y.val < cr23M t * s.val + cr23M t := Nat.add_lt_add_left y.isLt _
  have h2 : cr23M t * s.val + cr23M t = cr23M t * (s.val + 1) := by ring
  have h3 : cr23M t * (s.val + 1) ≤ cr23M t * cr23D N := Nat.mul_le_mul_left _ (by omega)
  calc cr23Check N t s y = y.val + cr23M t * s.val := rfl
    _ = cr23M t * s.val + y.val := by ring
    _ < cr23M t * s.val + cr23M t := h1
    _ = cr23M t * (s.val + 1) := h2
    _ ≤ cr23M t * cr23D N := h3
theorem progUp_at_pre : At progUp 0 progUpPre := by
  intro r hr
  have hr10 : r < 10 := by simpa [progUpPre] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem progUp_at_body : At progUp 11 progUpBody := by
  intro r hr
  have hr8 : r < 8 := by simpa [progUpBody] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem progUp_at_jmp : progUp[19]? = some (iJmp 10) := by
  simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
    progUpBody]
theorem progUp_at_halt : progUp[20]? = some iHalt := by
  simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
    progUpBody]
theorem progUp_at_loop :
    At progUp 10 (Stmt.compile (Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody)) 10) := by
  show At progUp 10 ([iJz r6 20] ++ progUpBody ++ [iJmp 10])
  intro r hr
  have hr10 : r < 10 := by simpa [progUpBody] using hr
  interval_cases r <;>
    simp [progUp, progUpStmt, Stmt.compile, Stmt.len, Cond.code, Cond.test, progUpPre,
      progUpBody]
theorem Sem.loopCountUp (P : Program) (E : RAMEnv) (a : ℕ) (r : Fin 16) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop (Cond.neqz r) b) a)) (hW : 1 < 2 ^ E.W)
    (n : ℕ) (R : ℕ → RAMState → Prop) (C : ℕ)
    (hirr : ∀ (j : ℕ) (s s' : RAMState), s.regs = s'.regs → s.mem = s'.mem → R j s → R j s')
    (hstop : ∀ s, R 0 s → s.regs r = 0)
    (hgo : ∀ j s, R (j + 1) s → s.regs r ≠ 0)
    (hstep : ∀ j s, R (j + 1) s → Sem P E (a + 1) a { s with pc := a + 1 }
      (fun k s' => k ≤ C ∧ R j s' ∧ s'.pc = a)) :
    ∀ s, s.pc = a → R n s → Sem P E a (a + b.len + 2) s
      (fun k s' => k ≤ n * (1 + C) + 1 ∧ R 0 s' ∧ s'.pc = a + b.len + 2) := by
  obtain ⟨-, hjz, -, -⟩ := at_loop hAt
  intro s hpc hR
  induction n generalizing s with
  | zero =>
      have hstop' : ¬ (Cond.neqz r).eval s := by
        simp only [Cond.eval, ne_eq, not_not]
        exact hstop s hR
      refine Sem.mono (Sem.loopExit P E a (Cond.neqz r) b s hAt hW hpc hstop') ?_
      intro k s' h
      obtain ⟨hk, hs⟩ := h
      subst hk
      subst hs
      refine ⟨?_, ?_, rfl⟩
      · simp only [Cond.code, List.length_nil, Nat.zero_add, Nat.zero_mul]
        omega
      · simp only [Cond.code, runBlock_nil]
        exact hirr 0 s _ rfl rfl hR
  | succ n ih =>
      have hgo' : (Cond.neqz r).eval s := hgo n s hR
      have hjzn : Sem P E a (a + 1) s (fun k s' => k = 1 ∧ s' = { s with pc := a + 1 }) :=
        Sem.jz_next P E a (a + b.len + 2) (Cond.neqz r) s
          (by simpa [Cond.code, Cond.test] using hjz) hpc (by simpa [Cond.eval, Cond.test] using hgo')
      have h1 : Sem P E a a s (fun k s' => k ≤ 1 + C ∧ R n s' ∧ s'.pc = a) := by
        refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = 1 ∧ s' = { s with pc := a + 1 })
          (Q₂ := fun k₁ k₂ s' => k₁ = 1 ∧ (k₂ ≤ C ∧ R n s' ∧ s'.pc = a)) hjzn ?_) ?_
        · intro k₁ s₁ hQ₁
          obtain ⟨rfl, rfl⟩ := hQ₁
          exact Sem.mono (hstep n s hR) (fun k s' h => ⟨rfl, h⟩)
        · intro k s' h
          obtain ⟨k₁, k₂, rfl, hk₁, hk₂, hR', hpc'⟩ := h
          exact ⟨by omega, hR', hpc'⟩
      refine Sem.mono (Sem.seq (Q₁ := fun k s' => k ≤ 1 + C ∧ R n s' ∧ s'.pc = a)
        (Q₂ := fun k₁ k₂ s' => k₁ ≤ 1 + C ∧ (k₂ ≤ n * (1 + C) + 1 ∧ R 0 s' ∧
          s'.pc = a + b.len + 2)) h1 ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨hk₁, hR₁, hpc₁⟩ := hQ₁
        exact Sem.mono (ih s₁ hpc₁ hR₁) (fun k s' h => ⟨hk₁, h⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, rfl, hk₁, hk₂, hR0, hpc'⟩ := h
        have harith : (1 + C) + (n * (1 + C) + 1) = (n + 1) * (1 + C) + 1 := by ring
        exact ⟨by omega, hR0, hpc'⟩
/-- The first four body instructions (up to just before the store) as a chunk. -/
def upBodyA : List Instr := [iTbl r8 r7, iTbl r9 r10, iLd r4 r8, iBxor r4 r4 r9]
theorem upBody_split :
    progUpBody =
      (upBodyA ++ [iSt r8 r4] ++ [iAdd r7 r7 r12, iAdd r10 r10 r12, iSub r6 r6 r13]) := rfl
theorem upBodyA_mem (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).mem = st.mem :=
  runBlock_mem_frame upBodyA E st
    (by
      intro i hi a v
      simp only [upBodyA, List.mem_cons, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | hi
      · simp
      · simp
      · simp
      · simp
      · simp at hi)
theorem upBodyA_r8 (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).regs r8 = E.det (st.regs r7) % 2 ^ E.W := by
  simp only [upBodyA, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_load, execInstr_bxor,
    Function.update_of_ne, Function.update_self]
  rfl
theorem upBodyA_r4 (E : RAMEnv) (st : RAMState) :
    (runBlock upBodyA E st).regs r4
      = ((st.mem (E.det (st.regs r7) % 2 ^ E.W) % 2 ^ E.W ^^^ (E.det (st.regs r10) % 2 ^ E.W))
          % 2 ^ E.W) := by
  simp only [upBodyA, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_load, execInstr_bxor,
    Function.update_of_ne, Function.update_self]
  rfl
theorem upBodyA_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r8)
    (hd2 : d ≠ r4) (hd3 : d ≠ r9) :
    (runBlock upBodyA E st).regs d = st.regs d :=
  runBlock_regs_frame upBodyA E st d
    (by
      intro i hi
      simp only [upBodyA, List.mem_cons, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | hi
      · exact fun h => hd (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd3 (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd2 (by simpa [Instr.dest?] using h.symm)
      · exact fun h => hd2 (by simpa [Instr.dest?] using h.symm)
      · simp at hi)
theorem nat_lor_self (n : ℕ) : n ||| n = n := by simp
/-- The runtime bound `10·D + 11` of the update program is below `65536·lg²(N+2)`. -/
theorem upCost_le (N : ℕ) (hN : 1 ≤ N) :
    10 * (cr23D N : ℝ) + 12 ≤ 65536 * lg ((N : ℝ) + 2) ^ 2 := by
  have hD : (cr23D N : ℝ) = 1024 * (cr23Lb N : ℝ) := by
    simp only [cr23D]
    push_cast
    ring
  have hc : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := cr23_lb_le N hN
  have hlg : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := cr23_one_le_lg N hN
  have hsq : lg ((N : ℝ) + 2) ≤ lg ((N : ℝ) + 2) ^ 2 := by nlinarith only [hlg]
  rw [hD]
  nlinarith only [hc, hlg, hsq]
end
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
variable {N' t' : ℕ}
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
/-- **Below the graph block the two tables agree**: the decoder's own cells are strictly above. -/
theorem cr23DecDet_agrees (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) {a : ℕ}
    (ha : a < cr23DecBase N) : cr23DecDet N t C a = cr23UpDet N t C a := by
  simp only [cr23DecDet, if_pos ha]
theorem cr23DecBase_pos (N : ℕ) : 0 < cr23DecBase N := by
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd]
  omega
/-- The record base of coordinate `v` lies below the decoder's own cells. -/
theorem cr23_succ_lt_decBase (N : ℕ) (v : Fin N) : 1 + v.val < cr23DecBase N := by
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd]
  omega
/-- The last cell of the last record of coordinate `v` lies below the decoder's own cells. -/
theorem cr23_upBase_lt_decBase (N : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    upBase N v.val + 2 * s.val + 1 < cr23DecBase N := by
  have h1 : 2 * (cr23D N * v.val) + 2 * s.val + 1 < 2 * (cr23D N * N) := by
    have hs : 2 * s.val + 1 < 2 * cr23D N := by omega
    calc 2 * (cr23D N * v.val) + 2 * s.val + 1
        < 2 * (cr23D N * v.val) + 2 * cr23D N := by omega
      _ = 2 * (cr23D N * (v.val + 1)) := by ring
      _ ≤ 2 * (cr23D N * N) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega))
  simp only [cr23DecBase, cr23Graph0, cr23PairEnd, upBase]
  omega
theorem cr23DecDet_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N) :
    cr23DecDet N t C 0 = cr23D N := by
  rw [cr23DecDet_agrees N t C (cr23DecBase_pos N), cr23UpDet_zero]
theorem cr23DecDet_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) : cr23DecDet N t C (1 + v.val) = upBase N v.val := by
  rw [cr23DecDet_agrees N t C (cr23_succ_lt_decBase N v), cr23UpDet_base]
theorem cr23DecDet_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDet N t C (upBase N v.val + 2 * s.val) = cr23Addr N t C s v := by
  have h := cr23_upBase_lt_decBase N v s
  rw [cr23DecDet_agrees N t C (by omega), cr23UpDet_addr]
theorem cr23DecDet_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDet N t C (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  rw [cr23DecDet_agrees N t C (cr23_upBase_lt_decBase N v s), cr23UpDet_mask]
theorem decScanWordLt_aux {V L j : ℕ} (hL : 1 ≤ L) (hj : j < V) :
    j / 1024 < (V * L + 1024 * L - 1) / (1024 * L) := by
  have hLpos : 0 < 1024 * L := Nat.mul_pos (by norm_num) (by omega)
  have hV : j + 1024 ≤ V + 1023 := by omega
  have hX : j / 1024 * 1024 ≤ j := Nat.div_mul_le_self _ _
  have h2 : (j / 1024 + 1) * 1024 ≤ V + 1023 := by
    calc (j / 1024 + 1) * 1024 = j / 1024 * 1024 + 1024 := by ring
      _ ≤ j + 1024 := Nat.add_le_add_right hX 1024
      _ ≤ V + 1023 := hV
  have h6 : (V + 1023) * L = V * L + 1023 * L := by ring
  have h8 : 1024 * L = 1023 * L + L := by ring
  have h7 : 1023 * L ≤ 1024 * L - 1 := by rw [h8]; omega
  have hstep : (j / 1024 + 1) * (1024 * L) ≤ V * L + 1024 * L - 1 := by
    calc (j / 1024 + 1) * (1024 * L) = ((j / 1024 + 1) * 1024) * L := by ring
      _ ≤ (V + 1023) * L := Nat.mul_le_mul_right _ h2
      _ = V * L + 1023 * L := h6
      _ ≤ V * L + (1024 * L - 1) := Nat.add_le_add_left h7 _
      _ = V * L + 1024 * L - 1 := (Nat.add_sub_assoc hLpos (V * L)).symm
  have hq : j / 1024 + 1 ≤ (V * L + 1024 * L - 1) / (1024 * L) := by
    rw [Nat.le_div_iff_mul_le hLpos]
    exact hstep
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hq
/-- The payload word index `j / 1024` of a check is inside the packed payload. -/
theorem decScanWordLt (N t : ℕ) (hN : 1 ≤ N) {j : ℕ} (hj : j < cr23D N * cr23M t) :
    j / 1024 < wordsOf (cr23Word N) (cr23R N t) := by
  have h := decScanWordLt_aux (V := cr23D N * cr23M t) (L := cr23Lb N + 1) (by omega) hj
  rw [wordsOf, cr23Word, cr23R]
  exact h
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecXorPay
/-- **The payload word of a check lies inside the packed payload** — this is the bound the restricted
memory clause needs, and it is `decScanWordLt` (already proved for `j / 1024`) plus
`cr23Addr = cr23Check / 1024 < D·M`. -/
theorem addr_wordsOf (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (s : Fin (cr23D N)) (v : Fin N) :
    cr23Addr N t C s v < wordsOf (cr23Word N) (cr23R N t) := by
  have h := cr23Check_lt N t s (C v s)
  rw [Nat.mul_comm] at h
  exact decScanWordLt N t hN h
end DecXorPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option maxRecDepth 8000
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
/-- One past the record block is exactly `cr23Graph0 N`. -/
theorem cr23RecLo_top (N : ℕ) : cr23RecLo N + 2 * (cr23D N * N) = cr23Graph0 N := by
  simp only [cr23RecLo, cr23Graph0, cr23PairEnd]
/-- **Every address cell is a record cell** `upBase N v + 2·s`. -/
theorem cr23AddrSlot_upBase {N : ℕ} (v : Fin N) (s : Fin (cr23D N)) :
    cr23AddrSlot N (upBase N v.val + 2 * s.val) := by
  have hv : v.val + 1 ≤ N := by omega
  have h1 : 2 * (cr23D N * v.val) + 2 * cr23D N = 2 * (cr23D N * (v.val + 1)) := by ring
  have h2 : 2 * (cr23D N * (v.val + 1)) ≤ 2 * (cr23D N * N) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv)
  refine ⟨?_, ?_, ?_⟩
  · simp only [cr23RecLo, upBase]; omega
  · rw [← cr23RecLo_top]
    simp only [upBase, cr23RecLo]
    omega
  · have e : upBase N v.val + 2 * s.val - cr23RecLo N
        = 2 * (cr23D N * v.val) + 2 * s.val := by
      simp only [cr23RecLo, upBase]; omega
    rw [e]; omega
/-- **The mask cell of a record is not an address cell.** -/
theorem cr23AddrSlot_mask_not {N : ℕ} (v : Fin N) (s : Fin (cr23D N)) :
    ¬ cr23AddrSlot N (upBase N v.val + 2 * s.val + 1) := by
  intro h
  obtain ⟨-, -, hpar⟩ := h
  have e : upBase N v.val + 2 * s.val + 1 - cr23RecLo N
      = 2 * (cr23D N * v.val) + 2 * s.val + 1 := by
    simp only [cr23RecLo, upBase]; omega
  rw [e] at hpar
  omega
theorem cr23AddrSlot_zero_not (N : ℕ) : ¬ cr23AddrSlot N 0 := by
  intro h; obtain ⟨h1, -⟩ := h; simp only [cr23RecLo] at h1; omega
theorem cr23AddrSlot_one_add_not {N : ℕ} (v : Fin N) : ¬ cr23AddrSlot N (1 + v.val) := by
  intro h; obtain ⟨h1, -⟩ := h; simp only [cr23RecLo] at h1; omega
/-- **Cells that are not address cells are untouched** — this is the whole content of the
classification: numbers and `det` indices do not move. -/
theorem cr23DecDetAt_agree (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β a : ℕ)
    (h : ¬ cr23AddrSlot N a) : cr23DecDetAt N t C β a = cr23DecDet N t C a := by
  simp only [cr23DecDetAt, if_neg h]
/-- `det 0 = D` — a **number**. -/
theorem cr23DecDetAt_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) : cr23DecDetAt N t C β 0 = cr23D N := by
  rw [cr23DecDetAt_agree N t C β 0 (cr23AddrSlot_zero_not N), cr23DecDet_zero N t C hN]
/-- `det (1+v) = upBase N v` — a **det index**: unchanged. -/
theorem cr23DecDetAt_base (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) : cr23DecDetAt N t C β (1 + v.val) = upBase N v.val := by
  rw [cr23DecDetAt_agree N t C β _ (cr23AddrSlot_one_add_not v), cr23DecDet_base N t C hN v]
/-- `det (upBase v + 2s) = cr23Addr` — a **memory address**: shifted by `β`. -/
theorem cr23DecDetAt_addr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDetAt N t C β (upBase N v.val + 2 * s.val) = β + cr23Addr N t C s v := by
  rw [cr23DecDetAt, if_pos (cr23AddrSlot_upBase v s), cr23DecDet_addr N t C hN v s]
/-- `det (upBase v + 2s + 1) = cr23Mask` — a **number**: unchanged. -/
theorem cr23DecDetAt_mask (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N)
    (β : ℕ) (v : Fin N) (s : Fin (cr23D N)) :
    cr23DecDetAt N t C β (upBase N v.val + 2 * s.val + 1) = cr23Mask N t C s v := by
  rw [cr23DecDetAt_agree N t C β _ (cr23AddrSlot_mask_not v s), cr23DecDet_mask N t C hN v s]
/-- Word `a` of the payload, read from base `β`, is word `a` of `y`. -/
theorem payMem_at {W M β : ℕ} (y : Fin M → ZMod 2) {a : ℕ} (ha : a < wordsOf W M) :
    payMem W β y (β + a) = packMem W y a := by
  rw [payMem, if_pos ⟨Nat.le_add_right _ _, by rwa [Nat.add_sub_cancel_left]⟩,
    Nat.add_sub_cancel_left]
/-- **`UpData` with the payload moved to base `β`.**  The nine register clauses are *identical* to
`UpData`'s — that is the content of the classification: no register of `progUp` holds a payload
address across a step.  The only register that ever does, `r8`, is written by `qDet` and consumed by
the following `load`/`store` inside `progUpBody` (`§R.4.1`). -/
def UpDataAt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (s : RAMState) : Prop :=
  s.regs r0 = v.val ∧ s.regs r3 = cr23D N ∧ s.regs r5 = upBase N v.val ∧ s.regs r6 = m ∧
    s.regs r7 = upBase N v.val + 2 * (cr23D N - m) ∧
    s.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - m) ∧
    s.regs r11 = upBase N v.val + 2 * cr23D N ∧ s.regs r12 = 2 ∧ s.regs r13 = 1 ∧
    (∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      s.mem (β + addr) = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - m) v) addr) ∧
    (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
      s.mem c = payMem (cr23Word N) β y c)
theorem UpDataAt.irrel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ)
    (s s' : RAMState) (hr : s.regs = s'.regs) (hm : s.mem = s'.mem)
    (h : UpDataAt N t C β y v m s) : UpDataAt N t C β y v m s' := by
  rcases h with ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem, hfr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact h0
  · rw [← hr]; exact h3
  · rw [← hr]; exact h5
  · rw [← hr]; exact h6
  · rw [← hr]; exact h7
  · rw [← hr]; exact h10
  · rw [← hr]; exact h11
  · rw [← hr]; exact h12
  · rw [← hr]; exact h13
  · intro addr ha; rw [← hm]; exact hmem addr ha
  · intro c hc; rw [← hm]; exact hfr c hc
theorem upBody_data_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (a j : ℕ) (hj : j + 1 ≤ cr23D N)
    (s : RAMState) (hR : UpDataAt N t C β y v (j + 1) s) :
    UpDataAt N t C β y v j
      (runBlock progUpBody (detEnv (cr23Word N) (cr23DecDetAt N t C β)) { s with pc := a + 1 }) := by
  obtain ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hm, hfr⟩ := hR
  have hW : 0 < cr23Word N := cr23Word_pos N
  have hD : 0 < cr23D N := cr23D_pos N hN
  have hi : cr23D N - (j + 1) < cr23D N := by omega
  have hsucc : cr23D N - (j + 1) + 1 = cr23D N - j := by omega
  have hjW : j < 2 ^ cr23Word N := lt_trans (by omega : j < cr23D N) (cr23D_lt_word N hN)
  have h2j : 2 * (cr23D N - j) ≤ 2 * cr23D N := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hdelta : cr23Delta N t C (cr23D N - j) v
      = cr23Delta N t C (cr23D N - (j + 1)) v + cr23Lvl N t C v (cr23D N - (j + 1)) := by
    rw [← hsucc]
    exact cr23Delta_succ N t C (cr23D N - (j + 1)) v
  have hpack : ∀ addr, packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v) addr
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v) addr
        ^^^ packMem (cr23Word N) (cr23Lvl N t C v (cr23D N - (j + 1))) addr := by
    intro addr
    rw [hdelta, ← add_assoc, packMem_add (cr23Word N) hW]
  have hval : packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
        (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
          (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
        ^^^ cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hpack, packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_pos rfl]
  have hdetA : cr23DecDetAt N t C β (upBase N v.val + 2 * (cr23D N - (j + 1)))
      = β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v :=
    cr23DecDetAt_addr N t C hN β v ⟨cr23D N - (j + 1), hi⟩
  have hdetM : cr23DecDetAt N t C β (upBase N v.val + 1 + 2 * (cr23D N - (j + 1)))
      = cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    have e : upBase N v.val + 1 + 2 * (cr23D N - (j + 1))
        = upBase N v.val + 2 * (cr23D N - (j + 1)) + 1 := by ring
    rw [e]
    exact cr23DecDetAt_mask N t C hN β v ⟨cr23D N - (j + 1), hi⟩
  have hAW : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
      < wordsOf (cr23Word N) (cr23R N t) := DecXorPay.addr_wordsOf N t hN htN C _ v
  have hbA : β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ cr23Word N := by omega
  have hmask_lt : cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ cr23Word N :=
    cr23Mask_lt N t C ⟨cr23D N - (j + 1), hi⟩ v
  have hmA : s.mem (β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
      = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - (j + 1)) v)
          (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v) := hm _ hAW
  -- first four body instructions
  set st1 : RAMState :=
    runBlock upBodyA (detEnv (cr23Word N) (cr23DecDetAt N t C β)) { s with pc := a + 1 } with hst1
  have h1mem : st1.mem = s.mem := by
    rw [hst1]
    exact upBodyA_mem _ _
  have h1r8 : st1.regs r8 = β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hst1, upBodyA_r8]
    simp only [detEnv]
    rw [h7, hdetA, Nat.mod_eq_of_lt hbA]
  have h1r10 : st1.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) := by
    rw [hst1, upBodyA_frame _ _ r10 (by decide) (by decide) (by decide)]
    exact h10
  have h1r7 : st1.regs r7 = upBase N v.val + 2 * (cr23D N - (j + 1)) := by
    rw [hst1, upBodyA_frame _ _ r7 (by decide) (by decide) (by decide)]
    exact h7
  have h1r12 : st1.regs r12 = 2 := by
    rw [hst1, upBodyA_frame _ _ r12 (by decide) (by decide) (by decide)]
    exact h12
  have h1r13 : st1.regs r13 = 1 := by
    rw [hst1, upBodyA_frame _ _ r13 (by decide) (by decide) (by decide)]
    exact h13
  have h1r6 : st1.regs r6 = j + 1 := by
    rw [hst1, upBodyA_frame _ _ r6 (by decide) (by decide) (by decide)]
    exact h6
  have h1r4 : st1.regs r4 = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
      (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v) := by
    rw [hst1, upBodyA_r4]
    simp only [detEnv]
    rw [h7, h10, hdetA, Nat.mod_eq_of_lt hbA, hdetM, Nat.mod_eq_of_lt hmask_lt, hmA,
      Nat.mod_eq_of_lt (packMem_lt (cr23Word N) hW _ _),
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (packMem_lt (cr23Word N) hW _ _) hmask_lt), hval]
  -- the store
  set st2 : RAMState :=
    execInstr (iSt r8 r4) (detEnv (cr23Word N) (cr23DecDetAt N t C β)) st1 with hst2
  have h2mem : st2.mem
      = Function.update s.mem (β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
          (packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - j) v)
            (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)) := by
    rw [hst2, execInstr_store, h1mem, h1r8, h1r4]
  have h2r0 : st2.regs r0 = v.val := by
    rw [hst2, execInstr_store]
    show st1.regs r0 = v.val
    rw [hst1, upBodyA_frame _ _ r0 (by decide) (by decide) (by decide)]
    exact h0
  have h2r3 : st2.regs r3 = cr23D N := by
    rw [hst2, execInstr_store]
    show st1.regs r3 = cr23D N
    rw [hst1, upBodyA_frame _ _ r3 (by decide) (by decide) (by decide)]
    exact h3
  have h2r5 : st2.regs r5 = upBase N v.val := by
    rw [hst2, execInstr_store]
    show st1.regs r5 = upBase N v.val
    rw [hst1, upBodyA_frame _ _ r5 (by decide) (by decide) (by decide)]
    exact h5
  have h2r11 : st2.regs r11 = upBase N v.val + 2 * cr23D N := by
    rw [hst2, execInstr_store]
    show st1.regs r11 = upBase N v.val + 2 * cr23D N
    rw [hst1, upBodyA_frame _ _ r11 (by decide) (by decide) (by decide)]
    exact h11
  have h2r6 : st2.regs r6 = j + 1 := by
    rw [hst2, execInstr_store]
    show st1.regs r6 = j + 1
    exact h1r6
  have h2r7 : st2.regs r7 = upBase N v.val + 2 * (cr23D N - (j + 1)) := by
    rw [hst2, execInstr_store]
    show st1.regs r7 = upBase N v.val + 2 * (cr23D N - (j + 1))
    exact h1r7
  have h2r10 : st2.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) := by
    rw [hst2, execInstr_store]
    show st1.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - (j + 1))
    exact h1r10
  have h2r12 : st2.regs r12 = 2 := by
    rw [hst2, execInstr_store]
    show st1.regs r12 = 2
    exact h1r12
  have h2r13 : st2.regs r13 = 1 := by
    rw [hst2, execInstr_store]
    show st1.regs r13 = 1
    exact h1r13
  -- the three counter/pointer bumps
  set st3 : RAMState :=
    execInstr (iAdd r7 r7 r12) (detEnv (cr23Word N) (cr23DecDetAt N t C β)) st2 with hst3
  set st4 : RAMState :=
    execInstr (iAdd r10 r10 r12) (detEnv (cr23Word N) (cr23DecDetAt N t C β)) st3 with hst4
  set st5 : RAMState :=
    execInstr (iSub r6 r6 r13) (detEnv (cr23Word N) (cr23DecDetAt N t C β)) st4 with hst5
  have h3f : ∀ d : Fin 16, r7 ≠ d → st3.regs d = st2.regs d := by
    intro d hd
    rw [hst3]
    exact execInstr_regs (iAdd r7 r7 r12) _ st2 d (by simpa [Instr.dest?] using hd)
  have h4f : ∀ d : Fin 16, r10 ≠ d → st4.regs d = st3.regs d := by
    intro d hd
    rw [hst4]
    exact execInstr_regs (iAdd r10 r10 r12) _ st3 d (by simpa [Instr.dest?] using hd)
  have h5f : ∀ d : Fin 16, r6 ≠ d → st5.regs d = st4.regs d := by
    intro d hd
    rw [hst5]
    exact execInstr_regs (iSub r6 r6 r13) _ st4 d (by simpa [Instr.dest?] using hd)
  have h3r7 : st3.regs r7 = (st2.regs r7 + 2) % 2 ^ cr23Word N := by
    simp only [hst3, execInstr_add, Function.update_self, detEnv, h2r12]
  have h4r10 : st4.regs r10 = (st3.regs r10 + 2) % 2 ^ cr23Word N := by
    simp only [hst4, execInstr_add, Function.update_self, detEnv, h3f r10 (by decide),
      h3f r12 (by decide), h2r12]
  have h5r6 : st5.regs r6 = (st4.regs r6 + 2 ^ cr23Word N - st4.regs r13) % 2 ^ cr23Word N := by
    simp only [hst5, execInstr_sub, Function.update_self, detEnv]
  -- the whole body is `st5`
  have hbody : runBlock progUpBody (detEnv (cr23Word N) (cr23DecDetAt N t C β)) { s with pc := a + 1 }
      = st5 := by
    simp only [upBody_split, runBlock_append, runBlock_cons, runBlock_nil, ← hst1, ← hst2,
      ← hst3, ← hst4, ← hst5]
  rw [hbody]
  have h5m : st5.mem = st2.mem := by
    simp only [hst5, hst4, hst3, execInstr_sub, execInstr_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5f r0 (by decide), h4f r0 (by decide), h3f r0 (by decide)]
    exact h2r0
  · rw [h5f r3 (by decide), h4f r3 (by decide), h3f r3 (by decide)]
    exact h2r3
  · rw [h5f r5 (by decide), h4f r5 (by decide), h3f r5 (by decide)]
    exact h2r5
  · rw [h5r6, h4f r6 (by decide), h3f r6 (by decide), h2r6, h4f r13 (by decide),
      h3f r13 (by decide), h2r13]
    have e : j + 1 + 2 ^ cr23Word N - 1 = j + 2 ^ cr23Word N := by omega
    rw [e, show j + 2 ^ cr23Word N = j + 1 * 2 ^ cr23Word N from by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjW]
  · rw [h5f r7 (by decide), h4f r7 (by decide), h3r7, h2r7]
    have e : upBase N v.val + 2 * (cr23D N - (j + 1)) + 2
        = upBase N v.val + 2 * (cr23D N - j) := by
      rw [show upBase N v.val + 2 * (cr23D N - (j + 1)) + 2
          = upBase N v.val + 2 * (cr23D N - (j + 1) + 1) from by ring, hsucc]
    rw [e]
    refine Nat.mod_eq_of_lt ?_
    calc upBase N v.val + 2 * (cr23D N - j) ≤ upBase N v.val + 2 * cr23D N := Nat.add_le_add_left h2j _
      _ < 2 ^ cr23Word N := upBase_end_lt N hN v
  · rw [h5f r10 (by decide), h4r10, h3f r10 (by decide), h2r10]
    have e : upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) + 2
        = upBase N v.val + 1 + 2 * (cr23D N - j) := by
      rw [show upBase N v.val + 1 + 2 * (cr23D N - (j + 1)) + 2
          = upBase N v.val + 1 + 2 * (cr23D N - (j + 1) + 1) from by ring, hsucc]
    rw [e]
    refine Nat.mod_eq_of_lt ?_
    have h1 : upBase N v.val + 1 + 2 * (cr23D N - j) ≤ upBase N v.val + 1 + 2 * cr23D N :=
      Nat.add_le_add_left h2j _
    have h2 : upBase N v.val + 1 + 2 * cr23D N < 2 ^ cr23Word N :=
      upBase_end_succ_lt N hN v
    omega
  · rw [h5f r11 (by decide), h4f r11 (by decide), h3f r11 (by decide)]
    exact h2r11
  · rw [h5f r12 (by decide), h4f r12 (by decide), h3f r12 (by decide)]
    exact h2r12
  · rw [h5f r13 (by decide), h4f r13 (by decide), h3f r13 (by decide)]
    exact h2r13
  · intro addr haddr
    rw [h5m, h2mem]
    by_cases had : addr = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
    · subst had
      rw [Function.update_self]
    · rw [Function.update_of_ne (by intro hh; exact had (Nat.add_left_cancel hh)),
        hm addr haddr, hpack addr, packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_neg had,
        Nat.xor_zero]
  · intro c hc
    rw [h5m, h2mem]
    have hne : c ≠ β + cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by omega
    rw [Function.update_of_ne hne]
    exact hfr c hc
theorem upBodyIter_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (j : ℕ) (hj : j + 1 ≤ cr23D N)
    (s : RAMState) (hR : UpDataAt N t C β y v (j + 1) s) :
    Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 11 10 { s with pc := 11 }
      (fun k s' => k ≤ 9 ∧ UpDataAt N t C β y v j s' ∧ s'.pc = 10) := by
  have hbd := upBody_data_at N t hN htN C β hβ y v 10 j hj s hR
  have hno : NoBranch progUpBody := by simp [progUpBody]
  have hblk : Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 11 19 { s with pc := 11 }
      (fun k s' => k = progUpBody.length ∧
        s' = runBlock progUpBody (detEnv (cr23Word N) (cr23DecDetAt N t C β)) { s with pc := 11 }) := by
    have h := Sem.block progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 11 progUpBody
      { s with pc := 11 } progUp_at_body hno rfl
    simpa [progUpBody] using h
  refine Sem.jmp_append progUp_at_jmp ?_
  refine Sem.mono hblk ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨?_, ?_, rfl⟩
  · have h8 : progUpBody.length = 8 := rfl
    omega
  · exact UpDataAt.irrel N t C β y v j _ _ rfl rfl hbd
theorem upPre_data_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) :
    UpDataAt N t C β y v (cr23D N)
      (runBlock progUpPre (detEnv (cr23Word N) (cr23DecDetAt N t C β))
        (payStart (cr23Word N) β y v.val)) := by
  have h1 : 1 % 2 ^ cr23Word N = 1 := Nat.mod_eq_of_lt (cr23_one_lt_word N hN)
  have h2 : 2 % 2 ^ cr23Word N = 2 := Nat.mod_eq_of_lt (cr23_two_lt_word N hN)
  have hw : cr23D N % 2 ^ cr23Word N = cr23D N :=
    Nat.mod_eq_of_lt (cr23D_lt_word N hN)
  have hv1 : (v.val + 1) % 2 ^ cr23Word N = v.val + 1 :=
    Nat.mod_eq_of_lt (cr23_succ_lt_word N hN v)
  have hv1' : (1 + v.val) % 2 ^ cr23Word N = 1 + v.val := by
    rw [Nat.add_comm 1 v.val, hv1]
  have hv1c : v.val + 1 = 1 + v.val := by omega
  have hb : upBase N v.val % 2 ^ cr23Word N = upBase N v.val :=
    Nat.mod_eq_of_lt (upBase_lt N hN v)
  have hb1 : (upBase N v.val + 1) % 2 ^ cr23Word N = upBase N v.val + 1 := by
    have h := upBase_add_lt N hN v
    have hD := cr23D_pos N hN
    exact Nat.mod_eq_of_lt (by omega)
  have hbw1 : (upBase N v.val + cr23D N) % 2 ^ cr23Word N = upBase N v.val + cr23D N :=
    Nat.mod_eq_of_lt (upBase_add_lt N hN v)
  have hbw2 : (upBase N v.val + cr23D N + cr23D N) % 2 ^ cr23Word N
      = upBase N v.val + 2 * cr23D N := by
    rw [show upBase N v.val + cr23D N + cr23D N = upBase N v.val + 2 * cr23D N from by ring]
    exact Nat.mod_eq_of_lt (upBase_end_lt N hN v)
  have hzero : cr23DecDetAt N t C β 0 = cr23D N := cr23DecDetAt_zero N t C hN β
  have hbase : cr23DecDetAt N t C β (1 + v.val) = upBase N v.val :=
    cr23DecDetAt_base N t C hN β v
  have hmem : (runBlock progUpPre (detEnv (cr23Word N) (cr23DecDetAt N t C β))
      (payStart (cr23Word N) β y v.val)).mem = payMem (cr23Word N) β y := by
    simp only [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · simp [progUpPre, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      execInstr_add, execInstr_bor, payStart, initState, detEnv, h1, h2, hw, hv1, hv1c, hb, hb1,
      hbw1, hbw2, hzero, hbase, hv1', nat_lor_self]
  · intro addr haddr
    rw [hmem, Nat.sub_self, cr23Delta_zero, add_zero]
    exact payMem_at y haddr
  · intro c hc
    rw [hmem]
theorem upLoop_data_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (s : RAMState)
    (hpc : s.pc = 10) (hR : UpDataAt N t C β y v (cr23D N) s) :
    Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 10 20 s
      (fun k s' => k ≤ cr23D N * 10 + 1 ∧ UpDataAt N t C β y v 0 s' ∧ s'.pc = 20) := by
  have hW : 1 < 2 ^ (detEnv (cr23Word N) (cr23DecDetAt N t C β)).W := by
    simp only [detEnv]
    exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), s.regs = s'.regs → s.mem = s'.mem →
      (UpDataAt N t C β y v j s ∧ j ≤ cr23D N) →
      (UpDataAt N t C β y v j s' ∧ j ≤ cr23D N) := by
    intro j s s' hr hm h
    exact ⟨UpDataAt.irrel N t C β y v j s s' hr hm h.1, h.2⟩
  have hstop : ∀ s, (UpDataAt N t C β y v 0 s ∧ 0 ≤ cr23D N) → s.regs r6 = 0 := by
    intro s h
    exact h.1.2.2.2.1
  have hgo : ∀ j s, (UpDataAt N t C β y v (j + 1) s ∧ j + 1 ≤ cr23D N) → s.regs r6 ≠ 0 := by
    intro j s h
    rw [h.1.2.2.2.1]
    omega
  have hstep : ∀ j s, (UpDataAt N t C β y v (j + 1) s ∧ j + 1 ≤ cr23D N) →
      Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 11 10 { s with pc := 11 }
        (fun k s' => k ≤ 9 ∧ (UpDataAt N t C β y v j s' ∧ j ≤ cr23D N) ∧ s'.pc = 10) := by
    intro j s h
    refine Sem.mono (upBodyIter_at N t hN htN C β hβ y v j h.2 s h.1) ?_
    intro k s' hk
    exact ⟨hk.1, ⟨hk.2.1, by omega⟩, hk.2.2⟩
  have hloop := Sem.loopCountUp progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 10 r6
    (Stmt.code progUpBody) progUp_at_loop hW (cr23D N)
    (fun j s => UpDataAt N t C β y v j s ∧ j ≤ cr23D N) 9 hirr hstop hgo hstep s hpc
    ⟨hR, le_rfl⟩
  exact Sem.mono hloop (fun k s' h => ⟨h.1, h.2.1.1, h.2.2⟩)
theorem upRun_data_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N)
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) :
    Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 0 20
      (payStart (cr23Word N) β y v.val)
      (fun k s' => k ≤ 10 + (cr23D N * 10 + 1) ∧ UpDataAt N t C β y v 0 s' ∧ s'.pc = 20) := by
  have hno : NoBranch progUpPre := by simp [progUpPre]
  have hpre : Sem progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 0 10
      (payStart (cr23Word N) β y v.val)
      (fun k s' => k = 10 ∧ s' = runBlock progUpPre
        (detEnv (cr23Word N) (cr23DecDetAt N t C β)) (payStart (cr23Word N) β y v.val)) :=
    Sem.block progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 0 progUpPre _ progUp_at_pre hno rfl
  have hpc : (runBlock progUpPre (detEnv (cr23Word N) (cr23DecDetAt N t C β))
      (payStart (cr23Word N) β y v.val)).pc = 10 := by
    rw [runBlock_pc progUpPre (detEnv (cr23Word N) (cr23DecDetAt N t C β)) _ hno]
    simp [progUpPre, payStart, initState]
  refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' => k1 = 10 ∧
    (k2 ≤ cr23D N * 10 + 1 ∧ UpDataAt N t C β y v 0 s' ∧ s'.pc = 20)) hpre ?_) ?_
  · intro k1 s1 h1
    obtain ⟨rfl, rfl⟩ := h1
    exact Sem.mono
      (upLoop_data_at N t hN htN C β hβ y v _ hpc (upPre_data_at N t hN htN C β y v))
      (fun k s' h => ⟨rfl, h⟩)
  · intro k s' h
    obtain ⟨k1, k2, hk, hk1, hlt, hU, hpc20⟩ := h
    subst hk1
    exact ⟨by omega, hU, hpc20⟩
/-- **The toggle program at an arbitrary payload base `β`.**  Its table is `cr23DecDetAt N t C β`;
it starts from the payload packed at word `β` and halts having XORed column `v` into it *in place*,
leaving everything outside the payload words alone. -/
theorem cr23_toggles_within_at_proof (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N) :
    ∀ (y : Fin (cr23R N t) → ZMod 2) (v : Fin N), ∃ s' : RAMState,
      HaltsWithin progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β))
        (65536 * lg ((N : ℝ) + 2) ^ 2) (payStart (cr23Word N) β y v.val) s' ∧
      (∀ addr < wordsOf (cr23Word N) (cr23R N t),
        s'.mem (β + addr)
          = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) addr) ∧
      s'.pc = 20 ∧ progUp.length = 21 ∧
      (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
        s'.mem c = payMem (cr23Word N) β y c) := by
  intro y v
  have hQ : ∀ (k : ℕ) (s' : RAMState),
      (k ≤ 10 + (cr23D N * 10 + 1) ∧ UpDataAt N t C β y v 0 s' ∧ s'.pc = 20) →
      ((k : ℝ) + 1 ≤ 65536 * lg ((N : ℝ) + 2) ^ 2) ∧
        ((∀ addr < wordsOf (cr23Word N) (cr23R N t),
            s'.mem (β + addr)
              = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) addr) ∧
          s'.pc = 20 ∧ progUp.length = 21 ∧
          (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
            s'.mem c = payMem (cr23Word N) β y c)) := by
    intro k s' h
    have hcost := upCost_le N hN
    have hk : (k : ℝ) ≤ ((10 + (cr23D N * 10 + 1) : ℕ) : ℝ) := by exact_mod_cast h.1
    have hk' : ((10 + (cr23D N * 10 + 1) : ℕ) : ℝ) = 10 * (cr23D N : ℝ) + 11 := by
      push_cast
      ring
    refine ⟨?_, ?_, h.2.2, rfl, ?_⟩
    · nlinarith only [hk, hk', hcost]
    · obtain ⟨-, -, -, -, -, -, -, -, -, hmem, -⟩ := h.2.1
      intro addr haddr
      have hcol : cr23Delta N t C (cr23D N) v = cr23Sketch N t C (Pi.single v 1) :=
        cr23Delta_full N t C v
      rw [Nat.sub_zero] at hmem
      rw [hcol] at hmem
      exact hmem addr haddr
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hfr⟩ := h.2.1
      exact hfr
  exact halts_of_run progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β)) 0 20
    (payStart (cr23Word N) β y v.val) (65536 * lg ((N : ℝ) + 2) ^ 2)
    (fun k s' => k ≤ 10 + (cr23D N * 10 + 1) ∧ UpDataAt N t C β y v 0 s' ∧ s'.pc = 20)
    (fun s' => (∀ addr < wordsOf (cr23Word N) (cr23R N t),
        s'.mem (β + addr)
          = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) addr) ∧
      s'.pc = 20 ∧ progUp.length = 21 ∧
      (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
        s'.mem c = payMem (cr23Word N) β y c))
    progUp_at_halt (upRun_data_at N t hN htN C β hβ y v) hQ
end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
theorem solution (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N) :
∀ (y : Fin (cr23R N t) → ZMod 2) (v : Fin N), ∃ s' : RAMState,
  HaltsWithin progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β))
    (65536 * lg ((N : ℝ) + 2) ^ 2) (payStart (cr23Word N) β y v.val) s' ∧
  (∀ addr < wordsOf (cr23Word N) (cr23R N t),
    s'.mem (β + addr)
      = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) addr) ∧
  s'.pc = 20 ∧ progUp.length = 21 ∧
  (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
    s'.mem c = payMem (cr23Word N) β y c) :=
  cr23_toggles_within_at_proof N t hN htN C β hβ
