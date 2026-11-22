-- Prove2me | solution 1 for LinearSetReconciliation327.Main.cr23_decoding
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T06:48:06.466032+00:00
-- url     : https://prove2.me/submissions/7b2308b1-b258-4d39-84b1-ac4aa3ca92de

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec
import Definitions.Def_LinearSetReconciliation327_Main_CR23Run20261122

set_option autoImplicit false
set_option linter.all false
namespace LinearSetReconciliation327.Main
open Finset
/-- Packing a `Fin K`-indexed family is the same as the sum of shifted fields. -/
theorem packL_ofFn (w K : ℕ) (f : Fin K → ℕ) :
    packL w (List.ofFn f) = ∑ j : Fin K, f j * 2 ^ (j.val * w) := by
  induction K with
  | zero => simp [packL]
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [packL, Fin.val_zero, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Fin.val_succ]
      rw [ih (fun i => f i.succ), Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have h2 : 2 ^ ((j.val + 1) * w) = 2 ^ w * 2 ^ (j.val * w) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
      rw [h2]
      ring
/-- Extracting the `k`-th `w`-bit field, in division form. -/
theorem extract_field_div (w : ℕ) (_hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w)
    (k : ℕ) : packL w l / 2 ^ (k * w) % 2 ^ w = l.getD k 0 := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, packL, List.getD_cons_zero]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  | succ k ih =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          have hpw : 0 < 2 ^ w := Nat.two_pow_pos w
          have hsplit : 2 ^ ((k + 1) * w) = 2 ^ w * 2 ^ (k * w) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
          have hlow : (x + 2 ^ w * packL w xs) / 2 ^ w = packL w xs := by
            rw [Nat.add_comm x (2 ^ w * packL w xs), Nat.mul_add_div hpw,
              Nat.div_eq_of_lt hx', Nat.add_zero]
          simp only [packL, List.getD_cons_succ, hsplit, ← Nat.div_div_eq_div_mul, hlow]
          exact ih xs (fun y hy => hx y (by simp [hy]))
/-- The `k`-th `w`-bit field of a packed word, extracted with `>>>` and `&&&`. -/
theorem extract_field (w : ℕ) (hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w) (k : ℕ) :
    (packL w l >>> (k * w)) &&& (2 ^ w - 1) = l.getD k 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact extract_field_div w hw l hx k
/-- Field extraction in the form used by the sketches: a word whose `j`-th `w`-bit field is
`f j` yields `f k` by shifting and masking. -/
theorem extract_field_sum (w K : ℕ) (hw : 0 < w) (f : Fin K → ℕ) (hf : ∀ j, f j < 2 ^ w)
    (k : Fin K) :
    ((∑ j : Fin K, f j * 2 ^ (j.val * w)) >>> (k.val * w)) &&& (2 ^ w - 1) = f k := by
  rw [← packL_ofFn w K f]
  rw [extract_field w hw (List.ofFn f) ?_ k.val]
  · have hk : k.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact k.isLt
    rw [List.getD_eq_getElem (List.ofFn f) 0 hk]
    simp [List.getElem_ofFn]
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hf j
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
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
theorem At.self (P : Program) : At P 0 P := by
  intro r _
  simp
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
/-- The un-bitmasked count-parity row of check `(s,y)`. -/
def cr23ParRow (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t)) : Cr23Row N t :=
  ((s, y), ⟨cr23Lb N, Nat.lt_succ_self _⟩)
/-- The bitmasked row of check `(s,y)` for label bit `k`. -/
def cr23BitRow (N t : ℕ) (s : Fin (cr23D N)) (y : Fin (cr23M t)) (k : Fin (cr23Lb N)) :
    Cr23Row N t :=
  ((s, y), ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
/-- The support of a vector, as the statement counts it. -/
def cr23Supp {N : ℕ} (x : Fin N → ZMod 2) : Finset (Fin N) := univ.filter (fun i => x i = 1)
theorem cr23_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h2 := ZMod.val_lt a
  have h : ((ZMod.val a : ℕ) : ZMod 2) = a := ZMod.natCast_zmod_val a
  rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h0 | h1
  · left; rw [← h, Nat.lt_one_iff.mp h0]; simp
  · right; rw [← h, h1]; norm_num
theorem cr23_zmod2_eq_zero {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  rcases cr23_zmod2_cases a with h0 | h1
  · exact h0
  · exact absurd h1 h
/-- The sketch at a row triple is `∑_v CR_{((s,y),k),v}·x_v`, i.e. the parity check. -/
theorem cr23Sketch_apply (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (q : Cr23Row N t) :
    cr23Sketch N t C x (cr23RowEquiv N t q) = ∑ v : Fin N, cr23Entry N t C q v * x v := by
  simp only [cr23Sketch, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, cr23Matrix,
    Equiv.symm_apply_apply]
/-- On the support of `x` the check is a plain sum of entries, because `x_v = 1` exactly there. -/
theorem cr23Sketch_apply_supp (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (q : Cr23Row N t) :
    cr23Sketch N t C x (cr23RowEquiv N t q) = ∑ v ∈ cr23Supp x, cr23Entry N t C q v := by
  rw [cr23Sketch_apply]
  have h1 : (∑ v ∈ cr23Supp x, cr23Entry N t C q v * x v)
      = ∑ v : Fin N, cr23Entry N t C q v * x v := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro v _ hv
    have hne : x v ≠ 1 := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    rw [cr23_zmod2_eq_zero hne, mul_zero]
  rw [← h1]
  refine Finset.sum_congr rfl ?_
  intro v hv
  rw [(Finset.mem_filter.mp hv).2, mul_one]
/-- The un-bitmasked row of a check is the indicator of its bucket. -/
theorem cr23Entry_par (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (s : Fin (cr23D N)) (y : Fin (cr23M t)) (v : Fin N) :
    cr23Entry N t C (cr23ParRow N t s y) v = if C v s = y then 1 else 0 := by
  simp [cr23Entry, cr23ParRow]
/-- **The count parity of a bucket**: the un-bitmasked row of check `(s,y)` is the parity of the
number of active coordinates in that bucket (CR23 §1.2, the stacked matrix). -/
theorem cr23Sketch_parity (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (y : Fin (cr23M t)) :
    cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s y)) =
      (((cr23Supp x).filter (fun v => C v s = y)).card : ZMod 2) := by
  rw [cr23Sketch_apply_supp]
  have h1 : ∀ v ∈ cr23Supp x,
      cr23Entry N t C (cr23ParRow N t s y) v = if C v s = y then 1 else 0 :=
    fun v _ => cr23Entry_par N t C s y v
  rw [Finset.sum_congr rfl h1, Finset.sum_boole]
/-- The bitmasked row of a check is the indicator of "in the bucket *and* label bit `k` set". -/
theorem cr23Entry_bit (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (s : Fin (cr23D N)) (y : Fin (cr23M t)) (k : Fin (cr23Lb N)) (v : Fin N) :
    cr23Entry N t C (cr23BitRow N t s y k) v
      = if C v s = y then (if (v.val / 2 ^ k.val) % 2 = 1 then 1 else 0) else 0 := by
  unfold cr23Entry cr23BitRow
  simp only [Fin.val_mk]
  rw [if_neg (Nat.ne_of_lt k.isLt)]
/-- **The label XOR of a bucket, bit by bit** (CR23 §1.2): the bitmasked row `(s,y,k)` is the
parity of the number of active coordinates of the bucket whose `k`-th label bit is set.  So a
decoder that reads all `log N` bitmasked rows of a check reconstructs
`∑_k bit_k · 2^k =` the XOR of the labels of the bucket's active coordinates; if the bucket holds
exactly one active coordinate `v` this is `v` itself (because `v < 2^(log N)`). -/
theorem cr23Sketch_bit (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (y : Fin (cr23M t)) (k : Fin (cr23Lb N)) :
    cr23Sketch N t C x (cr23RowEquiv N t (cr23BitRow N t s y k))
      = ((((cr23Supp x).filter
          (fun v => C v s = y ∧ (v.val / 2 ^ k.val) % 2 = 1)).card : ℕ) : ZMod 2) := by
  rw [cr23Sketch_apply_supp]
  have h1 : ∀ v ∈ cr23Supp x, cr23Entry N t C (cr23BitRow N t s y k) v
      = if (C v s = y ∧ (v.val / 2 ^ k.val) % 2 = 1) then 1 else 0 := by
    intro v _
    rw [cr23Entry_bit]
    by_cases hc : C v s = y
    · by_cases hb : (v.val / 2 ^ k.val) % 2 = 1
      · simp [hc, hb]
      · simp [hc, hb]
    · simp [hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_boole]
/-- The buckets of seed `s` that hold exactly one element of `S`. -/
def cr23Alone {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) : ℕ :=
  ((S.image (fun v => C v s)).filter (fun y => (S.filter (fun v => C v s = y)).card = 1)).card
/-- **CR23 Lemma 4, integer form.**  If at most `τ` buckets of seed `s` are hit by `S`, at least
`|S| - τ` elements of `S` are alone in their bucket — equivalently
`2·|Γ_s(S)| ≤ |S| + (number of singleton buckets)`.  With `|Γ_s(S)| ≥ (1-δ)|S|` this gives
`(1-2δ)|S|` singleton buckets, which is the quantity the peeling decoder of CR23 §4.1.1 consumes.
(The paper states it with `δ`; this integer form needs no division and no positivity side
conditions.) -/
theorem cr23_alone_bound {N t : ℕ} (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (S : Finset (Fin N)) (s : Fin (cr23D N)) :
    2 * cr23Neigh C S s ≤ S.card + cr23Alone C S s := by
  set g : Fin N → Fin (cr23M t) := fun v => C v s with hg
  set T := S.image g with hT
  set A := T.filter (fun y => (S.filter (fun v => g v = y)).card = 1) with hA
  set B := T.filter (fun y => ¬ (S.filter (fun v => g v = y)).card = 1) with hB
  have hcov : ∀ v ∈ S, g v ∈ T := fun v hv => Finset.mem_image_of_mem g hv
  have hfib : S.card = ∑ y ∈ T, (S.filter (fun v => g v = y)).card :=
    Finset.card_eq_sum_card_fiberwise hcov
  have hsplit : (∑ y ∈ A, (S.filter (fun v => g v = y)).card)
      + (∑ y ∈ B, (S.filter (fun v => g v = y)).card) = S.card := by
    rw [hfib]
    exact Finset.sum_filter_add_sum_filter_not (s := T)
      (p := fun y => (S.filter (fun v => g v = y)).card = 1)
      (f := fun y => (S.filter (fun v => g v = y)).card)
  have hAsum : (∑ y ∈ A, (S.filter (fun v => g v = y)).card) = A.card := by
    have hone : ∀ y ∈ A, (S.filter (fun v => g v = y)).card = 1 :=
      fun y hy => (Finset.mem_filter.mp hy).2
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, Nat.mul_one]
  have hBsum : 2 * B.card ≤ ∑ y ∈ B, (S.filter (fun v => g v = y)).card := by
    have h2 : ∀ y ∈ B, 2 ≤ (S.filter (fun v => g v = y)).card := by
      intro y hy
      have hyT : y ∈ T := (Finset.mem_filter.mp hy).1
      have hne : (S.filter (fun v => g v = y)).card ≠ 1 := (Finset.mem_filter.mp hy).2
      have hpos : 0 < (S.filter (fun v => g v = y)).card := by
        rw [Finset.card_pos]
        obtain ⟨v, hvS, hvy⟩ := Finset.mem_image.mp hyT
        exact ⟨v, Finset.mem_filter.mpr ⟨hvS, hvy⟩⟩
      omega
    calc 2 * B.card = ∑ y ∈ B, 2 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ y ∈ B, (S.filter (fun v => g v = y)).card := Finset.sum_le_sum h2
  have hAB : A.card + B.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T)
      (p := fun y => (S.filter (fun v => g v = y)).card = 1)
  have hneigh : cr23Neigh C S s = T.card := rfl
  have halone : cr23Alone C S s = A.card := rfl
  omega
/-- Column `v` of the sketch is what an update XORs in. -/
theorem cr23Sketch_single (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (v : Fin N) :
    cr23Sketch N t C (Pi.single v 1) = fun p => cr23Matrix N t C p v := by
  funext p
  simp [cr23Sketch]
/-- `N ≤ 2^(log N)`. -/
theorem cr23_le_pow_lb (N : ℕ) : N ≤ 2 ^ cr23Lb N := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) (N + 1)
  simp only [cr23Lb]
  omega
/-- The row count is `2^78·t·log(N+1)·(log(N+1)+1)`. -/
theorem cr23R_eq (N t : ℕ) :
    cr23R N t = 2 ^ 78 * (t * cr23Lb N * (cr23Lb N + 1)) := by
  simp only [cr23R, cr23D, cr23M]
  rw [show (2 : ℕ) ^ 78 = 1024 * 2 ^ 68 by norm_num]
  ring
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
theorem cr23N_lt_word (N : ℕ) (hN : 1 ≤ N) : N < 2 ^ cr23Word N := by
  apply cr23_lt_word N hN
  calc N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := by
        apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
        omega
theorem cr23_one_lt_word (N : ℕ) (hN : 1 ≤ N) : 1 < 2 ^ cr23Word N := by
  have h := cr23D_lt_word N hN
  have h1 : 0 < cr23D N := cr23D_pos N hN
  omega
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
theorem cr23Addr_lt (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : Fin (cr23D N)) (v : Fin N) :
    cr23Addr N t C s v < 2 ^ cr23Word N := by
  have hDM : cr23M t * cr23D N ≤ 2 ^ (3 * cr23Lb N + 78) := by
    have ht : t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
    have hl : cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
    calc cr23M t * cr23D N = 2 ^ 78 * (cr23Lb N * t) := by
          show 2 ^ 68 * t * (1024 * cr23Lb N) = 2 ^ 78 * (cr23Lb N * t)
          rw [show (2 : ℕ) ^ 78 = 1024 * 2 ^ 68 by norm_num]
          ring
      _ ≤ 2 ^ 78 * (2 ^ cr23Lb N * 2 ^ cr23Lb N) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hl ht)
      _ = 2 ^ (2 * cr23Lb N + 78) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ 2 ^ (3 * cr23Lb N + 78) := by
          apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
          omega
  have h1 : cr23Addr N t C s v ≤ cr23Check N t s (C v s) := Nat.div_le_self _ _
  have h2 : cr23Check N t s (C v s) < cr23M t * cr23D N := cr23Check_lt N t s _
  have hW : 2 ^ (3 * cr23Lb N + 78) < 2 ^ cr23Word N := by
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    have hlb := cr23_one_le_lb N hN
    simp only [cr23Word]
    omega
  exact lt_of_le_of_lt (le_trans (le_trans h1 (le_of_lt h2)) hDM) hW
/-- The loop invariant of `progUp`, with `m` seeds still to do: the registers hold the seed count,
both record pointers, the end pointer and the countdown, and the payload holds the column of `v`
for the seeds already processed. -/
def UpData (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (s : RAMState) : Prop :=
  s.regs r0 = v.val ∧ s.regs r3 = cr23D N ∧ s.regs r5 = upBase N v.val ∧ s.regs r6 = m ∧
    s.regs r7 = upBase N v.val + 2 * (cr23D N - m) ∧
    s.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - m) ∧
    s.regs r11 = upBase N v.val + 2 * cr23D N ∧ s.regs r12 = 2 ∧ s.regs r13 = 1 ∧
    ∀ addr, s.mem addr = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - m) v) addr
theorem UpData.irrel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ)
    (s s' : RAMState) (hr : s.regs = s'.regs) (hm : s.mem = s'.mem) (h : UpData N t C y v m s) :
    UpData N t C y v m s' := by
  rcases h with ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact h0
  · rw [← hr]; exact h3
  · rw [← hr]; exact h5
  · rw [← hr]; exact h6
  · rw [← hr]; exact h7
  · rw [← hr]; exact h10
  · rw [← hr]; exact h11
  · rw [← hr]; exact h12
  · rw [← hr]; exact h13
  · intro addr; rw [← hm]; exact hmem addr
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
end
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
/-- **The binary expansion.**  For `m < 2^n` the sum of the bits of `m` below position `n` is `m`.
With `n = cr23Lb N` this says that the `log N` bitmasked rows of a check reconstruct its label. -/
theorem cr23_sum_bits_lt : ∀ (n m : ℕ), m < 2 ^ n →
    (∑ k ∈ Finset.range n, (m / 2 ^ k % 2) * 2 ^ k) = m := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have h0 : m = 0 := by omega
      simp [h0]
  | succ n ih =>
      intro m hm
      have hdiv : m / 2 < 2 ^ n := by
        have h1 : 2 * (m / 2) + m % 2 = m := Nat.div_add_mod m 2
        have h2 : m % 2 < 2 := Nat.mod_lt m (by norm_num)
        have h3 : m < 2 ^ n * 2 := by
          rw [← pow_succ]
          exact hm
        omega
      have hsplit : (∑ k ∈ Finset.range (n + 1), (m / 2 ^ k % 2) * 2 ^ k)
          = (∑ k ∈ Finset.range n, ((m / 2) / 2 ^ k % 2) * 2 ^ k) * 2 + m % 2 := by
        rw [Finset.sum_range_succ']
        have hstep : ∀ k ∈ Finset.range n,
            (m / 2 ^ (k + 1) % 2) * 2 ^ (k + 1)
              = ((m / 2) / 2 ^ k % 2) * 2 ^ k * 2 := by
          intro k _
          have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ] <;> ring
          have h2 : m / 2 ^ (k + 1) = m / 2 / 2 ^ k := by
            rw [h1, Nat.div_div_eq_div_mul]
          rw [h2, h1]
          ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_mul]
        simp
      rw [hsplit, ih (m / 2) hdiv]
      have h2 : 2 * (m / 2) + m % 2 = m := Nat.div_add_mod m 2
      omega
/-- The buckets of seed `s` that `S` occupies. -/
def cr23Occ {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) :
    Finset (Fin M) := S.image (fun v => C v s)
/-- The load of bucket `b` of seed `s`: the number of elements of `S` whose bucket is `b`. -/
def cr23Ld {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D)
    (b : Fin M) : ℕ := (S.filter (fun v => C v s = b)).card
/-- The buckets of seed `s` holding an *odd* number of elements of `S`. -/
def cr23OddB {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) :
    Finset (Fin M) := (cr23Occ C S s).filter (fun b => Odd (cr23Ld C S s b))
/-- The elements of `S` that sit alone in their bucket. -/
def cr23AloneS {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) :
    Finset (Fin N) := S.filter (fun v => (S.filter (fun u => C u s = C v s)).card = 1)
/-- The loads of the occupied buckets sum to `|S|`. -/
theorem cr23_fiber_sum {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) :
    S.card = ∑ b ∈ cr23Occ C S s, cr23Ld C S s b :=
  Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_image_of_mem (fun v => C v s) hv)
theorem cr23OddB_subset {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N))
    (s : Fin D) : cr23OddB C S s ⊆ cr23Occ C S s := Finset.filter_subset _ _
/-- **At most `|S|` buckets are odd.** -/
theorem cr23OddB_card_le {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N))
    (s : Fin D) : (cr23OddB C S s).card ≤ S.card := by
  have h1 : (cr23OddB C S s).card ≤ (cr23Occ C S s).card :=
    Finset.card_le_card (cr23OddB_subset C S s)
  have h2 : (cr23Occ C S s).card ≤ S.card := Finset.card_image_le
  omega
/-- The alone elements and the singleton buckets are equinumerous: `v ↦ C v s` is a bijection
between them. -/
theorem cr23AloneS_image {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N))
    (s : Fin D) :
    (cr23AloneS C S s).image (fun v => C v s)
      = (cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1) := by
  ext b
  constructor
  · intro hv
    obtain ⟨v, hv', hvb⟩ := Finset.mem_image.mp hv
    have hvS : v ∈ S := (Finset.mem_filter.mp hv').1
    have h1 : (S.filter (fun u => C u s = C v s)).card = 1 := (Finset.mem_filter.mp hv').2
    subst hvb
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hvS, h1⟩
  · intro hb
    obtain ⟨hbT, h1⟩ := Finset.mem_filter.mp hb
    obtain ⟨v, hvS, hvb⟩ := Finset.mem_image.mp hbT
    refine Finset.mem_image.mpr ⟨v, ?_, hvb⟩
    exact Finset.mem_filter.mpr ⟨hvS, by rw [hvb]; exact h1⟩
/-- **`cr23Alone` counts the alone elements.** -/
theorem cr23Alone_eq {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) :
    cr23Alone C S s = (cr23AloneS C S s).card := by
  have hinj : ∀ v ∈ cr23AloneS C S s, ∀ u ∈ cr23AloneS C S s, C v s = C u s → v = u := by
    intro v hv u hu hvu
    have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
    have huS : u ∈ S := (Finset.mem_filter.mp hu).1
    have h1 : (S.filter (fun w => C w s = C v s)).card = 1 := (Finset.mem_filter.mp hv).2
    have hvmem : v ∈ S.filter (fun w => C w s = C v s) := Finset.mem_filter.mpr ⟨hvS, rfl⟩
    have humem : u ∈ S.filter (fun w => C w s = C v s) :=
      Finset.mem_filter.mpr ⟨huS, hvu.symm⟩
    exact (Finset.card_le_one.mp (le_of_eq h1)) v hvmem u humem
  have hcard : (cr23AloneS C S s).card
      = ((cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1)).card := by
    rw [← cr23AloneS_image C S s]
    exact (Finset.card_image_of_injOn hinj).symm
  have h1 : cr23Alone C S s
      = ((cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1)).card := rfl
  omega
/-- **`3·#odd ≤ 2·alone + |S|`.**  A bucket of odd load that is not a singleton holds at least
three elements of `S`; hence the elements of `S` in odd buckets, `3·#odd − 2·alone` of them at
least, are at most all of `S`. -/
theorem cr23_alone_odd {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N))
    (s : Fin D) : 3 * (cr23OddB C S s).card ≤ 2 * cr23Alone C S s + S.card := by
  classical
  have hTA : (cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1)
      = (cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1) := by
    ext b
    simp only [Finset.mem_filter, cr23OddB]
    constructor
    · rintro ⟨hbT, hb1⟩
      exact ⟨⟨hbT, by rw [hb1]; exact odd_one⟩, hb1⟩
    · rintro ⟨⟨hbT, -⟩, hb1⟩
      exact ⟨hbT, hb1⟩
  have hAcard : cr23Alone C S s
      = ((cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1)).card := by
    have h1 : cr23Alone C S s
        = ((cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1)).card := rfl
    rw [h1, hTA]
  have hsplit : ((cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1)).card
        + ((cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1)).card
      = (cr23OddB C S s).card :=
    Finset.card_filter_add_card_filter_not (s := cr23OddB C S s)
      (p := fun b => cr23Ld C S s b = 1)
  have hsum_split : (∑ b ∈ (cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1),
        cr23Ld C S s b)
        + (∑ b ∈ (cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1),
            cr23Ld C S s b)
      = ∑ b ∈ cr23OddB C S s, cr23Ld C S s b :=
    Finset.sum_filter_add_sum_filter_not (s := cr23OddB C S s)
      (p := fun b => cr23Ld C S s b = 1) (f := fun b => cr23Ld C S s b)
  have hsumO : ∑ b ∈ cr23OddB C S s, cr23Ld C S s b ≤ S.card := by
    rw [cr23_fiber_sum C S s]
    exact Finset.sum_le_sum_of_subset_of_nonneg (cr23OddB_subset C S s)
      (fun b _ _ => Nat.zero_le _)
  have hone : (∑ b ∈ (cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1), cr23Ld C S s b)
      = ((cr23OddB C S s).filter (fun b => cr23Ld C S s b = 1)).card := by
    rw [Finset.sum_congr rfl (fun b hb => (Finset.mem_filter.mp hb).2), Finset.sum_const,
      smul_eq_mul, Nat.mul_one]
  have hthree : 3 * ((cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1)).card
      ≤ ∑ b ∈ (cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1), cr23Ld C S s b := by
    have h3 : ∀ b ∈ (cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1),
        3 ≤ cr23Ld C S s b := by
      intro b hb
      obtain ⟨hbO, hbne⟩ := Finset.mem_filter.mp hb
      have hodd : Odd (cr23Ld C S s b) := (Finset.mem_filter.mp hbO).2
      obtain ⟨c, hc⟩ := hodd
      omega
    calc 3 * ((cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1)).card
        = ∑ b ∈ (cr23OddB C S s).filter (fun b => ¬ cr23Ld C S s b = 1), 3 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum h3
  omega
variable {N' t' : ℕ}
/-- The label XOR of bucket `b` of seed `s`, as a number: bit `k` is the parity of the elements of
`S` in that bucket whose `k`-th label bit is set.  These are exactly the `log N` bitmasked rows of
the check `(s,b)` (`cr23Sketch_bit`), so the machine reads this number with `log N` field
extractions. -/
def cr23XorLbl (C : Fin N' → Fin (cr23D N') → Fin (cr23M t')) (S : Finset (Fin N'))
    (s : Fin (cr23D N')) (b : Fin (cr23M t')) : ℕ :=
  ∑ k ∈ Finset.range (cr23Lb N'),
    ((S.filter (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card % 2) * 2 ^ k
/-- **The candidate of seed `s`**: the labels of its odd buckets that name a coordinate.  Labels
`≥ N` are discarded — they cannot be in `S`, so discarding them only helps. -/
def cr23Cand (C : Fin N' → Fin (cr23D N') → Fin (cr23M t')) (S : Finset (Fin N'))
    (s : Fin (cr23D N')) : Finset (Fin N') :=
  univ.filter (fun v => v.val ∈ (cr23OddB C S s).image (fun b => cr23XorLbl C S s b))
/-- **A singleton bucket's label is its element.** -/
theorem cr23XorLbl_singleton (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (S : Finset (Fin N')) (s : Fin (cr23D N')) (b : Fin (cr23M t')) (v : Fin N')
    (hvS : v ∈ S) (hvb : C v s = b) (h1 : (S.filter (fun u => C u s = b)).card = 1) :
    cr23XorLbl C S s b = v.val := by
  have hfib : S.filter (fun u => C u s = b) = {v} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hvS, hvb⟩, ?_⟩
    intro u hu
    exact (Finset.card_le_one.mp (le_of_eq h1)) u hu v (Finset.mem_filter.mpr ⟨hvS, hvb⟩)
  have hterm : ∀ k ∈ Finset.range (cr23Lb N'),
      ((S.filter (fun u => C u s = b ∧ u.val / 2 ^ k % 2 = 1)).card % 2)
        = v.val / 2 ^ k % 2 := by
    intro k _
    have hff : S.filter (fun u => C u s = b ∧ u.val / 2 ^ k % 2 = 1)
        = ({v} : Finset (Fin N')).filter (fun u => u.val / 2 ^ k % 2 = 1) := by
      rw [← Finset.filter_filter, hfib]
    rw [hff, Finset.filter_singleton]
    by_cases hb : v.val / 2 ^ k % 2 = 1
    · rw [if_pos hb]
      simp [hb]
    · have hb0 : v.val / 2 ^ k % 2 = 0 := by
        have := Nat.mod_lt (v.val / 2 ^ k) (by norm_num : 0 < 2)
        omega
      rw [if_neg hb]
      simp [hb0]
  simp only [cr23XorLbl]
  rw [← cr23_sum_bits_lt (cr23Lb N') v.val (lt_of_lt_of_le v.isLt (cr23_le_pow_lb N'))]
  exact Finset.sum_congr rfl (fun k hk => by rw [hterm k hk])
/-- Singleton buckets are odd, so there are at most as many lone elements as odd buckets. -/
theorem cr23Alone_le_odd (C : Fin N' → Fin (cr23D N') → Fin (cr23M t')) (S : Finset (Fin N'))
    (s : Fin (cr23D N')) : cr23Alone C S s ≤ (cr23OddB C S s).card := by
  have h1 : cr23Alone C S s
      = ((cr23Occ C S s).filter (fun b => cr23Ld C S s b = 1)).card := rfl
  rw [h1]
  refine Finset.card_le_card ?_
  intro b hb
  obtain ⟨hbT, hb1⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hbT, by rw [hb1]; exact odd_one⟩
/-- **The candidate is no larger than the number of odd buckets.** -/
theorem cr23Cand_card_le_odd (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (S : Finset (Fin N')) (s : Fin (cr23D N')) :
    (cr23Cand C S s).card ≤ (cr23OddB C S s).card := by
  have hinj : ∀ a ∈ cr23Cand C S s, ∀ b ∈ cr23Cand C S s, a.val = b.val → a = b :=
    fun a _ b _ h => Fin.ext h
  have h3 : ((cr23Cand C S s).image (fun v => v.val)).card = (cr23Cand C S s).card :=
    Finset.card_image_of_injOn hinj
  have h2 : (cr23Cand C S s).image (fun v => v.val)
      ⊆ (cr23OddB C S s).image (fun b => cr23XorLbl C S s b) := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hv).2
  rw [← h3]
  exact le_trans (Finset.card_le_card h2) Finset.card_image_le
/-- **Every lone element is in the candidate.** -/
theorem cr23AloneS_subset_cand (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (S : Finset (Fin N')) (s : Fin (cr23D N')) : cr23AloneS C S s ⊆ cr23Cand C S s := by
  intro v hv
  have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
  have h1 : (S.filter (fun u => C u s = C v s)).card = 1 := (Finset.mem_filter.mp hv).2
  have hb : C v s ∈ cr23OddB C S s := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hvS, ?_⟩
    show Odd ((S.filter (fun u => C u s = C v s)).card)
    rw [h1]
    exact odd_one
  have hlbl : cr23XorLbl C S s (C v s) = v.val :=
    cr23XorLbl_singleton C S s (C v s) v hvS rfl h1
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
  rw [← hlbl]
  exact Finset.mem_image_of_mem _ hb
/-- **`|S ∩ candidate| ≥ alone`.** -/
theorem cr23_alone_le_cand (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (S : Finset (Fin N')) (s : Fin (cr23D N')) :
    cr23Alone C S s ≤ (S ∩ cr23Cand C S s).card := by
  have h1 : cr23Alone C S s = (cr23AloneS C S s).card := cr23Alone_eq C S s
  rw [h1]
  refine Finset.card_le_card ?_
  intro v hv
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp hv).1, cr23AloneS_subset_cand C S s hv⟩
/-- **`|S Δ candidate| + 2·alone ≤ |S| + #odd`** for every seed. -/
theorem cr23Cand_diff_add (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (S : Finset (Fin N')) (s : Fin (cr23D N')) :
    ((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card + 2 * cr23Alone C S s
      ≤ S.card + (cr23OddB C S s).card := by
  have hdisj : Disjoint (S \ cr23Cand C S s) (cr23Cand C S s \ S) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hunion : ((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card
      = (S \ cr23Cand C S s).card + (cr23Cand C S s \ S).card :=
    Finset.card_union_of_disjoint hdisj
  have h1 : (S \ cr23Cand C S s).card + (S ∩ cr23Cand C S s).card = S.card :=
    Finset.card_sdiff_add_card_inter S (cr23Cand C S s)
  have h2 : (cr23Cand C S s \ S).card + (cr23Cand C S s ∩ S).card
      = (cr23Cand C S s).card :=
    Finset.card_sdiff_add_card_inter (cr23Cand C S s) S
  have h3 : (S ∩ cr23Cand C S s).card = (cr23Cand C S s ∩ S).card := by
    rw [Finset.inter_comm]
  have h4 : cr23Alone C S s ≤ (S ∩ cr23Cand C S s).card := cr23_alone_le_cand C S s
  have h5 : (cr23Cand C S s).card ≤ (cr23OddB C S s).card := cr23Cand_card_le_odd C S s
  omega
/-- **Oddness as a residue.**  `n`, read modulo `2`, is the indicator of `n % 2 = 1`. -/
theorem cr23_zmod2_ind (m : ℕ) :
    (if ((m : ZMod 2) = 1) then 1 else 0) = m % 2 := by
  have hv : ((m : ZMod 2)).val = m % 2 := ZMod.val_natCast 2 m
  by_cases h : ((m : ZMod 2)) = 1
  · rw [if_pos h, ← hv, h, ZMod.val_one 2]
  · rw [if_neg h, ← hv, cr23_zmod2_eq_zero h, ZMod.val_zero]
/-- A natural number is `1` in `ZMod 2` exactly when it is odd. -/
theorem cr23_zmod2_eq_one_iff (n : ℕ) : ((n : ZMod 2) = 1) ↔ Odd n := by
  have hmod : Odd n ↔ n % 2 = 1 := by
    constructor
    · rintro ⟨c, rfl⟩
      omega
    · intro h
      exact ⟨n / 2, by omega⟩
  rw [hmod]
  constructor
  · intro h
    rw [← cr23_zmod2_ind n, if_pos h]
  · intro h
    by_contra hne
    have h0 := cr23_zmod2_ind n
    rw [if_neg hne] at h0
    omega
/-- **The odd buckets are the buckets whose count-parity row is `1`.**  A bucket is odd for the
stored sketch exactly when its parity row reads `1`, so the decoder's parity pass over all `M`
buckets of a seed recovers `cr23OddB` without knowing `S`. -/
theorem cr23OddB_read (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) :
    (Finset.univ.filter (fun b : Fin (cr23M t) =>
        cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b)) = 1))
      = cr23OddB C (cr23Supp x) s := by
  classical
  ext b
  rw [Finset.mem_filter, cr23Sketch_parity, cr23OddB, Finset.mem_filter, cr23Occ,
    Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  rw [show cr23Ld C (cr23Supp x) s b
      = ((cr23Supp x).filter (fun v => C v s = b)).card from rfl]
  constructor
  · intro h1
    have hodd : Odd (((cr23Supp x).filter (fun v => C v s = b)).card) :=
      (cr23_zmod2_eq_one_iff _).mp h1
    refine ⟨?_, hodd⟩
    obtain ⟨c, hc⟩ := hodd
    have hpos : 0 < ((cr23Supp x).filter (fun v => C v s = b)).card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨-, hodd⟩
    exact (cr23_zmod2_eq_one_iff _).mpr hodd
/-- **The label XOR is what the `log N` bitmasked rows store.**  Reading the `j`-th bitmasked row
of a check for `j < log N` and multiplying by `2^j` accumulates exactly `cr23XorLbl`: no arithmetic
on labels is needed, only `log N` field extractions. -/
theorem cr23XorLbl_read (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23XorLbl C (cr23Supp x) s b =
      ∑ k : Fin (cr23Lb N),
        (if cr23Sketch N t C x (cr23RowEquiv N t (cr23BitRow N t s b k)) = 1 then 1 else 0)
          * 2 ^ k.val := by
  classical
  rw [cr23XorLbl]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => ((cr23Supp x).filter
      (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card % 2 * 2 ^ k) (cr23Lb N)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cr23Sketch_bit, cr23_zmod2_ind]
/-- The payload `y` read as a function of the bit position, with `0` outside the payload. -/
def payloadAt {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : ZMod 2 :=
  if h : p < M then y ⟨p, h⟩ else 0
/-- Bit `p` of the payload `y`, as a natural number. -/
def payloadBit {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : ℕ := (payloadAt y p).val
theorem payloadBit_lt_two {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p < 2 :=
  ZMod.val_lt _
theorem payloadBit_le_one {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p ≤ 1 := by
  have h := payloadBit_lt_two y p
  omega
/-- In `ZMod 2` the value of an element is `1` exactly at `1`. -/
theorem zmod2_val (z : ZMod 2) : z.val = if z = 1 then 1 else 0 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h z with h | h
  · rw [h]; decide
  · rw [h]; decide
/-- Adding one payload bit at the end only changes the bit at position `M`. -/
theorem payloadBit_succ {M : ℕ} (y : Fin (M + 1) → ZMod 2) (p : ℕ) :
    payloadBit y p =
      payloadBit (fun i : Fin M => y i.castSucc) p +
        (if p = M then (if y (Fin.last M) = 1 then 1 else 0) else 0) := by
  have hlast : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) = Fin.last M := Fin.ext rfl
  unfold payloadBit payloadAt
  by_cases h : p < M
  · rw [dif_pos h, dif_pos (Nat.lt_succ_of_lt h), if_neg (by omega)]
    simp
  · by_cases h2 : p = M
    · rw [h2, dif_pos (Nat.lt_succ_self M), if_pos rfl, hlast]
      simp [zmod2_val]
    · rw [dif_neg (by omega : ¬ p < M + 1), dif_neg (by omega : ¬ p < M), if_neg h2]
      simp
/-- Peeling the last payload bit off the word that holds it. -/
theorem packMem_succ {W M : ℕ} (y : Fin (M + 1) → ZMod 2) (addr : ℕ) :
    packMem W y addr =
      packMem W (fun i : Fin M => y i.castSucc) addr +
        (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
  have hsplit := Fin.sum_univ_castSucc
    (f := fun p : Fin (M + 1) =>
      (if p.val / W = addr ∧ y p = 1 then 2 ^ (p.val % W) else 0))
  simp only [packMem]
  rw [hsplit]
  simp only [Fin.val_castSucc, Fin.val_last]
/-- The bit position inside a word determines the word index. -/
theorem div_eq_of_mul_add {W M c b : ℕ} (hW : 0 < W) (hb : b < W) (h : c * W + b = M) :
    M / W = c := by
  rw [← h, Nat.mul_comm c W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
/-- The word `addr` contributes to exactly one bit position, namely `M % W` when `M / W = addr`. -/
theorem sum_range_ite_bit {W M addr v : ℕ} (hW : 0 < W) :
    (∑ b ∈ Finset.range W, (if addr * W + b = M then v else 0) * 2 ^ b)
      = if M / W = addr then v * 2 ^ (M % W) else 0 := by
  by_cases h : M / W = addr
  · have hsingle : addr * W + M % W = M := by
      have h0 := Nat.div_add_mod M W
      rw [h] at h0
      rw [Nat.mul_comm W addr] at h0
      exact h0
    rw [if_pos h,
      Finset.sum_eq_single (M % W)
        (fun b _ hne => by
          rw [if_neg (by intro he; exact hne (by omega))]
          simp)
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.mod_lt M hW)) hmem),
      if_pos hsingle]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [Finset.mem_range] at hb
    rw [if_neg (by intro he; exact h (div_eq_of_mul_add hW hb he))]
    simp
/-- **The packed-word layout**: a packed word is the sum of its payload bits, weighted by
position. -/
theorem packMem_eq_sum_bits {W : ℕ} (hW : 0 < W) :
    ∀ (M : ℕ) (y : Fin M → ZMod 2) (addr : ℕ),
      packMem W y addr = ∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b := by
  intro M
  induction M with
  | zero => intro y addr; simp [packMem, payloadBit, payloadAt]
  | succ M ih =>
      intro y addr
      have hstep :
          (∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b)
            = (∑ b ∈ Finset.range W,
                payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b)
              + (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
        have hpt : ∀ b ∈ Finset.range W,
            payloadBit y (addr * W + b) * 2 ^ b
              = payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b
                + (if addr * W + b = M then (if y (Fin.last M) = 1 then 1 else 0) else 0)
                    * 2 ^ b := by
          intro b _
          rw [payloadBit_succ, Nat.add_mul]
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, sum_range_ite_bit hW]
        congr 1
        by_cases h1 : M / W = addr <;> by_cases h2 : y (Fin.last M) = 1 <;> simp [h1, h2]
      rw [packMem_succ y addr, ih (fun i : Fin M => y i.castSucc) addr, hstep]
theorem sum_range_two_pow_lt (w : ℕ) : (∑ k ∈ Finset.range w, 2 ^ k) < 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ, Nat.pow_succ]
      omega
/-- A `w`-bit field built from payload bits is a `w`-bit number. -/
theorem bits_sum_lt_two_pow {w M : ℕ} (y : Fin M → ZMod 2) (c : ℕ) :
    (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k) < 2 ^ w := by
  have h1 : (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k)
      ≤ ∑ k ∈ Finset.range w, 2 ^ k := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc payloadBit y (c + k) * 2 ^ k ≤ 1 * 2 ^ k :=
          Nat.mul_le_mul_right _ (payloadBit_le_one y (c + k))
      _ = 2 ^ k := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt w)
/-- Splitting the bits of `n` words of `w` bits into `n` fields of `w` bits. -/
theorem sum_range_bits_split (w n : ℕ) (f : ℕ → ℕ) :
    (∑ b ∈ Finset.range (n * w), f b * 2 ^ b)
      = ∑ i ∈ Finset.range n,
          (∑ k ∈ Finset.range w, f (i * w + k) * 2 ^ k) * 2 ^ (i * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.pow_add]
      ring
/-- **Extraction of the `i`-th `w`-bit field of a packed word**, for a word of `m * w` bits. -/
theorem packMem_field_mul {w m : ℕ} (hw : 0 < w) (hm : 0 < m) (M : ℕ) (y : Fin M → ZMod 2)
    (addr : ℕ) (i : Fin m) :
    packMem (m * w) y addr / 2 ^ (i.val * w) % 2 ^ w
      = ∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + i.val * w + k) * 2 ^ k := by
  have hmw : 0 < m * w := Nat.mul_pos hm hw
  have hpack : packMem (m * w) y addr
      = ∑ j : Fin m,
          (∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + j.val * w + k) * 2 ^ k)
            * 2 ^ (j.val * w) := by
    rw [packMem_eq_sum_bits hmw,
      sum_range_bits_split w m (fun b => payloadBit y (addr * (m * w) + b))]
    simp only [Nat.add_assoc]
    exact (Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range w,
      payloadBit y (addr * (m * w) + (j * w + k)) * 2 ^ k) * 2 ^ (j * w)) m).symm
  rw [hpack, ← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  exact extract_field_sum w m hw _ (fun j => bits_sum_lt_two_pow y _) i
/-- The `lb+1` bits of check `q`, read as one integer. -/
noncomputable def cr23CheckField (N t : ℕ) (y : Fin (cr23R N t) → ZMod 2) (q : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (cr23Lb N + 1), payloadBit y (q * (cr23Lb N + 1) + k) * 2 ^ k
/-- The check index of a seed and bucket is below `D·M`. -/
theorem cr23DecCheck_lt (N t : ℕ) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23Check N t s b < cr23D N * cr23M t := by
  have hs : s.val < cr23D N := s.isLt
  have hb : b.val < cr23M t := b.isLt
  have h : b.val + cr23M t * s.val < cr23M t + cr23M t * s.val := Nat.add_lt_add_right hb _
  have h2 : cr23M t + cr23M t * s.val = cr23M t * (s.val + 1) := by ring
  rw [cr23Check]
  calc b.val + cr23M t * s.val < cr23M t * (s.val + 1) := by rw [← h2]; exact h
    _ ≤ cr23M t * cr23D N := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hs)
    _ = cr23D N * cr23M t := Nat.mul_comm _ _
/-- **A check's `lb+1` bits are contiguous inside one word**: shifting the payload word at
`q / 1024` down by `(q % 1024) · (lb+1)` and masking with `2^(lb+1)-1` reads exactly check `q`. -/
theorem cr23CheckField_read (N t : ℕ) (y : Fin (cr23R N t) → ZMod 2) (q : ℕ)
    (hq : q < cr23D N * cr23M t) :
    (packMem (cr23Word N) y (q / 1024)
        / 2 ^ ((q % 1024) * (cr23Lb N + 1))) % 2 ^ (cr23Lb N + 1)
      = cr23CheckField N t y q := by
  have hw : 0 < cr23Lb N + 1 := Nat.succ_pos _
  have hq1024 : q % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  rw [cr23Word]
  rw [packMem_field_mul hw (by norm_num : 0 < 1024) (cr23R N t) y (q / 1024)
    ⟨q % 1024, hq1024⟩]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hq1 : q / 1024 * 1024 + q % 1024 = q := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod q 1024
  have hsplit : (q / 1024) * (1024 * (cr23Lb N + 1)) + (q % 1024) * (cr23Lb N + 1) + k
      = q * (cr23Lb N + 1) + k := by
    calc (q / 1024) * (1024 * (cr23Lb N + 1)) + (q % 1024) * (cr23Lb N + 1) + k
        = ((q / 1024) * 1024 + q % 1024) * (cr23Lb N + 1) + k := by ring
      _ = q * (cr23Lb N + 1) + k := by rw [hq1]
  rw [hsplit]
/-- The read integer is the sum over the rows of the check. -/
theorem cr23CheckField_eq (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23CheckField N t (cr23Sketch N t C x) (cr23Check N t s b)
      = ∑ k : Fin (cr23Lb N + 1),
          (cr23Sketch N t C x (cr23RowEquiv N t ((s, b), k))).val * 2 ^ k.val := by
  classical
  rw [cr23CheckField, ← Fin.sum_univ_eq_sum_range
    (fun k => payloadBit (cr23Sketch N t C x) (cr23Check N t s b * (cr23Lb N + 1) + k) * 2 ^ k)
    (cr23Lb N + 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : k < cr23Lb N + 1 := k.isLt
  have hq := cr23DecCheck_lt N t s b
  have hlt : cr23Check N t s b * (cr23Lb N + 1) + k < cr23R N t := by
    rw [cr23R]
    have h1 : cr23Check N t s b * (cr23Lb N + 1) + k
        < cr23Check N t s b * (cr23Lb N + 1) + (cr23Lb N + 1) := Nat.add_lt_add_left hk _
    have h2 : cr23Check N t s b * (cr23Lb N + 1) + (cr23Lb N + 1)
        = (cr23Check N t s b + 1) * (cr23Lb N + 1) := by ring
    calc cr23Check N t s b * (cr23Lb N + 1) + k
        < (cr23Check N t s b + 1) * (cr23Lb N + 1) := by rw [← h2]; exact h1
      _ ≤ (cr23D N * cr23M t) * (cr23Lb N + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hq)
  have hfin : (⟨cr23Check N t s b * (cr23Lb N + 1) + k, hlt⟩ : Fin (cr23R N t))
      = cr23RowEquiv N t ((s, b), ⟨k, hk⟩) := by
    refine Fin.ext ?_
    rw [cr23RowEquiv_val]
    ring
  have hbit : payloadBit (cr23Sketch N t C x)
      (cr23Check N t s b * (cr23Lb N + 1) + k) = (cr23Sketch N t C x
        (cr23RowEquiv N t ((s, b), ⟨k, hk⟩))).val := by
    unfold payloadBit payloadAt
    rw [dif_pos hlt, hfin]
  rw [hbit]
/-- The label XOR of a bucket is below `2^lb`. -/
theorem cr23XorLbl_lt (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (S : Finset (Fin N)) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23XorLbl C S s b < 2 ^ cr23Lb N := by
  unfold cr23XorLbl
  have h1 : (∑ k ∈ Finset.range (cr23Lb N),
      ((S.filter (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card % 2) * 2 ^ k)
      ≤ ∑ k ∈ Finset.range (cr23Lb N), 2 ^ k := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hm : ((S.filter (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card % 2) ≤ 1 := by
      have h := Nat.mod_lt (S.filter (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card
        (by norm_num : 0 < 2)
      omega
    calc ((S.filter (fun v => C v s = b ∧ v.val / 2 ^ k % 2 = 1)).card % 2) * 2 ^ k
        ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ hm
      _ = 2 ^ k := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt _)
/-- **The machine's read of a check is the label XOR plus `2^lb` times the parity.** -/
theorem cr23CheckField_par_add (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23CheckField N t (cr23Sketch N t C x) (cr23Check N t s b)
      = cr23XorLbl C (cr23Supp x) s b
        + (cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b))).val * 2 ^ cr23Lb N := by
  classical
  rw [cr23CheckField_eq]
  rw [Fin.sum_univ_castSucc
    (f := fun k => (cr23Sketch N t C x (cr23RowEquiv N t ((s, b), k))).val * 2 ^ k.val)]
  have hlow : (∑ k : Fin (cr23Lb N),
      (cr23Sketch N t C x (cr23RowEquiv N t ((s, b), k.castSucc))).val * 2 ^ (k.castSucc).val)
      = cr23XorLbl C (cr23Supp x) s b := by
    rw [cr23XorLbl_read]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hrow : ((s, b), k.castSucc) = cr23BitRow N t s b k := rfl
    rw [hrow, zmod2_val]
    rfl
  have hlast : (cr23Sketch N t C x (cr23RowEquiv N t ((s, b), Fin.last (cr23Lb N)))).val
        * 2 ^ (Fin.last (cr23Lb N)).val
      = (cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b))).val * 2 ^ cr23Lb N := rfl
  rw [hlow, hlast]
/-- The low `lb` bits of the read are the label XOR. -/
theorem cr23CheckField_mod (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23CheckField N t (cr23Sketch N t C x) (cr23Check N t s b) % 2 ^ cr23Lb N
      = cr23XorLbl C (cr23Supp x) s b := by
  rw [cr23CheckField_par_add,
    Nat.mul_comm ((cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b))).val) (2 ^ cr23Lb N),
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (cr23XorLbl_lt N t C (cr23Supp x) s b)
/-- Bit `lb` of the read is the count parity. -/
theorem cr23CheckField_div (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    cr23CheckField N t (cr23Sketch N t C x) (cr23Check N t s b) / 2 ^ cr23Lb N % 2
      = (cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b))).val := by
  rw [cr23CheckField_par_add, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (cr23XorLbl_lt N t C (cr23Supp x) s b), Nat.zero_add,
    Nat.mod_eq_of_lt (ZMod.val_lt _)]
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
/-- **The bucket count** is the cell just past the graph block. -/
theorem cr23DecDet_M (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    cr23DecDet N t C (cr23DecBase N) = cr23M t := by
  simp [cr23DecDet]
/-- **The label width** is the cell after that. -/
theorem cr23DecDet_lb (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) :
    cr23DecDet N t C (cr23DecBase N + 1) = cr23Lb N := by
  simp [cr23DecDet]
/-- The first address of the decoder's frame. -/
def cr23DecFrame (N t : ℕ) : ℕ := cr23R N t + cr23Graph0 N + N * cr23D N + 2
/-- Offset `k` of the slot block, `k < 16`. -/
def decSlot (N t k : ℕ) : ℕ := cr23DecFrame N t + 1 + k
/-- The candidate list of the current round: at most `2t + 1` values. -/
def decCandBase (N t : ℕ) : ℕ := cr23DecFrame N t + 32
/-- The per-round tag array, indexed by the label value: `2^(lb+1)` cells. -/
def decTagBase (N t : ℕ) : ℕ := decCandBase N t + (2 * t + 1)
/-- The master list: every value ever put in a candidate, duplicate-free, at most `2t + 1` of them. -/
def decMstBase (N t : ℕ) : ℕ := decTagBase N t + 2 ^ (cr23Lb N + 1)
/-- The parity accumulator of the emitted set, indexed by the label value. -/
def decParBase (N t : ℕ) : ℕ := decMstBase N t + (2 * t + 1)
/-- The emitted list: at most `t + 1` values. -/
def decOutBase (N t : ℕ) : ℕ := decParBase N t + 2 ^ (cr23Lb N + 1)
/-- One past the last address of the frame. -/
def cr23DecEnd (N t : ℕ) : ℕ := decOutBase N t + (t + 1)
theorem cr23_pow_le_twenty (N : ℕ) {e : ℕ} (he : e ≤ 2 * cr23Lb N + 20) :
    2 ^ e ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) he
/-- Any number at most `2 ^ (3·lb + 26)` is a legal word. -/
theorem cr23_lt_word_frame (N : ℕ) (hN : 1 ≤ N) {j : ℕ} (hj : j ≤ 2 ^ (3 * cr23Lb N + 100)) :
    j < 2 ^ cr23Word N := by
  refine lt_of_le_of_lt hj (Nat.pow_lt_pow_right (by norm_num : 1 < 2) ?_)
  have h := cr23_one_le_lb N hN
  simp only [cr23Word]
  omega
/-- `R = D·M·(lb+1)` is at most `2^(3·lb+78)`. -/
theorem cr23R_le_pow (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23R N t ≤ 2 ^ (3 * cr23Lb N + 78) := by
  have ht : t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
  have hl : cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
  have hl1 : cr23Lb N + 1 ≤ 2 ^ cr23Lb N := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have h1 : t * cr23Lb N * (cr23Lb N + 1) ≤ 2 ^ cr23Lb N * 2 ^ cr23Lb N * 2 ^ cr23Lb N :=
    Nat.mul_le_mul (Nat.mul_le_mul ht hl) hl1
  rw [cr23R_eq]
  calc 2 ^ 78 * (t * cr23Lb N * (cr23Lb N + 1))
      ≤ 2 ^ 78 * (2 ^ cr23Lb N * 2 ^ cr23Lb N * 2 ^ cr23Lb N) := Nat.mul_le_mul_left (2 ^ 78) h1
    _ = 2 ^ (3 * cr23Lb N + 78) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        ring
theorem cr23DN_le_pow (N : ℕ) (hN : 1 ≤ N) : N * cr23D N ≤ 2 ^ (2 * cr23Lb N + 10) := by
  have hNle : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
  have hl : cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
  calc N * cr23D N = 1024 * (N * cr23Lb N) := by simp only [cr23D] <;> ring
    _ ≤ 1024 * (2 ^ cr23Lb N * 2 ^ cr23Lb N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hNle hl)
    _ = 2 ^ (2 * cr23Lb N + 10) := by
        rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, ← pow_add, ← pow_add]
        congr 1 <;> ring
theorem cr23_twoDN_le_pow (N : ℕ) (hN : 1 ≤ N) :
    2 * (cr23D N * N) ≤ 2 ^ (2 * cr23Lb N + 11) := by
  have h := cr23DN_le_pow N hN
  have e : 2 * (cr23D N * N) = 2 * (N * cr23D N) := by ring
  rw [e]
  calc 2 * (N * cr23D N) ≤ 2 * 2 ^ (2 * cr23Lb N + 10) := Nat.mul_le_mul_left 2 h
    _ = 2 ^ (2 * cr23Lb N + 11) := by
        rw [show 2 * cr23Lb N + 11 = (2 * cr23Lb N + 10) + 1 from by ring, pow_succ]
        ring
theorem cr23_graph0_le_pow (N : ℕ) (hN : 1 ≤ N) : cr23Graph0 N ≤ 2 ^ (2 * cr23Lb N + 13) := by
  have h1 : 1 + N ≤ 2 ^ (2 * cr23Lb N + 11) := by
    have h2 : 1 ≤ 2 ^ cr23Lb N := Nat.one_le_two_pow
    have h3 : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    have h4 : 1 + N ≤ 2 ^ (cr23Lb N + 1) := by
      calc 1 + N ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N := Nat.add_le_add h2 h3
        _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ] <;> ring
    exact le_trans h4 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 * (cr23D N * N) ≤ 2 ^ (2 * cr23Lb N + 11) := cr23_twoDN_le_pow N hN
  have e : cr23Graph0 N = (1 + N) + 2 * (cr23D N * N) := by
    simp only [cr23Graph0, cr23PairEnd] <;> ring
  rw [e]
  calc (1 + N) + 2 * (cr23D N * N) ≤ 2 ^ (2 * cr23Lb N + 11) + 2 ^ (2 * cr23Lb N + 11) :=
        Nat.add_le_add h1 h2
    _ = 2 ^ (2 * cr23Lb N + 12) := by
        rw [show 2 * cr23Lb N + 12 = (2 * cr23Lb N + 11) + 1 from by ring, pow_succ] <;> ring
    _ ≤ 2 ^ (2 * cr23Lb N + 13) := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem cr23_graphND_le_pow (N : ℕ) (hN : 1 ≤ N) :
    cr23Graph0 N + N * cr23D N ≤ 2 ^ (2 * cr23Lb N + 14) := by
  have h1 := cr23_graph0_le_pow N hN
  have h2 := cr23DN_le_pow N hN
  have h2' : N * cr23D N ≤ 2 ^ (2 * cr23Lb N + 13) :=
    le_trans h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc cr23Graph0 N + N * cr23D N ≤ 2 ^ (2 * cr23Lb N + 13) + 2 ^ (2 * cr23Lb N + 13) :=
        Nat.add_le_add h1 h2'
    _ = 2 ^ (2 * cr23Lb N + 14) := by
        rw [show 2 * cr23Lb N + 14 = (2 * cr23Lb N + 13) + 1 from by ring, pow_succ] <;> ring
theorem cr23_graph0_lt_word (N : ℕ) (hN : 1 ≤ N) : cr23Graph0 N < 2 ^ cr23Word N :=
  cr23_lt_word N hN (le_trans (cr23_graph0_le_pow N hN) (cr23_pow_le_twenty N (by omega)))
theorem cr23_graphND_lt_word (N : ℕ) (hN : 1 ≤ N) :
    cr23Graph0 N + N * cr23D N < 2 ^ cr23Word N :=
  cr23_lt_word N hN (le_trans (cr23_graphND_le_pow N hN) (cr23_pow_le_twenty N (by omega)))
theorem cr23_graphND1_lt_word (N : ℕ) (hN : 1 ≤ N) :
    cr23Graph0 N + N * cr23D N + 1 < 2 ^ cr23Word N := by
  have h := cr23_graphND_le_pow N hN
  refine cr23_lt_word N hN ?_
  calc cr23Graph0 N + N * cr23D N + 1 ≤ 2 ^ (2 * cr23Lb N + 14) + 1 := Nat.add_le_add_right h 1
    _ ≤ 2 ^ (2 * cr23Lb N + 14) + 2 ^ (2 * cr23Lb N + 14) :=
        Nat.add_le_add_left (Nat.one_le_two_pow) _
    _ = 2 ^ (2 * cr23Lb N + 15) := by
        rw [show 2 * cr23Lb N + 15 = (2 * cr23Lb N + 14) + 1 from by ring, pow_succ] <;> ring
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem cr23_lb_lt_word (N : ℕ) (hN : 1 ≤ N) : cr23Lb N < 2 ^ cr23Word N := by
  refine cr23_lt_word N hN ?_
  calc cr23Lb N ≤ 2 ^ cr23Lb N := le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := cr23_pow_le_twenty N (by omega)
theorem cr23_lb1_lt_word (N : ℕ) (hN : 1 ≤ N) : cr23Lb N + 1 < 2 ^ cr23Word N := by
  refine cr23_lt_word N hN ?_
  calc cr23Lb N + 1 ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N :=
        Nat.add_le_add (le_of_lt Nat.lt_two_pow_self) Nat.one_le_two_pow
    _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ] <;> ring
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := cr23_pow_le_twenty N (by omega)
theorem cr23_twoL_lt_word (N : ℕ) (hN : 1 ≤ N) : 2 ^ (cr23Lb N + 1) < 2 ^ cr23Word N :=
  cr23_lt_word N hN (cr23_pow_le_twenty N (by omega))
theorem cr23_succN_lt_word (N : ℕ) (hN : 1 ≤ N) : 1 + N < 2 ^ cr23Word N := by
  refine cr23_lt_word N hN ?_
  calc 1 + N ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N :=
        Nat.add_le_add Nat.one_le_two_pow (cr23_le_pow_lb N)
    _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ] <;> ring
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := cr23_pow_le_twenty N (by omega)
theorem cr23_t_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) : t < 2 ^ cr23Word N := by
  refine cr23_lt_word N hN ?_
  calc t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
    _ ≤ 2 ^ (2 * cr23Lb N + 20) := cr23_pow_le_twenty N (by omega)
/-- `M/2^68 = t`: the decoder recovers `t` from the table cell `M`. -/
theorem cr23M_div (t : ℕ) : cr23M t / 295147905179352825856 = t := by
  show 2 ^ 68 * t / 295147905179352825856 = t
  rw [Nat.mul_comm (2 ^ 68) t]
  exact Nat.mul_div_left t (by norm_num)
theorem cr23M_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) : cr23M t < 2 ^ cr23Word N := by
  refine cr23_lt_word_frame N hN ?_
  have ht : t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
  calc cr23M t = 2 ^ 68 * t := rfl
    _ ≤ 2 ^ 68 * 2 ^ cr23Lb N := Nat.mul_le_mul_left _ ht
    _ = 2 ^ (cr23Lb N + 68) := by rw [← pow_add]; congr 1 <;> ring
    _ ≤ 2 ^ (3 * cr23Lb N + 100) := Nat.pow_le_pow_right (by norm_num) (by omega)
/-- `D·M ≤ R`. -/
theorem cr23DM_le_pow (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t ≤ 2 ^ (3 * cr23Lb N + 78) := by
  have hR := cr23R_le_pow N t hN htN
  have hL : 1 ≤ cr23Lb N + 1 := by omega
  calc cr23D N * cr23M t = cr23D N * cr23M t * 1 := by ring
    _ ≤ cr23D N * cr23M t * (cr23Lb N + 1) := Nat.mul_le_mul_left _ hL
    _ = cr23R N t := by simp only [cr23R] <;> ring
    _ ≤ 2 ^ (3 * cr23Lb N + 78) := hR
theorem cr23DM_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t < 2 ^ cr23Word N :=
  cr23_lt_word_frame N hN (le_trans (cr23DM_le_pow N t hN htN)
    (Nat.pow_le_pow_right (by norm_num) (by omega)))
/-- **The frame start is at most `2^(3·lb+80)`** (hence a legal word). -/
theorem cr23DecFrame_le (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23DecFrame N t ≤ 2 ^ (3 * cr23Lb N + 80) := by
  have hR := cr23R_le_pow N t hN htN
  have hG := cr23_graph0_le_pow N hN
  have hND := cr23DN_le_pow N hN
  have hG' : cr23Graph0 N ≤ 2 ^ (3 * cr23Lb N + 78) :=
    le_trans hG (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hND' : N * cr23D N ≤ 2 ^ (3 * cr23Lb N + 78) :=
    le_trans hND (Nat.pow_le_pow_right (by norm_num) (by omega))
  have htwo : 2 ≤ 2 ^ (3 * cr23Lb N + 78) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * cr23Lb N + 78) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : cr23DecFrame N t = cr23R N t + (cr23Graph0 N + N * cr23D N) + 2 := by
    simp only [cr23DecFrame] <;> ring
  rw [e]
  have hsum : cr23R N t + (cr23Graph0 N + N * cr23D N) + 2 ≤ 4 * 2 ^ (3 * cr23Lb N + 78) := by
    omega
  calc cr23R N t + (cr23Graph0 N + N * cr23D N) + 2 ≤ 4 * 2 ^ (3 * cr23Lb N + 78) := hsum
    _ = 2 ^ (3 * cr23Lb N + 80) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1 <;> ring
theorem cr23DecFrame_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23DecFrame N t < 2 ^ cr23Word N :=
  cr23_lt_word_frame N hN (le_trans (cr23DecFrame_le N t hN htN)
    (Nat.pow_le_pow_right (by norm_num) (by omega)))
/-- t+1\ is below ^(lb+2)\. -/
theorem cr23_two_t_succ_le (N t : ℕ) (ht : t ≤ 2 ^ cr23Lb N) :
    2 * t + 1 ≤ 2 ^ (cr23Lb N + 2) := by
  have h1 : 2 * t ≤ 2 ^ (cr23Lb N + 1) := by
    calc 2 * t ≤ 2 * 2 ^ cr23Lb N := Nat.mul_le_mul_left 2 ht
      _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ] <;> ring
  have h2 : 1 ≤ 2 ^ (cr23Lb N + 1) := Nat.one_le_two_pow
  calc 2 * t + 1 ≤ 2 ^ (cr23Lb N + 1) + 2 ^ (cr23Lb N + 1) := by omega
    _ = 2 ^ (cr23Lb N + 2) := by
        rw [show cr23Lb N + 2 = (cr23Lb N + 1) + 1 from by ring, pow_succ] <;> ring
/-- \	+1\ is below ^(lb+1)\. -/
theorem cr23_succ_t_le (N t : ℕ) (ht : t ≤ 2 ^ cr23Lb N) :
    t + 1 ≤ 2 ^ (cr23Lb N + 1) := by
  have h2 : 1 ≤ 2 ^ cr23Lb N := Nat.one_le_two_pow
  calc t + 1 ≤ 2 ^ cr23Lb N + 2 ^ cr23Lb N := by omega
    _ = 2 ^ (cr23Lb N + 1) := by rw [pow_succ] <;> ring
/-- **The whole frame is at most 2^(3·lb+83).** -/
theorem cr23DecEnd_le (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23DecEnd N t ≤ 2 ^ (3 * cr23Lb N + 83) := by
  have hfr := cr23DecFrame_le N t hN htN
  have ht : t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
  have hK : ∀ e : ℕ, e ≤ 3 * cr23Lb N + 80 → (2 : ℕ) ^ e ≤ 2 ^ (3 * cr23Lb N + 80) :=
    fun e he => Nat.pow_le_pow_right (by norm_num) he
  have h2t : 2 * t + 1 ≤ 2 ^ (3 * cr23Lb N + 80) :=
    le_trans (cr23_two_t_succ_le N t ht) (hK (cr23Lb N + 2) (by omega))
  have ht1 : t + 1 ≤ 2 ^ (3 * cr23Lb N + 80) :=
    le_trans (cr23_succ_t_le N t ht) (hK (cr23Lb N + 1) (by omega))
  have h2L : 2 ^ (cr23Lb N + 1) ≤ 2 ^ (3 * cr23Lb N + 80) := hK (cr23Lb N + 1) (by omega)
  have hcc : 32 ≤ 2 ^ (3 * cr23Lb N + 80) := by
    have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h32]
    exact hK 5 (by omega)
  have e : cr23DecEnd N t = cr23DecFrame N t + 32 + (2 * t + 1) + 2 ^ (cr23Lb N + 1)
      + (2 * t + 1) + 2 ^ (cr23Lb N + 1) + (t + 1) := by
    simp only [cr23DecEnd, decOutBase, decParBase, decMstBase, decTagBase, decCandBase] <;> ring
  rw [e]
  have hbound : cr23DecFrame N t + 32 + (2 * t + 1) + 2 ^ (cr23Lb N + 1)
      + (2 * t + 1) + 2 ^ (cr23Lb N + 1) + (t + 1) ≤ 7 * 2 ^ (3 * cr23Lb N + 80) := by
    omega
  have h7 : 7 * 2 ^ (3 * cr23Lb N + 80) ≤ 2 ^ (3 * cr23Lb N + 83) := by
    have h8 : 8 * 2 ^ (3 * cr23Lb N + 80) = 2 ^ (3 * cr23Lb N + 83) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1 <;> ring
    omega
  exact le_trans hbound h7
/-- **The whole frame is a legal word range.** -/
theorem cr23DecEnd_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23DecEnd N t < 2 ^ cr23Word N :=
  cr23_lt_word_frame N hN (le_trans (cr23DecEnd_le N t hN htN)
    (Nat.pow_le_pow_right (by norm_num) (by omega)))
/-- The prologue of the decoder. -/
def progDecPre : List Instr := progDecPreC ++ progDecPreS
/-- The state after the computation half of the prologue. -/
def decPreCState (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) :
    RAMState :=
  runBlock progDecPreC (detEnv (cr23Word N) (cr23DecDet N t C)) s
def decPC0 : List Instr := [iImm r2 1, iTbl r3 r0, iTbl r4 r2, iSub r4 r4 r2, iAdd r5 r2 r4]
def decPC1 : List Instr := [iMul r6 r3 r4, iAdd r7 r6 r6, iAdd r5 r5 r7]
def decPC2 : List Instr := [iAdd r7 r5 r6, iTbl r8 r7, iAdd r7 r7 r2]
def decPC3 : List Instr := [iTbl r10 r7, iAdd r9 r10 r2, iShl r11 r2 r9, iImm r12 295147905179352825856]
def decPC4 : List Instr := [iDiv r13 r8 r12, iMul r14 r3 r8, iMul r14 r14 r9]
def decPC5 : List Instr := [iAdd r14 r14 r5, iAdd r14 r14 r6, iAdd r14 r14 r2, iAdd r14 r14 r2]
theorem progDecPreC_split :
    progDecPreC = decPC0 ++ decPC1 ++ decPC2 ++ decPC3 ++ decPC4 ++ decPC5 := rfl
/-- **A block whose destinations are known leaves every other register alone.** -/
theorem decFrame_of_dests (E : RAMEnv) (st : RAMState) (code : List Instr) (rs : List (Fin 16))
    (hcode : code.map Instr.dest? = rs.map some) (d : Fin 16) (hd : d ∉ rs) :
    (runBlock code E st).regs d = st.regs d := by
  refine runBlock_regs_frame code E st d ?_
  intro i hi hdest
  have h1 : i.dest? ∈ rs.map some := by
    rw [← hcode]
    exact List.mem_map_of_mem (f := Instr.dest?) hi
  obtain ⟨r, hr, hr'⟩ := List.mem_map.mp h1
  have hrd : r = d := Option.some.inj (hr'.trans hdest)
  exact hd (hrd ▸ hr)
theorem cr23_lt_word_of_exp (N : ℕ) (hN : 1 ≤ N) {e j : ℕ} (he : e ≤ 3 * cr23Lb N + 100)
    (hj : j ≤ 2 ^ e) : j < 2 ^ cr23Word N :=
  cr23_lt_word_frame N hN (le_trans hj (Nat.pow_le_pow_right (by norm_num) he))
theorem cr23_twoDN_lt_word (N : ℕ) (hN : 1 ≤ N) :
    cr23D N * N + cr23D N * N < 2 ^ cr23Word N := by
  have h := cr23_twoDN_le_pow N hN
  have e : cr23D N * N + cr23D N * N = 2 * (cr23D N * N) := by ring
  rw [e]
  exact cr23_lt_word_of_exp N hN (by omega) h
theorem cr23Graph0_form (N : ℕ) :
    cr23Graph0 N = (1 + N) + (cr23D N * N + cr23D N * N) := by
  simp only [cr23Graph0, cr23PairEnd]
  ring
theorem cr23_graphND_lt_word' (N : ℕ) (hN : 1 ≤ N) :
    (1 + N) + (cr23D N * N + cr23D N * N) + cr23D N * N < 2 ^ cr23Word N := by
  rw [← cr23Graph0_form N, Nat.mul_comm (cr23D N) N]
  exact cr23_graphND_lt_word N hN
theorem cr23_graphND1_lt_word' (N : ℕ) (hN : 1 ≤ N) :
    (1 + N) + (cr23D N * N + cr23D N * N) + cr23D N * N + 1 < 2 ^ cr23Word N := by
  rw [← cr23Graph0_form N, Nat.mul_comm (cr23D N) N]
  exact cr23_graphND1_lt_word N hN
theorem cr23_graph0_lt_word' (N : ℕ) (hN : 1 ≤ N) :
    (1 + N) + (cr23D N * N + cr23D N * N) < 2 ^ cr23Word N := by
  rw [← cr23Graph0_form N]
  exact cr23_graph0_lt_word N hN
theorem cr23DecFrame_form (N t : ℕ) :
    cr23DecFrame N t = cr23D N * cr23M t * (cr23Lb N + 1)
      + ((1 + N) + (cr23D N * N + cr23D N * N)) + cr23D N * N + 2 := by
  simp only [cr23DecFrame, cr23R, cr23Graph0, cr23PairEnd]
  ring
theorem cr23R_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t * (cr23Lb N + 1) < 2 ^ cr23Word N := by
  have h := cr23R_le_pow N t hN htN
  exact cr23_lt_word_of_exp N hN (by omega) h
theorem cr23_frame_a (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t * (cr23Lb N + 1)
      + ((1 + N) + (cr23D N * N + cr23D N * N)) < 2 ^ cr23Word N := by
  have h := cr23DecFrame_lt_word N t hN htN
  rw [cr23DecFrame_form N t] at h
  omega
theorem cr23_frame_b (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t * (cr23Lb N + 1)
      + ((1 + N) + (cr23D N * N + cr23D N * N)) + cr23D N * N < 2 ^ cr23Word N := by
  have h := cr23DecFrame_lt_word N t hN htN
  rw [cr23DecFrame_form N t] at h
  omega
theorem cr23_frame_c (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    cr23D N * cr23M t * (cr23Lb N + 1) + ((1 + N) + (cr23D N * N + cr23D N * N))
      + cr23D N * N + 1 < 2 ^ cr23Word N := by
  have h := cr23DecFrame_lt_word N t hN htN
  rw [cr23DecFrame_form N t] at h
  omega
theorem cr23DecDet_one (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (hN : 1 ≤ N) :
    cr23DecDet N t C 1 = 1 + N := by
  have h := cr23DecDet_base N t C hN (⟨0, by omega⟩ : Fin N)
  simpa [upBase, Nat.mul_zero, Nat.add_zero] using h
/-- **Chunk 0**: `r2 = 1`, `r3 = D = det 0`, `r4 = N = det 1 - 1`, `r5 = 1 + N`. -/
theorem decPC0_spec (E : RAMEnv) (st : RAMState) (D Nn : ℕ)
    (h0 : st.regs r0 = 0) (hd0 : E.det 0 = D) (hd1 : E.det 1 = 1 + Nn)
    (hW1 : 1 < 2 ^ E.W) (hDW : D < 2 ^ E.W) (h1NW : 1 + Nn < 2 ^ E.W)
    (hNW : Nn < 2 ^ E.W) :
    (runBlock decPC0 E st).regs r2 = 1 ∧
      (runBlock decPC0 E st).regs r3 = D ∧
      (runBlock decPC0 E st).regs r4 = Nn ∧
      (runBlock decPC0 E st).regs r5 = 1 + Nn ∧
      (runBlock decPC0 E st).mem = st.mem := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  have hDm : D % 2 ^ E.W = D := Nat.mod_eq_of_lt hDW
  have h1Nm : (1 + Nn) % 2 ^ E.W = 1 + Nn := Nat.mod_eq_of_lt h1NW
  have hNm : Nn % 2 ^ E.W = Nn := Nat.mod_eq_of_lt hNW
  have hsub : ((1 + Nn) + 2 ^ E.W - 1) % 2 ^ E.W = Nn := by
    have e : (1 + Nn) + 2 ^ E.W - 1 = Nn + 1 * 2 ^ E.W := by
      rw [Nat.one_mul]
      omega
    rw [e, Nat.add_mul_mod_self_right, hNm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [decPC0, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet, execInstr_add,
      execInstr_sub, h0, hd0, hd1, h1, hDm, h1Nm, hNm, hsub]
/-- **Chunk 1**: `r6 = D·N`, `r7 = 2·D·N`, `r5 = graph0`. -/
theorem decPC1_spec (E : RAMEnv) (st : RAMState) (D Nn : ℕ)
    (h5 : st.regs r5 = 1 + Nn) (h3 : st.regs r3 = D) (h4 : st.regs r4 = Nn)
    (hDN : D * Nn < 2 ^ E.W) (h2DN : D * Nn + D * Nn < 2 ^ E.W)
    (hg : (1 + Nn) + (D * Nn + D * Nn) < 2 ^ E.W) :
    (runBlock decPC1 E st).regs r6 = D * Nn ∧
      (runBlock decPC1 E st).regs r7 = D * Nn + D * Nn ∧
      (runBlock decPC1 E st).regs r5 = (1 + Nn) + (D * Nn + D * Nn) ∧
      (runBlock decPC1 E st).mem = st.mem := by
  have hDNm : D * Nn % 2 ^ E.W = D * Nn := Nat.mod_eq_of_lt hDN
  have h2DNm : (D * Nn + D * Nn) % 2 ^ E.W = D * Nn + D * Nn := Nat.mod_eq_of_lt h2DN
  have hgm : ((1 + Nn) + (D * Nn + D * Nn)) % 2 ^ E.W = (1 + Nn) + (D * Nn + D * Nn) :=
    Nat.mod_eq_of_lt hg
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [decPC1, runBlock_cons, runBlock_nil, execInstr_mul, execInstr_add,
      h5, h3, h4, hDNm, h2DNm, hgm]
/-- **Chunk 2**: `r7 = B = decBase`, `r8 = M = det B`, `r7 = B + 1`. -/
theorem decPC2_spec (E : RAMEnv) (st : RAMState) (D Nn B Mv : ℕ)
    (h2 : st.regs r2 = 1) (h5 : st.regs r5 = (1 + Nn) + (D * Nn + D * Nn))
    (h6 : st.regs r6 = D * Nn) (hbase : ((1 + Nn) + (D * Nn + D * Nn)) + D * Nn = B)
    (hBW : B < 2 ^ E.W) (hB1W : B + 1 < 2 ^ E.W) (hdB : E.det B = Mv) (hMvW : Mv < 2 ^ E.W) :
    (runBlock decPC2 E st).regs r7 = B + 1 ∧
      (runBlock decPC2 E st).regs r8 = Mv ∧
      (runBlock decPC2 E st).mem = st.mem := by
  have hBm : B % 2 ^ E.W = B := Nat.mod_eq_of_lt hBW
  have hB1m : (B + 1) % 2 ^ E.W = B + 1 := Nat.mod_eq_of_lt hB1W
  have hMvm : Mv % 2 ^ E.W = Mv := Nat.mod_eq_of_lt hMvW
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decPC2, runBlock_cons, runBlock_nil, execInstr_add, execInstr_qDet,
      h2, h5, h6, hbase, hBm, hB1m, hdB, hMvm]
/-- **Chunk 3**: `r10 = lb = det (B+1)`, `r9 = lb + 1`, `r11 = 2^(lb+1)`, `r12 = 2^68`. -/
theorem decPC3_spec (E : RAMEnv) (st : RAMState) (B Lb : ℕ)
    (h2 : st.regs r2 = 1) (h7 : st.regs r7 = B + 1) (hdL : E.det (B + 1) = Lb)
    (hLbW : Lb < 2 ^ E.W) (hLb1W : Lb + 1 < 2 ^ E.W) (h2LW : 2 ^ (Lb + 1) < 2 ^ E.W)
    (h4096W : 295147905179352825856 < 2 ^ E.W) :
    (runBlock decPC3 E st).regs r10 = Lb ∧
      (runBlock decPC3 E st).regs r9 = Lb + 1 ∧
      (runBlock decPC3 E st).regs r11 = 2 ^ (Lb + 1) ∧
      (runBlock decPC3 E st).regs r12 = 295147905179352825856 ∧
      (runBlock decPC3 E st).mem = st.mem := by
  have hLbm : Lb % 2 ^ E.W = Lb := Nat.mod_eq_of_lt hLbW
  have hLb1m : (Lb + 1) % 2 ^ E.W = Lb + 1 := Nat.mod_eq_of_lt hLb1W
  have h2Lm : 2 ^ (Lb + 1) % 2 ^ E.W = 2 ^ (Lb + 1) := Nat.mod_eq_of_lt h2LW
  have h4096m : (295147905179352825856 : ℕ) % 2 ^ E.W = 295147905179352825856 := Nat.mod_eq_of_lt h4096W
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [decPC3, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_shl,
      execInstr_imm, h2, h7, hdL, hLbm, hLb1m, h2Lm, h4096m]
/-- **Chunk 4**: `r13 = t = M/2^68`, `r14 = R = D·M·(lb+1)`. -/
theorem decPC4_spec (E : RAMEnv) (st : RAMState) (D Mv Lb1 T : ℕ)
    (h3 : st.regs r3 = D) (h8 : st.regs r8 = Mv) (h9 : st.regs r9 = Lb1)
    (h12 : st.regs r12 = 295147905179352825856) (hdiv : Mv / 295147905179352825856 = T) (hTW : T < 2 ^ E.W)
    (hDMW : D * Mv < 2 ^ E.W) (hRW : D * Mv * Lb1 < 2 ^ E.W) :
    (runBlock decPC4 E st).regs r13 = T ∧
      (runBlock decPC4 E st).regs r14 = D * Mv * Lb1 ∧
      (runBlock decPC4 E st).mem = st.mem := by
  have hTm : T % 2 ^ E.W = T := Nat.mod_eq_of_lt hTW
  have hRm : D * Mv * Lb1 % 2 ^ E.W = D * Mv * Lb1 := Nat.mod_eq_of_lt hRW
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decPC4, runBlock_cons, runBlock_nil, execInstr_div, execInstr_mul,
      h3, h8, h9, h12, hdiv, hTm, hRm]
/-- **Chunk 5**: `r14 = R + graph0 + D·N + 2 = cr23DecFrame`. -/
theorem decPC5_spec (E : RAMEnv) (st : RAMState) (R G F : ℕ)
    (h5 : st.regs r5 = G) (h6 : st.regs r6 = F) (h2 : st.regs r2 = 1)
    (h14 : st.regs r14 = R) (ha : R + G < 2 ^ E.W) (hb : R + G + F < 2 ^ E.W)
    (hc : R + G + F + 1 < 2 ^ E.W) (hd : R + G + F + 1 + 1 < 2 ^ E.W) :
    (runBlock decPC5 E st).regs r14 = R + G + F + 1 + 1 ∧
      (runBlock decPC5 E st).mem = st.mem := by
  have ham : (R + G) % 2 ^ E.W = R + G := Nat.mod_eq_of_lt ha
  have hbm : (R + G + F) % 2 ^ E.W = R + G + F := Nat.mod_eq_of_lt hb
  have hcm : (R + G + F + 1) % 2 ^ E.W = R + G + F + 1 := Nat.mod_eq_of_lt hc
  have hdm : (R + G + F + 1 + 1) % 2 ^ E.W = R + G + F + 1 + 1 := Nat.mod_eq_of_lt hd
  refine ⟨?_, ?_⟩ <;>
    simp [decPC5, runBlock_cons, runBlock_nil, execInstr_add, h5, h6, h2, h14,
      ham, hbm, hcm, hdm]
/-- **What the computation half leaves in the registers.**  `r2 = 1`, `r3 = D`, `r4 = N`,
`r8 = M`, `r9 = L`, `r10 = lb`, `r11 = 2^L`, `r13 = t`, `r14 = cr23DecFrame`, `r0` untouched,
and the payload intact — the prologue only ever writes above the frame. -/
theorem decPreC_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0) :
    (decPreCState N t C s).regs r2 = 1 ∧
    (decPreCState N t C s).regs r3 = cr23D N ∧
    (decPreCState N t C s).regs r4 = N ∧
    (decPreCState N t C s).regs r8 = cr23M t ∧
    (decPreCState N t C s).regs r9 = cr23Lb N + 1 ∧
    (decPreCState N t C s).regs r10 = cr23Lb N ∧
    (decPreCState N t C s).regs r11 = 2 ^ (cr23Lb N + 1) ∧
    (decPreCState N t C s).regs r13 = t ∧
    (decPreCState N t C s).regs r14 = cr23DecFrame N t ∧
    (decPreCState N t C s).regs r0 = 0 ∧
    (decPreCState N t C s).mem = s.mem := by
  simp only [decPreCState]
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set X1 : RAMState := runBlock decPC0 E s with hX1
  set X2 : RAMState := runBlock decPC1 E X1 with hX2
  set X3 : RAMState := runBlock decPC2 E X2 with hX3
  set X4 : RAMState := runBlock decPC3 E X3 with hX4
  set X5 : RAMState := runBlock decPC4 E X4 with hX5
  set X6 : RAMState := runBlock decPC5 E X5 with hX6
  have f0 : ∀ d : Fin 16, d ∉ [r2, r3, r4, r4, r5] →
      (runBlock decPC0 E s).regs d = s.regs d :=
    fun d hd => decFrame_of_dests E s decPC0 [r2, r3, r4, r4, r5] (by rfl) d hd
  have f1 : ∀ d : Fin 16, d ∉ [r6, r7, r5] →
      (runBlock decPC1 E X1).regs d = X1.regs d :=
    fun d hd => decFrame_of_dests E X1 decPC1 [r6, r7, r5] (by rfl) d hd
  have f2 : ∀ d : Fin 16, d ∉ [r7, r8, r7] →
      (runBlock decPC2 E X2).regs d = X2.regs d :=
    fun d hd => decFrame_of_dests E X2 decPC2 [r7, r8, r7] (by rfl) d hd
  have f3 : ∀ d : Fin 16, d ∉ [r10, r9, r11, r12] →
      (runBlock decPC3 E X3).regs d = X3.regs d :=
    fun d hd => decFrame_of_dests E X3 decPC3 [r10, r9, r11, r12] (by rfl) d hd
  have f4 : ∀ d : Fin 16, d ∉ [r13, r14, r14] →
      (runBlock decPC4 E X4).regs d = X4.regs d :=
    fun d hd => decFrame_of_dests E X4 decPC4 [r13, r14, r14] (by rfl) d hd
  have f5 : ∀ d : Fin 16, d ∉ [r14, r14, r14, r14] →
      (runBlock decPC5 E X5).regs d = X5.regs d :=
    fun d hd => decFrame_of_dests E X5 decPC5 [r14, r14, r14, r14] (by rfl) d hd
  have hD : cr23D N < 2 ^ cr23Word N := cr23D_lt_word N hN
  have hNw : N < 2 ^ cr23Word N := cr23N_lt_word N hN
  have h1Nw : 1 + N < 2 ^ cr23Word N := cr23_succN_lt_word N hN
  have hDNw : cr23D N * N < 2 ^ cr23Word N := by
    rw [Nat.mul_comm]
    exact cr23_lt_word_of_exp N hN (by omega) (cr23DN_le_pow N hN)
  have h2DNw : cr23D N * N + cr23D N * N < 2 ^ cr23Word N := cr23_twoDN_lt_word N hN
  have hgw : (1 + N) + (cr23D N * N + cr23D N * N) < 2 ^ cr23Word N := cr23_graph0_lt_word' N hN
  have hbase : ((1 + N) + (cr23D N * N + cr23D N * N)) + cr23D N * N = cr23DecBase N := by
    simp only [cr23DecBase, cr23Graph0, cr23PairEnd, Nat.mul_comm (cr23D N) N]
    ring
  have hBw : cr23DecBase N < 2 ^ cr23Word N := hbase ▸ cr23_graphND_lt_word' N hN
  have hB1w : cr23DecBase N + 1 < 2 ^ cr23Word N := hbase ▸ cr23_graphND1_lt_word' N hN
  have hMw : cr23M t < 2 ^ cr23Word N := cr23M_lt_word N t hN htN
  have hLbw : cr23Lb N < 2 ^ cr23Word N := cr23_lb_lt_word N hN
  have hLb1w : cr23Lb N + 1 < 2 ^ cr23Word N := cr23_lb1_lt_word N hN
  have h2Lw : 2 ^ (cr23Lb N + 1) < 2 ^ cr23Word N := cr23_twoL_lt_word N hN
  have h4096w : (2 : ℕ) ^ 68 < 2 ^ cr23Word N :=
    cr23_lt_word_of_exp N hN (e := 68) (by omega) le_rfl
  have htw : t < 2 ^ cr23Word N := cr23_t_lt_word N t hN htN
  have hDMw : cr23D N * cr23M t < 2 ^ cr23Word N := cr23DM_lt_word N t hN htN
  have hRw : cr23D N * cr23M t * (cr23Lb N + 1) < 2 ^ cr23Word N := cr23R_lt_word N t hN htN
  have hfaw : cr23D N * cr23M t * (cr23Lb N + 1)
      + ((1 + N) + (cr23D N * N + cr23D N * N)) < 2 ^ cr23Word N := cr23_frame_a N t hN htN
  have hfbw : cr23D N * cr23M t * (cr23Lb N + 1)
      + ((1 + N) + (cr23D N * N + cr23D N * N)) + cr23D N * N < 2 ^ cr23Word N :=
    cr23_frame_b N t hN htN
  have hfcw : cr23D N * cr23M t * (cr23Lb N + 1) + ((1 + N) + (cr23D N * N + cr23D N * N))
      + cr23D N * N + 1 < 2 ^ cr23Word N := cr23_frame_c N t hN htN
  have hfdw : cr23D N * cr23M t * (cr23Lb N + 1) + ((1 + N) + (cr23D N * N + cr23D N * N))
      + cr23D N * N + 1 + 1 < 2 ^ cr23Word N := by
    have hh := cr23DecFrame_lt_word N t hN htN
    rw [cr23DecFrame_form N t] at hh
    omega
  have hfr : cr23D N * cr23M t * (cr23Lb N + 1) + ((1 + N) + (cr23D N * N + cr23D N * N))
      + cr23D N * N + 1 + 1 = cr23DecFrame N t := by
    rw [cr23DecFrame_form N t]
  have hbase : ((1 + N) + (cr23D N * N + cr23D N * N)) + cr23D N * N = cr23DecBase N := by
    simp only [cr23DecBase, cr23Graph0, cr23PairEnd, Nat.mul_comm (cr23D N) N]
    ring
  -- chunk 0
  have hA := decPC0_spec E s (cr23D N) N h0 (cr23DecDet_zero N t C hN)
    (cr23DecDet_one N t C hN) (cr23_one_lt_word N hN) hD h1Nw hNw
  rw [← hX1] at hA
  obtain ⟨hA2, hA3, hA4, hA5, hAmem⟩ := hA
  -- chunk 1 (needs `r5`, `r3`, `r4` of `X1`)
  have hB := decPC1_spec E X1 (cr23D N) N hA5 hA3 hA4 hDNw h2DNw hgw
  rw [← hX2] at hB
  obtain ⟨hB6, hB7, hB5, hBmem⟩ := hB
  have g22 : X2.regs r2 = 1 := by rw [hX2, f1 r2 (by decide)]; exact hA2
  have g23 : X2.regs r3 = cr23D N := by rw [hX2, f1 r3 (by decide)]; exact hA3
  have g24 : X2.regs r4 = N := by rw [hX2, f1 r4 (by decide)]; exact hA4
  -- chunk 2 (needs `r2`, `r5`, `r6` of `X2`)
  have hC := decPC2_spec E X2 (cr23D N) N (cr23DecBase N) (cr23M t) g22 hB5 hB6 hbase
    hBw hB1w (cr23DecDet_M N t C) hMw
  rw [← hX3] at hC
  obtain ⟨hC7, hC8, hCmem⟩ := hC
  have g32 : X3.regs r2 = 1 := by rw [hX3, f2 r2 (by decide)]; exact g22
  have g33 : X3.regs r3 = cr23D N := by rw [hX3, f2 r3 (by decide)]; exact g23
  have g35 : X3.regs r5 = (1 + N) + (cr23D N * N + cr23D N * N) := by
    rw [hX3, f2 r5 (by decide)]; exact hB5
  have g36 : X3.regs r6 = cr23D N * N := by rw [hX3, f2 r6 (by decide)]; exact hB6
  have g38 : X3.regs r8 = cr23M t := hC8
  -- chunk 3 (needs `r2`, `r7` of `X3`)
  have hD3 := decPC3_spec E X3 (cr23DecBase N) (cr23Lb N) g32 hC7 (cr23DecDet_lb N t C)
    hLbw hLb1w h2Lw h4096w
  rw [← hX4] at hD3
  obtain ⟨hD10, hD9, hD11, hD12, hDmem⟩ := hD3
  have g42 : X4.regs r2 = 1 := by rw [hX4, f3 r2 (by decide)]; exact g32
  have g43 : X4.regs r3 = cr23D N := by rw [hX4, f3 r3 (by decide)]; exact g33
  have g45 : X4.regs r5 = (1 + N) + (cr23D N * N + cr23D N * N) := by
    rw [hX4, f3 r5 (by decide)]; exact g35
  have g46 : X4.regs r6 = cr23D N * N := by rw [hX4, f3 r6 (by decide)]; exact g36
  have g48 : X4.regs r8 = cr23M t := by rw [hX4, f3 r8 (by decide)]; exact g38
  -- chunk 4 (needs `r3`, `r8`, `r9`, `r12` of `X4`)
  have hE4 := decPC4_spec E X4 (cr23D N) (cr23M t) (cr23Lb N + 1) t g43 g48 hD9 hD12
    (cr23M_div t) htw hDMw hRw
  rw [← hX5] at hE4
  obtain ⟨hE13, hE14, hEmem⟩ := hE4
  have g52 : X5.regs r2 = 1 := by rw [hX5, f4 r2 (by decide)]; exact g42
  have g55 : X5.regs r5 = (1 + N) + (cr23D N * N + cr23D N * N) := by
    rw [hX5, f4 r5 (by decide)]; exact g45
  have g56 : X5.regs r6 = cr23D N * N := by rw [hX5, f4 r6 (by decide)]; exact g46
  have g58 : X5.regs r8 = cr23M t := by rw [hX5, f4 r8 (by decide)]; exact g48
  have g59 : X5.regs r9 = cr23Lb N + 1 := by rw [hX5, f4 r9 (by decide)]; exact hD9
  have g510 : X5.regs r10 = cr23Lb N := by rw [hX5, f4 r10 (by decide)]; exact hD10
  have g511 : X5.regs r11 = 2 ^ (cr23Lb N + 1) := by rw [hX5, f4 r11 (by decide)]; exact hD11
  -- chunk 5 (needs `r5`, `r6`, `r2`, `r14` of `X5`)
  have hF := decPC5_spec E X5 (cr23D N * cr23M t * (cr23Lb N + 1))
    ((1 + N) + (cr23D N * N + cr23D N * N)) (cr23D N * N) g55 g56 g52 hE14
    hfaw hfbw hfcw hfdw
  rw [← hX6] at hF
  obtain ⟨hF14, hFmem⟩ := hF
  have g62 : X6.regs r2 = 1 := by rw [hX6, f5 r2 (by decide)]; exact g52
  have g63 : X6.regs r3 = cr23D N := by
    rw [hX6, f5 r3 (by decide), hX5, f4 r3 (by decide), hX4, f3 r3 (by decide)]
    exact g33
  have g64 : X6.regs r4 = N := by
    rw [hX6, f5 r4 (by decide), hX5, f4 r4 (by decide), hX4, f3 r4 (by decide),
      hX3, f2 r4 (by decide), hX2, f1 r4 (by decide)]
    exact hA4
  have g68 : X6.regs r8 = cr23M t := by rw [hX6, f5 r8 (by decide)]; exact g58
  have g69 : X6.regs r9 = cr23Lb N + 1 := by rw [hX6, f5 r9 (by decide)]; exact g59
  have g610 : X6.regs r10 = cr23Lb N := by rw [hX6, f5 r10 (by decide)]; exact g510
  have g611 : X6.regs r11 = 2 ^ (cr23Lb N + 1) := by rw [hX6, f5 r11 (by decide)]; exact g511
  have g613 : X6.regs r13 = t := by rw [hX6, f5 r13 (by decide)]; exact hE13
  have g614 : X6.regs r14 = cr23DecFrame N t := by rw [hF14, hfr]
  have g60 : X6.regs r0 = 0 := by
    rw [hX6, f5 r0 (by decide), hX5, f4 r0 (by decide), hX4, f3 r0 (by decide),
      hX3, f2 r0 (by decide), hX2, f1 r0 (by decide), hX1, f0 r0 (by decide)]
    exact h0
  have g6mem : X6.mem = s.mem := by rw [hFmem, hEmem, hDmem, hCmem, hBmem, hAmem]
  have hC6 : runBlock progDecPreC E s = X6 := by
    rw [progDecPreC_split]
    simp only [runBlock_append]
    rw [← hX1, ← hX2, ← hX3, ← hX4, ← hX5, ← hX6]
  rw [hC6]
  exact ⟨g62, g63, g64, g68, g69, g610, g611, g613, g614, g60, g6mem⟩
/-- `wordsOf W M ≤ M`: the packed payload never reaches the frame. -/
theorem wordsOf_le_self {W M : ℕ} (hW : 0 < W) : wordsOf W M ≤ M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [wordsOf, Nat.zero_add]
    rw [Nat.div_eq_of_lt (by omega)]
  · rw [wordsOf, Nat.div_le_iff_le_mul hW]
    have h1 : M ≤ M * W := Nat.le_mul_of_pos_right M hW
    omega
/-- The packed payload occupies at most `R` words, and `R` is below the frame. -/
theorem cr23_wordsOf_le_frame (N t : ℕ) (hN : 1 ≤ N) :
    wordsOf (cr23Word N) (cr23R N t) ≤ cr23DecFrame N t := by
  refine le_trans (wordsOf_le_self (W := cr23Word N) (cr23Word_pos N)) ?_
  simp only [cr23DecFrame]
  omega
def decPS0 : List Instr := [iBor r15 r14 r14, iAdd r15 r15 r2]
def decPS1 : List Instr := [iSt r15 r3, iAdd r15 r15 r2]
def decPS2 : List Instr := [iSt r15 r4, iAdd r15 r15 r2]
def decPS3 : List Instr := [iSt r15 r8, iAdd r15 r15 r2]
def decPS4 : List Instr := [iSt r15 r9, iAdd r15 r15 r2]
def decPS5 : List Instr := [iSt r15 r10, iAdd r15 r15 r2]
def decPS6 : List Instr := [iSt r15 r11, iAdd r15 r15 r2]
def decPS7 : List Instr := [iSt r15 r13, iAdd r15 r15 r2]
def decPS8 : List Instr := [iSt r15 r13, iAdd r15 r15 r2]
def decPS9 : List Instr := [iSt r15 r2]
def decPS10 : List Instr := [iImm r7 32, iAdd r7 r14 r7, iAdd r15 r15 r2, iSt r15 r7]
def decPS11 : List Instr :=
  [iAdd r7 r7 r13, iAdd r7 r7 r13, iAdd r7 r7 r2, iAdd r15 r15 r2, iSt r15 r7]
def decPS12 : List Instr := [iAdd r7 r7 r11, iAdd r15 r15 r2, iSt r15 r7]
def decPS15 : List Instr := [iAdd r15 r15 r2, iSt r15 r0]
/-- The store half, chunk by chunk.  `decPS13 = decPS11` and `decPS14 = decPS12`: the tag base and
the parity base are built by the same code. -/
theorem progDecPreS_split :
    progDecPreS = decPS0 ++ decPS1 ++ decPS2 ++ decPS3 ++ decPS4 ++ decPS5 ++ decPS6 ++
      decPS7 ++ decPS8 ++ decPS9 ++ decPS10 ++ decPS11 ++ decPS12 ++ decPS11 ++ decPS12 ++
      decPS15 := rfl
/-- The fifteen slot values, indexed by `k` (slot `k` lives at `cr23DecFrame N t + 1 + k`). -/
def decSlotVal (N t : ℕ) : ℕ → ℕ
  | 0 => cr23D N
  | 1 => N
  | 2 => cr23M t
  | 3 => cr23Lb N + 1
  | 4 => cr23Lb N
  | 5 => 2 ^ (cr23Lb N + 1)
  | 6 => t
  | 7 => t
  | 8 => 1
  | 9 => decCandBase N t
  | 10 => decTagBase N t
  | 11 => decMstBase N t
  | 12 => decParBase N t
  | 13 => decOutBase N t
  | _ => 0
/-- **A write list never touches an address it does not write.** -/
theorem writeList_out (m : ℕ → ℕ) (l : List (ℕ × ℕ)) (a : ℕ)
    (h : ∀ p ∈ l, p.1 ≠ a) : writeList m l a = m a := by
  induction l generalizing m with
  | nil => rfl
  | cons p tl ih =>
      rw [writeList_cons, ih (m := Function.update m p.1 p.2) (fun q hq => h q (by simp [hq]))]
      exact Function.update_of_ne (Ne.symm (h p (by simp))) p.2 m
/-- **A write list with pairwise distinct addresses reads back what it wrote.** -/
theorem writeList_get (m : ℕ → ℕ) (l : List (ℕ × ℕ)) (a v : ℕ)
    (hn : (l.map Prod.fst).Nodup) (hm : (a, v) ∈ l) : writeList m l a = v := by
  induction l generalizing m with
  | nil => simp at hm
  | cons p tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hn
      rw [writeList_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst h
        rw [writeList_out (h := fun q hq hqa => hn.1 (List.mem_map.mpr ⟨q, hq, hqa⟩)),
          Function.update_self]
      · exact ih (m := Function.update m p.1 p.2) hn.2 h
/-- The fifteen slot writes, in order. -/
def decSlotList (N t : ℕ) : List (ℕ × ℕ) :=
  (List.range 15).map (fun k => (decSlot N t k, decSlotVal N t k))
/-- The fifteen slot addresses are pairwise distinct. -/
theorem decSlotList_keys_nodup (N t : ℕ) : ((decSlotList N t).map Prod.fst).Nodup := by
  simp only [decSlotList]
  rw [List.map_map]
  refine List.Nodup.map (f := Prod.fst ∘ fun k => (decSlot N t k, decSlotVal N t k)) ?_ List.nodup_range
  intro a b hab
  have hab' : cr23DecFrame N t + 1 + a = cr23DecFrame N t + 1 + b := hab
  omega
/-- The write of slot `k` sits in the list. -/
theorem decSlotList_mem (N t : ℕ) {k : ℕ} (hk : k < 15) :
    (decSlot N t k, decSlotVal N t k) ∈ decSlotList N t := by
  rw [decSlotList]
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
/-- `cr23DecFrame N t + c` is a legal word for every `c ≤ 32`. -/
theorem cr23_frame_add_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {c : ℕ} (hc : c ≤ 32) :
    cr23DecFrame N t + c < 2 ^ cr23Word N := by
  refine cr23_lt_word_frame N hN ?_
  have hfr := cr23DecFrame_le N t hN htN
  have h32 : (32 : ℕ) ≤ 2 ^ (3 * cr23Lb N + 80) := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (3 * cr23Lb N + 80) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc cr23DecFrame N t + c ≤ 2 ^ (3 * cr23Lb N + 80) + 32 := Nat.add_le_add hfr hc
    _ ≤ 2 ^ (3 * cr23Lb N + 80) + 2 ^ (3 * cr23Lb N + 80) := Nat.add_le_add_left h32 _
    _ = 2 ^ (3 * cr23Lb N + 81) := by
        rw [show 3 * cr23Lb N + 81 = (3 * cr23Lb N + 80) + 1 from by ring, pow_succ]
        ring
    _ ≤ 2 ^ (3 * cr23Lb N + 100) := Nat.pow_le_pow_right (by norm_num) (by omega)
/-- `cr23DecEnd` in the shape `omega` can use. -/
theorem cr23DecEnd_form (N t : ℕ) :
    cr23DecEnd N t = cr23DecFrame N t + 32 + (2 * t + 1) + 2 ^ (cr23Lb N + 1)
      + (2 * t + 1) + 2 ^ (cr23Lb N + 1) + (t + 1) := by
  simp only [cr23DecEnd, decOutBase, decParBase, decMstBase, decTagBase, decCandBase]
/-- Anything at most `cr23DecEnd` is a legal word. -/
theorem cr23_lt_word_of_le_end (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {j : ℕ}
    (hj : j ≤ cr23DecEnd N t) : j < 2 ^ cr23Word N :=
  lt_of_le_of_lt hj (cr23DecEnd_lt_word N t hN htN)
/-- `x ≤ x + y`. -/
theorem dec_le_add_self (x y : ℕ) : x ≤ x + y := by omega
theorem decFrame_le_candBase (N t : ℕ) : cr23DecFrame N t ≤ decCandBase N t := by
  simp only [decCandBase]
  exact dec_le_add_self _ _
theorem decCandBase_le_tagBase (N t : ℕ) : decCandBase N t ≤ decTagBase N t := by
  simp only [decTagBase]
  exact dec_le_add_self _ _
theorem decTagBase_le_mstBase (N t : ℕ) : decTagBase N t ≤ decMstBase N t := by
  simp only [decMstBase]
  exact dec_le_add_self _ _
theorem decMstBase_le_parBase (N t : ℕ) : decMstBase N t ≤ decParBase N t := by
  simp only [decParBase]
  exact dec_le_add_self _ _
theorem decFrame_le_tagBase (N t : ℕ) : cr23DecFrame N t ≤ decTagBase N t :=
  le_trans (decFrame_le_candBase N t) (decCandBase_le_tagBase N t)
theorem decFrame_le_parBase (N t : ℕ) : cr23DecFrame N t ≤ decParBase N t :=
  le_trans (decFrame_le_tagBase N t)
    (le_trans (decTagBase_le_mstBase N t) (decMstBase_le_parBase N t))
theorem decSlot_lt_candBase (N t : ℕ) {k : ℕ} (hk : k < 15) :
    decSlot N t k < decCandBase N t := by
  simp only [decSlot, decCandBase]
  omega
theorem DecPSKeep.refl (st : RAMState) : DecPSKeep st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- **One step of the store half**: a chunk that writes only `r15` and `r7` keeps all ten carried
registers. -/
theorem DecPSKeep.step {st st' st0 : RAMState} (h : DecPSKeep st st0)
    (hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → st'.regs d = st.regs d) : DecPSKeep st' st0 := by
  obtain ⟨h0, h2, h3, h4, h8, h9, h10, h11, h13, h14⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hf r0 (by decide) (by decide)]; exact h0)
    | (rw [hf r2 (by decide) (by decide)]; exact h2)
    | (rw [hf r3 (by decide) (by decide)]; exact h3)
    | (rw [hf r4 (by decide) (by decide)]; exact h4)
    | (rw [hf r8 (by decide) (by decide)]; exact h8)
    | (rw [hf r9 (by decide) (by decide)]; exact h9)
    | (rw [hf r10 (by decide) (by decide)]; exact h10)
    | (rw [hf r11 (by decide) (by decide)]; exact h11)
    | (rw [hf r13 (by decide) (by decide)]; exact h13)
    | (rw [hf r14 (by decide) (by decide)]; exact h14)
/-- **Shape 0** (`decPS0`) `[bor r15 r14 r14, add r15 r15 r2]`: `r15` becomes `F + 1`, memory is
untouched. -/
theorem decPS0_spec (E : RAMEnv) (st st0 : RAMState) (F : ℕ) (keep : DecPSKeep st st0)
    (h14 : st.regs r14 = F) (h2 : st.regs r2 = 1) (hFW : F < 2 ^ E.W)
    (hF1W : F + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock decPS0 E st) st0 ∧
      (runBlock decPS0 E st).regs r15 = F + 1 ∧
      (runBlock decPS0 E st).mem = st.mem := by
  have hlor : F ||| F = F := nat_lor_self F
  have hFm : F % 2 ^ E.W = F := Nat.mod_eq_of_lt hFW
  have hF1m : (F + 1) % 2 ^ E.W = F + 1 := Nat.mod_eq_of_lt hF1W
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS0 E st).regs d = st.regs d := by
    intro d h1 h2'
    refine runBlock_regs_frame decPS0 E st d ?_
    intro i hi
    simp only [decPS0, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Instr.dest?, h1]
    · simp [Instr.dest?, h1]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_⟩
  · simp [decPS0, runBlock_cons, runBlock_nil, execInstr_bor, execInstr_add, h14, h2, hlor, hFm,
      hF1m]
  · simp [decPS0, runBlock_cons, runBlock_nil, execInstr_bor, execInstr_add]
/-- **Shape 1** `[st r15 rv, add r15 r15 r2]`: one store at `A`, then the address moves to `A + 1`. -/
theorem decPS_st_store_add (E : RAMEnv) (st st0 : RAMState) (rv : Fin 16) (A V : ℕ)
    (keep : DecPSKeep st st0) (hA : st.regs r15 = A) (hV : st.regs rv = V)
    (h2 : st.regs r2 = 1) (hA1 : A + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock [iSt r15 rv, iAdd r15 r15 r2] E st) st0 ∧
      (runBlock [iSt r15 rv, iAdd r15 r15 r2] E st).mem = Function.update st.mem A V ∧
      (runBlock [iSt r15 rv, iAdd r15 r15 r2] E st).regs r15 = A + 1 := by
  have hA1m : (A + 1) % 2 ^ E.W = A + 1 := Nat.mod_eq_of_lt hA1
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d →
      (runBlock [iSt r15 rv, iAdd r15 r15 r2] E st).regs d = st.regs d := by
    intro d h1 h2'
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Instr.dest?]
    · simp [Instr.dest?, h1]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_⟩
  · simp [runBlock_cons, runBlock_nil, execInstr_store, execInstr_add, hA, hV]
  · simp [runBlock_cons, runBlock_nil, execInstr_store, execInstr_add, hA, h2, hA1m]
/-- **Shape 2** (`decPS9`) `[st r15 r2]`: the increment `1` is stored, the address stays. -/
theorem decPS_st_only (E : RAMEnv) (st st0 : RAMState) (A V : ℕ)
    (keep : DecPSKeep st st0) (hA : st.regs r15 = A) (hV : st.regs r2 = V) :
    DecPSKeep (runBlock decPS9 E st) st0 ∧
      (runBlock decPS9 E st).mem = Function.update st.mem A V ∧
      (runBlock decPS9 E st).regs r15 = A := by
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS9 E st).regs d = st.regs d := by
    intro d h1 h2'
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [decPS9, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    simp [Instr.dest?]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_⟩
  · simp [decPS9, runBlock_cons, runBlock_nil, execInstr_store, hA, hV]
  · simp [decPS9, runBlock_cons, runBlock_nil, execInstr_store, hA]
/-- **Shape 3** (`decPS10`) `[imm r7 32, add r7 r14 r7, add r15 r15 r2, st r15 r7]`: the candidate
base is `frame + 32`. -/
theorem decPS_base32 (E : RAMEnv) (st st0 : RAMState) (F A : ℕ)
    (keep : DecPSKeep st st0) (h14 : st.regs r14 = F) (hA : st.regs r15 = A)
    (h2 : st.regs r2 = 1) (h32 : (32 : ℕ) < 2 ^ E.W) (hF32 : F + 32 < 2 ^ E.W)
    (hA1 : A + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock decPS10 E st) st0 ∧
      (runBlock decPS10 E st).mem = Function.update st.mem (A + 1) (F + 32) ∧
      (runBlock decPS10 E st).regs r15 = A + 1 ∧
      (runBlock decPS10 E st).regs r7 = F + 32 := by
  have h32m : (32 : ℕ) % 2 ^ E.W = 32 := Nat.mod_eq_of_lt h32
  have hF32m : (F + 32) % 2 ^ E.W = F + 32 := Nat.mod_eq_of_lt hF32
  have hA1m : (A + 1) % 2 ^ E.W = A + 1 := Nat.mod_eq_of_lt hA1
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS10 E st).regs d = st.regs d := by
    intro d h1 h2'
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [decPS10, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [Instr.dest?, h2']
    · simp [Instr.dest?, h2']
    · simp [Instr.dest?, h1]
    · simp [Instr.dest?]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_, ?_⟩
  · simp [decPS10, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_add, execInstr_store,
      h14, hA, h2, h32m, hF32m, hA1m]
  · simp [decPS10, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_add, execInstr_store,
      h14, hA, h2, h32m, hF32m, hA1m]
  · simp [decPS10, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_add, execInstr_store,
      h14, hA, h2, h32m, hF32m, hA1m]
/-- **Shape 4** (`decPS11`) `[add r7 r7 r13, add r7 r7 r13, add r7 r7 r2, add r15 r15 r2, st r15 r7]`:
`r7` grows by `2·t + 1`, then the result is stored at `A + 1`. -/
theorem decPS_base_add (E : RAMEnv) (st st0 : RAMState) (P T A : ℕ)
    (keep : DecPSKeep st st0) (h7 : st.regs r7 = P) (h13 : st.regs r13 = T)
    (hA : st.regs r15 = A) (h2 : st.regs r2 = 1)
    (hPT : P + T < 2 ^ E.W) (hPTT : P + T + T < 2 ^ E.W) (hPTT1 : P + T + T + 1 < 2 ^ E.W)
    (hA1 : A + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock decPS11 E st) st0 ∧
      (runBlock decPS11 E st).mem = Function.update st.mem (A + 1) (P + T + T + 1) ∧
      (runBlock decPS11 E st).regs r15 = A + 1 ∧
      (runBlock decPS11 E st).regs r7 = P + T + T + 1 := by
  have h1 : (P + T) % 2 ^ E.W = P + T := Nat.mod_eq_of_lt hPT
  have h2' : (P + T + T) % 2 ^ E.W = P + T + T := Nat.mod_eq_of_lt hPTT
  have h3 : (P + T + T + 1) % 2 ^ E.W = P + T + T + 1 := Nat.mod_eq_of_lt hPTT1
  have h4 : (A + 1) % 2 ^ E.W = A + 1 := Nat.mod_eq_of_lt hA1
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS11 E st).regs d = st.regs d := by
    intro d h5 h6
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [decPS11, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simp [Instr.dest?, h6]
    · simp [Instr.dest?, h6]
    · simp [Instr.dest?, h6]
    · simp [Instr.dest?, h5]
    · simp [Instr.dest?]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_, ?_⟩
  · simp [decPS11, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store,
      h7, h13, hA, h2, h1, h2', h3, h4]
  · simp [decPS11, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store,
      h7, h13, hA, h2, h1, h2', h3, h4]
  · simp [decPS11, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store,
      h7, h13, hA, h2, h1, h2', h3, h4]
/-- **Shape 5** (`decPS12`) `[add r7 r7 r11, add r15 r15 r2, st r15 r7]`: `r7` grows by `2^L`, then
the result is stored at `A + 1`. -/
theorem decPS_base_addL (E : RAMEnv) (st st0 : RAMState) (P Q A : ℕ)
    (keep : DecPSKeep st st0) (h7 : st.regs r7 = P) (h11 : st.regs r11 = Q)
    (hA : st.regs r15 = A) (h2 : st.regs r2 = 1)
    (hPQ : P + Q < 2 ^ E.W) (hA1 : A + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock decPS12 E st) st0 ∧
      (runBlock decPS12 E st).mem = Function.update st.mem (A + 1) (P + Q) ∧
      (runBlock decPS12 E st).regs r15 = A + 1 ∧
      (runBlock decPS12 E st).regs r7 = P + Q := by
  have h1 : (P + Q) % 2 ^ E.W = P + Q := Nat.mod_eq_of_lt hPQ
  have hA1m : (A + 1) % 2 ^ E.W = A + 1 := Nat.mod_eq_of_lt hA1
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS12 E st).regs d = st.regs d := by
    intro d h5 h6
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [decPS12, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Instr.dest?, h6]
    · simp [Instr.dest?, h5]
    · simp [Instr.dest?]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_, ?_⟩
  · simp [decPS12, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store, h7, h11, hA, h2,
      h1, hA1m]
  · simp [decPS12, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store, h7, h11, hA, h2,
      h1, hA1m]
  · simp [decPS12, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store, h7, h11, hA, h2,
      h1, hA1m]
/-- **Shape 6** (`decPS15`) `[add r15 r15 r2, st r15 r0]`: the last slot is `r0` at `A + 1`. -/
theorem decPS_last (E : RAMEnv) (st st0 : RAMState) (A V : ℕ)
    (keep : DecPSKeep st st0) (hA : st.regs r15 = A) (h0 : st.regs r0 = V)
    (h2 : st.regs r2 = 1) (hA1 : A + 1 < 2 ^ E.W) :
    DecPSKeep (runBlock decPS15 E st) st0 ∧
      (runBlock decPS15 E st).mem = Function.update st.mem (A + 1) V ∧
      (runBlock decPS15 E st).regs r15 = A + 1 := by
  have hA1m : (A + 1) % 2 ^ E.W = A + 1 := Nat.mod_eq_of_lt hA1
  have hf : ∀ d : Fin 16, r15 ≠ d → r7 ≠ d → (runBlock decPS15 E st).regs d = st.regs d := by
    intro d h1 h2'
    refine runBlock_regs_frame _ E st d ?_
    intro i hi
    simp only [decPS15, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Instr.dest?, h1]
    · simp [Instr.dest?]
  refine ⟨DecPSKeep.step keep hf, ?_, ?_⟩
  · simp [decPS15, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store, hA, h0, h2, hA1m]
  · simp [decPS15, runBlock_cons, runBlock_nil, execInstr_add, execInstr_store, hA, h0, h2, hA1m]
/-- The state after the store half. -/
def decPreState (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) :
    RAMState :=
  runBlock progDecPreS (detEnv (cr23Word N) (cr23DecDet N t C)) (decPreCState N t C s)
/-- **What the store half leaves in memory**: exactly the fifteen slot writes, in order. -/
theorem decPreS_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0) :
    (decPreState N t C s).mem = writeList s.mem (decSlotList N t) := by
  obtain ⟨g2, g3, g4, g8, g9, g10, g11, g13, g14, g0, gmem⟩ :=
    decPreC_data N t hN htN C s h0
  simp only [decPreState, progDecPreS_split]
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set X : RAMState := decPreCState N t C s with hX
  have hb : ∀ c, c ≤ 32 → cr23DecFrame N t + c < 2 ^ cr23Word N :=
    fun c hc => cr23_frame_add_lt_word N t hN htN hc
  have hle : ∀ {a : ℕ}, a ≤ cr23DecFrame N t + 32 + (2 * t + 1) + 2 ^ (cr23Lb N + 1)
      + (2 * t + 1) + 2 ^ (cr23Lb N + 1) + (t + 1) → a < 2 ^ cr23Word N := by
    intro a ha
    refine cr23_lt_word_of_le_end N t hN htN ?_
    rwa [cr23DecEnd_form]
  have hct : decCandBase N t + t < 2 ^ cr23Word N := hle (by simp only [decCandBase]; omega)
  have hctt : decCandBase N t + t + t < 2 ^ cr23Word N := hle (by simp only [decCandBase]; omega)
  have hctt1 : decCandBase N t + t + t + 1 < 2 ^ cr23Word N :=
    hle (by simp only [decCandBase]; omega)
  have hmst : decMstBase N t < 2 ^ cr23Word N :=
    hle (by simp only [decMstBase, decTagBase, decCandBase]; omega)
  have hmt : decMstBase N t + t < 2 ^ cr23Word N :=
    hle (by simp only [decMstBase, decTagBase, decCandBase]; omega)
  have hmtt : decMstBase N t + t + t < 2 ^ cr23Word N :=
    hle (by simp only [decMstBase, decTagBase, decCandBase]; omega)
  have hmtt1 : decMstBase N t + t + t + 1 < 2 ^ cr23Word N :=
    hle (by simp only [decMstBase, decTagBase, decCandBase]; omega)
  have hout : decOutBase N t < 2 ^ cr23Word N :=
    hle (by simp only [decOutBase, decParBase, decMstBase, decTagBase, decCandBase]; omega)
  set Y1 : RAMState := runBlock decPS0 E X with hY1
  set Y2 : RAMState := runBlock decPS1 E Y1 with hY2
  set Y3 : RAMState := runBlock decPS2 E Y2 with hY3
  set Y4 : RAMState := runBlock decPS3 E Y3 with hY4
  set Y5 : RAMState := runBlock decPS4 E Y4 with hY5
  set Y6 : RAMState := runBlock decPS5 E Y5 with hY6
  set Y7 : RAMState := runBlock decPS6 E Y6 with hY7
  set Y8 : RAMState := runBlock decPS7 E Y7 with hY8
  set Y9 : RAMState := runBlock decPS8 E Y8 with hY9
  set Y10 : RAMState := runBlock decPS9 E Y9 with hY10
  set Y11 : RAMState := runBlock decPS10 E Y10 with hY11
  set Y12 : RAMState := runBlock decPS11 E Y11 with hY12
  set Y13 : RAMState := runBlock decPS12 E Y12 with hY13
  set Y14 : RAMState := runBlock decPS11 E Y13 with hY14
  set Y15 : RAMState := runBlock decPS12 E Y14 with hY15
  set Y16 : RAMState := runBlock decPS15 E Y15 with hY16
  obtain ⟨K1, a1, m1⟩ := decPS0_spec E X X (cr23DecFrame N t) (DecPSKeep.refl X) g14 g2
    (cr23DecFrame_lt_word N t hN htN) (hb 1 (by norm_num))
  have h15_1 : Y1.regs r15 = decSlot N t 0 := a1
  obtain ⟨K2, m2, a2⟩ := decPS_st_store_add E Y1 X r3 (decSlot N t 0) (cr23D N) K1 h15_1
    (K1.k3.trans g3) (K1.k2.trans g2) (hb 2 (by norm_num))
  have h15_2 : Y2.regs r15 = decSlot N t 1 := a2
  obtain ⟨K3, m3, a3⟩ := decPS_st_store_add E Y2 X r4 (decSlot N t 1) N K2 h15_2
    (K2.k4.trans g4) (K2.k2.trans g2) (hb 3 (by norm_num))
  have h15_3 : Y3.regs r15 = decSlot N t 2 := a3
  obtain ⟨K4, m4, a4⟩ := decPS_st_store_add E Y3 X r8 (decSlot N t 2) (cr23M t) K3 h15_3
    (K3.k8.trans g8) (K3.k2.trans g2) (hb 4 (by norm_num))
  have h15_4 : Y4.regs r15 = decSlot N t 3 := a4
  obtain ⟨K5, m5, a5⟩ := decPS_st_store_add E Y4 X r9 (decSlot N t 3) (cr23Lb N + 1) K4 h15_4
    (K4.k9.trans g9) (K4.k2.trans g2) (hb 5 (by norm_num))
  have h15_5 : Y5.regs r15 = decSlot N t 4 := a5
  obtain ⟨K6, m6, a6⟩ := decPS_st_store_add E Y5 X r10 (decSlot N t 4) (cr23Lb N) K5 h15_5
    (K5.k10.trans g10) (K5.k2.trans g2) (hb 6 (by norm_num))
  have h15_6 : Y6.regs r15 = decSlot N t 5 := a6
  obtain ⟨K7, m7, a7⟩ := decPS_st_store_add E Y6 X r11 (decSlot N t 5) (2 ^ (cr23Lb N + 1)) K6
    h15_6 (K6.k11.trans g11) (K6.k2.trans g2) (hb 7 (by norm_num))
  have h15_7 : Y7.regs r15 = decSlot N t 6 := a7
  obtain ⟨K8, m8, a8⟩ := decPS_st_store_add E Y7 X r13 (decSlot N t 6) t K7 h15_7
    (K7.k13.trans g13) (K7.k2.trans g2) (hb 8 (by norm_num))
  have h15_8 : Y8.regs r15 = decSlot N t 7 := a8
  obtain ⟨K9, m9, a9⟩ := decPS_st_store_add E Y8 X r13 (decSlot N t 7) t K8 h15_8
    (K8.k13.trans g13) (K8.k2.trans g2) (hb 9 (by norm_num))
  have h15_9 : Y9.regs r15 = decSlot N t 8 := a9
  obtain ⟨K10, m10, a10⟩ := decPS_st_only E Y9 X (decSlot N t 8) 1 K9 h15_9 (K9.k2.trans g2)
  have h15_10 : Y10.regs r15 = decSlot N t 8 := a10
  obtain ⟨K11, m11, a11, b11⟩ := decPS_base32 E Y10 X (cr23DecFrame N t) (decSlot N t 8) K10
    (K10.k14.trans g14) h15_10 (K10.k2.trans g2)
    (cr23_lt_word_of_exp N hN (e := 5) (by omega) (by norm_num)) (hb 32 (by norm_num))
    (hb 10 (by norm_num))
  have h15_11 : Y11.regs r15 = decSlot N t 9 := a11
  have h7_11 : Y11.regs r7 = decCandBase N t := b11
  obtain ⟨K12, m12, a12, b12⟩ := decPS_base_add E Y11 X (decCandBase N t) t (decSlot N t 9) K11
    h7_11 (K11.k13.trans g13) h15_11 (K11.k2.trans g2) hct hctt hctt1 (hb 11 (by norm_num))
  have h15_12 : Y12.regs r15 = decSlot N t 10 := a12
  have h7_12 : Y12.regs r7 = decTagBase N t := by
    rw [b12, show decCandBase N t + t + t + 1 = decTagBase N t by
      simp only [decTagBase]; ring]
  obtain ⟨K13, m13, a13, b13⟩ := decPS_base_addL E Y12 X (decTagBase N t) (2 ^ (cr23Lb N + 1))
    (decSlot N t 10) K12 h7_12 (K12.k11.trans g11) h15_12 (K12.k2.trans g2) hmst (hb 12 (by norm_num))
  have h15_13 : Y13.regs r15 = decSlot N t 11 := a13
  have h7_13 : Y13.regs r7 = decMstBase N t := b13
  obtain ⟨K14, m14, a14, b14⟩ := decPS_base_add E Y13 X (decMstBase N t) t (decSlot N t 11) K13
    h7_13 (K13.k13.trans g13) h15_13 (K13.k2.trans g2) hmt hmtt hmtt1 (hb 13 (by norm_num))
  have h15_14 : Y14.regs r15 = decSlot N t 12 := a14
  have h7_14 : Y14.regs r7 = decParBase N t := by
    rw [b14, show decMstBase N t + t + t + 1 = decParBase N t by
      simp only [decParBase]; ring]
  obtain ⟨K15, m15, a15, b15⟩ := decPS_base_addL E Y14 X (decParBase N t) (2 ^ (cr23Lb N + 1))
    (decSlot N t 12) K14 h7_14 (K14.k11.trans g11) h15_14 (K14.k2.trans g2) hout (hb 14 (by norm_num))
  have h15_15 : Y15.regs r15 = decSlot N t 13 := a15
  obtain ⟨K16, m16, a16⟩ := decPS_last E Y15 X (decSlot N t 13) 0 K15 h15_15
    (K15.k0.trans g0) (K15.k2.trans g2) (hb 15 (by norm_num))
  have n1 : Y1.mem = X.mem := m1
  have n2 : Y2.mem = Function.update Y1.mem (decSlot N t 0) (decSlotVal N t 0) := m2
  have n3 : Y3.mem = Function.update Y2.mem (decSlot N t 1) (decSlotVal N t 1) := m3
  have n4 : Y4.mem = Function.update Y3.mem (decSlot N t 2) (decSlotVal N t 2) := m4
  have n5 : Y5.mem = Function.update Y4.mem (decSlot N t 3) (decSlotVal N t 3) := m5
  have n6 : Y6.mem = Function.update Y5.mem (decSlot N t 4) (decSlotVal N t 4) := m6
  have n7 : Y7.mem = Function.update Y6.mem (decSlot N t 5) (decSlotVal N t 5) := m7
  have n8 : Y8.mem = Function.update Y7.mem (decSlot N t 6) (decSlotVal N t 6) := m8
  have n9 : Y9.mem = Function.update Y8.mem (decSlot N t 7) (decSlotVal N t 7) := m9
  have n10 : Y10.mem = Function.update Y9.mem (decSlot N t 8) (decSlotVal N t 8) := m10
  have n11 : Y11.mem = Function.update Y10.mem (decSlot N t 9) (decSlotVal N t 9) := m11
  have n12 : Y12.mem = Function.update Y11.mem (decSlot N t 10) (decSlotVal N t 10) := by
    rw [m12, show decCandBase N t + t + t + 1 = decTagBase N t by
      simp only [decTagBase]; ring]
    rfl
  have n13 : Y13.mem = Function.update Y12.mem (decSlot N t 11) (decSlotVal N t 11) := m13
  have n14 : Y14.mem = Function.update Y13.mem (decSlot N t 12) (decSlotVal N t 12) := by
    rw [m14, show decMstBase N t + t + t + 1 = decParBase N t by
      simp only [decParBase]; ring]
    rfl
  have n15 : Y15.mem = Function.update Y14.mem (decSlot N t 13) (decSlotVal N t 13) := m15
  have n16 : Y16.mem = Function.update Y15.mem (decSlot N t 14) (decSlotVal N t 14) := m16
  have hcode : runBlock (decPS0 ++ decPS1 ++ decPS2 ++ decPS3 ++ decPS4 ++ decPS5 ++ decPS6 ++
      decPS7 ++ decPS8 ++ decPS9 ++ decPS10 ++ decPS11 ++ decPS12 ++ decPS11 ++ decPS12 ++
      decPS15) E X = Y16 := by
    simp only [runBlock_append]
    rw [← hY1, ← hY2, ← hY3, ← hY4, ← hY5, ← hY6, ← hY7, ← hY8, ← hY9, ← hY10, ← hY11,
      ← hY12, ← hY13, ← hY14, ← hY15, ← hY16]
  rw [← gmem, hcode, n16, n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1]
  rfl
/-- **The decoder's 19-clause invariant.**  `z` is the residual vector (the payload holds its
syndrome), `w` the current bound on `|supp z|`, `tag` the round tag, `mstLen` the length of the
master list, `P` the emitted parity set and `mst` the master list itself. -/
def DecData (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w tag mstLen : ℕ) (P : Finset (Fin N)) (mst : List ℕ) (s : RAMState) : Prop :=
  s.mem (decSlot N t 0) = cr23D N ∧
  s.mem (decSlot N t 1) = N ∧
  s.mem (decSlot N t 2) = cr23M t ∧
  s.mem (decSlot N t 3) = cr23Lb N + 1 ∧
  s.mem (decSlot N t 4) = cr23Lb N ∧
  s.mem (decSlot N t 5) = 2 ^ (cr23Lb N + 1) ∧
  s.mem (decSlot N t 6) = t ∧
  s.mem (decSlot N t 7) = w ∧
  s.mem (decSlot N t 8) = tag ∧
  s.mem (decSlot N t 9) = decCandBase N t ∧
  s.mem (decSlot N t 10) = decTagBase N t ∧
  s.mem (decSlot N t 11) = decMstBase N t ∧
  s.mem (decSlot N t 12) = decParBase N t ∧
  s.mem (decSlot N t 13) = decOutBase N t ∧
  s.mem (decSlot N t 14) = mstLen ∧
  (∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C z) a) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → s.mem (decTagBase N t + v) < tag) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) →
      (s.mem (decParBase N t + v) = 1 ↔ ∃ i : Fin N, i.val = v ∧ i ∈ P)) ∧
  (∀ i, i < mstLen → s.mem (decMstBase N t + i) = mst.getD i 0)
/-- **The prologue establishes the invariant**: `DecData` at `w = t`, `tag = 1`, `mstLen = 0`, the
emitted set empty and the master list empty — the interface the round loop consumes. -/
theorem decPrepare (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (s : RAMState)
    (h0 : s.regs r0 = 0)
    (hpay : ∀ a < wordsOf (cr23Word N) (cr23R N t),
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → s.mem a = 0) :
    DecData N t C x t 1 0 ∅ [] (decPreState N t C s) := by
  have hmem := decPreS_data N t hN htN C s h0
  have hnod := decSlotList_keys_nodup N t
  have hget : ∀ k < 15, (decPreState N t C s).mem (decSlot N t k) = decSlotVal N t k := by
    intro k hk
    rw [hmem]
    exact writeList_get s.mem (decSlotList N t) (decSlot N t k) (decSlotVal N t k) hnod
      (decSlotList_mem N t hk)
  have hout : ∀ a, (∀ k < 15, a ≠ decSlot N t k) →
      (decPreState N t C s).mem a = s.mem a := by
    intro a ha
    rw [hmem]
    refine writeList_out s.mem (decSlotList N t) a (fun p hp hpa => ?_)
    rw [decSlotList] at hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ha k (List.mem_range.mp hk) hpa.symm
  refine ⟨hget 0 (by norm_num), hget 1 (by norm_num), hget 2 (by norm_num), hget 3 (by norm_num),
    hget 4 (by norm_num), hget 5 (by norm_num), hget 6 (by norm_num), hget 7 (by norm_num),
    hget 8 (by norm_num), hget 9 (by norm_num), hget 10 (by norm_num), hget 11 (by norm_num),
    hget 12 (by norm_num), hget 13 (by norm_num), hget 14 (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro a ha
    have houta : (decPreState N t C s).mem a = s.mem a := by
      refine hout a (fun k hk => ?_)
      have h1 : a < cr23DecFrame N t := lt_of_lt_of_le ha (cr23_wordsOf_le_frame N t hN)
      simp only [decSlot]
      omega
    rw [houta]
    exact hpay a ha
  · intro v _
    have hz : s.mem (decTagBase N t + v) = 0 :=
      hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
        (le_trans (decFrame_le_tagBase N t) (dec_le_add_self _ v)))
    have houta : (decPreState N t C s).mem (decTagBase N t + v)
        = s.mem (decTagBase N t + v) := by
      refine hout _ (fun k hk => ?_)
      exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
        (le_trans (decCandBase_le_tagBase N t) (dec_le_add_self _ v)))
    rw [houta, hz]
    omega
  · intro v _
    have hz : s.mem (decParBase N t + v) = 0 :=
      hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
        (le_trans (decFrame_le_parBase N t) (dec_le_add_self _ v)))
    have houta : (decPreState N t C s).mem (decParBase N t + v)
        = s.mem (decParBase N t + v) := by
      refine hout _ (fun k hk => ?_)
      exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
        (le_trans (decCandBase_le_tagBase N t)
          (le_trans (decTagBase_le_mstBase N t)
            (le_trans (decMstBase_le_parBase N t) (dec_le_add_self _ v)))))
    rw [houta, hz]
    simp
  · intro i hi
    omega
/-- **The number of odd buckets of a seed is the sum of its count-parity bits** — the quantity the
seed scan accumulates, and hence the quantity whose maximum over the seeds `cr23_shrink` consumes. -/
theorem cr23OddB_card_eq_sum (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) :
    (cr23OddB C (cr23Supp x) s).card
      = ∑ b : Fin (cr23M t),
          (cr23Sketch N t C x (cr23RowEquiv N t (cr23ParRow N t s b))).val := by
  classical
  rw [← cr23OddB_read]
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl (fun b _ => (zmod2_val _).symm)
/-- `n &&& 1 = n % 2`, the mask the machine applies to extract a bit. -/
theorem dec_nat_and_one (n : ℕ) : n &&& 1 = n % 2 := Nat.and_one_is_mod n
/-- **Low bits only depend on the low bits**: `(n / 2^lb) % 2 = (n % 2^L) / 2^lb % 2` for `lb < L`. -/
theorem dec_div_pow_mod_two (n lb L : ℕ) (h : lb < L) :
    (n / 2 ^ lb) % 2 = (n % 2 ^ L) / 2 ^ lb % 2 := by
  have h2 : 0 < 2 ^ lb := Nat.two_pow_pos lb
  have hL : 2 ^ L = 2 ^ lb * 2 ^ (L - lb) := by
    rw [← pow_add]
    congr 1
    omega
  set K := n / 2 ^ L with hK
  set F := n % 2 ^ L with hF
  have hn : 2 ^ L * K + F = n := by
    rw [hK, hF]
    exact Nat.div_add_mod n (2 ^ L)
  have hmul : 2 ^ L * K = 2 ^ lb * (2 ^ (L - lb) * K) := by
    rw [hL]
    ring
  have hdiv : n / 2 ^ lb = 2 ^ (L - lb) * K + F / 2 ^ lb := by
    conv_lhs => rw [← hn]
    rw [hmul, Nat.mul_add_div h2]
  have hstep : (2 ^ (L - lb) * K + F / 2 ^ lb) % 2 = F / 2 ^ lb % 2 := by
    have hp : 2 ^ (L - lb) * K = 2 * (2 ^ (L - lb - 1) * K) := by
      conv_lhs => rw [show L - lb = L - lb - 1 + 1 from by omega, pow_succ]
      ring
    rw [hp, Nat.add_comm, Nat.add_mul_mod_self_left]
  rw [hdiv, hstep, hF]
/-- The same, with the shift split as `a + lb`. -/
theorem dec_div_pow_mod_two' (n a lb L : ℕ) (h : lb < L) :
    (n / 2 ^ (a + lb)) % 2 = (n / 2 ^ a % 2 ^ L) / 2 ^ lb % 2 := by
  have h1 : n / 2 ^ (a + lb) = n / 2 ^ a / 2 ^ lb := by
    rw [pow_add, Nat.div_div_eq_div_mul]
  rw [h1]
  exact dec_div_pow_mod_two (n / 2 ^ a) lb L h
/-- `1 − z` on the machine: `(1 + 2^W − z) % 2^W`. -/
theorem dec_one_sub (W z : ℕ) (hz : z ≤ 1) (hW : 1 < 2 ^ W) :
    (1 + 2 ^ W - z) % 2 ^ W = 1 - z := by
  have hz' : z = 0 ∨ z = 1 := by omega
  rcases hz' with rfl | rfl
  · rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hW, Nat.sub_zero]
  · have h : 1 + 2 ^ W - 1 = 2 ^ W := by omega
    rw [h, Nat.mod_self]
/-- A `0`/`1` valued quantity: the indicator of "equals one" is the quantity. -/
theorem dec_ind_eq (bit : ℕ → ℕ) {j : ℕ} (hb : bit j ≤ 1) :
    (if bit j = 1 then 1 else 0) = bit j := by
  rcases (by omega : bit j = 0 ∨ bit j = 1) with h | h <;> simp [h]
theorem dec_succ_mod {M : ℕ} (hM : 0 < M) (j : ℕ) : (j + 1) % M = (j % M + 1) % M := by
  have h : M * (j / M) + (j % M + 1) = j + 1 := by
    have := Nat.div_add_mod j M
    omega
  conv_lhs => rw [← h]
  rw [Nat.add_comm (M * (j / M)) (j % M + 1), Nat.add_mul_mod_self_left]
theorem dec_succ_div_lt {M : ℕ} (hM : 0 < M) (j : ℕ) (h : j % M + 1 < M) :
    (j + 1) / M = j / M := by
  have h1 : M * (j / M) + (j % M + 1) = j + 1 := by
    have := Nat.div_add_mod j M
    omega
  conv_lhs => rw [← h1]
  rw [Nat.add_comm (M * (j / M)) (j % M + 1), Nat.add_mul_div_left _ _ hM,
    Nat.div_eq_of_lt h, Nat.zero_add]
theorem dec_succ_div_eq {M : ℕ} (hM : 0 < M) (j : ℕ) (h : j % M + 1 = M) :
    (j + 1) / M = j / M + 1 := by
  have h1 : M * (j / M) + (j % M + 1) = j + 1 := by
    have := Nat.div_add_mod j M
    omega
  conv_lhs => rw [← h1, h]
  rw [Nat.add_comm (M * (j / M)) M, Nat.add_mul_div_left _ _ hM, Nat.div_self hM, Nat.one_add]
/-- `j % M = M − 1` when the next index starts a new seed. -/
theorem dec_mod_of_succ_zero {M : ℕ} (hM : 0 < M) {j : ℕ} (h : (j + 1) % M = 0) :
    j % M = M - 1 := by
  have hmod := dec_succ_mod hM j
  rw [h] at hmod
  by_contra hne
  have hle : j % M + 1 < M := by
    have := Nat.mod_lt j hM
    omega
  rw [Nat.mod_eq_of_lt hle] at hmod
  omega
/-- The complementary case: the seed does not close. -/
theorem dec_mod_of_succ_ne {M : ℕ} (hM : 0 < M) {j : ℕ} (h : (j + 1) % M ≠ 0) :
    j % M + 1 < M := by
  have hmod := dec_succ_mod hM j
  by_contra hge
  have hge' : j % M + 1 = M := by
    have := Nat.mod_lt j hM
    omega
  rw [hge', Nat.mod_self] at hmod
  exact h hmod
theorem dec_succ_div_eq' {M : ℕ} (hM : 0 < M) {j : ℕ} (h : (j + 1) % M = 0) :
    (j + 1) / M = j / M + 1 :=
  dec_succ_div_eq hM j (by rw [dec_mod_of_succ_zero hM h]; omega)
theorem dec_succ_div_lt' {M : ℕ} (hM : 0 < M) {j : ℕ} (h : (j + 1) % M ≠ 0) :
    (j + 1) / M = j / M :=
  dec_succ_div_lt hM j (dec_mod_of_succ_ne hM h)
/-- The bucket countdown `b = M − j % M` steps correctly. -/
theorem dec_b_step {M : ℕ} (hM : 0 < M) (j : ℕ) :
    M - (j + 1) % M = (M - j % M - 1) + (if (j + 1) % M = 0 then 1 else 0) * M := by
  have hlt : j % M < M := Nat.mod_lt _ hM
  by_cases h : (j + 1) % M = 0
  · rw [h, if_pos rfl]
    have hM1 := dec_mod_of_succ_zero hM h
    omega
  · rw [if_neg h, dec_succ_mod hM j, Nat.mod_eq_of_lt (dec_mod_of_succ_ne hM h)]
    omega
/-- `b = 1` exactly when the seed closes. -/
theorem dec_b_eq_one {M : ℕ} (hM : 0 < M) {j : ℕ} (h : (j + 1) % M = 0) :
    M - j % M = 1 := by
  have h1 := dec_mod_of_succ_zero hM h
  have h2 := Nat.mod_lt j hM
  omega
/-- Odd buckets seen so far in the current seed, after `j` checks. -/
def decScanCnt (M : ℕ) (bit : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (j % M), (if bit (M * (j / M) + b) = 1 then 1 else 0)
/-- The load of seed `s`: how many of its buckets are odd. -/
def decScanLoad (M : ℕ) (bit : ℕ → ℕ) (s : ℕ) : ℕ :=
  ∑ b ∈ Finset.range M, (if bit (M * s + b) = 1 then 1 else 0)
/-- One step of the scan: `(cnt, best, bestseed)`. -/
def decScanStep (M : ℕ) (bit : ℕ → ℕ) (j : ℕ) (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if (j + 1) % M = 0 then
    (0, max p.2.1 (p.1 + bit j), if p.2.1 < p.1 + bit j then j / M else p.2.2)
  else (p.1 + bit j, p.2.1, p.2.2)
/-- The scan state after `j` checks. -/
def decScanSt (M : ℕ) (bit : ℕ → ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | (j + 1) => decScanStep M bit j (decScanSt M bit j)
theorem decScanSt_succ (M : ℕ) (bit : ℕ → ℕ) (j : ℕ) :
    decScanSt M bit (j + 1) = decScanStep M bit j (decScanSt M bit j) := rfl
theorem decScanLoad_le (M : ℕ) (bit : ℕ → ℕ) (s : ℕ) : decScanLoad M bit s ≤ M := by
  unfold decScanLoad
  calc ∑ b ∈ Finset.range M, (if bit (M * s + b) = 1 then 1 else 0)
      ≤ ∑ b ∈ Finset.range M, 1 := Finset.sum_le_sum (fun b _ => by split_ifs <;> omega)
    _ = M := by simp
theorem decScanCnt_le {M : ℕ} (hM : 0 < M) (bit : ℕ → ℕ) (j : ℕ) : decScanCnt M bit j ≤ M := by
  unfold decScanCnt
  calc ∑ b ∈ Finset.range (j % M), (if bit (M * (j / M) + b) = 1 then 1 else 0)
      ≤ ∑ b ∈ Finset.range (j % M), 1 := Finset.sum_le_sum (fun b _ => by split_ifs <;> omega)
    _ = j % M := by simp
    _ ≤ M := le_of_lt (Nat.mod_lt _ hM)
theorem decScanCnt_succ_of_mod {M : ℕ} (hM : 0 < M) (bit : ℕ → ℕ) {j : ℕ}
    (h : (j + 1) % M ≠ 0) (hb : bit j ≤ 1) :
    decScanCnt M bit (j + 1) = decScanCnt M bit j + bit j := by
  have hle := dec_mod_of_succ_ne hM h
  have hmod : (j + 1) % M = j % M + 1 := by
    rw [dec_succ_mod hM j, Nat.mod_eq_of_lt hle]
  have hdiv := dec_succ_div_lt' hM h
  unfold decScanCnt
  rw [hmod, hdiv, Finset.sum_range_succ]
  congr 1
  rw [Nat.div_add_mod j M, dec_ind_eq bit hb]
theorem decScanCnt_succ_of_zero {M : ℕ} (hM : 0 < M) (bit : ℕ → ℕ) (j : ℕ)
    (h : (j + 1) % M = 0) : decScanCnt M bit (j + 1) = 0 := by
  unfold decScanCnt
  rw [h]
  simp
/-- In the closing step the load of the finished seed is exactly what the counter holds. -/
theorem decScanLoad_split {M : ℕ} (hM : 0 < M) (bit : ℕ → ℕ) {j : ℕ}
    (h : (j + 1) % M = 0) (hb : bit j ≤ 1) :
    decScanLoad M bit (j / M) = decScanCnt M bit j + bit j := by
  have hr : Finset.range M = Finset.range (j % M + 1) := by
    rw [dec_mod_of_succ_zero hM h]
    congr 1
    have := Nat.mod_lt j hM
    omega
  unfold decScanLoad decScanCnt
  rw [hr, Finset.sum_range_succ]
  congr 1
  rw [Nat.div_add_mod j M, dec_ind_eq bit hb]
/-- The three components of the scan state, one case per branch of the step.  These are what the
program's straight-line body computes, and they avoid any `if`-reduction at the use site. -/
theorem decScanSt_cnt_zero {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M = 0) :
    (decScanSt M bit (j + 1)).1 = 0 := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · simp [h']
  · exact absurd h h'
theorem decScanSt_cnt_succ {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M ≠ 0) :
    (decScanSt M bit (j + 1)).1 = (decScanSt M bit j).1 + bit j := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · exact absurd h' h
  · simp [h']
theorem decScanSt_best_zero {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M = 0) :
    (decScanSt M bit (j + 1)).2.1
      = max (decScanSt M bit j).2.1 ((decScanSt M bit j).1 + bit j) := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · simp [h']
  · exact absurd h h'
theorem decScanSt_best_succ {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M ≠ 0) :
    (decScanSt M bit (j + 1)).2.1 = (decScanSt M bit j).2.1 := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · exact absurd h' h
  · simp [h']
theorem decScanSt_seed_zero {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M = 0) :
    (decScanSt M bit (j + 1)).2.2
      = if (decScanSt M bit j).2.1 < (decScanSt M bit j).1 + bit j then j / M
        else (decScanSt M bit j).2.2 := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · simp [h']
  · exact absurd h h'
theorem decScanSt_seed_succ {M : ℕ} (bit : ℕ → ℕ) {j : ℕ} (h : (j + 1) % M ≠ 0) :
    (decScanSt M bit (j + 1)).2.2 = (decScanSt M bit j).2.2 := by
  rw [decScanSt_succ]
  unfold decScanStep
  by_cases h' : (j + 1) % M = 0
  · exact absurd h' h
  · simp [h']
theorem decScanSt_cnt (M : ℕ) (bit : ℕ → ℕ) (hM : 0 < M) (hb : ∀ j, bit j ≤ 1) :
    ∀ j, (decScanSt M bit j).1 = decScanCnt M bit j := by
  intro j
  induction j with
  | zero => simp [decScanSt, decScanCnt]
  | succ j ih =>
      by_cases h : (j + 1) % M = 0
      · rw [decScanSt_cnt_zero bit h, decScanCnt_succ_of_zero hM bit j h]
      · rw [decScanSt_cnt_succ bit h, decScanCnt_succ_of_mod hM bit h (hb j), ih]
theorem decScanSt_argmax (M : ℕ) (bit : ℕ → ℕ) (hM : 0 < M) (hb : ∀ j, bit j ≤ 1) :
    ∀ j, (∀ s < j / M, decScanLoad M bit s ≤ (decScanSt M bit j).2.1) ∧
      ((decScanSt M bit j).2.2 < j / M ∨ j / M = 0) ∧
      (decScanSt M bit j).2.2 ≤ j / M ∧
      (j / M = 0 → (decScanSt M bit j).2.2 = 0) ∧
      (j / M = 0 → (decScanSt M bit j).2.1 = 0) ∧
      (j / M = 0 ∨ decScanLoad M bit (decScanSt M bit j).2.2 = (decScanSt M bit j).2.1) ∧
      (decScanSt M bit j).2.1 ≤ M := by
  intro j
  induction j with
  | zero =>
      have hz : (decScanSt M bit 0).2.1 = 0 := rfl
      have hz2 : (decScanSt M bit 0).2.2 = 0 := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [Nat.zero_div] at hs
        omega
      · right
        rw [Nat.zero_div]
      · rw [Nat.zero_div]
        exact le_of_eq hz2
      · intro _
        exact hz2
      · intro _
        exact hz
      · exact Or.inl (by rw [Nat.zero_div])
      · rw [hz]
        exact Nat.zero_le M
  | succ j ih =>
      obtain ⟨hA, hB, hBle, hC, hF, hD, hE⟩ := ih
      by_cases hcl : (j + 1) % M = 0
      · have hdiv := dec_succ_div_eq' hM hcl
        rw [decScanSt_best_zero bit hcl, decScanSt_seed_zero bit hcl, hdiv]
        have hload : decScanLoad M bit (j / M) = (decScanSt M bit j).1 + bit j := by
          rw [decScanLoad_split hM bit hcl (hb j), ← decScanSt_cnt M bit hM hb j]
        have hvM : (decScanSt M bit j).1 + bit j ≤ M := by
          rw [← hload]; exact decScanLoad_le M bit (j / M)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro s hs
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with h1 | h1
          · exact le_trans (hA s h1) (le_max_left _ _)
          · rw [h1, ← hload]
            exact le_max_right _ _
        · left
          split_ifs with hltv
          · exact Nat.lt_succ_self _
          · rcases hB with h | h
            · exact lt_trans h (Nat.lt_succ_self _)
            · rw [hC h]
              exact Nat.succ_pos _
        · split_ifs with hltv
          · exact Nat.le_succ _
          · exact le_trans hBle (Nat.le_succ _)
        · intro h0
          exact absurd h0 (Nat.succ_ne_zero _)
        · intro h0
          exact absurd h0 (Nat.succ_ne_zero _)
        · right
          split_ifs with hltv
          · rw [hload]
            exact le_antisymm (le_max_right _ _) (max_le (le_of_lt hltv) (le_refl _))
          · have hm : max (decScanSt M bit j).2.1 ((decScanSt M bit j).1 + bit j)
                = (decScanSt M bit j).2.1 :=
              le_antisymm (max_le (le_refl _) (by omega)) (le_max_left _ _)
            rw [hm]
            rcases hD with hD0 | hD0
            · have hb0 : (decScanSt M bit j).2.1 = 0 := hF hD0
              have hY0 : (decScanSt M bit j).1 + bit j = 0 := by
                have hYX : (decScanSt M bit j).1 + bit j ≤ (decScanSt M bit j).2.1 := by omega
                rw [hF hD0] at hYX
                omega
              have hld : decScanLoad M bit 0 = 0 := by
                conv_lhs => rw [← hD0]
                rw [hload, hY0]
              rw [hC hD0, hb0, hld]
            · exact hD0
        · exact max_le hE hvM
      · have hdiv := dec_succ_div_lt' hM hcl
        rw [decScanSt_best_succ bit hcl, decScanSt_seed_succ bit hcl, hdiv]
        exact ⟨hA, hB, hBle, hC, hF, hD, hE⟩
/-- **The seed scan's result.**  Walking all `D·M` checks makes `best` the maximum load and leaves in
`bestseed` a seed attaining it. -/
theorem decScanSt_final (M : ℕ) (bit : ℕ → ℕ) (hM : 0 < M) (hb : ∀ j, bit j ≤ 1) (D : ℕ)
    (hD : 0 < D) :
    (∀ s < D, decScanLoad M bit s ≤ (decScanSt M bit (D * M)).2.1) ∧
      (decScanSt M bit (D * M)).2.2 < D ∧
      decScanLoad M bit (decScanSt M bit (D * M)).2.2 = (decScanSt M bit (D * M)).2.1 ∧
      (decScanSt M bit (D * M)).2.1 ≤ M := by
  obtain ⟨hA, hB, hBle, hC, hF, hD', hE⟩ := decScanSt_argmax M bit hM hb (D * M)
  have hdiv : D * M / M = D := Nat.mul_div_left D hM
  rw [hdiv] at hA hB hBle hC hF hD'
  refine ⟨hA, ?_, ?_, hE⟩
  · rcases hB with h | h
    · exact h
    · omega
  · rcases hD' with h | h
    · omega
    · exact h
/-- The count-parity bit of check `q`, read as one integer. -/
def decBit (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (q : ℕ) : ℕ :=
  cr23CheckField N t (cr23Sketch N t C z) q / 2 ^ cr23Lb N % 2
theorem decBit_le_one (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (z : Fin N → ZMod 2) (q : ℕ) : decBit N t C z q ≤ 1 := by
  unfold decBit
  have := Nat.mod_lt (cr23CheckField N t (cr23Sketch N t C z) q / 2 ^ cr23Lb N)
    (by norm_num : 0 < 2)
  omega
/-- **The machine's shift-and-mask reads exactly `decBit`**: one `ld` plus a shift and a mask. -/
theorem decBit_read (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (z : Fin N → ZMod 2) (q : ℕ) (hq : q < cr23D N * cr23M t) :
    (packMem (cr23Word N) (cr23Sketch N t C z) (q / 1024)
        / 2 ^ ((q % 1024) * (cr23Lb N + 1) + cr23Lb N)) % 2
      = decBit N t C z q := by
  rw [dec_div_pow_mod_two' (packMem (cr23Word N) (cr23Sketch N t C z) (q / 1024))
    ((q % 1024) * (cr23Lb N + 1)) (cr23Lb N) (cr23Lb N + 1) (by omega)]
  rw [cr23CheckField_read N t (cr23Sketch N t C z) q hq]
  rfl
/-- `decBit` of a check is the count-parity row of that check. -/
theorem decBit_eq_check (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (z : Fin N → ZMod 2) (s : Fin (cr23D N)) (b : Fin (cr23M t)) :
    decBit N t C z (cr23Check N t s b)
      = (cr23Sketch N t C z (cr23RowEquiv N t (cr23ParRow N t s b))).val := by
  unfold decBit
  exact cr23CheckField_div N t C z s b
/-- The bucket count `M = 4096·t` is positive. -/
theorem decScanM_pos {t : ℕ} (ht : 1 ≤ t) : 0 < cr23M t := by
  simp only [cr23M]
  omega
theorem decScanLoad_eq_oddB (N t : ℕ) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (s : ℕ)
    (h : s < cr23D N) :
    (cr23OddB C (cr23Supp z) ⟨s, h⟩).card
      = decScanLoad (cr23M t) (decBit N t C z) s := by
  have hM : 0 < cr23M t := decScanM_pos ht
  rw [cr23OddB_card_eq_sum N t C z ⟨s, h⟩]
  unfold decScanLoad
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if decBit N t C z (cr23M t * s + i) = 1 then 1 else 0) (cr23M t)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hck : cr23M t * s + b.val = cr23Check N t ⟨s, h⟩ b := by
    simp only [cr23Check]
    ring
  rw [hck, decBit_eq_check]
  split_ifs with hv
  · exact hv
  · have := ZMod.val_lt (cr23Sketch N t C z (cr23RowEquiv N t (cr23ParRow N t ⟨s, h⟩ b)))
    omega
/-- **Body (a), end to end.**  The `D·M`-step scan computes the maximum load over all seeds, and the
seed it records attains that maximum: the two facts the candidate step (body (b)) and
`cr23_shrink` consume. -/
theorem decScan_correct (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) :
    ((∀ s : Fin (cr23D N),
        (cr23OddB C (cr23Supp z) s).card
          ≤ (decScanSt (cr23M t) (decBit N t C z) (cr23D N * cr23M t)).2.1) ∧
      ∃ s : Fin (cr23D N),
        (decScanSt (cr23M t) (decBit N t C z) (cr23D N * cr23M t)).2.2 = s.val ∧
        (cr23OddB C (cr23Supp z) s).card
          = (decScanSt (cr23M t) (decBit N t C z) (cr23D N * cr23M t)).2.1) := by
  obtain ⟨hA, hB, hC, hE⟩ := decScanSt_final (cr23M t) (decBit N t C z) (decScanM_pos ht)
    (fun j => decBit_le_one N t C z j) (cr23D N) (cr23D_pos N hN)
  refine ⟨fun s => ?_, ⟨⟨_, hB⟩, rfl, ?_⟩⟩
  · rw [decScanLoad_eq_oddB N t ht C z s.val s.isLt]
    exact hA s.val s.isLt
  · rw [decScanLoad_eq_oddB N t ht C z _ hB]
    exact hC
theorem decScanBody_split :
    decScanBody
      = decScanBA ++ decScanBB ++ decScanBC ++ decScanBD ++ decScanBE ++ decScanBF ++ decScanBG :=
  rfl
theorem decScanBA_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBA E st).mem = st.mem := by
  simp [decScanBA]
theorem decScanBA_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r15) : (runBlock decScanBA E st).regs d = st.regs d := by
  simp [decScanBA, hd, hd2]
theorem decScanBB_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBB E st).mem = st.mem := by
  simp [decScanBB]
theorem decScanBB_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r2) : (runBlock decScanBB E st).regs d = st.regs d := by
  simp [decScanBB, hd, hd2]
theorem decScanBC_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBC E st).mem = st.mem := by
  simp [decScanBC]
theorem decScanBC_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r15) : (runBlock decScanBC E st).regs d = st.regs d := by
  simp [decScanBC, hd, hd2]
theorem decScanBD_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBD E st).mem = st.mem := by
  simp [decScanBD]
theorem decScanBD_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r4) : (runBlock decScanBD E st).regs d = st.regs d := by
  simp [decScanBD, hd, hd2]
theorem decScanBE_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBE E st).mem = st.mem := by
  simp [decScanBE]
theorem decScanBE_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r3) : (runBlock decScanBE E st).regs d = st.regs d := by
  simp [decScanBE, hd, hd2]
theorem decScanBF_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBF E st).mem = st.mem := by
  simp [decScanBF]
theorem decScanBF_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r13)
    (hd2 : d ≠ r15) (hd3 : d ≠ r5) : (runBlock decScanBF E st).regs d = st.regs d := by
  simp [decScanBF, hd, hd2, hd3]
theorem decScanBG_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decScanBG E st).mem = st.mem := by
  simp [decScanBG]
theorem decScanBG_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (hd : d ≠ r2)
    (hd2 : d ≠ r15) (hd3 : d ≠ r6) (hd4 : d ≠ r0) :
    (runBlock decScanBG E st).regs d = st.regs d := by
  simp [decScanBG, hd, hd2, hd3, hd4]
theorem dec_two_dvd_pow (W : ℕ) (hW : 1 ≤ W) : 2 ∣ 2 ^ W := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hW
  exact ⟨2 ^ k, by rw [pow_add, pow_one, Nat.mul_comm]⟩
theorem dec_mod_pow_two (W n : ℕ) (hW : 1 ≤ W) : n % 2 ^ W % 2 = n % 2 :=
  Nat.mod_mod_of_dvd n (dec_two_dvd_pow W hW)
theorem dec_sub_mach (W a b : ℕ) (hba : b ≤ a) (ha : a < 2 ^ W) :
    (a + 2 ^ W - b) % 2 ^ W = a - b := by
  have h : a + 2 ^ W - b = (a - b) + 2 ^ W := by omega
  rw [h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)
theorem dec_one_le_of_one_lt_pow {W : ℕ} (h : 1 < 2 ^ W) : 1 ≤ W := by
  rcases Nat.eq_zero_or_pos W with h0 | h0
  · rw [h0] at h; exact absurd h (by norm_num)
  · exact h0
/-- **The close indicator.**  If `b = M − j % M` is the countdown, then `1 − (1 < b)` is `1` exactly
when the seed closes. -/
theorem decScanClose_ind (W M : ℕ) (hM : 0 < M) (hW : 1 < 2 ^ W) (j : ℕ) :
    (1 + 2 ^ W - (if 1 < M - j % M then 1 else 0) % 2 ^ W) % 2 ^ W
      = (if (j + 1) % M = 0 then 1 else 0) := by
  by_cases h : (j + 1) % M = 0
  · have hb : M - j % M = 1 := dec_b_eq_one hM h
    have hif : (if 1 < M - j % M then 1 else 0) % 2 ^ W = 0 := by
      rw [hb, if_neg (by omega : ¬ (1 < 1)), Nat.zero_mod]
    have hgz : (if (j + 1) % M = 0 then (1 : ℕ) else 0) = 1 := if_pos h
    rw [hif, Nat.sub_zero, hgz]
    simpa using dec_one_sub W 0 (by omega) hW
  · have hb2 : 1 < M - j % M := by
      have h1 := dec_mod_of_succ_ne hM h
      have h2 := Nat.mod_lt j hM
      omega
    have hif : (if 1 < M - j % M then 1 else 0) % 2 ^ W = 1 := by
      rw [if_pos hb2, Nat.mod_eq_of_lt hW]
    have hgz : (if (j + 1) % M = 0 then (1 : ℕ) else 0) = 0 := if_neg h
    rw [hif, hgz]
    simpa using dec_one_sub W 1 (by omega) hW
/-- The branchless `max`: with `gg = (a < v)·zc`, the fold `a + gg·(v − a)` is `max a v` exactly
when the seed closes (`zc = 1`), and `a` otherwise. -/
theorem decMax_full (W a v gg zc : ℕ) (hW : 1 < 2 ^ W) (ha : a < 2 ^ W) (hv : v < 2 ^ W)
    (hz : zc ≤ 1)
    (hgg : gg = (if a < v then 1 else 0) * zc % 2 ^ W) :
    (a + (v + 2 ^ W - a) % 2 ^ W * gg) % 2 ^ W = if zc = 1 then max a v else a := by
  by_cases hz1 : zc = 1
  · rw [if_pos hz1]
    have hgg1 : gg = (if a < v then 1 else 0) := by
      rw [hgg, hz1, Nat.mul_one]
      split_ifs with h
      · exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 ^ W)
      · exact Nat.zero_mod _
    rw [hgg1]
    by_cases h : a < v
    · rw [if_pos h, Nat.mul_one, dec_sub_mach W v a (le_of_lt h) hv,
        Nat.add_sub_of_le (le_of_lt h), Nat.mod_eq_of_lt hv, max_eq_right (le_of_lt h)]
    · rw [if_neg h, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt ha, max_eq_left (by omega)]
  · rw [if_neg hz1]
    have hz0 : zc = 0 := by omega
    have hgg0 : gg = 0 := by rw [hgg, hz0, Nat.mul_zero, Nat.zero_mod]
    rw [hgg0, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt ha]
/-- The branchless select: with `gg = (best < cnt)·zc`, `y + gg·(s − y)` is `s` when the seed closes
and the comparison holds, and `y` otherwise. -/
theorem decSel_full (W best cnt s y gg zc : ℕ) (hW : 1 < 2 ^ W) (hy : y ≤ s) (hs : s < 2 ^ W)
    (hz : zc ≤ 1)
    (hgg : gg = (if best < cnt then 1 else 0) * zc % 2 ^ W) :
    (y + (s + 2 ^ W - y) % 2 ^ W * gg) % 2 ^ W
      = if zc = 1 then (if best < cnt then s else y) else y := by
  by_cases hz1 : zc = 1
  · rw [if_pos hz1]
    have hgg1 : gg = (if best < cnt then 1 else 0) := by
      rw [hgg, hz1, Nat.mul_one]
      split_ifs with h
      · exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 ^ W)
      · exact Nat.zero_mod _
    rw [hgg1, dec_sub_mach W s y hy hs]
    by_cases h : best < cnt
    · rw [if_pos h, if_pos h, Nat.mul_one, Nat.add_sub_of_le hy, Nat.mod_eq_of_lt hs]
    · rw [if_neg h, if_neg h, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hz1]
    have hz0 : zc = 0 := by omega
    have hgg0 : gg = 0 := by rw [hgg, hz0, Nat.mul_zero, Nat.zero_mod]
    rw [hgg0, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
/-- `cnt := cnt·(1 − zc)`: the counter reset. -/
theorem decCnt_branch (W cnt zc : ℕ) (hz : zc ≤ 1) (hc : cnt < 2 ^ W) :
    cnt * (1 - zc) % 2 ^ W = if zc = 1 then 0 else cnt := by
  by_cases h : zc = 1
  · rw [if_pos h, h, Nat.sub_self, Nat.mul_zero, Nat.zero_mod]
  · rw [if_neg h]
    have h0 : zc = 0 := by omega
    rw [h0, Nat.sub_zero, Nat.mul_one, Nat.mod_eq_of_lt hc]
theorem decScanBA_spec (E : RAMEnv) (st : RAMState) (q L lb : ℕ)
    (h0 : st.regs r0 = q) (h8 : st.regs r8 = L) (h10 : st.regs r10 = lb)
    (h12 : st.regs r12 = 1024) (hqW : q < 2 ^ E.W) (hq1024 : q % 1024 < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hlb : lb < 2 ^ E.W) (hoff : (q % 1024) * L + lb < 2 ^ E.W) :
    (runBlock decScanBA E st).regs r13 = st.mem (q / 1024) % 2 ^ E.W ∧
      (runBlock decScanBA E st).regs r15 = (q % 1024) * L + lb := by
  have hmul : (q % 1024) * L < 2 ^ E.W := lt_of_le_of_lt (Nat.le_add_right _ lb) hoff
  have hqw : q / 1024 < 2 ^ E.W := lt_of_le_of_lt (Nat.div_le_self _ _) hqW
  have hmem : st.mem (q / 1024 % 2 ^ E.W) = st.mem (q / 1024) := by
    rw [Nat.mod_eq_of_lt hqw]
  refine ⟨?_, ?_⟩
  · simp [decScanBA, h0, h8, h10, h12, hmem]
  · simp [decScanBA, h0, h8, h10, h12, Nat.mod_eq_of_lt hq1024, Nat.mod_eq_of_lt hL,
      Nat.mod_eq_of_lt hlb, Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hoff]
theorem decScanBB_spec (E : RAMEnv) (st : RAMState) (word off cnt : ℕ)
    (h13 : st.regs r13 = word) (h15 : st.regs r15 = off) (h11 : st.regs r11 = 1)
    (h2 : st.regs r2 = cnt) (hW : 1 < 2 ^ E.W)
    (hcnt : cnt + word / 2 ^ off % 2 < 2 ^ E.W) :
    (runBlock decScanBB E st).regs r13 = word / 2 ^ off % 2 ∧
      (runBlock decScanBB E st).regs r2 = cnt + word / 2 ^ off % 2 := by
  have hW1 : 1 ≤ E.W := dec_one_le_of_one_lt_pow hW
  have hlt : word / 2 ^ off % 2 < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2)) (by omega)
  refine ⟨?_, ?_⟩
  · simp [decScanBB, h13, h15, h11, h2, dec_nat_and_one,
      dec_mod_pow_two E.W (word / 2 ^ off) hW1, Nat.mod_eq_of_lt hlt]
  · simp [decScanBB, h13, h15, h11, h2, dec_nat_and_one,
      dec_mod_pow_two E.W (word / 2 ^ off) hW1, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hcnt]
theorem decScanBC_spec (E : RAMEnv) (st : RAMState) (b best cnt zc gg : ℕ)
    (h11 : st.regs r11 = 1) (h6 : st.regs r6 = b) (h3 : st.regs r3 = best)
    (h2 : st.regs r2 = cnt) (hW : 1 < 2 ^ E.W)
    (hz : zc = (1 + 2 ^ E.W - (if 1 < b then 1 else 0) % 2 ^ E.W) % 2 ^ E.W)
    (hg : gg = ((if best < cnt then 1 else 0) * zc) % 2 ^ E.W) :
    (runBlock decScanBC E st).regs r13 = zc ∧ (runBlock decScanBC E st).regs r15 = gg := by
  have hz' : (1 + 2 ^ E.W - (if 1 < b then 1 else 0) % 2 ^ E.W) % 2 ^ E.W = zc := hz.symm
  have hgv : (if best < cnt then 1 else 0) % 2 ^ E.W = (if best < cnt then 1 else 0) := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 ^ E.W)
    · exact Nat.zero_mod _
  have hg' : ((if best < cnt then 1 else 0) % 2 ^ E.W * zc) % 2 ^ E.W = gg := by
    rw [hgv]; exact hg.symm
  refine ⟨?_, ?_⟩
  · simp [decScanBC, h11, h6, h3, h2, hz']
  · simp [decScanBC, h11, h6, h3, h2, hz', hg']
theorem decScanBD_spec (E : RAMEnv) (st : RAMState) (s bestseed gg : ℕ)
    (h5 : st.regs r5 = s) (h4 : st.regs r4 = bestseed) (h15 : st.regs r15 = gg)
    (hW : 1 < 2 ^ E.W) (hgg : gg ≤ 1) :
    (runBlock decScanBD E st).regs r4
        = (bestseed + (s + 2 ^ E.W - bestseed) % 2 ^ E.W * gg) % 2 ^ E.W ∧
      (runBlock decScanBD E st).regs r13 = (s + 2 ^ E.W - bestseed) % 2 ^ E.W * gg := by
  have hdm : (s + 2 ^ E.W - bestseed) % 2 ^ E.W < 2 ^ E.W := Nat.mod_lt _ (by omega)
  have hmul : (s + 2 ^ E.W - bestseed) % 2 ^ E.W * gg < 2 ^ E.W := by
    have h1 : (s + 2 ^ E.W - bestseed) % 2 ^ E.W * gg
        ≤ (s + 2 ^ E.W - bestseed) % 2 ^ E.W * 1 := Nat.mul_le_mul_left _ hgg
    rw [Nat.mul_one] at h1
    omega
  refine ⟨?_, ?_⟩
  · simp [decScanBD, h5, h4, h15, Nat.mod_eq_of_lt hmul]
  · simp [decScanBD, h5, h4, h15, Nat.mod_eq_of_lt hmul]
theorem decScanBE_spec (E : RAMEnv) (st : RAMState) (best cnt gg : ℕ)
    (h3 : st.regs r3 = best) (h2 : st.regs r2 = cnt) (h15 : st.regs r15 = gg)
    (hW : 1 < 2 ^ E.W) (hgg : gg ≤ 1) :
    (runBlock decScanBE E st).regs r3
        = (best + (cnt + 2 ^ E.W - best) % 2 ^ E.W * gg) % 2 ^ E.W ∧
      (runBlock decScanBE E st).regs r13 = (cnt + 2 ^ E.W - best) % 2 ^ E.W * gg := by
  have hdm : (cnt + 2 ^ E.W - best) % 2 ^ E.W < 2 ^ E.W := Nat.mod_lt _ (by omega)
  have hmul : (cnt + 2 ^ E.W - best) % 2 ^ E.W * gg < 2 ^ E.W := by
    have h1 : (cnt + 2 ^ E.W - best) % 2 ^ E.W * gg
        ≤ (cnt + 2 ^ E.W - best) % 2 ^ E.W * 1 := Nat.mul_le_mul_left _ hgg
    rw [Nat.mul_one] at h1
    omega
  refine ⟨?_, ?_⟩
  · simp [decScanBE, h3, h2, h15, Nat.mod_eq_of_lt hmul]
  · simp [decScanBE, h3, h2, h15, Nat.mod_eq_of_lt hmul]
theorem decScanBF_spec (E : RAMEnv) (st : RAMState) (b s zc : ℕ)
    (h11 : st.regs r11 = 1) (h6 : st.regs r6 = b) (h5 : st.regs r5 = s)
    (hW : 1 < 2 ^ E.W) (hs : s + zc < 2 ^ E.W) (hzc : zc ≤ 1)
    (hz : zc = (1 + 2 ^ E.W - (if 1 < b then 1 else 0) % 2 ^ E.W) % 2 ^ E.W) :
    (runBlock decScanBF E st).regs r5 = s + zc ∧ (runBlock decScanBF E st).regs r13 = zc ∧
      (runBlock decScanBF E st).regs r15 = 1 - zc := by
  have hz' : (1 + 2 ^ E.W - (if 1 < b then 1 else 0) % 2 ^ E.W) % 2 ^ E.W = zc := hz.symm
  refine ⟨?_, ?_, ?_⟩
  · simp [decScanBF, h11, h6, h5, hz', Nat.mod_eq_of_lt hs]
  · simp [decScanBF, h11, h6, h5, hz']
  · simp [decScanBF, h11, h6, h5, hz', dec_one_sub E.W zc hzc hW]
theorem decScanBG_spec (E : RAMEnv) (st : RAMState) (M b cnt q zc : ℕ)
    (h7 : st.regs r7 = M) (h6 : st.regs r6 = b) (h2 : st.regs r2 = cnt)
    (h13 : st.regs r13 = zc) (h15 : st.regs r15 = 1 - zc) (h11 : st.regs r11 = 1)
    (h0 : st.regs r0 = q) (hW : 1 < 2 ^ E.W) (hb1 : 1 ≤ b) (hbb : b ≤ M)
    (hMw : M < 2 ^ E.W)
    (hzc : zc ≤ 1) (hc : cnt < 2 ^ E.W) (hq : q + 1 < 2 ^ E.W)
    (hbM : b - 1 + zc * M < 2 ^ E.W) :
    (runBlock decScanBG E st).regs r2 = (if zc = 1 then 0 else cnt) ∧
      (runBlock decScanBG E st).regs r6 = b - 1 + zc * M ∧
      (runBlock decScanBG E st).regs r0 = q + 1 := by
  have hcnt' : cnt * (1 - zc) % 2 ^ E.W = (if zc = 1 then 0 else cnt) :=
    decCnt_branch E.W cnt zc hzc hc
  have hzcM : zc * M < 2 ^ E.W := by
    rcases Nat.eq_zero_or_pos zc with h0 | h0
    · rw [h0, Nat.zero_mul]
      exact lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hW)
    · have h1 : zc = 1 := by omega
      rw [h1, Nat.one_mul]
      exact hMw
  have hb1' : (b + 2 ^ E.W - 1) % 2 ^ E.W = b - 1 :=
    dec_sub_mach E.W b 1 hb1 (lt_of_le_of_lt hbb hMw)
  refine ⟨?_, ?_, ?_⟩
  · simp [decScanBG, h7, h6, h2, h13, h15, h11, h0, hcnt']
  · simp [decScanBG, h7, h6, h2, h13, h15, h11, h0, hb1', Nat.mod_eq_of_lt hzcM,
      Nat.mod_eq_of_lt hbM]
  · simp [decScanBG, h7, h6, h2, h13, h15, h11, h0, Nat.mod_eq_of_lt hq]
/-- The loop-head invariant of body (a)'s scan.  `m₀` is the (read-only) memory of the round head, so
`DecData` transfers across the whole body by `mem`-congruence alone. -/
def DecScanInv (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w j : ℕ) (m₀ : ℕ → ℕ) (st : RAMState) : Prop :=
  st.mem = m₀ ∧
  st.regs r0 = j ∧
  st.regs r1 = cr23D N * cr23M t ∧
  st.regs r2 = decScanCnt (cr23M t) (decBit N t C z) j ∧
  st.regs r3 = (decScanSt (cr23M t) (decBit N t C z) j).2.1 ∧
  st.regs r4 = (decScanSt (cr23M t) (decBit N t C z) j).2.2 ∧
  st.regs r5 = j / cr23M t ∧
  st.regs r6 = cr23M t - j % cr23M t ∧
  st.regs r7 = cr23M t ∧
  st.regs r8 = cr23Lb N + 1 ∧
  st.regs r10 = cr23Lb N ∧
  st.regs r11 = 1 ∧
  st.regs r12 = 1024 ∧
  st.regs r9 = w ∧
  st.regs r14 = cr23DecFrame N t
/-- The test code of a condition touches no memory. -/
theorem runBlock_cond_mem (c : Cond) (E : RAMEnv) (s : RAMState) :
    (runBlock c.code E s).mem = s.mem := by
  cases c with
  | neqz r => simp [Cond.code]
  | lt d a b => simp [Cond.code, runBlock_cons, runBlock_nil, execInstr_lt]
/-- The test code of a condition writes only its test register. -/
theorem runBlock_cond_regs (c : Cond) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (hd : d ≠ c.test) : (runBlock c.code E s).regs d = s.regs d := by
  cases c with
  | neqz r => simp [Cond.code]
  | lt d' a b =>
      simp only [Cond.code, Cond.test] at hd ⊢
      simp only [Cond.code, runBlock_cons, runBlock_nil, execInstr_lt]
      exact Function.update_of_ne hd _ _
/-- One iteration of a loop with a predicate invariant: the test holds, the body runs back to the
head, and the invariant advances. -/
theorem Sem.loopStepPred (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (s : RAMState) (R : RAMState → Prop) (cost : ℕ)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : s.pc = a) (hgo : c.eval s)
    (hbody : Sem P E (a + c.code.length + 1) a
      { runBlock c.code E s with pc := a + c.code.length + 1 }
      (fun k s'' => k = cost ∧ R s'' ∧ s''.pc = a)) :
    Sem P E a a s (fun k s'' => k = (c.code.length + 1) + cost ∧ R s'' ∧ s''.pc = a) := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hne : (runBlock c.code E s).regs c.test ≠ 0 := (Cond.eval_iff c E s hW).mp hgo
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E s)
      (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + 1 }) :=
    Sem.jz_next P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT hne
  refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = c.code.length + 1 ∧
      s' = { runBlock c.code E s with pc := a + c.code.length + 1 })
    (Q₂ := fun k₁ k₂ s' => k₁ = c.code.length + 1 ∧ k₂ = cost ∧ R s' ∧ s'.pc = a)
    (Sem.trans htest hfall) ?_) ?_
  · intro k₁ s₁ hQ₁
    obtain ⟨rfl, rfl⟩ := hQ₁
    exact Sem.mono hbody (fun k s' h => ⟨rfl, h⟩)
  · intro k s' h
    obtain ⟨k₁, k₂, hk, h1, h2, hR, hpc'⟩ := h
    exact ⟨by omega, hR, hpc'⟩
/-- **The loop rule.**  `n` iterations from the loop head, then the failing test.  The iteration
invariant is a predicate family `R : ℕ → RAMState → Prop`, the per-iteration costs are `cost j`, and
`R` must be insensitive to the test register (`hirr`). -/
theorem Sem.loopPred (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (R : ℕ → RAMState → Prop) (cost : ℕ → ℕ),
      (∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ c.test → s.regs d = s'.regs d) →
        s.mem = s'.mem → R j s → R j s') →
      (∀ j, j < n → ∀ s, R j s → c.eval s) →
      (∀ s, R n s → ¬ c.eval s) →
      (∀ j, j < n → ∀ s, s.pc = a → R j s →
        Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
          (fun k s' => k = cost j ∧ R (j + 1) s' ∧ s'.pc = a)) →
      ∀ s, s.pc = a → R 0 s →
        Sem P E a (a + c.code.length + b.len + 2) s
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
            R n s' ∧ s'.pc = a + c.code.length + b.len + 2) := by
  intro n
  induction n with
  | zero =>
      intro R cost hirr hgo hstop hstep s hpc hR
      refine Sem.mono (Sem.loopExit P E a c b s hAt hW hpc (hstop s hR)) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, ?_, rfl⟩
      exact hirr 0 s _ (fun d hd => (runBlock_cond_regs c E s d hd).symm)
        (runBlock_cond_mem c E s).symm hR
  | succ n ih =>
      intro R cost hirr hgo hstop hstep s hpc hR
      have hgo0 : c.eval s := hgo 0 (by omega) s hR
      have hfirst := Sem.loopStepPred P E a c b s (R 1) (cost 0) hAt hW hpc hgo0
        (hstep 0 (by omega) s hpc hR)
      have hirr' : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ c.test → s.regs d = s'.regs d) →
          s.mem = s'.mem → (fun j => R (j + 1)) j s → (fun j => R (j + 1)) j s' :=
        fun j s s' hd hm h => hirr (j + 1) s s' hd hm h
      have hgo' : ∀ j, j < n → ∀ s, (fun j => R (j + 1)) j s → c.eval s :=
        fun j hj s h => hgo (j + 1) (by omega) s h
      have hstop' : ∀ s, (fun j => R (j + 1)) n s → ¬ c.eval s :=
        fun s h => hstop s h
      have hstep' : ∀ j, j < n → ∀ s, s.pc = a → (fun j => R (j + 1)) j s →
          Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
            (fun k s' => k = (fun j => cost (j + 1)) j ∧ (fun j => R (j + 1)) (j + 1) s' ∧
              s'.pc = a) :=
        fun j hj s hp hs => hstep (j + 1) (by omega) s hp hs
      refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = (c.code.length + 1) + cost 0 ∧ R 1 s' ∧
          s'.pc = a)
        (Q₂ := fun k₁ k₂ s' => k₁ = (c.code.length + 1) + cost 0 ∧
          (k₂ ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            R (n + 1) s' ∧ s'.pc = a + c.code.length + b.len + 2)) hfirst ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨rfl, hR1, hpc1⟩ := hQ₁
        exact Sem.mono (ih (fun j => R (j + 1)) (fun j => cost (j + 1)) hirr' hgo' hstop' hstep'
          s₁ hpc1 hR1) (fun k s' h => ⟨rfl, h⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, hk, h1, h2, h3, h4⟩ := h
        rw [Finset.sum_range_succ']
        exact ⟨by omega, h3, h4⟩
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
theorem decScanSt_seed_le (M : ℕ) (bit : ℕ → ℕ) (hM : 0 < M) (hb : ∀ j, bit j ≤ 1) (j : ℕ) :
    (decScanSt M bit j).2.2 ≤ j / M :=
  (decScanSt_argmax M bit hM hb j).2.2.1
theorem decScanSt_best_le (M : ℕ) (bit : ℕ → ℕ) (hM : 0 < M) (hb : ∀ j, bit j ≤ 1) (j : ℕ) :
    (decScanSt M bit j).2.1 ≤ M :=
  (decScanSt_argmax M bit hM hb j).2.2.2.2.2.2
/-- **The 27-instruction body, as a data lemma.**  From the loop-head invariant at `j < D·M` it
produces the invariant at `j+1`; the body writes no memory, so `DecData` transfers by `mem`
congruence. -/
theorem decScanBody_data (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w j : ℕ) (m₀ : ℕ → ℕ) (st : RAMState)
    (hmem : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      m₀ a = packMem (cr23Word N) (cr23Sketch N t C z) a)
    (hR : DecScanInv N t C z w j m₀ st) (hj : j < cr23D N * cr23M t) :
    DecScanInv N t C z w (j + 1) m₀
      (runBlock decScanBody (detEnv (cr23Word N) (cr23DecDet N t C)) st) := by
  obtain ⟨hm, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq10, hq11, hq12, hq9, hq14⟩ := hR
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hW0 : 0 < cr23Word N := cr23Word_pos N
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hDMw : cr23D N * cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23DM_lt_word N t hN htN
  have hMw : cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23M_lt_word N t hN htN
  have hjW : j < 2 ^ E.W := lt_trans hj hDMw
  have hj1W : j + 1 < 2 ^ E.W := by omega
  have hMpos : 0 < cr23M t := decScanM_pos ht
  have hD2 : 2 ≤ cr23D N := by
    have h1 := cr23_one_le_lb N hN; simp only [cr23D]; omega
  have h1024 : 1024 ≤ 2 ^ E.W := by
    rw [hEW]
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ cr23Word N := le_of_lt (cr23_pow_lt_word N hN)
  have hj1024 : j % 1024 < 2 ^ E.W := lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h1024
  have hLw : cr23Lb N + 1 < 2 ^ E.W := by
    rw [hEW]
    calc cr23Lb N + 1 ≤ 2 ^ (cr23Lb N + 1) := le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hlbw : cr23Lb N < 2 ^ E.W := lt_trans (Nat.lt_succ_self _) hLw
  have hoff : (j % 1024) * (cr23Lb N + 1) + cr23Lb N < 2 ^ E.W := by
    rw [hEW]
    apply cr23_lt_word N hN
    have h1 : j % 1024 ≤ 1023 := by
      have := Nat.mod_lt j (by norm_num : 0 < 1024); omega
    calc (j % 1024) * (cr23Lb N + 1) + cr23Lb N
        ≤ 1023 * (cr23Lb N + 1) + cr23Lb N := by
          have h2 : (j % 1024) * (cr23Lb N + 1) ≤ 1023 * (cr23Lb N + 1) :=
            Nat.mul_le_mul_right _ h1
          omega
      _ ≤ 1023 * (cr23Lb N + 1) + (cr23Lb N + 1) := by omega
      _ = 1024 * (cr23Lb N + 1) := by ring
      _ ≤ 1024 * 2 ^ (cr23Lb N + 1) :=
          Nat.mul_le_mul_left _ (le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ 10 * 2 ^ (cr23Lb N + 1) := by norm_num
      _ = 2 ^ (cr23Lb N + 11) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set zc : ℕ := (if (j + 1) % cr23M t = 0 then 1 else 0) with hzcdef
  set cnt1 : ℕ := decScanCnt (cr23M t) (decBit N t C z) j + decBit N t C z j with hcnt1def
  set gg : ℕ := ((if (decScanSt (cr23M t) (decBit N t C z) j).2.1 < cnt1 then 1 else 0) * zc)
    % 2 ^ E.W with hggdef
  have hzc1 : zc ≤ 1 := by rw [hzcdef]; split_ifs <;> omega
  have hgg1 : gg ≤ 1 := by
    rw [hggdef]
    have h1 : (if (decScanSt (cr23M t) (decBit N t C z) j).2.1 < cnt1 then 1 else 0) * zc ≤ 1 := by
      have h2 : (if (decScanSt (cr23M t) (decBit N t C z) j).2.1 < cnt1 then 1 else 0) ≤ 1 := by
        split_ifs <;> omega
      calc (if (decScanSt (cr23M t) (decBit N t C z) j).2.1 < cnt1 then 1 else 0) * zc
          ≤ 1 * 1 := Nat.mul_le_mul h2 hzc1
        _ = 1 := Nat.one_mul 1
    exact le_trans (Nat.mod_le _ _) h1
  have hcnt1w : cnt1 < 2 ^ E.W := by
    rw [hcnt1def]
    have h1 := decScanCnt_le hMpos (decBit N t C z) j
    have h2 := decBit_le_one N t C z j
    have h3 : cr23M t + 1 ≤ 2 * cr23M t := by omega
    have h4 : 2 * cr23M t ≤ cr23D N * cr23M t := Nat.mul_le_mul_right _ hD2
    have h5 : cr23D N * cr23M t ≤ 2 ^ E.W := le_of_lt hDMw
    omega
  have hb1 : 1 ≤ cr23M t - j % cr23M t := by have := Nat.mod_lt j hMpos; omega
  have hbM : cr23M t - j % cr23M t - 1 + zc * cr23M t < 2 ^ E.W := by
    have h1 := Nat.mod_lt j hMpos
    have h3 : zc * cr23M t ≤ cr23M t := by
      calc zc * cr23M t ≤ 1 * cr23M t := Nat.mul_le_mul_right _ hzc1
        _ = cr23M t := Nat.one_mul _
    have h4 : cr23M t - j % cr23M t - 1 + cr23M t ≤ 2 * cr23M t := by omega
    have h5 : 2 * cr23M t ≤ 2 ^ E.W := le_of_lt
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ hD2) hDMw)
    omega
  -- chunk A
  set st1 : RAMState := runBlock decScanBA E st with hst1
  have hA := decScanBA_spec E st j (cr23Lb N + 1) (cr23Lb N) hq0 hq8 hq10 hq12 hjW hj1024 hLw
    hlbw hoff
  have hA13 : st1.regs r13 = st.mem (j / 1024) % 2 ^ E.W := hA.1
  have hA15 : st1.regs r15 = (j % 1024) * (cr23Lb N + 1) + cr23Lb N := hA.2
  have hAfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r15 → st1.regs d = st.regs d := by
    intro d hd hd2; rw [hst1]; exact decScanBA_frame E st d hd hd2
  have hbound : j / 1024 < wordsOf (cr23Word N) (cr23R N t) := decScanWordLt N t hN hj
  have hword : st.mem (j / 1024) % 2 ^ E.W
      = packMem (cr23Word N) (cr23Sketch N t C z) (j / 1024) := by
    rw [hm, hmem (j / 1024) hbound,
      Nat.mod_eq_of_lt (by rw [hEW]; exact packMem_lt (cr23Word N) hW0 _ (j / 1024))]
  have hbit : st1.regs r13 / 2 ^ st1.regs r15 % 2 = decBit N t C z j := by
    rw [hA13, hA15, hword]
    exact decBit_read N t C z j hj
  have hb11 : st1.regs r11 = 1 := by rw [hAfr r11 (by decide) (by decide)]; exact hq11
  have hb2 : st1.regs r2 = decScanCnt (cr23M t) (decBit N t C z) j := by
    rw [hAfr r2 (by decide) (by decide)]; exact hq2
  -- chunk B
  set st2 : RAMState := runBlock decScanBB E st1 with hst2
  have hB := decScanBB_spec E st1 (st1.regs r13) (st1.regs r15)
    (decScanCnt (cr23M t) (decBit N t C z) j) rfl rfl hb11 hb2 hW
    (by rw [hbit, ← hcnt1def]; exact hcnt1w)
  have hB13 : st2.regs r13 = decBit N t C z j := by
    rw [hst2]; exact hB.1.trans hbit
  have hB2 : st2.regs r2 = cnt1 := by rw [hst2, hcnt1def]; exact hB.2.trans (by rw [hbit])
  have hBfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r2 → st2.regs d = st1.regs d := by
    intro d hd hd2; rw [hst2]; exact decScanBB_frame E st1 d hd hd2
  have hc11 : st2.regs r11 = 1 := by rw [hBfr r11 (by decide) (by decide)]; exact hb11
  have hc6 : st2.regs r6 = cr23M t - j % cr23M t := by
    rw [hBfr r6 (by decide) (by decide), hAfr r6 (by decide) (by decide)]; exact hq6
  have hc3 : st2.regs r3 = (decScanSt (cr23M t) (decBit N t C z) j).2.1 := by
    rw [hBfr r3 (by decide) (by decide), hAfr r3 (by decide) (by decide)]; exact hq3
  -- chunk C
  set st3 : RAMState := runBlock decScanBC E st2 with hst3
  have hC := decScanBC_spec E st2 (cr23M t - j % cr23M t)
    (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 zc gg hc11 hc6 hc3 hB2 hW
    (decScanClose_ind E.W (cr23M t) hMpos hW j).symm hggdef
  have hC13 : st3.regs r13 = zc := by rw [hst3]; exact hC.1
  have hC15 : st3.regs r15 = gg := by rw [hst3]; exact hC.2
  have hCfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r15 → st3.regs d = st2.regs d := by
    intro d hd hd2; rw [hst3]; exact decScanBC_frame E st2 d hd hd2
  have hd5 : st3.regs r5 = j / cr23M t := by
    rw [hCfr r5 (by decide) (by decide), hBfr r5 (by decide) (by decide),
      hAfr r5 (by decide) (by decide)]
    exact hq5
  have hd4 : st3.regs r4 = (decScanSt (cr23M t) (decBit N t C z) j).2.2 := by
    rw [hCfr r4 (by decide) (by decide), hBfr r4 (by decide) (by decide),
      hAfr r4 (by decide) (by decide)]
    exact hq4
  -- chunk D
  set st4 : RAMState := runBlock decScanBD E st3 with hst4
  have hD := decScanBD_spec E st3 (j / cr23M t) (decScanSt (cr23M t) (decBit N t C z) j).2.2 gg
    hd5 hd4 hC15 hW hgg1
  have hDfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r4 → st4.regs d = st3.regs d := by
    intro d hd hd2; rw [hst4]; exact decScanBD_frame E st3 d hd hd2
  have he3 : st4.regs r3 = (decScanSt (cr23M t) (decBit N t C z) j).2.1 := by
    rw [hDfr r3 (by decide) (by decide), hCfr r3 (by decide) (by decide),
      hBfr r3 (by decide) (by decide), hAfr r3 (by decide) (by decide)]
    exact hq3
  have he2 : st4.regs r2 = cnt1 := by
    rw [hDfr r2 (by decide) (by decide), hCfr r2 (by decide) (by decide)]; exact hB2
  have he15 : st4.regs r15 = gg := by
    rw [hDfr r15 (by decide) (by decide)]
    exact hC15
  -- chunk E
  set st5 : RAMState := runBlock decScanBE E st4 with hst5
  have hE5 := decScanBE_spec E st4 (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 gg
    he3 he2 he15 hW hgg1
  have hEfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r3 → st5.regs d = st4.regs d := by
    intro d hd hd2; rw [hst5]; exact decScanBE_frame E st4 d hd hd2
  have hf11 : st5.regs r11 = 1 := by
    rw [hEfr r11 (by decide) (by decide), hDfr r11 (by decide) (by decide),
      hCfr r11 (by decide) (by decide), hBfr r11 (by decide) (by decide),
      hAfr r11 (by decide) (by decide)]
    exact hq11
  have hf6 : st5.regs r6 = cr23M t - j % cr23M t := by
    rw [hEfr r6 (by decide) (by decide), hDfr r6 (by decide) (by decide),
      hCfr r6 (by decide) (by decide), hBfr r6 (by decide) (by decide),
      hAfr r6 (by decide) (by decide)]
    exact hq6
  have hf5 : st5.regs r5 = j / cr23M t := by
    rw [hEfr r5 (by decide) (by decide), hDfr r5 (by decide) (by decide), hd5]
  -- chunk F
  set st6 : RAMState := runBlock decScanBF E st5 with hst6
  have hszc : j / cr23M t + zc < 2 ^ E.W := by
    have h1 : j / cr23M t ≤ j := Nat.div_le_self _ _
    omega
  have hF := decScanBF_spec E st5 (cr23M t - j % cr23M t) (j / cr23M t) zc hf11 hf6 hf5 hW
    hszc hzc1 (decScanClose_ind E.W (cr23M t) hMpos hW j).symm
  have hF5 : st6.regs r5 = j / cr23M t + zc := by rw [hst6]; exact hF.1
  have hF13 : st6.regs r13 = zc := by rw [hst6]; exact hF.2.1
  have hF15 : st6.regs r15 = 1 - zc := by rw [hst6]; exact hF.2.2
  have hFfr : ∀ d : Fin 16, d ≠ r13 → d ≠ r15 → d ≠ r5 → st6.regs d = st5.regs d := by
    intro d hd hd2 hd3; rw [hst6]; exact decScanBF_frame E st5 d hd hd2 hd3
  have hg7 : st6.regs r7 = cr23M t := by
    rw [hFfr r7 (by decide) (by decide) (by decide), hEfr r7 (by decide) (by decide),
      hDfr r7 (by decide) (by decide), hCfr r7 (by decide) (by decide),
      hBfr r7 (by decide) (by decide), hAfr r7 (by decide) (by decide)]
    exact hq7
  have hg6 : st6.regs r6 = cr23M t - j % cr23M t := by
    rw [hFfr r6 (by decide) (by decide) (by decide)]
    exact hf6
  have hg2 : st6.regs r2 = cnt1 := by
    rw [hFfr r2 (by decide) (by decide) (by decide), hEfr r2 (by decide) (by decide)]
    exact he2
  have hg11 : st6.regs r11 = 1 := by
    rw [hFfr r11 (by decide) (by decide) (by decide)]
    exact hf11
  have hg0 : st6.regs r0 = j := by
    rw [hFfr r0 (by decide) (by decide) (by decide), hEfr r0 (by decide) (by decide),
      hDfr r0 (by decide) (by decide), hCfr r0 (by decide) (by decide),
      hBfr r0 (by decide) (by decide), hAfr r0 (by decide) (by decide)]
    exact hq0
  -- chunk G
  set st7 : RAMState := runBlock decScanBG E st6 with hst7
  have hG := decScanBG_spec E st6 (cr23M t) (cr23M t - j % cr23M t) cnt1 j zc hg7 hg6 hg2
    hF13 hF15 hg11 hg0 hW hb1 (Nat.sub_le _ _) hMw hzc1 hcnt1w hj1W hbM
  have hGr2 : st7.regs r2 = (if zc = 1 then 0 else cnt1) := by rw [hst7]; exact hG.1
  have hGr6 : st7.regs r6 = cr23M t - j % cr23M t - 1 + zc * cr23M t := by
    rw [hst7]; exact hG.2.1
  have hGr0 : st7.regs r0 = j + 1 := by rw [hst7]; exact hG.2.2
  have hGfr : ∀ d : Fin 16, d ≠ r2 → d ≠ r15 → d ≠ r6 → d ≠ r0 →
      st7.regs d = st6.regs d := by
    intro d hd hd2 hd3 hd4; rw [hst7]; exact decScanBG_frame E st6 d hd hd2 hd3 hd4
  have h7r3 : st7.regs r3 = st5.regs r3 := by
    rw [hGfr r3 (by decide) (by decide) (by decide) (by decide),
      hFfr r3 (by decide) (by decide) (by decide)]
  have h7r4 : st7.regs r4 = st4.regs r4 := by
    rw [hGfr r4 (by decide) (by decide) (by decide) (by decide),
      hFfr r4 (by decide) (by decide) (by decide), hEfr r4 (by decide) (by decide)]
  have h7r5 : st7.regs r5 = st6.regs r5 := by
    rw [hGfr r5 (by decide) (by decide) (by decide) (by decide)]
  have h7keep : ∀ d : Fin 16, d ≠ r0 → d ≠ r2 → d ≠ r3 → d ≠ r4 → d ≠ r5 → d ≠ r6 →
      d ≠ r13 → d ≠ r15 → st7.regs d = st.regs d := by
    intro d k0 k2 k3 k4 k5 k6 k13 k15
    rw [hGfr d k2 k15 k6 k0, hFfr d k13 k15 k5, hEfr d k13 k3, hDfr d k13 k4,
      hCfr d k13 k15, hBfr d k13 k2, hAfr d k13 k15]
  have h7mem : st7.mem = st.mem := by
    rw [hst7, hst6, hst5, hst4, hst3, hst2, hst1, decScanBG_mem, decScanBF_mem,
      decScanBE_mem, decScanBD_mem, decScanBC_mem, decScanBB_mem, decScanBA_mem]
  have hbody : runBlock decScanBody E st = st7 := by
    rw [decScanBody_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3, ← hst4, ← hst5, ← hst6, ← hst7]
  rw [hbody]
  have hcntSt : (decScanSt (cr23M t) (decBit N t C z) j).1
      = decScanCnt (cr23M t) (decBit N t C z) j :=
    decScanSt_cnt (cr23M t) (decBit N t C z) hMpos (fun i => decBit_le_one N t C z i) j
  have hseedle : (decScanSt (cr23M t) (decBit N t C z) j).2.2 ≤ j / cr23M t :=
    decScanSt_seed_le (cr23M t) (decBit N t C z) hMpos (fun i => decBit_le_one N t C z i) j
  have hsw : j / cr23M t < 2 ^ E.W := lt_of_le_of_lt (Nat.div_le_self _ _) hjW
  have hbestw : (decScanSt (cr23M t) (decBit N t C z) j).2.1 < 2 ^ E.W :=
    lt_of_le_of_lt (decScanSt_best_le (cr23M t) (decBit N t C z) hMpos
      (fun i => decBit_le_one N t C z i) j) hMw
  by_cases hcl : (j + 1) % cr23M t = 0
  · have hz1 : zc = 1 := by rw [hzcdef]; exact if_pos hcl
    have hze : ¬ (0 : ℕ) = 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h7mem, hm]
    · exact hGr0
    · exact (h7keep r1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq1
    · rw [hGr2, hz1, if_pos rfl, decScanCnt_succ_of_zero hMpos (decBit N t C z) j hcl]
    · rw [h7r3, hE5.1,
        decMax_full E.W (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 gg zc hW hbestw hcnt1w
          hzc1 hggdef,
        hz1, if_pos rfl, decScanSt_best_zero (decBit N t C z) hcl, hcnt1def, ← hcntSt]
    · rw [h7r4, hD.1,
        decSel_full E.W (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 (j / cr23M t)
          (decScanSt (cr23M t) (decBit N t C z) j).2.2 gg zc hW hseedle hsw hzc1 hggdef,
        hz1, if_pos rfl, decScanSt_seed_zero (decBit N t C z) hcl, hcnt1def, ← hcntSt]
    · rw [h7r5, hF5, hz1, dec_succ_div_eq' hMpos hcl]
    · simp only [hGr6, hz1, dec_b_step hMpos j, if_pos hcl, Nat.one_mul]
    · exact (h7keep r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq7
    · exact (h7keep r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq8
    · exact (h7keep r10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq10
    · exact (h7keep r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq11
    · exact (h7keep r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq12
    · exact (h7keep r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq9
    · exact (h7keep r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq14
  · have hz0 : zc = 0 := by rw [hzcdef]; exact if_neg hcl
    have hze : ¬ (0 : ℕ) = 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h7mem, hm]
    · exact hGr0
    · exact (h7keep r1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq1
    · rw [hGr2, hz0, if_neg hze,
        decScanCnt_succ_of_mod hMpos (decBit N t C z) hcl (decBit_le_one N t C z j), hcnt1def]
    · rw [h7r3, hE5.1,
        decMax_full E.W (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 gg zc hW hbestw hcnt1w
          hzc1 hggdef,
        hz0, if_neg hze, decScanSt_best_succ (decBit N t C z) hcl]
    · rw [h7r4, hD.1,
        decSel_full E.W (decScanSt (cr23M t) (decBit N t C z) j).2.1 cnt1 (j / cr23M t)
          (decScanSt (cr23M t) (decBit N t C z) j).2.2 gg zc hW hseedle hsw hzc1 hggdef,
        hz0, if_neg hze, decScanSt_seed_succ (decBit N t C z) hcl]
    · rw [h7r5, hF5, hz0, Nat.add_zero, dec_succ_div_lt' hMpos hcl]
    · simp only [hGr6, hz0, dec_b_step hMpos j, if_neg hcl, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero]
    · exact (h7keep r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq7
    · exact (h7keep r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq8
    · exact (h7keep r10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq10
    · exact (h7keep r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq11
    · exact (h7keep r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq12
    · exact (h7keep r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq9
    · exact (h7keep r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hq14
/-- The initialisation, cut into five chunks so that each `simp` sees at most five instructions. -/
def decScanIA : List Instr :=
  [iImm r13 1, iAdd r13 r14 r13, iLd r13 r13, iImm r15 3, iAdd r15 r14 r15]
def decScanIB : List Instr := [iLd r7 r15, iMul r1 r13 r7, iImm r15 4, iAdd r15 r14 r15, iLd r8 r15]
def decScanIC : List Instr := [iImm r15 5, iAdd r15 r14 r15, iLd r10 r15, iImm r11 1, iImm r12 1024]
def decScanID : List Instr := [iBor r6 r7 r7, iImm r0 0, iImm r2 0, iImm r3 0, iImm r4 0]
def decScanIE : List Instr := [iImm r5 0]
theorem decScanInit_split :
    decScanInit = decScanIA ++ decScanIB ++ decScanIC ++ decScanID ++ decScanIE := rfl
/-- **The initialisation, as a data lemma**: from `DecData` at the round head it produces the
loop-head invariant at `j = 0`. -/
theorem decScanInit_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (w : ℕ)
    (m₀ : ℕ → ℕ) (st : RAMState) (hm : st.mem = m₀)
    (h9 : st.regs r9 = w) (h14 : st.regs r14 = cr23DecFrame N t)
    (hD : st.mem (decSlot N t 0) = cr23D N) (hM : st.mem (decSlot N t 2) = cr23M t)
    (hL : st.mem (decSlot N t 3) = cr23Lb N + 1) (hlb : st.mem (decSlot N t 4) = cr23Lb N) :
    DecScanInv N t C z w 0 m₀
      (runBlock decScanInit (detEnv (cr23Word N) (cr23DecDet N t C)) st) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hDw : cr23D N < 2 ^ E.W := by rw [hEW]; exact cr23D_lt_word N hN
  have hMw : cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23M_lt_word N t hN htN
  have hDMw : cr23D N * cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23DM_lt_word N t hN htN
  have hLw : cr23Lb N + 1 < 2 ^ E.W := by
    rw [hEW]
    calc cr23Lb N + 1 ≤ 2 ^ (cr23Lb N + 1) := le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hlbw : cr23Lb N < 2 ^ E.W := lt_trans (Nat.lt_succ_self _) hLw
  have h1024w : 1024 < 2 ^ E.W := by
    rw [hEW]
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have h5w : 5 < 2 ^ E.W := by omega
  have hF1 : cr23DecFrame N t + 1 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 1) (by norm_num)
  have hF3 : cr23DecFrame N t + 3 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 3) (by norm_num)
  have hF4 : cr23DecFrame N t + 4 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 4) (by norm_num)
  have hF5 : cr23DecFrame N t + 5 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 5) (by norm_num)
  have hD' : st.mem (cr23DecFrame N t + 1) = cr23D N := by simpa [decSlot] using hD
  have hM' : st.mem (cr23DecFrame N t + 3) = cr23M t := by simpa [decSlot] using hM
  have hL' : st.mem (cr23DecFrame N t + 4) = cr23Lb N + 1 := by simpa [decSlot] using hL
  have hlb' : st.mem (cr23DecFrame N t + 5) = cr23Lb N := by simpa [decSlot] using hlb
  set st1 : RAMState := runBlock decScanIA E st with hst1
  have i1a : st1.regs r13 = st.mem (cr23DecFrame N t + 1) % 2 ^ E.W := by
    rw [hst1]; simp [decScanIA, h14, Nat.mod_eq_of_lt hF1, Nat.mod_eq_of_lt hW]
  have i1b : st1.regs r15 = cr23DecFrame N t + 3 := by
    rw [hst1]; simp [decScanIA, h14, Nat.mod_eq_of_lt hF3, Nat.mod_eq_of_lt hW]
  have i1mem : st1.mem = st.mem := by rw [hst1]; simp [decScanIA]
  have i1fr : ∀ d : Fin 16, d ≠ r13 → d ≠ r15 → st1.regs d = st.regs d := by
    intro d hd hd2; rw [hst1]; simp [decScanIA, hd, hd2]
  have i1r14 : st1.regs r14 = cr23DecFrame N t :=
    (i1fr r14 (by decide) (by decide)).trans h14
  set st2 : RAMState := runBlock decScanIB E st1 with hst2
  have i2a : st2.regs r7 = cr23M t := by
    rw [hst2]
    simp [decScanIB, i1b, i1mem, hM', Nat.mod_eq_of_lt hMw]
  have i2b : st2.regs r1 = cr23D N * cr23M t := by
    rw [hst2]
    simp [decScanIB, i1a, i1b, i1mem, i1r14, hD', hM', Nat.mod_eq_of_lt hDw,
      Nat.mod_eq_of_lt hMw, Nat.mod_eq_of_lt hDMw]
  have i2c : st2.regs r15 = cr23DecFrame N t + 4 := by
    rw [hst2]
    simp [decScanIB, i1b, i1r14, Nat.mod_eq_of_lt hF4]
  have i2mem : st2.mem = st.mem := by rw [hst2]; simp [decScanIB, i1mem]
  have i2d : st2.regs r8 = cr23Lb N + 1 := by
    rw [hst2]
    simp [decScanIB, i2c, i1mem, i1r14, hL', Nat.mod_eq_of_lt hF4, Nat.mod_eq_of_lt hLw]
  have i2fr : ∀ d : Fin 16, d ≠ r7 → d ≠ r1 → d ≠ r15 → d ≠ r8 → st2.regs d = st1.regs d := by
    intro d hd hd2 hd3 hd4; rw [hst2]; simp [decScanIB, hd, hd2, hd3, hd4]
  have i2r14 : st2.regs r14 = cr23DecFrame N t :=
    (i2fr r14 (by decide) (by decide) (by decide) (by decide)).trans i1r14
  set st3 : RAMState := runBlock decScanIC E st2 with hst3
  have i3a : st3.regs r15 = cr23DecFrame N t + 5 := by
    rw [hst3]
    simp [decScanIC, i2c, i2r14, Nat.mod_eq_of_lt hF5]
  have i3mem : st3.mem = st.mem := by rw [hst3]; simp [decScanIC, i2mem]
  have i3b : st3.regs r10 = cr23Lb N := by
    rw [hst3]
    simp [decScanIC, i3a, i2mem, i2r14, hlb', Nat.mod_eq_of_lt hF5,
      Nat.mod_eq_of_lt hlbw]
  have i3c : st3.regs r11 = 1 := by
    rw [hst3]; simp [decScanIC, Nat.mod_eq_of_lt hW]
  have i3d : st3.regs r12 = 1024 := by
    rw [hst3]; simp [decScanIC, Nat.mod_eq_of_lt h1024w]
  have i3fr : ∀ d : Fin 16, d ≠ r15 → d ≠ r10 → d ≠ r11 → d ≠ r12 →
      st3.regs d = st2.regs d := by
    intro d hd hd2 hd3 hd4; rw [hst3]; simp [decScanIC, hd, hd2, hd3, hd4]
  set st4 : RAMState := runBlock decScanID E st3 with hst4
  have i4a : st4.regs r6 = cr23M t := by
    rw [hst4]
    have h7 : st3.regs r7 = cr23M t :=
      (i3fr r7 (by decide) (by decide) (by decide) (by decide)).trans i2a
    simp [decScanID, h7, Nat.mod_eq_of_lt hMw, nat_lor_self]
  have i4b : st4.regs r0 = 0 := by rw [hst4]; simp [decScanID]
  have i4c : st4.regs r2 = 0 := by rw [hst4]; simp [decScanID]
  have i4d : st4.regs r3 = 0 := by rw [hst4]; simp [decScanID]
  have i4e : st4.regs r4 = 0 := by rw [hst4]; simp [decScanID]
  have i4mem : st4.mem = st.mem := by rw [hst4]; simp [decScanID, i3mem]
  have i4fr : ∀ d : Fin 16, d ≠ r6 → d ≠ r0 → d ≠ r2 → d ≠ r3 → d ≠ r4 →
      st4.regs d = st3.regs d := by
    intro d hd hd2 hd3 hd4 hd5; rw [hst4]; simp [decScanID, hd, hd2, hd3, hd4, hd5]
  set st5 : RAMState := runBlock decScanIE E st4 with hst5
  have i5a : st5.regs r5 = 0 := by rw [hst5]; simp [decScanIE]
  have i5fr : ∀ d : Fin 16, d ≠ r5 → st5.regs d = st4.regs d := by
    intro d hd; rw [hst5]; simp [decScanIE, hd]
  have h5mem : st5.mem = st.mem := by rw [hst5]; simp [decScanIE, i4mem]
  have hbody : runBlock decScanInit E st = st5 := by
    rw [decScanInit_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3, ← hst4, ← hst5]
  rw [hbody]
  -- the six registers the block leaves at a value
  have k9 : st5.regs r9 = w := by
    rw [i5fr r9 (by decide), i4fr r9 (by decide) (by decide) (by decide) (by decide) (by decide),
      i3fr r9 (by decide) (by decide) (by decide) (by decide),
      i2fr r9 (by decide) (by decide) (by decide) (by decide),
      i1fr r9 (by decide) (by decide)]
    exact h9
  have k14 : st5.regs r14 = cr23DecFrame N t := by
    rw [i5fr r14 (by decide), i4fr r14 (by decide) (by decide) (by decide) (by decide) (by decide),
      i3fr r14 (by decide) (by decide) (by decide) (by decide),
      i2fr r14 (by decide) (by decide) (by decide) (by decide),
      i1fr r14 (by decide) (by decide)]
    exact h14
  have k1 : st5.regs r1 = cr23D N * cr23M t := by
    rw [i5fr r1 (by decide), i4fr r1 (by decide) (by decide) (by decide) (by decide) (by decide),
      i3fr r1 (by decide) (by decide) (by decide) (by decide)]
    exact i2b
  have k7 : st5.regs r7 = cr23M t := by
    rw [i5fr r7 (by decide), i4fr r7 (by decide) (by decide) (by decide) (by decide) (by decide),
      i3fr r7 (by decide) (by decide) (by decide) (by decide)]
    exact i2a
  have k8 : st5.regs r8 = cr23Lb N + 1 := by
    rw [i5fr r8 (by decide), i4fr r8 (by decide) (by decide) (by decide) (by decide) (by decide),
      i3fr r8 (by decide) (by decide) (by decide) (by decide)]
    exact i2d
  have k10 : st5.regs r10 = cr23Lb N := by
    rw [i5fr r10 (by decide), i4fr r10 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact i3b
  have k11 : st5.regs r11 = 1 := by
    rw [i5fr r11 (by decide), i4fr r11 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact i3c
  have k12 : st5.regs r12 = 1024 := by
    rw [i5fr r12 (by decide), i4fr r12 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact i3d
  have k6 : st5.regs r6 = cr23M t := by rw [i5fr r6 (by decide)]; exact i4a
  have k0 : st5.regs r0 = 0 := by rw [i5fr r0 (by decide)]; exact i4b
  have k2 : st5.regs r2 = 0 := by rw [i5fr r2 (by decide)]; exact i4c
  have k3 : st5.regs r3 = 0 := by rw [i5fr r3 (by decide)]; exact i4d
  have k4 : st5.regs r4 = 0 := by rw [i5fr r4 (by decide)]; exact i4e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k7, k8, k10, k11, k12, k9, k14⟩
  · rw [h5mem, hm]
  · exact k0
  · exact k1
  · rw [k2]; simp [decScanCnt]
  · rw [k3]; simp [decScanSt]
  · rw [k4]; simp [decScanSt]
  · rw [i5a]; simp
  · rw [k6]; simp
theorem decScanBody_len : decScanBody.length = 27 := by decide
theorem decScanInit_len : decScanInit.length = 21 := by decide
theorem decScanBA_noBranch : NoBranch decScanBA := by simp [decScanBA]
theorem decScanBB_noBranch : NoBranch decScanBB := by simp [decScanBB]
theorem decScanBC_noBranch : NoBranch decScanBC := by simp [decScanBC]
theorem decScanBD_noBranch : NoBranch decScanBD := by simp [decScanBD]
theorem decScanBE_noBranch : NoBranch decScanBE := by simp [decScanBE]
theorem decScanBF_noBranch : NoBranch decScanBF := by simp [decScanBF]
theorem decScanBG_noBranch : NoBranch decScanBG := by simp [decScanBG]
theorem decScanBody_noBranch : NoBranch decScanBody := by
  rw [decScanBody_split]
  simp [decScanBA_noBranch, decScanBB_noBranch, decScanBC_noBranch, decScanBD_noBranch,
    decScanBE_noBranch, decScanBF_noBranch, decScanBG_noBranch]
theorem decScanIA_noBranch : NoBranch decScanIA := by simp [decScanIA]
theorem decScanIB_noBranch : NoBranch decScanIB := by simp [decScanIB]
theorem decScanIC_noBranch : NoBranch decScanIC := by simp [decScanIC]
theorem decScanID_noBranch : NoBranch decScanID := by simp [decScanID]
theorem decScanIE_noBranch : NoBranch decScanIE := by simp [decScanIE]
theorem decScanInit_noBranch : NoBranch decScanInit := by
  rw [decScanInit_split]
  simp [decScanIA_noBranch, decScanIB_noBranch, decScanIC_noBranch, decScanID_noBranch,
    decScanIE_noBranch]
/-- **`DecScanInv` never looks at the program counter** (stated as its own lemma: transporting it
across a `pc` update is then a purely syntactic match at every use site). -/
theorem DecScanInv_pc (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w j : ℕ) (m₀ : ℕ → ℕ) (p : ℕ) (s : RAMState) (h : DecScanInv N t C z w j m₀ s) :
    DecScanInv N t C z w j m₀ { s with pc := p } := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩ := h
  exact ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩
/-- **One iteration of the scan**: the test, the `jz`, the 27-instruction body and the trailing `jmp`.
The two facts about `P` that `at_loop` produces are hypotheses here, at the exact addresses the body
runs at, so that no proof ever has to reduce `Stmt.compile` or a list length. -/
theorem decScan_bodyIter (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (w j : ℕ)
    (m₀ : ℕ → ℕ) (P : Program) (a : ℕ)
    (hAtBody : At P (a + (Cond.lt r13 r0 r1).code.length + 1) decScanBody)
    (hjmpAt : P[(a + (Cond.lt r13 r0 r1).code.length + 1) + decScanBody.length]? =
      some (iJmp a))
    (hmem : ∀ b, b < wordsOf (cr23Word N) (cr23R N t) →
      m₀ b = packMem (cr23Word N) (cr23Sketch N t C z) b)
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r13 r0 r1).code.length + 1)
    (hR : DecScanInv N t C z w j m₀ st) (hj : j < cr23D N * cr23M t) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) (a + (Cond.lt r13 r0 r1).code.length + 1) a
      { st with pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
      (fun k s' => k = decScanBody.length + 1 ∧
        DecScanInv N t C z w (j + 1) m₀ s' ∧ s'.pc = a) := by
  have hno : NoBranch decScanBody := decScanBody_noBranch
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set b : ℕ := a + (Cond.lt r13 r0 r1).code.length + 1 with hb
  have hblk : Sem P E b (b + decScanBody.length) { st with pc := b }
      (fun k s' => k = decScanBody.length ∧ s' = runBlock decScanBody E { st with pc := b }) :=
    Sem.block P E b decScanBody { st with pc := b } hAtBody hno rfl
  have hpcB : (runBlock decScanBody E { st with pc := b }).pc = b + decScanBody.length := by
    rw [runBlock_pc decScanBody E _ hno]
  have hjmpSem : Sem P E (b + decScanBody.length) a
      (runBlock decScanBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock decScanBody E { st with pc := b } with pc := a }) :=
    Sem.exec P E (b + decScanBody.length) a _ (iJmp a) hjmpAt hpcB rfl
  refine Sem.mono (Sem.trans hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨rfl, DecScanInv_pc N t C z w (j + 1) m₀ a _
    (decScanBody_data N t hN ht htN C z w j m₀ { st with pc := b } hmem hR hj), rfl⟩
/-- **The scan loop**: `D·M` iterations, then the failing test. -/
theorem decScan_loop (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (w : ℕ)
    (m₀ : ℕ → ℕ) (P : Program) (a : ℕ)
    (hAt : At P a (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decScanBody)) a))
    (hmem : ∀ b, b < wordsOf (cr23Word N) (cr23R N t) →
      m₀ b = packMem (cr23Word N) (cr23Sketch N t C z) b)
    (st : RAMState) (hpc : st.pc = a) (hR : DecScanInv N t C z w 0 m₀ st) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decScanBody).len + 2) st
      (fun k s' => k ≤ 2 + 30 * (cr23D N * cr23M t) ∧
        DecScanInv N t C z w (cr23D N * cr23M t) m₀ s' ∧
        s'.pc = a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decScanBody).len + 2) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hW : 1 < 2 ^ E.W := by
    rw [hE]
    exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → DecScanInv N t C z w j m₀ s → DecScanInv N t C z w j m₀ s' := by
    intro j s s' hd hm' h
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩ := h
    refine ⟨hm'.symm.trans m1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [← hd _ (by decide)] <;> assumption
  have hgo : ∀ j, j < cr23D N * cr23M t → ∀ s, DecScanInv N t C z w j m₀ s →
      (Cond.lt r13 r0 r1).eval s := by
    intro j hj s h
    obtain ⟨-, h0, h1, -⟩ := h
    show s.regs r0 < s.regs r1
    rw [h0, h1]; exact hj
  have hstop : ∀ s, DecScanInv N t C z w (cr23D N * cr23M t) m₀ s →
      ¬ (Cond.lt r13 r0 r1).eval s := by
    intro s h
    obtain ⟨-, h0, h1, -⟩ := h
    show ¬ (s.regs r0 < s.regs r1)
    rw [h0, h1]; omega
  have hstep : ∀ j, j < cr23D N * cr23M t → ∀ s, s.pc = a →
      DecScanInv N t C z w j m₀ s →
      Sem P E (a + (Cond.lt r13 r0 r1).code.length + 1) a
        { runBlock (Cond.lt r13 r0 r1).code E s with pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
        (fun k s' => k = decScanBody.length + 1 ∧
          DecScanInv N t C z w (j + 1) m₀ s' ∧ s'.pc = a) := by
    intro j hj s hpc' hRs
    obtain ⟨-, -, hbody, hjmp⟩ := at_loop hAt
    have hlen : (Stmt.code decScanBody).len = decScanBody.length := rfl
    have hbody' : At P (a + (Cond.lt r13 r0 r1).code.length + 1) decScanBody := hbody
    have hjmpAt : P[(a + (Cond.lt r13 r0 r1).code.length + 1) + decScanBody.length]? =
        some (iJmp a) := by
      rw [← hlen]
      exact hjmp
    have hR' : DecScanInv N t C z w j m₀
        { runBlock (Cond.lt r13 r0 r1).code E s with
          pc := a + (Cond.lt r13 r0 r1).code.length + 1 } :=
      hirr j (runBlock (Cond.lt r13 r0 r1).code E s) s
        (fun d hd => runBlock_cond_regs (Cond.lt r13 r0 r1) E s d hd)
        (runBlock_cond_mem (Cond.lt r13 r0 r1) E s) hRs
    exact decScan_bodyIter N t hN ht htN C z w j m₀ P a hbody' hjmpAt hmem
      { runBlock (Cond.lt r13 r0 r1).code E s with
        pc := a + (Cond.lt r13 r0 r1).code.length + 1 } rfl hR' hj
  have hloop := Sem.loopPred P E a (Cond.lt r13 r0 r1) (Stmt.code decScanBody) hAt hW
    (cr23D N * cr23M t) (fun j s => DecScanInv N t C z w j m₀ s)
    (fun _ => decScanBody.length + 1) hirr hgo hstop hstep st hpc hR
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1, h.2.2⟩)
  obtain ⟨h1, h2, h3⟩ := h
  have hsum : (∑ j ∈ Finset.range (cr23D N * cr23M t),
        ((Cond.lt r13 r0 r1).code.length + 1 + (decScanBody.length + 1)))
      = 30 * (cr23D N * cr23M t) := by
    simp [Finset.sum_const, Finset.card_range, Cond.code, decScanBody_len, Nat.mul_comm]
  have hcl : (Cond.lt r13 r0 r1).code.length = 1 := rfl
  rw [hsum] at h1
  rw [hcl] at h1
  omega
theorem decXorLoad_len : decXorLoad.length = 4 := rfl
theorem decXorPre_len : decXorPre.length = 14 := rfl
theorem decXorPost_len : decXorPost.length = 2 := rfl
/-- The payload after the first `i` candidate values: `y` plus their columns. -/
def decLstDelta (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (l : List ℕ) (i : ℕ) :
    Fin (cr23R N t) → ZMod 2 :=
  ∑ k ∈ Finset.range i,
    if h : l.getD k 0 < N then cr23Delta N t C (cr23D N) ⟨l.getD k 0, h⟩ else 0
/-- One more candidate value adds its column. -/
theorem decLstDelta_succ (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (l : List ℕ)
    (i : ℕ) (h : l.getD i 0 < N) :
    decLstDelta N t C l (i + 1)
      = decLstDelta N t C l i + cr23Delta N t C (cr23D N) ⟨l.getD i 0, h⟩ := by
  funext p
  simp only [decLstDelta, Finset.sum_range_succ, Pi.add_apply, dif_pos h]
/-- The loop invariant of body (c).  Note the **restricted** memory clause: the decoder's frame (slots,
candidate list, tag array) sits above the packed payload and holds non-zero values, so the global
equation `∀ addr, mem addr = packMem … addr` of `UpData` is *false* here and must not be used (§10.3 of
the notes). -/
def DecXorInv (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2)
    (l : List ℕ) (len i : ℕ) (s : RAMState) : Prop :=
  s.regs r1 = i ∧ s.regs r2 = len ∧ s.regs r14 = cr23DecFrame N t ∧
  s.mem (decSlot N t 0) = cr23D N ∧ s.mem (decSlot N t 1) = N ∧
  (∀ k, k < len → s.mem (decCandBase N t + k) = l.getD k 0) ∧
  (∀ k, k < len → l.getD k 0 < N) ∧
  (∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
    s.mem addr = packMem (cr23Word N) (y + decLstDelta N t C l i) addr)
theorem decXorL1_spec (E : RAMEnv) (st : RAMState) (N t : ℕ)
    (h14 : st.regs r14 = cr23DecFrame N t)
    (h32 : 32 < 2 ^ E.W) (hfr : cr23DecFrame N t + 32 < 2 ^ E.W) :
    (runBlock decXorL1 E st).regs r8 = cr23DecFrame N t + 32 ∧
      (runBlock decXorL1 E st).mem = st.mem := by
  refine ⟨?_, ?_⟩
  · simp [decXorL1, h14, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt hfr]
  · simp [decXorL1]
theorem decXorL2_spec (E : RAMEnv) (st : RAMState) (N t : ℕ) (i : ℕ) (l : List ℕ)
    (h8 : st.regs r8 = cr23DecFrame N t + 32) (h1 : st.regs r1 = i)
    (hget : st.mem (cr23DecFrame N t + 32 + i) = l.getD i 0)
    (hfr : cr23DecFrame N t + 32 + i < 2 ^ E.W) (hv : l.getD i 0 < 2 ^ E.W) :
    (runBlock decXorL2 E st).regs r0 = l.getD i 0 ∧
      (runBlock decXorL2 E st).mem = st.mem := by
  have haddr : cr23DecFrame N t + 32 + i < 2 ^ E.W := hfr
  have hv' : l[i]?.getD 0 < 2 ^ E.W := hv
  have hget' : st.mem (cr23DecFrame N t + 32 + i) = l[i]?.getD 0 := hget
  refine ⟨?_, ?_⟩
  · simp [decXorL2, h8, h1, Nat.mod_eq_of_lt haddr, hget', Nat.mod_eq_of_lt hv']
  · simp [decXorL2]
/-- The candidate load: `r0 := mem (decCandBase N t + i)`. -/
theorem decXorLoad_data (E : RAMEnv) (st : RAMState) (N t i : ℕ) (l : List ℕ)
    (h1 : st.regs r1 = i) (h14 : st.regs r14 = cr23DecFrame N t)
    (hget : st.mem (decCandBase N t + i) = l.getD i 0)
    (h32 : 32 < 2 ^ E.W) (hfr : cr23DecFrame N t + 32 + i < 2 ^ E.W)
    (hv : l.getD i 0 < 2 ^ E.W) :
    (runBlock decXorLoad E st).regs r0 = l.getD i 0 ∧
      (runBlock decXorLoad E st).mem = st.mem := by
  have hfr' : cr23DecFrame N t + 32 < 2 ^ E.W := by omega
  set st1 : RAMState := runBlock decXorL1 E st with hst1
  have hL1 := decXorL1_spec E st N t h14 h32 hfr'
  have h1r8 : st1.regs r8 = cr23DecFrame N t + 32 := hL1.1
  have h1mem : st1.mem = st.mem := hL1.2
  have hget' : st1.mem (cr23DecFrame N t + 32 + i) = l.getD i 0 := by
    rw [h1mem]
    simpa only [decCandBase] using hget
  have hL2 := decXorL2_spec E st1 N t i l h1r8 h1 hget' hfr hv
  have hbody : runBlock decXorLoad E st = runBlock decXorL2 E st1 := by
    rw [decXorLoad]
    simp only [runBlock_append]
    rw [← hst1]
  rw [hbody]
  exact ⟨hL2.1, hL2.2.trans h1mem⟩
/-- The three pieces of the `UpData` prologue. -/
def decXorP1 : List Instr := [iImm r8 1, iAdd r8 r14 r8, iLd r3 r8, iImm r8 1, iAdd r8 r0 r8]
def decXorP2 : List Instr := [iTbl r5 r8, iBor r6 r3 r3, iBor r7 r5 r5, iImm r15 1, iAdd r10 r5 r15]
def decXorP3 : List Instr := [iAdd r11 r5 r3, iAdd r11 r11 r3, iImm r12 2, iBor r13 r15 r15]
theorem decXorPre_split : decXorPre = decXorP1 ++ decXorP2 ++ decXorP3 := rfl
theorem decXorP1_spec (E : RAMEnv) (st : RAMState) (N t : ℕ) (v D : ℕ)
    (h0 : st.regs r0 = v) (h14 : st.regs r14 = cr23DecFrame N t)
    (hD : st.mem (decSlot N t 0) = D)
    (hone : 1 < 2 ^ E.W) (hDlt : D < 2 ^ E.W) (hfr : cr23DecFrame N t + 1 < 2 ^ E.W)
    (hv : v + 1 < 2 ^ E.W) :
    (runBlock decXorP1 E st).regs r3 = D ∧ (runBlock decXorP1 E st).regs r8 = v + 1 ∧
      (runBlock decXorP1 E st).mem = st.mem := by
  have hwr : ((cr23DecFrame N t + 1) % 2 ^ E.W) = cr23DecFrame N t + 1 :=
    Nat.mod_eq_of_lt hfr
  have hslot : decSlot N t 0 = cr23DecFrame N t + 1 := rfl
  have hload : st.mem ((cr23DecFrame N t + 1) % 2 ^ E.W) = D := by
    rw [hwr, ← hslot]
    exact hD
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hone
  refine ⟨?_, ?_, ?_⟩
  · simp [decXorP1, h14, hload, h1m, Nat.mod_eq_of_lt hDlt]
  · simp [decXorP1, h0, h14, h1m, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hfr]
  · simp [decXorP1]
theorem decXorP2_spec (E : RAMEnv) (st : RAMState) (N t : ℕ) (v D : ℕ)
    (h8 : st.regs r8 = v + 1) (h3 : st.regs r3 = D)
    (hbase : E.det (v + 1) = upBase N v)
    (hone : 1 < 2 ^ E.W) (hB : upBase N v < 2 ^ E.W)
    (hB1 : upBase N v + 1 < 2 ^ E.W) (hDlt : D < 2 ^ E.W) :
    (runBlock decXorP2 E st).regs r5 = upBase N v ∧ (runBlock decXorP2 E st).regs r6 = D ∧
      (runBlock decXorP2 E st).regs r7 = upBase N v ∧ (runBlock decXorP2 E st).regs r15 = 1 ∧
      (runBlock decXorP2 E st).regs r10 = upBase N v + 1 ∧
      (runBlock decXorP2 E st).mem = st.mem := by
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hone
  have hbv : E.det (v + 1) % 2 ^ E.W = upBase N v := by
    rw [hbase]; exact Nat.mod_eq_of_lt hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [decXorP2, h8, hbv]
  · simp [decXorP2, h3, nat_lor_self, Nat.mod_eq_of_lt hDlt]
  · simp [decXorP2, h8, h3, hbv, nat_lor_self, Nat.mod_eq_of_lt hB]
  · simp [decXorP2, h1m]
  · simp [decXorP2, h8, hbv, h1m, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hB1]
  · simp [decXorP2]
theorem decXorP3_spec (E : RAMEnv) (st : RAMState) (N t : ℕ) (v D : ℕ)
    (h5 : st.regs r5 = upBase N v) (h3 : st.regs r3 = D) (h15 : st.regs r15 = 1)
    (hone : 1 < 2 ^ E.W) (h2 : 2 < 2 ^ E.W) (hE2 : upBase N v + 2 * D < 2 ^ E.W) :
    (runBlock decXorP3 E st).regs r11 = upBase N v + 2 * D ∧
      (runBlock decXorP3 E st).regs r12 = 2 ∧ (runBlock decXorP3 E st).regs r13 = 1 ∧
      (runBlock decXorP3 E st).mem = st.mem := by
  have h1 : upBase N v + D < 2 ^ E.W := by omega
  have he : upBase N v + D + D = upBase N v + 2 * D := by ring
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hone
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [decXorP3, h5, h3, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hE2, he]
  · simp [decXorP3, Nat.mod_eq_of_lt h2]
  · simp [decXorP3, h15, nat_lor_self, h1m]
  · simp [decXorP3]
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
/-- **The exact memory effect of one body step**: it is a single `Function.update` of the word
`det r7 = cr23Addr` of the current seed, with the XOR of the two records as value. -/
theorem body_mem (E : RAMEnv) (s : RAMState) :
    (runBlock progUpBody E s).mem
      = Function.update s.mem (E.det (s.regs r7) % 2 ^ E.W)
          ((s.mem (E.det (s.regs r7) % 2 ^ E.W) % 2 ^ E.W
            ^^^ (E.det (s.regs r10) % 2 ^ E.W)) % 2 ^ E.W) := by
  rw [upBody_split]
  simp only [runBlock_append, runBlock_cons, runBlock_nil, execInstr_add, execInstr_sub,
    execInstr_store, upBodyA_mem, upBodyA_r8, upBodyA_r4]
/-- **Outside the touched payload word, one body step leaves memory alone.** -/
theorem body_mem_frame (E : RAMEnv) (s : RAMState) (a : ℕ)
    (h : a ≠ E.det (s.regs r7) % 2 ^ E.W) :
    (runBlock progUpBody E s).mem a = s.mem a := by
  rw [body_mem, Function.update_of_ne h]
/-- **`UpData` with the memory clause restricted to the payload.**  `y` is the payload vector, `v` the
column being toggled and `m` the countdown (seeds `0, …, D - m - 1` already done). -/
def UpData (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ) (s : RAMState) : Prop :=
  s.regs r0 = v.val ∧ s.regs r3 = cr23D N ∧ s.regs r5 = upBase N v.val ∧ s.regs r6 = m ∧
    s.regs r7 = upBase N v.val + 2 * (cr23D N - m) ∧
    s.regs r10 = upBase N v.val + 1 + 2 * (cr23D N - m) ∧
    s.regs r11 = upBase N v.val + 2 * cr23D N ∧ s.regs r12 = 2 ∧ s.regs r13 = 1 ∧
    (∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      s.mem addr = packMem (cr23Word N) (y + cr23Delta N t C (cr23D N - m) v) addr)
theorem UpData.irrel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m : ℕ)
    (s s' : RAMState) (hr : s.regs = s'.regs) (hm : s.mem = s'.mem)
    (h : UpData N t C y v m s) : UpData N t C y v m s' := by
  rcases h with ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
/-- The invariant never looks at the program counter (abstract-state transport lemma, so that the use
site across a `jmp` is a syntactic match). -/
theorem UpData_pc (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (m p : ℕ) (s : RAMState)
    (h : UpData N t C y v m s) : UpData N t C y v m { s with pc := p } := by
  rcases h with ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem⟩
  exact ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hmem⟩
theorem body_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (j : ℕ)
    (hj : j + 1 ≤ cr23D N)
    (s : RAMState) (hR : UpData N t C y v (j + 1) s) :
    UpData N t C y v j (runBlock progUpBody (detEnv (cr23Word N) (cr23DecDet N t C)) s) := by
  obtain ⟨h0, h3, h5, h6, h7, h10, h11, h12, h13, hm⟩ := hR
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
  have hdetA : cr23DecDet N t C (upBase N v.val + 2 * (cr23D N - (j + 1)))
      = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v :=
    cr23DecDet_addr N t C hN v ⟨cr23D N - (j + 1), hi⟩
  have hdetM : cr23DecDet N t C (upBase N v.val + 1 + 2 * (cr23D N - (j + 1)))
      = cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    have e : upBase N v.val + 1 + 2 * (cr23D N - (j + 1))
        = upBase N v.val + 2 * (cr23D N - (j + 1)) + 1 := by ring
    rw [e]
    exact cr23DecDet_mask N t C hN v ⟨cr23D N - (j + 1), hi⟩
  have haddr_lt : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ cr23Word N :=
    cr23Addr_lt N t hN htN C ⟨cr23D N - (j + 1), hi⟩ v
  have hmask_lt : cr23Mask N t C ⟨cr23D N - (j + 1), hi⟩ v < 2 ^ cr23Word N :=
    cr23Mask_lt N t C ⟨cr23D N - (j + 1), hi⟩ v
  -- **the new bound**: the touched word is inside the payload
  have haddrW : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
      < wordsOf (cr23Word N) (cr23R N t) :=
    addr_wordsOf N t hN htN C ⟨cr23D N - (j + 1), hi⟩ v
  -- first four body instructions
  set st1 : RAMState :=
    runBlock upBodyA (detEnv (cr23Word N) (cr23DecDet N t C)) s with hst1
  have h1mem : st1.mem = s.mem := by
    rw [hst1]
    exact upBodyA_mem _ _
  have h1r8 : st1.regs r8 = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by
    rw [hst1, upBodyA_r8]
    simp only [detEnv]
    rw [h7, hdetA, Nat.mod_eq_of_lt haddr_lt]
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
    rw [h7, h10, hdetA, Nat.mod_eq_of_lt haddr_lt, hdetM, Nat.mod_eq_of_lt hmask_lt,
      hm _ haddrW,
      Nat.mod_eq_of_lt (packMem_lt (cr23Word N) hW _ _),
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (packMem_lt (cr23Word N) hW _ _) hmask_lt), hval]
  -- the store
  set st2 : RAMState :=
    execInstr (iSt r8 r4) (detEnv (cr23Word N) (cr23DecDet N t C)) st1 with hst2
  have h2mem : st2.mem = Function.update s.mem (cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v)
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
    execInstr (iAdd r7 r7 r12) (detEnv (cr23Word N) (cr23DecDet N t C)) st2 with hst3
  set st4 : RAMState :=
    execInstr (iAdd r10 r10 r12) (detEnv (cr23Word N) (cr23DecDet N t C)) st3 with hst4
  set st5 : RAMState :=
    execInstr (iSub r6 r6 r13) (detEnv (cr23Word N) (cr23DecDet N t C)) st4 with hst5
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
  have hbody : runBlock progUpBody (detEnv (cr23Word N) (cr23DecDet N t C)) s = st5 := by
    simp only [upBody_split, runBlock_append, runBlock_cons, runBlock_nil, ← hst1, ← hst2,
      ← hst3, ← hst4, ← hst5]
  rw [hbody]
  have h5m : st5.mem = st2.mem := by
    simp only [hst5, hst4, hst3, execInstr_sub, execInstr_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro addr ha
    rw [h5m, h2mem, hpack addr]
    by_cases haddr : addr = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
    · rw [haddr, Function.update_self, hval,
        packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_pos rfl]
    · rw [Function.update_of_ne haddr, hm addr ha,
        packMem_cr23Lvl N t C v (cr23D N - (j + 1)) hi, if_neg haddr, Nat.xor_zero]
/-- **The payload after the whole loop**: with the countdown at `0` the payload is `y` plus the column
of `v`, which is what the outer element loop needs. -/
theorem body_result (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (v : Fin N) (s : RAMState)
    (h : UpData N t C y v 0 s) :
    ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      s.mem a = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm⟩ := h
  intro a ha
  rw [Nat.sub_zero, cr23Delta_full] at hm
  exact hm a ha
end DecXorPay
/-- The body of (c)'s outer loop, as a statement. -/
def decXorBody : Stmt :=
  Stmt.seq (Stmt.code decXorLoad)
    (Stmt.seq (Stmt.code decXorPre) (Stmt.seq decXorInner (Stmt.code decXorPost)))
theorem decXorStmt_eq : decXorStmt = Stmt.loop (Cond.lt r8 r1 r2) decXorBody := rfl
theorem decXorBody_len : decXorBody.len = 30 := by decide
/-- The registers `progUpBody` writes. -/
theorem progUpBody_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (h8 : d ≠ r8) (h9 : d ≠ r9) (h4 : d ≠ r4) (h7 : d ≠ r7) (h10 : d ≠ r10) (h6 : d ≠ r6) :
    (runBlock progUpBody E st).regs d = st.regs d := by
  refine runBlock_regs_frame progUpBody E st d ?_
  intro i hi hdest
  simp [progUpBody] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Instr.dest?] at hdest; exact h8 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h9 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h4 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h4 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact nomatch hdest
  · simp only [Instr.dest?] at hdest; exact h7 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h10 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h6 (Option.some.inj hdest).symm
theorem progUpBody_frame_r1 (E : RAMEnv) (st : RAMState) :
    (runBlock progUpBody E st).regs r1 = st.regs r1 :=
  progUpBody_frame E st r1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem progUpBody_frame_r2 (E : RAMEnv) (st : RAMState) :
    (runBlock progUpBody E st).regs r2 = st.regs r2 :=
  progUpBody_frame E st r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem progUpBody_frame_r14 (E : RAMEnv) (st : RAMState) :
    (runBlock progUpBody E st).regs r14 = st.regs r14 :=
  progUpBody_frame E st r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- The registers `decXorP2` writes. -/
theorem decXorP2_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (hd : d ∉ [r5, r6, r7, r15, r10]) : (runBlock decXorP2 E st).regs d = st.regs d :=
  decFrame_of_dests E st decXorP2 [r5, r6, r7, r15, r10] (by decide) d hd
/-- The registers `decXorP3` writes. -/
theorem decXorP3_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (hd : d ∉ [r11, r11, r12, r13]) : (runBlock decXorP3 E st).regs d = st.regs d :=
  decFrame_of_dests E st decXorP3 [r11, r11, r12, r13] (by decide) d hd
/-- The registers `decXorLoad` writes. -/
theorem decXorLoad_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (hd : d ∉ [r8, r8, r8, r0]) : (runBlock decXorLoad E st).regs d = st.regs d :=
  decFrame_of_dests E st decXorLoad [r8, r8, r8, r0] (by decide) d hd
/-- The registers `decXorPre` writes. -/
theorem decXorPre_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (hd : d ∉ [r8, r8, r3, r8, r8, r5, r6, r7, r15, r10, r11, r11, r12, r13]) :
    (runBlock decXorPre E st).regs d = st.regs d :=
  decFrame_of_dests E st decXorPre
    [r8, r8, r3, r8, r8, r5, r6, r7, r15, r10, r11, r11, r12, r13] (by decide) d hd
/-- `2 ^ cr23Word N > 32`: the word is more than five bits wide (`W ≥ 1024`). -/
theorem cr23_32_lt_word (N : ℕ) : 32 < 2 ^ cr23Word N := by
  have h : 5 < cr23Word N := by simp only [cr23Word]; omega
  calc 32 = 2 ^ 5 := by norm_num
    _ < 2 ^ cr23Word N := Nat.pow_lt_pow_right (by norm_num) h
/-- One iteration with a bounded cost: `Sem.loopStepPred` with `k ≤ cost` instead of `k = cost`. -/
theorem Sem.loopStepPredLe (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (s : RAMState) (R : RAMState → Prop) (cost : ℕ)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : s.pc = a) (hgo : c.eval s)
    (hbody : Sem P E (a + c.code.length + 1) a
      { runBlock c.code E s with pc := a + c.code.length + 1 }
      (fun k s'' => k ≤ cost ∧ R s'' ∧ s''.pc = a)) :
    Sem P E a a s (fun k s'' => k ≤ (c.code.length + 1) + cost ∧ R s'' ∧ s''.pc = a) := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hne : (runBlock c.code E s).regs c.test ≠ 0 := (Cond.eval_iff c E s hW).mp hgo
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E s)
      (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + 1 }) :=
    Sem.jz_next P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT hne
  refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = c.code.length + 1 ∧
      s' = { runBlock c.code E s with pc := a + c.code.length + 1 })
    (Q₂ := fun k₁ k₂ s' => k₁ = c.code.length + 1 ∧ k₂ ≤ cost ∧ R s' ∧ s'.pc = a)
    (Sem.trans htest hfall) ?_) ?_
  · intro k₁ s₁ hQ₁
    obtain ⟨rfl, rfl⟩ := hQ₁
    exact Sem.mono hbody (fun k s' h => ⟨rfl, h⟩)
  · intro k s' h
    obtain ⟨k₁, k₂, hk, h1, h2, hR, hpc'⟩ := h
    exact ⟨by omega, hR, hpc'⟩
/-- **The loop rule, bounded version.**  `Sem.loopPred` with `k ≤ cost j` for the iteration cost. -/
theorem Sem.loopPredLe (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (R : ℕ → RAMState → Prop) (cost : ℕ → ℕ),
      (∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ c.test → s.regs d = s'.regs d) →
        s.mem = s'.mem → R j s → R j s') →
      (∀ j, j < n → ∀ s, R j s → c.eval s) →
      (∀ s, R n s → ¬ c.eval s) →
      (∀ j, j < n → ∀ s, s.pc = a → R j s →
        Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
          (fun k s' => k ≤ cost j ∧ R (j + 1) s' ∧ s'.pc = a)) →
      ∀ s, s.pc = a → R 0 s →
        Sem P E a (a + c.code.length + b.len + 2) s
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
            R n s' ∧ s'.pc = a + c.code.length + b.len + 2) := by
  intro n
  induction n with
  | zero =>
      intro R cost hirr hgo hstop hstep s hpc hR
      refine Sem.mono (Sem.loopExit P E a c b s hAt hW hpc (hstop s hR)) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, ?_, rfl⟩
      exact hirr 0 s _ (fun d hd => (runBlock_cond_regs c E s d hd).symm)
        (runBlock_cond_mem c E s).symm hR
  | succ n ih =>
      intro R cost hirr hgo hstop hstep s hpc hR
      have hgo0 : c.eval s := hgo 0 (by omega) s hR
      have hfirst := Sem.loopStepPredLe P E a c b s (R 1) (cost 0) hAt hW hpc hgo0
        (hstep 0 (by omega) s hpc hR)
      have hirr' : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ c.test → s.regs d = s'.regs d) →
          s.mem = s'.mem → (fun j => R (j + 1)) j s → (fun j => R (j + 1)) j s' :=
        fun j s s' hd hm h => hirr (j + 1) s s' hd hm h
      have hgo' : ∀ j, j < n → ∀ s, (fun j => R (j + 1)) j s → c.eval s :=
        fun j hj s h => hgo (j + 1) (by omega) s h
      have hstop' : ∀ s, (fun j => R (j + 1)) n s → ¬ c.eval s :=
        fun s h => hstop s h
      have hstep' : ∀ j, j < n → ∀ s, s.pc = a → (fun j => R (j + 1)) j s →
          Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
            (fun k s' => k ≤ (fun j => cost (j + 1)) j ∧
              (fun j => R (j + 1)) (j + 1) s' ∧ s'.pc = a) :=
        fun j hj s hp hs => hstep (j + 1) (by omega) s hp hs
      refine Sem.mono (Sem.seq (Q₁ := fun k s' => k ≤ (c.code.length + 1) + cost 0 ∧ R 1 s' ∧
          s'.pc = a)
        (Q₂ := fun k₁ k₂ s' => k₁ ≤ (c.code.length + 1) + cost 0 ∧
          (k₂ ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            R (n + 1) s' ∧ s'.pc = a + c.code.length + b.len + 2)) hfirst ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨hk₁, hR1, hpc1⟩ := hQ₁
        exact Sem.mono (ih (fun j => R (j + 1)) (fun j => cost (j + 1)) hirr' hgo' hstop' hstep'
          s₁ hpc1 hR1) (fun k s' h => ⟨hk₁, h⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, hk, h1, h2, h3, h4⟩ := h
        rw [Finset.sum_range_succ']
        exact ⟨by omega, h3, h4⟩
/-- **What body (c)'s inner loop must not disturb**: the outer index `r1`, the outer bound `r2`, the
frame register `r14`, and every word outside the packed payload. -/
def DecXorSame (N t : ℕ) (st s : RAMState) : Prop :=
  s.regs r1 = st.regs r1 ∧ s.regs r2 = st.regs r2 ∧ s.regs r14 = st.regs r14 ∧
    (∀ addr, wordsOf (cr23Word N) (cr23R N t) ≤ addr → s.mem addr = st.mem addr)
/-- **One inner step, with the frame**: `DecXorPay.bodyIter` plus "the store is inside the payload". -/
theorem decXorBodyIter_frame (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2) (v : Fin N)
    (j : ℕ) (hj : j + 1 ≤ cr23D N) (P : Program) (a : ℕ)
    (hAtBody : At P (a + (Cond.neqz r6).code.length + 1) progUpBody)
    (hAtJmp : P[(a + (Cond.neqz r6).code.length + 1) + progUpBody.length]? = some (iJmp a))
    (st : RAMState) (hpc : st.pc = a + (Cond.neqz r6).code.length + 1)
    (hR : DecXorPay.UpData N t C y v (j + 1) st) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C))
      (a + (Cond.neqz r6).code.length + 1) a
      { st with pc := a + (Cond.neqz r6).code.length + 1 }
      (fun k s' => k ≤ progUpBody.length + 1 ∧ DecXorPay.UpData N t C y v j s' ∧
        DecXorSame N t st s' ∧ s'.pc = a) := by
  have hno : NoBranch progUpBody := by simp [progUpBody]
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set b : ℕ := a + (Cond.neqz r6).code.length + 1 with hb
  have hblk : Sem P E b (b + progUpBody.length) { st with pc := b }
      (fun k s' => k = progUpBody.length ∧ s' = runBlock progUpBody E { st with pc := b }) :=
    Sem.block P E b progUpBody { st with pc := b } hAtBody hno rfl
  have hpcB : (runBlock progUpBody E { st with pc := b }).pc = b + progUpBody.length := by
    rw [runBlock_pc progUpBody E _ hno]
  have hjmpSem : Sem P E (b + progUpBody.length) a
      (runBlock progUpBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock progUpBody E { st with pc := b } with pc := a }) :=
    Sem.exec P E (b + progUpBody.length) a _ (iJmp a) hAtJmp hpcB rfl
  -- the store address is a payload word, so the frame is untouched
  have hi : cr23D N - (j + 1) < cr23D N := by omega
  have hmem : ∀ addr, wordsOf (cr23Word N) (cr23R N t) ≤ addr →
      (runBlock progUpBody E { st with pc := b }).mem addr = st.mem addr := by
    intro addr ha
    refine DecXorPay.body_mem_frame E { st with pc := b } addr ?_
    intro hc
    have hr7 : ({ st with pc := b } : RAMState).regs r7
        = upBase N v.val + 2 * (cr23D N - (j + 1)) := hR.2.2.2.2.1
    have hdet : E.det (({ st with pc := b } : RAMState).regs r7) % 2 ^ E.W
        = cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v := by
      rw [hr7, hE]
      simp only [detEnv]
      rw [cr23DecDet_addr N t C hN v ⟨cr23D N - (j + 1), hi⟩,
        Nat.mod_eq_of_lt (cr23Addr_lt N t hN htN C ⟨cr23D N - (j + 1), hi⟩ v)]
    rw [hdet] at hc
    have hlt : cr23Addr N t C ⟨cr23D N - (j + 1), hi⟩ v
        < wordsOf (cr23Word N) (cr23R N t) :=
      DecXorPay.addr_wordsOf N t hN htN C ⟨cr23D N - (j + 1), hi⟩ v
    omega
  have hreg1 : (runBlock progUpBody E { st with pc := b }).regs r1 = st.regs r1 := by
    rw [progUpBody_frame_r1 E _]
  have hreg2 : (runBlock progUpBody E { st with pc := b }).regs r2 = st.regs r2 := by
    rw [progUpBody_frame_r2 E _]
  have hreg14 : (runBlock progUpBody E { st with pc := b }).regs r14 = st.regs r14 := by
    rw [progUpBody_frame_r14 E _]
  refine Sem.mono (Sem.trans hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨?_, DecXorPay.UpData_pc N t C y v j a _
    (DecXorPay.body_data N t hN htN C y v j hj { st with pc := b } hR), ?_, rfl⟩
  · simp [progUpBody]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hreg1
    · simpa using hreg2
    · simpa using hreg14
    · simpa using hmem
/-- **The inner loop, with the frame**: `DecXorPay.loop_data` plus `DecXorSame`. -/
theorem decXorLoop_frame (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2) (v : Fin N)
    (P : Program) (a : ℕ)
    (hAt : At P a (Stmt.compile decXorInner a))
    (st : RAMState) (hpc : st.pc = a) (hU : DecXorPay.UpData N t C y v (cr23D N) st) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2) st
      (fun k s' => k ≤ cr23D N * 10 + 1 ∧ DecXorPay.UpData N t C y v 0 s' ∧
        DecXorSame N t st s' ∧
        s'.pc = a + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2) := by
  have hInner : decXorInner = Stmt.loop (Cond.neqz r6) (Stmt.code progUpBody) := rfl
  rw [hInner] at hAt
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hW : 1 < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), s.regs = s'.regs → s.mem = s'.mem →
      (DecXorPay.UpData N t C y v j s ∧ j ≤ cr23D N ∧ DecXorSame N t st s) →
      (DecXorPay.UpData N t C y v j s' ∧ j ≤ cr23D N ∧ DecXorSame N t st s') := by
    intro j s s' hr hm h
    obtain ⟨h3, h4, h5, h6⟩ := h.2.2
    refine ⟨DecXorPay.UpData.irrel N t C y v j s s' hr hm h.1, h.2.1, ?_, ?_, ?_, ?_⟩
    · rw [← hr]; exact h3
    · rw [← hr]; exact h4
    · rw [← hr]; exact h5
    · rw [← hm]; exact h6
  have hstop : ∀ s, (DecXorPay.UpData N t C y v 0 s ∧ 0 ≤ cr23D N ∧ DecXorSame N t st s) →
      s.regs r6 = 0 := by
    intro s h
    exact h.1.2.2.2.1
  have hgo : ∀ j s, (DecXorPay.UpData N t C y v (j + 1) s ∧ j + 1 ≤ cr23D N ∧
      DecXorSame N t st s) → s.regs r6 ≠ 0 := by
    intro j s h
    rw [h.1.2.2.2.1]
    omega
  have hstep : ∀ j s, (DecXorPay.UpData N t C y v (j + 1) s ∧ j + 1 ≤ cr23D N ∧
      DecXorSame N t st s) →
      Sem P E (a + 1) a { s with pc := a + 1 }
        (fun k s' => k ≤ progUpBody.length + 1 ∧ (DecXorPay.UpData N t C y v j s' ∧
          j ≤ cr23D N ∧ DecXorSame N t st s') ∧ s'.pc = a) := by
    intro j s h
    obtain ⟨hU, hjD, hSame⟩ := h
    obtain ⟨-, -, hAtBody, hAtJmp⟩ := at_loop hAt
    have hlen : (Stmt.code progUpBody).len = progUpBody.length := rfl
    have hAtBody' : At P (a + (Cond.neqz r6).code.length + 1) progUpBody := hAtBody
    have hAtJmp' : P[(a + (Cond.neqz r6).code.length + 1) + progUpBody.length]? = some (iJmp a) := by
      rw [← hlen]
      exact hAtJmp
    have hpc' : ({ s with pc := a + 1 } : RAMState).pc
        = a + (Cond.neqz r6).code.length + 1 := rfl
    refine Sem.mono (decXorBodyIter_frame N t hN htN C y v j hjD P a hAtBody' hAtJmp'
      { s with pc := a + 1 } hpc' hU) ?_
    intro k s' hk
    obtain ⟨hk1, hU', hSame', hpcS⟩ := hk
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hSame'
    obtain ⟨ht1, ht2, ht3, ht4⟩ := hSame
    refine ⟨by omega, ⟨hU', by omega, ⟨?_, ?_, ?_, ?_⟩⟩, hpcS⟩
    · simpa using hs1.trans ht1
    · simpa using hs2.trans ht2
    · simpa using hs3.trans ht3
    · intro addr ha
      simpa using (hs4 addr ha).trans (ht4 addr ha)
  have hR0 : DecXorPay.UpData N t C y v (cr23D N) st ∧ cr23D N ≤ cr23D N ∧
      DecXorSame N t st st :=
    ⟨hU, le_rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hloop := Sem.loopCountUp P E a r6 (Stmt.code progUpBody) hAt hW (cr23D N)
    (fun j s => DecXorPay.UpData N t C y v j s ∧ j ≤ cr23D N ∧ DecXorSame N t st s)
    (progUpBody.length + 1) hirr hstop hgo hstep st hpc hR0
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1.1, h.2.1.2.2, h.2.2⟩)
  have hk := h.1
  have he : cr23D N * (1 + (progUpBody.length + 1)) + 1 = cr23D N * 10 + 1 := by
    rw [show progUpBody.length = 8 from by decide]
  rw [he] at hk
  exact hk
/-- The four chunks of `decXorBody`, read back out of one `At` fact. -/
theorem decXorBody_at {P : Program} {a : ℕ} (h : At P a (Stmt.compile decXorBody a)) :
    At P a decXorLoad ∧ At P (a + decXorLoad.length) decXorPre ∧
      At P (a + decXorLoad.length + decXorPre.length)
        (Stmt.compile decXorInner (a + decXorLoad.length + decXorPre.length)) ∧
      At P (a + decXorLoad.length + decXorPre.length + decXorInner.len) decXorPost := by
  have hsplit : Stmt.compile decXorBody a
      = decXorLoad ++ (decXorPre ++ (Stmt.compile decXorInner
          (a + decXorLoad.length + decXorPre.length) ++ decXorPost)) := rfl
  rw [hsplit] at h
  obtain ⟨h1, h2⟩ := At.append.mp h
  obtain ⟨h3, h4⟩ := At.append.mp h2
  obtain ⟨h5, h6⟩ := At.append.mp h4
  exact ⟨h1, h3, h5, h6⟩
/-- **The prologue of body (c) establishes the payload-restricted `UpData`** (at countdown `D`), and
leaves `r0`, `r1`, `r2`, `r14` and the whole memory alone. -/
theorem decXorPre_data (E : RAMEnv) (st : RAMState) (N t : ℕ)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2)
    (l : List ℕ) (i : ℕ) (v : Fin N)
    (h0 : st.regs r0 = v.val) (h14 : st.regs r14 = cr23DecFrame N t)
    (hD : st.mem (decSlot N t 0) = cr23D N)
    (hbase : E.det (v.val + 1) = upBase N v.val)
    (hpay : ∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      st.mem addr = packMem (cr23Word N) (y + decLstDelta N t C l i) addr)
    (hone : 1 < 2 ^ E.W) (hDlt : cr23D N < 2 ^ E.W) (hfr : cr23DecFrame N t + 1 < 2 ^ E.W)
    (hv : v.val + 1 < 2 ^ E.W) (hB : upBase N v.val < 2 ^ E.W)
    (hB1 : upBase N v.val + 1 < 2 ^ E.W) (h2w : 2 < 2 ^ E.W)
    (hE2 : upBase N v.val + 2 * cr23D N < 2 ^ E.W) :
    DecXorPay.UpData N t C (y + decLstDelta N t C l i) v (cr23D N) (runBlock decXorPre E st) ∧
      (runBlock decXorPre E st).mem = st.mem ∧
      (runBlock decXorPre E st).regs r0 = st.regs r0 ∧
      (runBlock decXorPre E st).regs r1 = st.regs r1 ∧
      (runBlock decXorPre E st).regs r2 = st.regs r2 ∧
      (runBlock decXorPre E st).regs r14 = st.regs r14 := by
  have hP1 := decXorP1_spec E st N t v.val (cr23D N) h0 h14 hD hone hDlt hfr hv
  have hP2 := decXorP2_spec E (runBlock decXorP1 E st) N t v.val (cr23D N)
    hP1.2.1 hP1.1 hbase hone hB hB1 hDlt
  have h2r3 : (runBlock decXorP2 E (runBlock decXorP1 E st)).regs r3 = cr23D N := by
    rw [decXorP2_frame E _ r3 (by decide)]
    exact hP1.1
  have hP3 := decXorP3_spec E (runBlock decXorP2 E (runBlock decXorP1 E st)) N t v.val (cr23D N)
    hP2.1 h2r3 hP2.2.2.2.1 hone h2w hE2
  have hpre : runBlock decXorPre E st
      = runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st)) := by
    rw [decXorPre_split, runBlock_append, runBlock_append]
  have hmem3 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).mem
      = st.mem := by
    rw [hP3.2.2.2, hP2.2.2.2.2.2, hP1.2.2]
  have hr3 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).regs r3
      = cr23D N := by
    rw [decXorP3_frame E _ r3 (by decide)]
    exact h2r3
  have hr5 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).regs r5
      = upBase N v.val := by
    rw [decXorP3_frame E _ r5 (by decide)]
    exact hP2.1
  have hr6 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).regs r6
      = cr23D N := by
    rw [decXorP3_frame E _ r6 (by decide)]
    exact hP2.2.1
  have hr7 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).regs r7
      = upBase N v.val := by
    rw [decXorP3_frame E _ r7 (by decide)]
    exact hP2.2.2.1
  have hr10 : (runBlock decXorP3 E (runBlock decXorP2 E (runBlock decXorP1 E st))).regs r10
      = upBase N v.val + 1 := by
    rw [decXorP3_frame E _ r10 (by decide)]
    exact hP2.2.2.2.2.1
  have hr0 : (runBlock decXorPre E st).regs r0 = st.regs r0 :=
    decXorPre_frame E st r0 (by decide)
  have hr1 : (runBlock decXorPre E st).regs r1 = st.regs r1 :=
    decXorPre_frame E st r1 (by decide)
  have hr2 : (runBlock decXorPre E st).regs r2 = st.regs r2 :=
    decXorPre_frame E st r2 (by decide)
  have hr14 : (runBlock decXorPre E st).regs r14 = st.regs r14 :=
    decXorPre_frame E st r14 (by decide)
  rw [hpre] at hr0 hr1 hr2 hr14 ⊢
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hmem3, hr0, hr1, hr2, hr14⟩
  · rw [hr0]; exact h0
  · exact hr3
  · exact hr5
  · exact hr6
  · rw [hr7, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  · rw [hr10, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  · exact hP3.1
  · exact hP3.2.1
  · exact hP3.2.2.1
  · intro addr ha
    rw [hmem3, Nat.sub_self, cr23Delta_zero]
    simpa using hpay addr ha
/-- The bump `i := i + 1` of body (c). -/
theorem decXorPost_spec (E : RAMEnv) (st : RAMState) (j : ℕ)
    (h1 : st.regs r1 = j) (hone : 1 < 2 ^ E.W) (hj : j + 1 < 2 ^ E.W) :
    (runBlock decXorPost E st).regs r1 = j + 1 ∧ (runBlock decXorPost E st).mem = st.mem ∧
      (runBlock decXorPost E st).regs r2 = st.regs r2 ∧
      (runBlock decXorPost E st).regs r14 = st.regs r14 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [decXorPost, h1, Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hj]
  · simp [decXorPost]
  · simp [decXorPost]
  · simp [decXorPost]
/-- **One more candidate value adds its column**: `y + decLstDelta i + column v = y + decLstDelta (i+1)`
when `v` is the `i`-th candidate.  This is the bridge from `DecXorPay.body_result` (which produces the
left-hand side) to `DecXorInv`'s payload clause at `i + 1`. -/
theorem decXor_delta_step (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (y : Fin (cr23R N t) → ZMod 2) (l : List ℕ) (i : ℕ) (v : Fin N)
    (hv : v.val = l.getD i 0) :
    y + decLstDelta N t C l i + cr23Sketch N t C (Pi.single v 1)
      = y + decLstDelta N t C l (i + 1) := by
  have h : l.getD i 0 < N := hv ▸ v.isLt
  have hve : v = ⟨l.getD i 0, h⟩ := Fin.ext hv
  rw [hve, decLstDelta_succ N t C l i h, ← cr23Delta_full N t C ⟨l.getD i 0, h⟩, add_assoc]
/-- 2·t + 1 ≤ cr23DecEnd: the candidate list sits inside the frame. -/
theorem cr23DecEnd_ge_two (N t : ℕ) : 2 * t + 1 ≤ cr23DecEnd N t := by
  rw [cr23DecEnd_form]
  generalize h : 2 ^ (cr23Lb N + 1) = y
  omega
/-- The candidate-list address decCandBase + j is inside the frame. -/
theorem cr23DecEnd_ge_cand (N t j : ℕ) (hj : j < 2 * t + 1) :
    cr23DecFrame N t + 32 + j < cr23DecEnd N t := by
  rw [cr23DecEnd_form]
  generalize h : 2 ^ (cr23Lb N + 1) = y
  omega
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
/-- A product of two `0/1` numbers is `0/1`. -/
theorem dec_mul_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  have ha' : a < 2 := by omega
  have hb' : b < 2 := by omega
  interval_cases a <;> interval_cases b <;> simp
/-- **`DecCandInv`** (§10.4): the loop counter is `b`, the list length is `len`, the list is stored at
`decCandBase`, it is duplicate-free, all its entries are coordinates, the tag array holds `tag`
exactly on the list, and the list is the set (b) must produce.

**The two tag clauses are restricted to the tag array's own region** `v < 2 ^ (cr23Lb N + 1)` — the
same bound `DecData` uses, and exactly the region `[decTagBase, decMstBase)`.  Above it lies the
master list (`decMstBase N t = decTagBase N t + 2 ^ (cr23Lb N + 1)` *by definition*), which holds
candidate values `< N` and certainly not tags, so an unrestricted assertion there is false from round
one on (`decHtag_not_implied` in `_cr23_roundf.lean.txt`).  The second clause is the "domination"
half: every tag cell is `≤ tag`, which is what makes the *next* round's `DecData` tag bound
(`mem < tag + 1`) hold. -/
def DecCandInv (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState) : Prop :=
  st.regs r0 = b ∧ st.regs r2 = len ∧
  (∀ i, i < len → st.mem (decCandBase N t + i) = l.getD i 0) ∧
  l.Nodup ∧ len = l.length ∧ (∀ i ∈ l, i < N) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → (st.mem (decTagBase N t + v) = tag ↔ v ∈ l)) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → st.mem (decTagBase N t + v) ≤ tag) ∧
  l.toFinset
    = ((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
        (fun v => v < N)
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
/-- **The machine's conditional write.**  With `sel ∈ {0,1}` the modular update
`old + sel·((tag + 2^W - old) % 2^W)` stores `tag` when `sel = 1` and leaves `old` alone otherwise —
with no hypothesis on the order of `old` and `tag`. -/
theorem decCand_upd_mod (W old tag sel : ℕ) (ho : old < 2 ^ W) (ht : tag < 2 ^ W)
    (hs : sel ≤ 1) :
    (old + sel * ((tag + 2 ^ W - old) % 2 ^ W)) % 2 ^ W
      = if sel = 1 then tag else old := by
  rcases (by omega : sel = 0 ∨ sel = 1) with h | h
  · rw [h, if_neg (by omega), Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt ho]
  · rw [h, if_pos rfl, Nat.one_mul]
    by_cases hle : old ≤ tag
    · have he : (tag + 2 ^ W - old) % 2 ^ W = tag - old := by
        rw [show tag + 2 ^ W - old = (tag - old) + 2 ^ W from by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [he, show old + (tag - old) = tag from by omega, Nat.mod_eq_of_lt ht]
    · have hlt : tag < old := by omega
      have he : (tag + 2 ^ W - old) % 2 ^ W = 2 ^ W - (old - tag) := by
        rw [show tag + 2 ^ W - old = 2 ^ W - (old - tag) from by omega,
          Nat.mod_eq_of_lt (by omega)]
      rw [he, show old + (2 ^ W - (old - tag)) = 2 ^ W + tag from by omega,
        show 2 ^ W + tag = tag + 2 ^ W from by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt ht]
/-- A `0/1` mask survives the `% 2^W` of every register write. -/
theorem decCand_ind_mod (W : ℕ) (P : Prop) [Decidable P] (hW : 1 < 2 ^ W) :
    (if P then 1 else 0) % 2 ^ W = if P then 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt hW
  · exact Nat.zero_mod _
/-- Two strict comparisons of the same pair are never both `1`, so their sum is a `0/1` mask. -/
theorem decCand_ind_add (a b : ℕ) :
    (if a < b then 1 else 0) + (if b < a then 1 else 0) ≤ 1 := by
  by_cases h1 : a < b
  · rw [if_pos h1, if_neg (show ¬ b < a by omega)]
  · rw [if_neg h1]
    by_cases h2 : b < a
    · rw [if_pos h2]
    · rw [if_neg h2]
      norm_num
/-- A `ZMod 2` element whose `val` is `1` is `1`: `decBit` reads the `val`, `cr23OddB_read` reads
`= 1`. -/
theorem decCand_zmod2_val_one {z : ZMod 2} (h : z.val = 1) : z = 1 := by
  rw [← ZMod.natCast_zmod_val z, h]
  norm_num
/-- **Membership in `cr23OddB` is oddness of the load** (the occupied-bucket side condition is
automatic: an odd load is positive). -/
theorem decCand_oddB_mem {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D)
    (b : Fin M) : b ∈ cr23OddB C S s ↔ Odd (cr23Ld C S s b) := by
  rw [cr23OddB, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨k, hk⟩ := h
    have hpos : 0 < (S.filter (fun v => C v s = b)).card := by
      have he : cr23Ld C S s b = (S.filter (fun v => C v s = b)).card := rfl
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    obtain ⟨hvS, hvb⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_image.mpr ⟨v, hvS, hvb⟩
/-- **The machine's parity bit is the bucket's oddness**: the `par` of check `(s,j)` is `1` exactly
when bucket `j` of seed `s` is odd. -/
theorem decCand_par_one {N t : ℕ} (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (j : Fin (cr23M t)) :
    (decBit N t C x (cr23Check N t s j) = 1) ↔ j ∈ cr23OddB C (cr23Supp x) s := by
  rw [← cr23OddB_read, decBit_eq_check, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, decCand_zmod2_val_one h⟩,
    fun h => by rw [h.2, ZMod.val_one 2]⟩
theorem decCand_getD_append {l : List ℕ} {x i : ℕ} (h : i < l.length) :
    (l ++ [x]).getD i 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih (by simpa using h)
theorem decCand_getD_concat (l : List ℕ) (x : ℕ) : (l ++ [x]).getD l.length 0 = x := by
  induction l with
  | nil => rfl
  | cons a t ih => simpa using ih
theorem decCand_mem_concat (l : List ℕ) (x v : ℕ) : v ∈ l ++ [x] ↔ v ∈ l ∨ v = x := by
  simp
theorem decCand_nodup_concat (x : ℕ) : ∀ l : List ℕ, l.Nodup → x ∉ l → (l ++ [x]).Nodup
  | [], _, _ => by simp
  | a :: t, h, hx => by
      rw [List.nodup_cons] at h
      rw [List.cons_append, List.nodup_cons]
      have h1 : x ∉ t := fun hc => hx (by simp [hc])
      have h2 : a ≠ x := fun hc => hx (by simp [hc])
      refine ⟨?_, decCand_nodup_concat x t h.2 h1⟩
      intro hac
      rw [decCand_mem_concat] at hac
      rcases hac with h3 | h3
      · exact h.1 h3
      · exact h2 h3
theorem decCand_cand_lt_tag (N t len : ℕ) (hlen : len < 2 * t + 1) :
    decCandBase N t + len < decTagBase N t := by
  simp only [decTagBase]
  omega
theorem decCand_candAddr_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {j : ℕ}
    (hj : j < 2 * t + 1) : decCandBase N t + j < 2 ^ cr23Word N :=
  cr23_lt_word_of_le_end N t hN htN (le_of_lt (cr23DecEnd_ge_cand N t j hj))
theorem decCand_tagBase_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    decTagBase N t < 2 ^ cr23Word N := by
  refine cr23_lt_word_of_le_end N t hN htN ?_
  have h1 : decTagBase N t ≤ decMstBase N t := decTagBase_le_mstBase N t
  have h2 : decMstBase N t ≤ decParBase N t := decMstBase_le_parBase N t
  have h3 : decParBase N t ≤ decOutBase N t := by
    simp only [decOutBase]; exact dec_le_add_self _ _
  have h4 : decOutBase N t ≤ cr23DecEnd N t := by
    simp only [cr23DecEnd]; exact dec_le_add_self _ _
  omega
theorem decCand_tagAddr_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {v : ℕ}
    (hv : v < 2 ^ (cr23Lb N + 1)) : decTagBase N t + v < 2 ^ cr23Word N := by
  have h2 : decTagBase N t + v < decTagBase N t + 2 ^ (cr23Lb N + 1) := by omega
  have h3 : decTagBase N t + 2 ^ (cr23Lb N + 1) = decMstBase N t := by
    simp only [decMstBase]
  have h5 : decMstBase N t ≤ decParBase N t := decMstBase_le_parBase N t
  have h6 : decParBase N t ≤ decOutBase N t := by
    simp only [decOutBase]; exact dec_le_add_self _ _
  have h7 : decOutBase N t ≤ cr23DecEnd N t := by
    simp only [cr23DecEnd]; exact dec_le_add_self _ _
  have h8 : decTagBase N t + v < cr23DecEnd N t := by omega
  exact cr23_lt_word_of_le_end N t hN htN (le_of_lt h8)
theorem decCandInit_split :
    decCandInit = decCandIA ++ decCandIB ++ decCandIC ++ decCandID := rfl
theorem decCandInit_len : decCandInit.length = 16 := by decide
theorem decCandBody_split :
    decCandBody = decCandBA ++ decCandBB ++ decCandBC ++ decCandBD ++ decCandBE ++ decCandBF
      ++ decCandBG ++ decCandBH := rfl
theorem decCandBody_len : decCandBody.length = 36 := by decide
/-- **The candidate scan's loop invariant.**  `l` holds the labels contributed by the buckets
`0 … b-1`, in scan order; it is stored at `decCandBase`, duplicate-free, all entries are coordinates;
the tag array holds `tag` exactly on `l` **inside its own region** `v < 2 ^ (cr23Lb N + 1)` (above it
lies the master list, see `DecCandInv`), every such cell is `≤ tag`, and the payload is untouched. -/
def DecCandInvP (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState) : Prop :=
  st.regs r0 = b ∧
  st.regs r2 = len ∧
  st.regs r3 = tag ∧
  st.regs r4 = s.val ∧
  st.regs r7 = cr23M t ∧
  st.regs r8 = cr23Lb N + 1 ∧
  st.regs r10 = cr23Lb N ∧
  st.regs r11 = 1 ∧
  st.regs r12 = 1024 ∧
  st.regs r14 = cr23DecFrame N t ∧
  (∀ i, i < len → st.mem (decCandBase N t + i) = l.getD i 0) ∧
  l.Nodup ∧
  len = l.length ∧
  (∀ i ∈ l, i < N) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → (st.mem (decTagBase N t + v) = tag ↔ v ∈ l)) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → st.mem (decTagBase N t + v) ≤ tag) ∧
  (∀ v, v ∈ l ↔ v < N ∧ ∃ j : Fin (cr23M t), j.val < b ∧
      Odd (cr23Ld C (cr23Supp x) s j) ∧ cr23XorLbl C (cr23Supp x) s j = v) ∧
  (∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a) ∧
  st.mem (decSlot N t 1) = N ∧
  st.mem (decSlot N t 9) = decCandBase N t ∧
  st.mem (decSlot N t 10) = decTagBase N t
/-- The invariant never looks at the program counter. -/
theorem DecCandInvP_pc (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (p : ℕ) (st : RAMState)
    (h : DecCandInvP N t C x s tag b len l st) :
    DecCandInvP N t C x s tag b len l { st with pc := p } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩
theorem decCandIA_spec (E : RAMEnv) (st : RAMState) (F Mv : ℕ)
    (h14 : st.regs r14 = F) (hF : F + 11 < 2 ^ E.W) (hM : st.mem (F + 3) % 2 ^ E.W = Mv) :
    (runBlock decCandIA E st).regs r0 = 0 ∧ (runBlock decCandIA E st).regs r2 = 0 ∧
      (runBlock decCandIA E st).regs r7 = Mv ∧ (runBlock decCandIA E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r0 → d ≠ r2 → d ≠ r6 → d ≠ r7 →
        (runBlock decCandIA E st).regs d = st.regs d) := by
  have h3 : (3 : ℕ) % 2 ^ E.W = 3 := Nat.mod_eq_of_lt (by omega)
  have hF3 : F + 3 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandIA]
  · simp [decCandIA]
  · simp [decCandIA, h14, h3, Nat.mod_eq_of_lt hF3, hM]
  · simp [decCandIA]
  · intro d hd1 hd2 hd3 hd4
    simp [decCandIA, hd1, hd2, hd3, hd4]
theorem decCandIB_spec (E : RAMEnv) (st : RAMState) (F Lv : ℕ)
    (h14 : st.regs r14 = F) (hF : F + 11 < 2 ^ E.W)
    (hL : st.mem (F + 4) % 2 ^ E.W = Lv) :
    (runBlock decCandIB E st).regs r8 = Lv ∧ (runBlock decCandIB E st).regs r6 = F + 5 ∧
      (runBlock decCandIB E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r6 → d ≠ r8 → (runBlock decCandIB E st).regs d = st.regs d) := by
  have h4 : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by omega)
  have h5 : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by omega)
  have hF4 : F + 4 < 2 ^ E.W := by omega
  have hF5 : F + 5 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [decCandIB, h14, h4, h5, Nat.mod_eq_of_lt hF4, hL]
  · simp [decCandIB, h14, h4, h5, Nat.mod_eq_of_lt hF5]
  · simp [decCandIB]
  · intro d hd hd2
    simp [decCandIB, hd, hd2]
theorem decCandIC_spec (E : RAMEnv) (st : RAMState) (F lb tg : ℕ)
    (h6 : st.regs r6 = F + 5) (h14 : st.regs r14 = F) (hF : F + 11 < 2 ^ E.W)
    (hlb : st.mem (F + 5) % 2 ^ E.W = lb) (htg : st.mem (F + 9) % 2 ^ E.W = tg) :
    (runBlock decCandIC E st).regs r10 = lb ∧ (runBlock decCandIC E st).regs r3 = tg ∧
      (runBlock decCandIC E st).regs r11 = 1 ∧ (runBlock decCandIC E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r6 → d ≠ r10 → d ≠ r3 → d ≠ r11 →
        (runBlock decCandIC E st).regs d = st.regs d) := by
  have hF5 : F + 5 < 2 ^ E.W := by omega
  have hF9 : F + 9 < 2 ^ E.W := by omega
  have h9m : (9 : ℕ) % 2 ^ E.W = 9 := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandIC, h6, h14, Nat.mod_eq_of_lt hF5, hlb]
  · simp [decCandIC, h6, h14, h9m, Nat.mod_eq_of_lt hF9, htg]
  · simp [decCandIC, h6, h14, h9m, h1]
  · simp [decCandIC]
  · intro d hd1 hd2 hd3 hd4
    simp [decCandIC, hd1, hd2, hd3, hd4]
theorem decCandID_spec (E : RAMEnv) (st : RAMState) (h1024 : 1024 < 2 ^ E.W) :
    (runBlock decCandID E st).regs r12 = 1024 ∧ (runBlock decCandID E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r12 → (runBlock decCandID E st).regs d = st.regs d) := by
  have h1024m : (1024 : ℕ) % 2 ^ E.W = 1024 := Nat.mod_eq_of_lt h1024
  refine ⟨?_, ?_, ?_⟩
  · simp [decCandID, h1024m]
  · simp [decCandID]
  · intro d hd
    simp [decCandID, hd]
theorem decCandBA_spec (E : RAMEnv) (st : RAMState) (Mv sv b : ℕ)
    (h7 : st.regs r7 = Mv) (h4 : st.regs r4 = sv) (h0 : st.regs r0 = b)
    (h12 : st.regs r12 = 1024) (h1024 : 1024 ≤ 2 ^ E.W)
    (hMs : Mv * sv < 2 ^ E.W) (hq : Mv * sv + b < 2 ^ E.W)
    (hqw : (Mv * sv + b) / 1024 < 2 ^ E.W) :
    (runBlock decCandBA E st).regs r5 = st.mem ((Mv * sv + b) / 1024) % 2 ^ E.W ∧
      (runBlock decCandBA E st).regs r6 = (Mv * sv + b) % 1024 ∧
      (runBlock decCandBA E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r6 → d ≠ r5 → (runBlock decCandBA E st).regs d = st.regs d) := by
  have hq1024 : (Mv * sv + b) % 1024 < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h1024
  have hmd : st.mem ((Mv * sv + b) / 1024 % 2 ^ E.W) = st.mem ((Mv * sv + b) / 1024) := by
    rw [Nat.mod_eq_of_lt hqw]
  have h1 : Mv * sv % 2 ^ E.W = Mv * sv := Nat.mod_eq_of_lt hMs
  have h2 : (Mv * sv + b) % 2 ^ E.W = Mv * sv + b := Nat.mod_eq_of_lt hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [decCandBA, h7, h4, h0, h12, h1, h2, Nat.mod_eq_of_lt hqw, hmd]
  · simp [decCandBA, h7, h4, h0, h12, h1, h2, Nat.mod_eq_of_lt hq1024]
  · simp [decCandBA]
  · intro d hd hd2
    simp [decCandBA, hd, hd2]
theorem decCandBB_spec (E : RAMEnv) (st : RAMState) (word qm Lb1 lb : ℕ)
    (h5 : st.regs r5 = word) (h6 : st.regs r6 = qm) (h8 : st.regs r8 = Lb1)
    (h11 : st.regs r11 = 1) (h10 : st.regs r10 = lb)
    (hword : word < 2 ^ E.W) (hoff : qm * Lb1 < 2 ^ E.W) (h2lb : 2 ^ lb < 2 ^ E.W) :
    (runBlock decCandBB E st).regs r5 = word / 2 ^ (qm * Lb1) ∧
      (runBlock decCandBB E st).regs r1 = 2 ^ lb ∧
      (runBlock decCandBB E st).regs r15 = word / 2 ^ (qm * Lb1) / 2 ^ lb ∧
      (runBlock decCandBB E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r6 → d ≠ r5 → d ≠ r1 → d ≠ r15 →
        (runBlock decCandBB E st).regs d = st.regs d) := by
  have hqmL : qm * Lb1 % 2 ^ E.W = qm * Lb1 := Nat.mod_eq_of_lt hoff
  have hsh : word / 2 ^ (qm * Lb1) % 2 ^ E.W = word / 2 ^ (qm * Lb1) :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hword)
  have hdiv : word / 2 ^ (qm * Lb1) / 2 ^ lb < 2 ^ E.W :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt (Nat.div_le_self _ _) hword)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandBB, h5, h6, h8, h11, h10, hqmL, hsh]
  · simp [decCandBB, h5, h6, h8, h11, h10, hqmL, hsh, Nat.one_mul,
      Nat.mod_eq_of_lt h2lb]
  · simp [decCandBB, h5, h6, h8, h11, h10, hqmL, hsh, Nat.one_mul,
      Nat.mod_eq_of_lt h2lb, Nat.mod_eq_of_lt hdiv]
  · simp [decCandBB]
  · intro d hd1 hd2 hd3 hd4
    simp [decCandBB, hd1, hd2, hd3, hd4]
theorem decCandBC_spec (E : RAMEnv) (st : RAMState) (p0 cf lb F Nv : ℕ)
    (h15 : st.regs r15 = p0) (h5 : st.regs r5 = cf) (h1 : st.regs r1 = 2 ^ lb)
    (h11 : st.regs r11 = 1) (h14 : st.regs r14 = F)
    (hcf : cf < 2 ^ E.W) (hF : F + 11 < 2 ^ E.W)
    (hNm : st.mem (F + 2) % 2 ^ E.W = Nv) :
    (runBlock decCandBC E st).regs r15 = p0 % 2 ∧
      (runBlock decCandBC E st).regs r5 = cf % 2 ^ lb ∧
      (runBlock decCandBC E st).regs r6 = Nv ∧
      (runBlock decCandBC E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r15 → d ≠ r6 → d ≠ r5 →
        (runBlock decCandBC E st).regs d = st.regs d) := by
  have hF2 : F + 2 < 2 ^ E.W := by omega
  have h2d : (2 : ℕ) % 2 ^ E.W = 2 := Nat.mod_eq_of_lt (by omega)
  have hmod : p0 % 2 % 2 ^ E.W = p0 % 2 := by
    refine Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) ?_)
    omega
  have hcfm : cf % 2 ^ lb % 2 ^ E.W = cf % 2 ^ lb :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) hcf)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandBC, h15, h5, h1, h11, h14, hmod]
  · simp [decCandBC, h15, h5, h1, h11, h14, hmod, hcfm]
  · simp [decCandBC, h15, h5, h1, h11, h14, hmod, hcfm, h2d, Nat.mod_eq_of_lt hF2, hNm]
  · simp [decCandBC]
  · intro d hd1 hd2 hd3
    simp [decCandBC, hd1, hd2, hd3]
theorem decCandBD_spec (E : RAMEnv) (st : RAMState) (lbl Nv par F cb : ℕ)
    (h6 : st.regs r6 = Nv) (h5 : st.regs r5 = lbl) (h15 : st.regs r15 = par)
    (h14 : st.regs r14 = F) (hpar : par ≤ 1) (hW1 : 1 < 2 ^ E.W) (hF : F + 11 < 2 ^ E.W)
    (hCB : st.mem (F + 10) % 2 ^ E.W = cb) :
    (runBlock decCandBD E st).regs r6 = (if lbl < Nv then 1 else 0) ∧
      (runBlock decCandBD E st).regs r15 = par * (if lbl < Nv then 1 else 0) ∧
      (runBlock decCandBD E st).regs r1 = cb ∧
      (runBlock decCandBD E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r6 → d ≠ r15 → d ≠ r1 →
        (runBlock decCandBD E st).regs d = st.regs d) := by
  have hF10 : F + 10 < 2 ^ E.W := by omega
  have hif : (if lbl < Nv then 1 else 0) % 2 ^ E.W = (if lbl < Nv then 1 else 0) :=
    decCand_ind_mod E.W (lbl < Nv) hW1
  have hparW : par < 2 ^ E.W := by omega
  have hmul : (if lbl < Nv then par else 0) % 2 ^ E.W = (if lbl < Nv then par else 0) := by
    split_ifs with hh
    · exact Nat.mod_eq_of_lt hparW
    · exact Nat.zero_mod _
  have h10 : (10 : ℕ) % 2 ^ E.W = 10 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandBD, h6, h5, h15, h14, hif]
  · simp [decCandBD, h6, h5, h15, h14, hif, hmul]
  · simp [decCandBD, h6, h5, h15, h14, hif, hmul, h10, Nat.mod_eq_of_lt hF10, hCB]
  · simp [decCandBD]
  · intro d hd1 hd2 hd3
    simp [decCandBD, hd1, hd2, hd3]
theorem decCandBE_spec (E : RAMEnv) (st : RAMState) (cb len lbl F : ℕ)
    (h1 : st.regs r1 = cb) (h2 : st.regs r2 = len) (h5 : st.regs r5 = lbl)
    (h14 : st.regs r14 = F) (hcl : cb + len < 2 ^ E.W) (hF : F + 11 < 2 ^ E.W)
    (hne : F + 11 ≠ cb + len) :
    (runBlock decCandBE E st).regs r1 = st.mem (F + 11) % 2 ^ E.W ∧
      (runBlock decCandBE E st).mem = Function.update st.mem (cb + len) lbl ∧
      (∀ d : Fin 16, d ≠ r1 → (runBlock decCandBE E st).regs d = st.regs d) := by
  have h11 : (11 : ℕ) % 2 ^ E.W = 11 := Nat.mod_eq_of_lt (by omega)
  have hupd : Function.update st.mem (cb + len) lbl (F + 11) = st.mem (F + 11) :=
    Function.update_of_ne hne lbl st.mem
  refine ⟨?_, ?_, ?_⟩
  · simp [decCandBE, h1, h2, h5, h14, h11, Nat.mod_eq_of_lt hcl, Nat.mod_eq_of_lt hF, hupd]
  · simp [decCandBE, h1, h2, h5, h14, Nat.mod_eq_of_lt hcl]
  · intro d hd
    simp [decCandBE, hd]
theorem decCandBF_spec (E : RAMEnv) (st : RAMState) (tb lbl tg old : ℕ)
    (h1 : st.regs r1 = tb) (h5 : st.regs r5 = lbl) (h3 : st.regs r3 = tg)
    (hW1 : 1 < 2 ^ E.W) (htb : tb + lbl < 2 ^ E.W)
    (hold : st.mem (tb + lbl) % 2 ^ E.W = old) :
    (runBlock decCandBF E st).regs r1 = tb + lbl ∧
      (runBlock decCandBF E st).regs r6 = old ∧
      (runBlock decCandBF E st).regs r13 = (if tg < old then 1 else 0) ∧
      (runBlock decCandBF E st).regs r5
        = (if old < tg then 1 else 0) + (if tg < old then 1 else 0) ∧
      (runBlock decCandBF E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r1 → d ≠ r6 → d ≠ r13 → d ≠ r5 →
        (runBlock decCandBF E st).regs d = st.regs d) := by
  have hm1 : (if old < tg then 1 else 0) % 2 ^ E.W = if old < tg then 1 else 0 :=
    decCand_ind_mod E.W (old < tg) hW1
  have hm2 : (if tg < old then 1 else 0) % 2 ^ E.W = if tg < old then 1 else 0 :=
    decCand_ind_mod E.W (tg < old) hW1
  have hadd : ((if old < tg then 1 else 0) + (if tg < old then 1 else 0)) % 2 ^ E.W
      = (if old < tg then 1 else 0) + (if tg < old then 1 else 0) :=
    Nat.mod_eq_of_lt (by
      have := decCand_ind_add old tg
      omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandBF, h1, h5, h3, hW1, Nat.mod_eq_of_lt htb]
  · simp [decCandBF, h1, h5, h3, hW1, Nat.mod_eq_of_lt htb, hold]
  · simp [decCandBF, h1, h5, h3, hW1, Nat.mod_eq_of_lt htb, hold, hm1, hm2]
  · simp [decCandBF, h1, h5, h3, hW1, Nat.mod_eq_of_lt htb, hold, hm1, hm2, hadd]
  · simp [decCandBF]
  · intro d hd1 hd2 hd3 hd4
    simp [decCandBF, hd1, hd2, hd3, hd4]
theorem decCandBG_spec (E : RAMEnv) (st : RAMState) (ps ne len tg old : ℕ)
    (h15 : st.regs r15 = ps) (h5 : st.regs r5 = ne) (h2 : st.regs r2 = len)
    (h3 : st.regs r3 = tg) (h6 : st.regs r6 = old)
    (hps : ps ≤ 1) (hne : ne ≤ 1) (hlen : len + 1 < 2 ^ E.W) :
    (runBlock decCandBG E st).regs r15 = ps * ne ∧
      (runBlock decCandBG E st).regs r2 = len + ps * ne ∧
      (runBlock decCandBG E st).regs r6
        = (old + ((tg + 2 ^ E.W - old) % 2 ^ E.W) * (ps * ne) % 2 ^ E.W) % 2 ^ E.W ∧
      (runBlock decCandBG E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r15 → d ≠ r2 → d ≠ r5 → d ≠ r13 → d ≠ r6 →
        (runBlock decCandBG E st).regs d = st.regs d) := by
  have hsel : ps * ne ≤ 1 := by
    calc ps * ne ≤ 1 * 1 := Nat.mul_le_mul hps hne
      _ = 1 := Nat.one_mul 1
  have hselW : ps * ne % 2 ^ E.W = ps * ne := Nat.mod_eq_of_lt (by omega)
  have hlenW : (len + ps * ne) % 2 ^ E.W = len + ps * ne := Nat.mod_eq_of_lt (by omega)
  have hx : (tg + 2 ^ E.W - old) % 2 ^ E.W < 2 ^ E.W := Nat.mod_lt _ (by omega)
  have hprod : ((tg + 2 ^ E.W - old) % 2 ^ E.W) * (ps * ne) % 2 ^ E.W
      = ((tg + 2 ^ E.W - old) % 2 ^ E.W) * (ps * ne) := by
    refine Nat.mod_eq_of_lt ?_
    calc ((tg + 2 ^ E.W - old) % 2 ^ E.W) * (ps * ne)
        ≤ ((tg + 2 ^ E.W - old) % 2 ^ E.W) * 1 := Nat.mul_le_mul_left _ hsel
      _ = (tg + 2 ^ E.W - old) % 2 ^ E.W := Nat.mul_one _
      _ < 2 ^ E.W := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decCandBG, h15, h5, h2, h3, h6, hselW]
  · simp [decCandBG, h15, h5, h2, h3, h6, hselW, hlenW]
  · simp [decCandBG, h15, h5, h2, h3, h6, hselW, hprod]
  · simp [decCandBG]
  · intro d hd1 hd2 hd3 hd4 hd5
    simp [decCandBG, hd1, hd2, hd3, hd4, hd5]
theorem decCandBH_spec (E : RAMEnv) (st : RAMState) (ta val b : ℕ)
    (h1 : st.regs r1 = ta) (h6 : st.regs r6 = val) (h0 : st.regs r0 = b)
    (h11 : st.regs r11 = 1) (hb : b + 1 < 2 ^ E.W) :
    (runBlock decCandBH E st).regs r0 = b + 1 ∧
      (runBlock decCandBH E st).mem = Function.update st.mem ta val ∧
      (∀ d : Fin 16, d ≠ r0 → (runBlock decCandBH E st).regs d = st.regs d) := by
  have hW1 : 1 < 2 ^ E.W := by omega
  have h1m : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW1
  refine ⟨?_, ?_, ?_⟩
  · simp [decCandBH, h1, h6, h0, h11, h1m, Nat.mod_eq_of_lt hb]
  · simp [decCandBH, h1, h6]
  · intro d hd
    simp [decCandBH, hd]
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
/-- The label of bucket `jj`: the label XOR of the bucket. -/
def decCandLbl (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (jj : Fin (cr23M t)) : ℕ := cr23XorLbl C (cr23Supp x) s jj
/-- The parity bit of bucket `jj`: `1` exactly when the bucket is odd. -/
def decCandPar (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (jj : Fin (cr23M t)) : ℕ := decBit N t C x (cr23Check N t s jj)
/-- The tag cell the bucket reads: `old`. -/
def decCandOld (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (jj : Fin (cr23M t)) (st : RAMState) : ℕ :=
  st.mem (decTagBase N t + decCandLbl N t C x s jj)
/-- The two comparison masks of one bucket. -/
def decCandNeOf (tag old : ℕ) : ℕ := (if old < tag then 1 else 0) + (if tag < old then 1 else 0)
/-- `1 - eq` of §10.4, in the machine's `g1 + g2` form. -/
def decCandNe (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag : ℕ) (jj : Fin (cr23M t)) (st : RAMState) : ℕ :=
  decCandNeOf tag (decCandOld N t C x s jj st)
/-- **The selection mask**: `sel = 1` iff the bucket is odd, its label names a coordinate and it is
new. -/
def decCandSel (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag : ℕ) (jj : Fin (cr23M t)) (st : RAMState) : ℕ :=
  decCandPar N t C x s jj * (if decCandLbl N t C x s jj < N then 1 else 0)
    * decCandNe N t C x s tag jj st
theorem decCand_neOf_one (tag old : ℕ) : decCandNeOf tag old = 1 ↔ old ≠ tag := by
  unfold decCandNeOf
  constructor
  · intro h he
    rw [he] at h
    omega
  · intro h
    have hle := decCand_ind_add old tag
    have hne : (if old < tag then 1 else 0) + (if tag < old then 1 else 0) ≠ 0 := by
      intro h0
      rw [Nat.add_eq_zero_iff] at h0
      obtain ⟨h1, h2⟩ := h0
      by_cases hlt : old < tag
      · rw [if_pos hlt] at h1; omega
      · by_cases hgt : tag < old
        · rw [if_pos hgt] at h2; omega
        · exact h (by omega)
    omega
/-- The product of three `0/1` masks is `1` iff all three are. -/
theorem decCand_mask_one {a b c : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    a * b * c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro h
    have h1 : a * b * c ≤ 1 * 1 * 1 := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0, Nat.zero_mul, Nat.zero_mul] at h; exact absurd h (by norm_num)
    have hb0 : b ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero, Nat.zero_mul] at h; exact absurd h (by norm_num)
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero] at h; exact absurd h (by norm_num)
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num
theorem decCandLen_le (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState)
    (hR : DecCandInvP N t C x s tag b len l st) : len ≤ t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnodup, hlen, -, -, -, hset, -, -, -, -⟩ := hR
  have hsub : l.toFinset ⊆
      ((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
        (fun v => v < N) := by
    intro v hv
    rw [List.mem_toFinset] at hv
    obtain ⟨hvN, j, -, hodd, hxl⟩ := (hset v).mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, ?_, hxl⟩, ?_⟩
    · exact (decCand_oddB_mem C (cr23Supp x) s j).mpr hodd
    · exact hvN
  have h1 : l.toFinset.card ≤
      (((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
        (fun v => v < N)).card := Finset.card_le_card hsub
  have h2 : (((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
      (fun v => v < N)).card ≤ (cr23OddB C (cr23Supp x) s).card :=
    le_trans (Finset.card_filter_le _ _) Finset.card_image_le
  have h3 : (cr23OddB C (cr23Supp x) s).card ≤ t :=
    le_trans (cr23OddB_card_le C (cr23Supp x) s) hsup
  have h4 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  omega
theorem decCandSet_step {N t : ℕ} (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (tag b : ℕ) (jj : Fin (cr23M t))
    (hjb : jj.val = b) (l : List ℕ) (lbl sel : ℕ)
    (hlbl : lbl = cr23XorLbl C (cr23Supp x) s jj)
    (hpar : decCandPar N t C x s jj = 1 ↔ Odd (cr23Ld C (cr23Supp x) s jj))
    (hsel : sel = 1 ↔ decCandPar N t C x s jj = 1 ∧ lbl < N ∧ lbl ∉ l)
    (hset : ∀ v, v ∈ l ↔ v < N ∧ ∃ j : Fin (cr23M t), j.val < b ∧
      Odd (cr23Ld C (cr23Supp x) s j) ∧ cr23XorLbl C (cr23Supp x) s j = v) :
    ∀ v, v ∈ (if sel = 1 then l ++ [lbl] else l) ↔
      v < N ∧ ∃ j : Fin (cr23M t), j.val < b + 1 ∧
        Odd (cr23Ld C (cr23Supp x) s j) ∧ cr23XorLbl C (cr23Supp x) s j = v := by
  have hjlt : ∀ j : Fin (cr23M t), j.val < b + 1 ↔ j.val < b ∨ j = jj := by
    intro j
    constructor
    · intro h
      rcases lt_or_eq_of_le (by omega : j.val ≤ b) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Fin.ext (by rw [hjb]; exact h1))
    · rintro (h1 | h1)
      · omega
      · rw [h1, hjb]; omega
  intro v
  have key : (v < N ∧ ∃ j : Fin (cr23M t), j.val < b + 1 ∧
      Odd (cr23Ld C (cr23Supp x) s j) ∧ cr23XorLbl C (cr23Supp x) s j = v)
      ↔ (v ∈ l ∨ (v < N ∧ Odd (cr23Ld C (cr23Supp x) s jj) ∧ v = lbl)) := by
    constructor
    · rintro ⟨hvN, j, hj, hodd, hxl⟩
      rcases (hjlt j).mp hj with hj1 | hj1
      · exact Or.inl ((hset v).mpr ⟨hvN, j, hj1, hodd, hxl⟩)
      · refine Or.inr ⟨hvN, ?_, ?_⟩
        · rw [hj1] at hodd; exact hodd
        · rw [hj1] at hxl; exact hxl.symm.trans hlbl.symm
    · rintro (h1 | ⟨hvN, hodd, hvl⟩)
      · obtain ⟨hvN, j, hj, hodd, hxl⟩ := (hset v).mp h1
        exact ⟨hvN, j, (hjlt j).mpr (Or.inl hj), hodd, hxl⟩
      · exact ⟨hvN, jj, (hjlt jj).mpr (Or.inr rfl), hodd, by rw [hvl, ← hlbl]⟩
  by_cases hs : sel = 1
  · obtain ⟨hpar1, hlblN, -⟩ := hsel.mp hs
    rw [if_pos hs, decCand_mem_concat, key]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ⟨by rw [h1]; exact hlblN, hpar.mp hpar1, h1⟩
    · rintro (h1 | ⟨-, -, h1⟩)
      · exact Or.inl h1
      · exact Or.inr h1
  · rw [if_neg hs, key]
    constructor
    · intro h1; exact Or.inl h1
    · rintro (h1 | ⟨hvN, hodd, hvl⟩)
      · exact h1
      · by_cases hmem : lbl ∈ l
        · rw [hvl]; exact hmem
        · exact absurd (hsel.mpr ⟨hpar.mpr hodd, by rw [← hvl]; exact hvN, hmem⟩) hs
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
theorem decCand_update_self (f : ℕ → ℕ) (a v : ℕ) : Function.update f a v a = v := by
  rw [Function.update_apply, if_pos rfl]
theorem decCand_mem_ne {m : ℕ → ℕ} {A B a : ℕ} {x y : ℕ} (hB : a ≠ B) (hA : a ≠ A) :
    Function.update (Function.update m A x) B y a = m a := by
  rw [Function.update_of_ne hB y (Function.update m A x), Function.update_of_ne hA x m]
theorem decCand_mem_outer {m : ℕ → ℕ} {A B : ℕ} {x y : ℕ} (h : B ≠ A) :
    Function.update (Function.update m A x) B y B = y := by
  rw [decCand_update_self]
theorem decCand_mem_inner {m : ℕ → ℕ} {A B : ℕ} {x y : ℕ} (h : A ≠ B) :
    Function.update (Function.update m A x) B y A = x := by
  rw [Function.update_of_ne h y (Function.update m A x), decCand_update_self]
/-- **The machine's conditional tag write**, in the exact shape `decCandBG_spec` produces. -/
theorem decCand_upd_mod' (W old tag sel : ℕ) (ho : old < 2 ^ W) (ht : tag < 2 ^ W)
    (hs : sel ≤ 1) :
    (old + ((tag + 2 ^ W - old) % 2 ^ W) * sel % 2 ^ W) % 2 ^ W
      = if sel = 1 then tag else old := by
  rcases (by omega : sel = 0 ∨ sel = 1) with h | h
  · rw [h, if_neg (by omega), Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt ho]
  · rw [h, if_pos rfl, Nat.mul_one,
      Nat.mod_eq_of_lt (Nat.mod_lt (tag + 2 ^ W - old) (by omega))]
    have h2 := decCand_upd_mod W old tag 1 ho ht (by omega)
    rw [Nat.one_mul, if_pos rfl] at h2
    exact h2
/-- **The invariant only reads the registers `r0, r2, r3, r4, r7, r8, r10, r11, r12, r14` and `mem`**, so
it survives the loop test (which writes `r15`) and any memory-preserving state change. -/
theorem decCandInvP_irr (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ)
    (st st' : RAMState) (hd : ∀ d : Fin 16, d ≠ r15 → st.regs d = st'.regs d)
    (hm : st.mem = st'.mem) (h : DecCandInvP N t C x s tag b len l st) :
    DecCandInvP N t C x s tag b len l st' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, a12, a13, a14, ?_, ?_, a17, ?_, ?_, ?_, ?_⟩
  · rw [← hd r0 (by decide)]; exact a1
  · rw [← hd r2 (by decide)]; exact a2
  · rw [← hd r3 (by decide)]; exact a3
  · rw [← hd r4 (by decide)]; exact a4
  · rw [← hd r7 (by decide)]; exact a5
  · rw [← hd r8 (by decide)]; exact a6
  · rw [← hd r10 (by decide)]; exact a7
  · rw [← hd r11 (by decide)]; exact a8
  · rw [← hd r12 (by decide)]; exact a9
  · rw [← hd r14 (by decide)]; exact a10
  · rw [← hm]; exact a11
  · rw [← hm]; exact a15
  · rw [← hm]; exact a16
  · rw [← hm]; exact a18
  · rw [← hm]; exact a19
  · rw [← hm]; exact a20
  · rw [← hm]; exact a21
/-- **The exit step** (§12.3): at `b = M` the prefix set clause is the whole set, because every
`j : Fin (cr23M t)` satisfies `j.val < cr23M t` and `j ∈ cr23OddB` is exactly oddness of the load. -/
theorem decCandInvP_final (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) (s : Fin (cr23D N)) (tag len : ℕ) (l : List ℕ) (st : RAMState)
    (h : DecCandInvP N t C x s tag (cr23M t) len l st) :
    DecCandInv N t C x s tag (cr23M t) len l st := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := h
  refine ⟨a1, a2, a11, a12, a13, a14, a15, a16, ?_⟩
  ext v
  rw [List.mem_toFinset, a17 v, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hvN, j, -, hodd, hxl⟩
    exact ⟨⟨j, (decCand_oddB_mem C (cr23Supp x) s j).mpr hodd, hxl⟩, hvN⟩
  · rintro ⟨⟨j, hjb, hxl⟩, hvN⟩
    exact ⟨hvN, j, j.isLt, (decCand_oddB_mem C (cr23Supp x) s j).mp hjb, hxl⟩
/-- **One bucket of the candidate scan.**  From the prefix invariant at `b` the 36-instruction body
reaches it at `b+1`, with the label of bucket `jj` appended exactly when the bucket is odd, names a
coordinate and is new.  The twelve chunk specs of §12.2 are chained `st1 … st8`; the semantic
quantities `lbl … sel` are parameters with defining equations, so no `simp` ever unfolds arithmetic. -/
theorem decCandBody_data_aux (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState)
    (jj : Fin (cr23M t)) (lbl par sN old g1 g2 ne ps sel : ℕ)
    (hsup : (cr23Supp x).card ≤ t) (htagW : tag < 2 ^ cr23Word N)
    (hjb : jj.val = b) (hbM : b < cr23M t)
    (hlbl : lbl = cr23XorLbl C (cr23Supp x) s jj)
    (hpar : par = decCandPar N t C x s jj)
    (hparodd : par = 1 ↔ Odd (cr23Ld C (cr23Supp x) s jj))
    (hsN : sN = (if lbl < N then 1 else 0))
    (hold : old = st.mem (decTagBase N t + lbl))
    (hg1 : g1 = (if old < tag then 1 else 0)) (hg2 : g2 = (if tag < old then 1 else 0))
    (hne : ne = g1 + g2) (hps : ps = par * sN) (hsel : sel = ps * ne)
    (hR : DecCandInvP N t C x s tag b len l st) :
    DecCandInvP N t C x s tag (b + 1) (len + sel) (if sel = 1 then l ++ [lbl] else l)
      (runBlock decCandBody (detEnv (cr23Word N) (cr23DecDet N t C)) st) := by
  have hlenle : len ≤ t := decCandLen_le N t hN ht C x hsup s tag b len l st hR
  obtain ⟨hq0, hq2, hq3, hq4, hq7, hq8, hq10, hq11, hq12, hq14, hlist, hnodup, hlen, hentries,
    htagarr, htagbound, hset, hpay, hslot1, hslot9, hslot10⟩ := hR
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hW0 : 0 < 2 ^ E.W := by omega
  have hMw : cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23M_lt_word N t hN htN
  have hDMw : cr23D N * cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23DM_lt_word N t hN htN
  have hNw : N < 2 ^ E.W := by rw [hEW]; exact cr23N_lt_word N hN
  have h2lbw : 2 ^ cr23Lb N < 2 ^ E.W := by
    rw [hEW]
    calc 2 ^ cr23Lb N ≤ 2 ^ (2 * cr23Lb N + 20) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hF11 : cr23DecFrame N t + 11 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 11) (by norm_num)
  have hfrW : cr23DecFrame N t < 2 ^ E.W := by
    rw [hEW]; simpa using cr23_frame_add_lt_word N t hN htN (c := 0) (by norm_num)
  have hMpos : 0 < cr23M t := by simp only [cr23M]; omega
  have h1024 : 1024 ≤ 2 ^ E.W := by
    rw [hEW]
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ cr23Word N := le_of_lt (cr23_pow_lt_word N hN)
  -- ### the payload word of the bucket
  have hMs : cr23M t * s.val < 2 ^ E.W := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (le_of_lt s.isLt)) ?_
    rw [Nat.mul_comm (cr23M t) (cr23D N)]
    exact hDMw
  have hqDM : cr23M t * s.val + b < cr23D N * cr23M t := by
    have h1 : cr23M t * s.val + b < cr23M t * (s.val + 1) := by
      rw [show cr23M t * (s.val + 1) = cr23M t * s.val + cr23M t from by ring]
      exact Nat.add_lt_add_left hbM _
    have h3 : cr23M t * (s.val + 1) ≤ cr23D N * cr23M t := by
      calc cr23M t * (s.val + 1) ≤ cr23M t * cr23D N := Nat.mul_le_mul_left _ (by omega)
        _ = cr23D N * cr23M t := Nat.mul_comm _ _
    omega
  have hqW : cr23M t * s.val + b < 2 ^ E.W := lt_trans hqDM hDMw
  have hqcheck : cr23M t * s.val + b = cr23Check N t s jj := by
    rw [cr23Check, hjb]; omega
  have hqw : (cr23M t * s.val + b) / 1024 < 2 ^ E.W :=
    lt_of_lt_of_le (decScanWordLt N t hN hqDM)
      (le_trans (cr23_wordsOf_le_frame N t hN) (le_of_lt hfrW))
  have hoff : (cr23M t * s.val + b) % 1024 * (cr23Lb N + 1) < 2 ^ E.W := by
    rw [hEW]
    apply cr23_lt_word N hN
    have h1 : (cr23M t * s.val + b) % 1024 ≤ 1023 := by
      have := Nat.mod_lt (cr23M t * s.val + b) (by norm_num : 0 < 1024)
      omega
    calc (cr23M t * s.val + b) % 1024 * (cr23Lb N + 1)
        ≤ 1023 * (cr23Lb N + 1) := Nat.mul_le_mul_right _ h1
      _ ≤ 1023 * (cr23Lb N + 1) + (cr23Lb N + 1) := by omega
      _ = 1024 * (cr23Lb N + 1) := by ring
      _ ≤ 1024 * 2 ^ (cr23Lb N + 1) :=
          Nat.mul_le_mul_left _ (le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ 10 * 2 ^ (cr23Lb N + 1) := by norm_num
      _ = 2 ^ (cr23Lb N + 11) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1W : b + 1 < 2 ^ E.W := by omega
  -- ### lengths and addresses
  have hlenlt : len < 2 * t + 1 := by omega
  have hcbtb : decCandBase N t + len < decTagBase N t := decCand_cand_lt_tag N t len hlenlt
  have hclW : decCandBase N t + len < 2 ^ E.W := by
    rw [hEW]; exact decCand_candAddr_lt_word N t hN htN hlenlt
  have hcbW : decCandBase N t < 2 ^ E.W := by
    rw [hEW]; exact decCand_candAddr_lt_word N t hN htN (j := 0) (by omega)
  have htbW : decTagBase N t < 2 ^ E.W := by
    rw [hEW]; exact decCand_tagBase_lt_word N t hN htN
  have hfr11 : cr23DecFrame N t + 11 < decCandBase N t := by
    have h := decSlot_lt_candBase N t (k := 10) (by norm_num)
    simpa only [decSlot] using h
  have hlen1W : len + 1 < 2 ^ E.W := by
    have htDM : t + 1 ≤ cr23D N * cr23M t := by
      have h1 : t + 1 ≤ 2 * t := by omega
      have h2 : 2 * t ≤ cr23M t := by simp only [cr23M]; omega
      calc t + 1 ≤ 2 * t := h1
        _ ≤ cr23M t := h2
        _ = 1 * cr23M t := (Nat.one_mul _).symm
        _ ≤ cr23D N * cr23M t := Nat.mul_le_mul_right _ (by omega)
    omega
  have hcbLen : cr23DecFrame N t + 11 ≠ decCandBase N t + len := by omega
  have hsl1 : st.mem (cr23DecFrame N t + 2) = N := by
    simpa only [decSlot] using hslot1
  have hsl9 : st.mem (cr23DecFrame N t + 10) = decCandBase N t := by
    simpa only [decSlot] using hslot9
  have hsl10 : st.mem (cr23DecFrame N t + 11) = decTagBase N t := by
    simpa only [decSlot] using hslot10
  -- ### the label
  have hlbLb : lbl < 2 ^ cr23Lb N := by
    rw [hlbl]; exact cr23XorLbl_lt N t C (cr23Supp x) s jj
  have hlbLb1 : lbl < 2 ^ (cr23Lb N + 1) :=
    lt_of_lt_of_le hlbLb (Nat.pow_le_pow_right (by norm_num) (by omega))
  have htlW : decTagBase N t + lbl < 2 ^ E.W := by
    rw [hEW]; exact decCand_tagAddr_lt_word N t hN htN hlbLb1
  have htagW' : tag < 2 ^ E.W := by rw [hEW]; exact htagW
  have holdW : old < 2 ^ E.W := by
    rw [hold]
    exact lt_of_le_of_lt (htagbound lbl hlbLb1) htagW'
  -- ### the masks
  have hpar1 : par ≤ 1 := by rw [hpar]; exact decBit_le_one N t C x (cr23Check N t s jj)
  have hsN1 : sN ≤ 1 := by rw [hsN]; split_ifs <;> omega
  have hps1 : ps ≤ 1 := by rw [hps]; exact dec_mul_le_one hpar1 hsN1
  have hgg : g1 + g2 ≤ 1 := by rw [hg1, hg2]; exact decCand_ind_add old tag
  have hne1 : ne ≤ 1 := by rw [hne]; exact hgg
  have hsel1 : sel ≤ 1 := by rw [hsel]; exact dec_mul_le_one hps1 hne1
  have htagmem : lbl ∈ l ↔ old = tag := by
    have h := (htagarr lbl hlbLb1).symm
    rw [← hold] at h
    exact h
  have hselone : sel = 1 ↔ par = 1 ∧ lbl < N ∧ lbl ∉ l := by
    rw [hsel, hps, hne]
    rw [decCand_mask_one hpar1 hsN1 hgg]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h2' : lbl < N := by
        by_contra hh
        rw [hsN, if_neg hh] at h2
        exact absurd h2 (by norm_num)
      have hneof : decCandNeOf tag old = 1 := by
        rw [decCandNeOf, ← hg1, ← hg2]; exact h3
      have h3' : old ≠ tag := (decCand_neOf_one tag old).mp hneof
      exact ⟨h1, h2', fun hmem => h3' (htagmem.mp hmem)⟩
    · rintro ⟨h1, h2, h3⟩
      have h2' : sN = 1 := by rw [hsN, if_pos h2]
      have hneof : decCandNeOf tag old = 1 :=
        (decCand_neOf_one tag old).mpr (fun he => h3 (htagmem.mpr he))
      rw [decCandNeOf, ← hg1, ← hg2] at hneof
      exact ⟨h1, h2', hneof⟩
  -- ### chunk A: q = M·s* + b, its payload word and q % 1024
  set st1 : RAMState := runBlock decCandBA E st with hst1
  have hA := decCandBA_spec E st (cr23M t) s.val b hq7 hq4 hq0 hq12 h1024 hMs hqW hqw
  have hA5 : st1.regs r5 = st.mem ((cr23M t * s.val + b) / 1024) % 2 ^ E.W := hA.1
  have hA6 : st1.regs r6 = (cr23M t * s.val + b) % 1024 := hA.2.1
  have hAmem : st1.mem = st.mem := hA.2.2.1
  have hAfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r5 → st1.regs d = st.regs d := hA.2.2.2
  have hkeep1 : ∀ d : Fin 16, d ≠ r5 → d ≠ r6 → st1.regs d = st.regs d := by
    intro d k5 k6
    exact hAfr d k6 k5
  have hword : st1.regs r5 < 2 ^ E.W := by
    rw [hA5]; exact Nat.mod_lt _ hW0
  have hA5' : st1.regs r5
      = packMem (cr23Word N) (cr23Sketch N t C x) ((cr23M t * s.val + b) / 1024) := by
    rw [hA5, hpay _ (decScanWordLt N t hN hqDM),
      Nat.mod_eq_of_lt (by rw [hEW]; exact packMem_lt (cr23Word N) (cr23Word_pos N) _ _)]
  -- ### chunk B: the field `word >>> off`, `2^lb` and `field / 2^lb`
  set st2 : RAMState := runBlock decCandBB E st1 with hst2
  have hoff' : st1.regs r6 * (cr23Lb N + 1) < 2 ^ E.W := by rw [hA6]; exact hoff
  have hB := decCandBB_spec E st1 (st1.regs r5) (st1.regs r6) (cr23Lb N + 1) (cr23Lb N)
    rfl rfl
    ((hkeep1 r8 (by decide) (by decide)).trans hq8)
    ((hkeep1 r11 (by decide) (by decide)).trans hq11)
    ((hkeep1 r10 (by decide) (by decide)).trans hq10)
    hword hoff' h2lbw
  have hB5 : st2.regs r5 = st1.regs r5 / 2 ^ (st1.regs r6 * (cr23Lb N + 1)) := hB.1
  have hB1 : st2.regs r1 = 2 ^ cr23Lb N := hB.2.1
  have hB15 : st2.regs r15
      = st1.regs r5 / 2 ^ (st1.regs r6 * (cr23Lb N + 1)) / 2 ^ cr23Lb N := hB.2.2.1
  have hBmem : st2.mem = st1.mem := hB.2.2.2.1
  have hBfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r5 → d ≠ r1 → d ≠ r15 →
      st2.regs d = st1.regs d := hB.2.2.2.2
  have hkeep2 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st2.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hBfr d k6 k5 k1 k15, hkeep1 d k5 k6]
  have hfield : st2.regs r5
      = packMem (cr23Word N) (cr23Sketch N t C x) ((cr23M t * s.val + b) / 1024)
        / 2 ^ ((cr23M t * s.val + b) % 1024 * (cr23Lb N + 1)) := by
    rw [hB5, hA6, hA5']
  have hword2 : st2.regs r5 < 2 ^ E.W := by
    rw [hfield]
    refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_
    rw [hEW]; exact packMem_lt (cr23Word N) (cr23Word_pos N) _ _
  have hdvd : 2 ^ cr23Lb N ∣ 2 ^ (cr23Lb N + 1) := ⟨2, pow_succ 2 (cr23Lb N)⟩
  have hlblEq : st2.regs r5 % 2 ^ cr23Lb N = cr23XorLbl C (cr23Supp x) s jj := by
    rw [hfield, ← Nat.mod_mod_of_dvd _ hdvd,
      cr23CheckField_read N t (cr23Sketch N t C x) (cr23M t * s.val + b) hqDM, hqcheck]
    exact cr23CheckField_mod N t C x s jj
  have hparEq : st2.regs r15 % 2 = decCandPar N t C x s jj := by
    rw [hB15, hA5', hA6]
    rw [show packMem (cr23Word N) (cr23Sketch N t C x) ((cr23M t * s.val + b) / 1024)
          / 2 ^ ((cr23M t * s.val + b) % 1024 * (cr23Lb N + 1)) / 2 ^ cr23Lb N
        = packMem (cr23Word N) (cr23Sketch N t C x) ((cr23M t * s.val + b) / 1024)
          / 2 ^ ((cr23M t * s.val + b) % 1024 * (cr23Lb N + 1) + cr23Lb N) from by
        rw [Nat.div_div_eq_div_mul, ← pow_add]]
    rw [dec_div_pow_mod_two'
      (packMem (cr23Word N) (cr23Sketch N t C x) ((cr23M t * s.val + b) / 1024))
      ((cr23M t * s.val + b) % 1024 * (cr23Lb N + 1)) (cr23Lb N) (cr23Lb N + 1) (by omega)]
    rw [cr23CheckField_read N t (cr23Sketch N t C x) (cr23M t * s.val + b) hqDM, hqcheck]
    rfl
  -- ### chunk C: par, lbl and N
  set st3 : RAMState := runBlock decCandBC E st2 with hst3
  have hNm2 : st2.mem (cr23DecFrame N t + 2) % 2 ^ E.W = N := by
    rw [hBmem, hAmem, hsl1, Nat.mod_eq_of_lt hNw]
  have hC := decCandBC_spec E st2 (st2.regs r15) (st2.regs r5) (cr23Lb N) (cr23DecFrame N t) N
    rfl rfl hB1
    ((hkeep2 r11 (by decide) (by decide) (by decide) (by decide)).trans hq11)
    ((hkeep2 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hword2 hF11 hNm2
  have hC15 : st3.regs r15 = par := by
    rw [hC.1, hparEq]; exact hpar.symm
  have hC5 : st3.regs r5 = lbl := by
    rw [hC.2.1, hlblEq]; exact hlbl.symm
  have hC6 : st3.regs r6 = N := hC.2.2.1
  have hCmem : st3.mem = st2.mem := hC.2.2.2.1
  have hCfr : ∀ d : Fin 16, d ≠ r15 → d ≠ r6 → d ≠ r5 → st3.regs d = st2.regs d :=
    hC.2.2.2.2
  have hkeep3 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st3.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hCfr d k15 k6 k5, hkeep2 d k1 k5 k6 k15]
  -- ### chunk D: sN = (lbl < N), ps = par·sN, the candidate base
  set st4 : RAMState := runBlock decCandBD E st3 with hst4
  have hCB2 : st3.mem (cr23DecFrame N t + 10) % 2 ^ E.W = decCandBase N t := by
    rw [hCmem, hBmem, hAmem, hsl9, Nat.mod_eq_of_lt hcbW]
  have hD := decCandBD_spec E st3 lbl N par (cr23DecFrame N t) (decCandBase N t)
    hC6 hC5 hC15
    ((hkeep3 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hpar1 hW hF11 hCB2
  have hD6 : st4.regs r6 = sN := by rw [hD.1]; exact hsN.symm
  have hD15 : st4.regs r15 = ps := by rw [hD.2.1, ← hsN]; exact hps.symm
  have hD1 : st4.regs r1 = decCandBase N t := hD.2.2.1
  have hDmem : st4.mem = st3.mem := hD.2.2.2.1
  have hDfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r15 → d ≠ r1 → st4.regs d = st3.regs d :=
    hD.2.2.2.2
  have hkeep4 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st4.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hDfr d k6 k15 k1, hkeep3 d k1 k5 k6 k15]
  -- ### chunk E: the unconditional candidate store and the tag base
  set st5 : RAMState := runBlock decCandBE E st4 with hst5
  have hE5 := decCandBE_spec E st4 (decCandBase N t) len lbl (cr23DecFrame N t)
    hD1
    ((hkeep4 r2 (by decide) (by decide) (by decide) (by decide)).trans hq2)
    ((hDfr r5 (by decide) (by decide) (by decide)).trans hC5)
    ((hkeep4 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hclW hF11 hcbLen
  have hE5r1 : st5.regs r1 = decTagBase N t := by
    rw [hE5.1, hDmem, hCmem, hBmem, hAmem, hsl10, Nat.mod_eq_of_lt htbW]
  have hE5mem : st5.mem = Function.update st4.mem (decCandBase N t + len) lbl := hE5.2.1
  have hE5fr : ∀ d : Fin 16, d ≠ r1 → st5.regs d = st4.regs d := hE5.2.2
  have hkeep5 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st5.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hE5fr d k1, hkeep4 d k1 k5 k6 k15]
  -- ### chunk F: the tag address, `old`, and the two comparison masks
  set st6 : RAMState := runBlock decCandBF E st5 with hst6
  have hneAddr : decTagBase N t + lbl ≠ decCandBase N t + len := by omega
  have hold5 : st5.mem (decTagBase N t + lbl) % 2 ^ E.W = old := by
    rw [hE5mem, Function.update_of_ne hneAddr lbl st4.mem, hDmem, hCmem, hBmem, hAmem,
      ← hold, Nat.mod_eq_of_lt holdW]
  have hF := decCandBF_spec E st5 (decTagBase N t) lbl tag old hE5r1
    ((hE5fr r5 (by decide)).trans hC5)
    ((hkeep5 r3 (by decide) (by decide) (by decide) (by decide)).trans hq3)
    hW htlW hold5
  have hF1 : st6.regs r1 = decTagBase N t + lbl := hF.1
  have hF6 : st6.regs r6 = old := hF.2.1
  have hF13 : st6.regs r13 = g2 := by rw [hF.2.2.1]; exact hg2.symm
  have hF5 : st6.regs r5 = ne := by rw [hF.2.2.2.1, ← hg1, ← hg2]; exact hne.symm
  have hFmem : st6.mem = st5.mem := hF.2.2.2.2.1
  have hFfr : ∀ d : Fin 16, d ≠ r1 → d ≠ r6 → d ≠ r13 → d ≠ r5 → st6.regs d = st5.regs d :=
    hF.2.2.2.2.2
  have hkeep6 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r13 → d ≠ r15 →
      st6.regs d = st.regs d := by
    intro d k1 k5 k6 k13 k15
    rw [hFfr d k1 k6 k13 k5, hkeep5 d k1 k5 k6 k15]
  -- ### chunk G: sel, len and the tag store value
  set st7 : RAMState := runBlock decCandBG E st6 with hst7
  have hG := decCandBG_spec E st6 ps ne len tag old
    ((hFfr r15 (by decide) (by decide) (by decide) (by decide)).trans
      ((hE5fr r15 (by decide)).trans hD15))
    hF5
    ((hkeep6 r2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq2)
    ((hkeep6 r3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq3)
    hF6 hps1 hne1 hlen1W
  have hG15 : st7.regs r15 = ps * ne := hG.1
  have hG2 : st7.regs r2 = len + ps * ne := hG.2.1
  have hG6 : st7.regs r6 = (if sel = 1 then tag else old) := by
    rw [hG.2.2.1, ← hsel]
    exact decCand_upd_mod' E.W old tag sel holdW htagW' hsel1
  have hGmem : st7.mem = st6.mem := hG.2.2.2.1
  have hGfr : ∀ d : Fin 16, d ≠ r15 → d ≠ r2 → d ≠ r5 → d ≠ r13 → d ≠ r6 →
      st7.regs d = st6.regs d := hG.2.2.2.2
  have hkeep7 : ∀ d : Fin 16, d ≠ r1 → d ≠ r2 → d ≠ r5 → d ≠ r6 → d ≠ r13 → d ≠ r15 →
      st7.regs d = st.regs d := by
    intro d k1 k2 k5 k6 k13 k15
    rw [hGfr d k15 k2 k5 k13 k6, hkeep6 d k1 k5 k6 k13 k15]
  -- ### chunk H: the tag store and the bucket counter
  set st8 : RAMState := runBlock decCandBH E st7 with hst8
  have hH := decCandBH_spec E st7 (decTagBase N t + lbl) (if sel = 1 then tag else old) b
    ((hGfr r1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hF1)
    hG6
    ((hkeep7 r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq0)
    ((hkeep7 r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq11)
    hb1W
  have hH0 : st8.regs r0 = b + 1 := hH.1
  have hHmem : st8.mem = Function.update st7.mem (decTagBase N t + lbl)
      (if sel = 1 then tag else old) := hH.2.1
  have hHfr : ∀ d : Fin 16, d ≠ r0 → st8.regs d = st7.regs d := hH.2.2
  have hkeep : ∀ d : Fin 16, d ≠ r0 → d ≠ r1 → d ≠ r2 → d ≠ r5 → d ≠ r6 → d ≠ r13 → d ≠ r15 →
      st8.regs d = st.regs d := by
    intro d k0 k1 k2 k5 k6 k13 k15
    rw [hHfr d k0, hkeep7 d k1 k2 k5 k6 k13 k15]
  -- ### the memory of the end state
  have hm8 : st8.mem = Function.update (Function.update st.mem (decCandBase N t + len) lbl)
      (decTagBase N t + lbl) (if sel = 1 then tag else old) := by
    rw [hHmem, hGmem, hFmem, hE5mem, hDmem, hCmem, hBmem, hAmem]
  have hout : ∀ a : ℕ, a ≠ decCandBase N t + len → a ≠ decTagBase N t + lbl →
      st8.mem a = st.mem a := by
    intro a h1 h2
    rw [hm8]
    exact decCand_mem_ne h2 h1
  have hbody : runBlock decCandBody E st = st8 := by
    rw [decCandBody_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3, ← hst4, ← hst5, ← hst6, ← hst7, ← hst8]
  rw [hbody]
  have hwframe := cr23_wordsOf_le_frame N t hN
  have hfrCand := decFrame_le_candBase N t
  have hcandTag := decCandBase_le_tagBase N t
  have hsel01 : sel = 0 ∨ sel = 1 := by omega
  have hslot1' : decSlot N t 1 = cr23DecFrame N t + 2 := by simp only [decSlot]
  have hslot9' : decSlot N t 9 = cr23DecFrame N t + 10 := by simp only [decSlot]
  have hslot10' : decSlot N t 10 = cr23DecFrame N t + 11 := by simp only [decSlot]
  refine ⟨hH0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHfr r2 (by decide), hG2, ← hsel]
  · exact (hkeep r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq3
  · exact (hkeep r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq4
  · exact (hkeep r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq7
  · exact (hkeep r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq8
  · exact (hkeep r10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq10
  · exact (hkeep r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq11
  · exact (hkeep r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq12
  · exact (hkeep r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hq14
  · -- the candidate list, entry by entry
    intro i hi
    by_cases hs : sel = 1
    · have hi' : i ≤ len := by omega
      rw [hs, if_pos rfl]
      rcases lt_or_eq_of_le hi' with hlt | heq
      · rw [hout (decCandBase N t + i) (by omega) (by omega),
          decCand_getD_append (by omega : i < l.length)]
        exact hlist i hlt
      · have hget : (l ++ [lbl]).getD len 0 = lbl := by
          rw [hlen]; exact decCand_getD_concat l lbl
        rw [heq, hget, hm8]
        exact decCand_mem_inner (by omega)
    · have hs0 : sel = 0 := by omega
      have hi' : i < len := by omega
      rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1),
        hout (decCandBase N t + i) (by omega) (by omega)]
      exact hlist i hi'
  · -- the list is duplicate-free
    by_cases hs : sel = 1
    · rw [hs, if_pos rfl]
      exact decCand_nodup_concat lbl l hnodup (fun hc => (hselone.mp hs).2.2 hc)
    · have hs0 : sel = 0 := by omega
      rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1)]; exact hnodup
  · -- its length
    by_cases hs : sel = 1
    · rw [hs, if_pos rfl, List.length_append, List.length_singleton]; omega
    · have hs0 : sel = 0 := by omega
      rw [hs0, Nat.add_zero, if_neg (by omega : ¬ (0 : ℕ) = 1)]; exact hlen
  · -- its entries are coordinates
    intro i hi
    by_cases hs : sel = 1
    · rw [hs, if_pos rfl, decCand_mem_concat] at hi
      rcases hi with hi | rfl
      · exact hentries i hi
      · exact (hselone.mp hs).2.1
    · have hs0 : sel = 0 := by omega
      rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1)] at hi
      exact hentries i hi
  · -- the tag array holds `tag` exactly on the list (inside the tag region)
    intro v hv
    by_cases hvl : v = lbl
    · rw [hvl]
      rw [hm8, decCand_mem_outer (by omega : decTagBase N t + lbl ≠ decCandBase N t + len)]
      by_cases hs : sel = 1
      · rw [hs, if_pos rfl, if_pos rfl]
        exact ⟨fun _ => (decCand_mem_concat l lbl lbl).mpr (Or.inr rfl), fun _ => rfl⟩
      · have hs0 : sel = 0 := by omega
        rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1), if_neg (by omega : ¬ (0 : ℕ) = 1)]
        exact htagmem.symm
    · have h1 : decTagBase N t + v ≠ decCandBase N t + len := by omega
      have h2 : decTagBase N t + v ≠ decTagBase N t + lbl := by omega
      rw [hout (decTagBase N t + v) h1 h2, htagarr v hv]
      by_cases hs : sel = 1
      · rw [hs, if_pos rfl, decCand_mem_concat]
        exact ⟨Or.inl, fun h => h.elim id (fun he => absurd he hvl)⟩
      · have hs0 : sel = 0 := by omega
        rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1)]
  · -- every tag cell of the region is `≤ tag` (the next round's `DecData` bound)
    intro v hv
    by_cases hvl : v = lbl
    · rw [hvl]
      rw [hm8, decCand_mem_outer (by omega : decTagBase N t + lbl ≠ decCandBase N t + len)]
      by_cases hs : sel = 1
      · rw [hs, if_pos rfl]
      · have hs0 : sel = 0 := by omega
        rw [hs0, if_neg (by omega : ¬ (0 : ℕ) = 1)]
        rw [hold]; exact htagbound lbl hlbLb1
    · rw [hout (decTagBase N t + v) (by omega) (by omega)]
      exact htagbound v hv
  · -- the prefix set clause, one bucket further
    exact decCandSet_step C x s tag b jj hjb l lbl sel hlbl (hpar ▸ hparodd)
      (hpar ▸ hselone) hset
  · -- the payload is untouched
    intro a ha
    rw [hout a (by omega) (by omega)]
    exact hpay a ha
  · -- the three slot reads
    rw [hslot1', hout (cr23DecFrame N t + 2) (by omega) (by omega)]
    exact hsl1
  · rw [hslot9', hout (cr23DecFrame N t + 10) (by omega) (by omega)]
    exact hsl9
  · rw [hslot10', hout (cr23DecFrame N t + 11) (by omega) (by omega)]
    exact hsl10
/-- **The data lemma of body (b)**: the corollary of `decCandBody_data_aux` at the semantic
quantities of bucket `jj`.  Every arithmetic hypothesis is `rfl`; the oddness bridge is
`decCand_par_one` composed with `decCand_oddB_mem`. -/
theorem decCandBody_data (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState)
    (jj : Fin (cr23M t)) (hsup : (cr23Supp x).card ≤ t) (htagW : tag < 2 ^ cr23Word N)
    (hjb : jj.val = b) (hbM : b < cr23M t)
    (hR : DecCandInvP N t C x s tag b len l st) :
    DecCandInvP N t C x s tag (b + 1) (len + decCandSel N t C x s tag jj st)
      (if decCandSel N t C x s tag jj st = 1 then l ++ [decCandLbl N t C x s jj] else l)
      (runBlock decCandBody (detEnv (cr23Word N) (cr23DecDet N t C)) st) := by
  have hparodd : decCandPar N t C x s jj = 1 ↔ Odd (cr23Ld C (cr23Supp x) s jj) :=
    (decCand_par_one C x s jj).trans (decCand_oddB_mem C (cr23Supp x) s jj)
  exact decCandBody_data_aux N t hN ht htN C x s tag b len l st jj
    (decCandLbl N t C x s jj) (decCandPar N t C x s jj)
    (if decCandLbl N t C x s jj < N then 1 else 0)
    (st.mem (decTagBase N t + decCandLbl N t C x s jj))
    (if st.mem (decTagBase N t + decCandLbl N t C x s jj) < tag then 1 else 0)
    (if tag < st.mem (decTagBase N t + decCandLbl N t C x s jj) then 1 else 0)
    (decCandNeOf tag (st.mem (decTagBase N t + decCandLbl N t C x s jj)))
    (decCandPar N t C x s jj * (if decCandLbl N t C x s jj < N then 1 else 0))
    (decCandSel N t C x s tag jj st)
    hsup htagW hjb hbM rfl rfl hparodd rfl rfl rfl rfl rfl rfl rfl hR
theorem decCandBA_noBranch : NoBranch decCandBA := by simp [decCandBA]
theorem decCandBB_noBranch : NoBranch decCandBB := by simp [decCandBB]
theorem decCandBC_noBranch : NoBranch decCandBC := by simp [decCandBC]
theorem decCandBD_noBranch : NoBranch decCandBD := by simp [decCandBD]
theorem decCandBE_noBranch : NoBranch decCandBE := by simp [decCandBE]
theorem decCandBF_noBranch : NoBranch decCandBF := by simp [decCandBF]
theorem decCandBG_noBranch : NoBranch decCandBG := by simp [decCandBG]
theorem decCandBH_noBranch : NoBranch decCandBH := by simp [decCandBH]
theorem decCandBody_noBranch : NoBranch decCandBody := by
  rw [decCandBody_split]
  simp [decCandBA_noBranch, decCandBB_noBranch, decCandBC_noBranch, decCandBD_noBranch,
    decCandBE_noBranch, decCandBF_noBranch, decCandBG_noBranch, decCandBH_noBranch]
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
theorem decCandIA_noBranch : NoBranch decCandIA := by simp [decCandIA]
theorem decCandIB_noBranch : NoBranch decCandIB := by simp [decCandIB]
theorem decCandIC_noBranch : NoBranch decCandIC := by simp [decCandIC]
theorem decCandID_noBranch : NoBranch decCandID := by simp [decCandID]
theorem decCandInit_noBranch : NoBranch decCandInit := by
  rw [decCandInit_split]
  simp [decCandIA_noBranch, decCandIB_noBranch, decCandIC_noBranch, decCandID_noBranch]
/-- **Body (b)'s initialisation, as a data lemma**: the sixteen instructions turn `DecData` at the
round head into the loop invariant at `b = 0`, `len = 0`, `l = []`. -/
theorem decCandInit_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag : ℕ) (m₀ : ℕ → ℕ) (st : RAMState)
    (hm : st.mem = m₀) (h14 : st.regs r14 = cr23DecFrame N t) (h4 : st.regs r4 = s.val)
    (hMv : m₀ (decSlot N t 2) = cr23M t)
    (hLv : m₀ (decSlot N t 3) = cr23Lb N + 1)
    (hlb : m₀ (decSlot N t 4) = cr23Lb N)
    (htg : m₀ (decSlot N t 8) = tag)
    (hNv : m₀ (decSlot N t 1) = N)
    (hcb : m₀ (decSlot N t 9) = decCandBase N t)
    (htb : m₀ (decSlot N t 10) = decTagBase N t)
    (htagW : tag < 2 ^ E.W)
    (htaglt : ∀ v, v < 2 ^ (cr23Lb N + 1) → m₀ (decTagBase N t + v) < tag)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      m₀ a = packMem (cr23Word N) (cr23Sketch N t C x) a) :
    DecCandInvP N t C x s tag 0 0 [] (runBlock decCandInit E st) := by
  have htagW' : tag < 2 ^ cr23Word N := by rw [← hEW]; exact htagW
  have hbig : 1024 < 2 ^ E.W := by
    rw [hEW]
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hMw : cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23M_lt_word N t hN htN
  have hF11 : cr23DecFrame N t + 11 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 11) (by norm_num)
  have hLw : cr23Lb N + 1 < 2 ^ E.W := by
    rw [hEW]
    calc cr23Lb N + 1 ≤ 2 ^ (cr23Lb N + 1) := le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hlw : cr23Lb N < 2 ^ E.W := lt_trans (Nat.lt_succ_self _) hLw
  -- the four slot addresses the block reads, in the shape the chunk specs expect
  have hsl2 : decSlot N t 2 = cr23DecFrame N t + 3 := by simp only [decSlot] <;> omega
  have hsl3 : decSlot N t 3 = cr23DecFrame N t + 4 := by simp only [decSlot] <;> omega
  have hsl4 : decSlot N t 4 = cr23DecFrame N t + 5 := by simp only [decSlot] <;> omega
  have hsl8 : decSlot N t 8 = cr23DecFrame N t + 9 := by simp only [decSlot] <;> omega
  -- ### chunk IA: `r0 = 0`, `r2 = 0`, `r7 = M`
  set st1 : RAMState := runBlock decCandIA E st with hst1
  have hIA := decCandIA_spec E st (cr23DecFrame N t) (cr23M t) h14 hF11 (by
    rw [hm, ← hsl2, hMv, Nat.mod_eq_of_lt hMw])
  obtain ⟨hA0, hA2, hA7, hAmem, hAfr⟩ := hIA
  have hA14 : st1.regs r14 = cr23DecFrame N t :=
    (hAfr r14 (by decide) (by decide) (by decide) (by decide)).trans h14
  -- ### chunk IB: `r8 = L`, `r6 = frame + 5`
  set st2 : RAMState := runBlock decCandIB E st1 with hst2
  have hIB := decCandIB_spec E st1 (cr23DecFrame N t) (cr23Lb N + 1) hA14 hF11 (by
    rw [hAmem, hm, ← hsl3, hLv, Nat.mod_eq_of_lt hLw])
  obtain ⟨hB8, hB6, hBmem, hBfr⟩ := hIB
  have hB14 : st2.regs r14 = cr23DecFrame N t :=
    (hBfr r14 (by decide) (by decide)).trans hA14
  -- ### chunk IC: `r10 = lb`, `r3 = tag`, `r11 = 1`
  set st3 : RAMState := runBlock decCandIC E st2 with hst3
  have hIC := decCandIC_spec E st2 (cr23DecFrame N t) (cr23Lb N) tag hB6 hB14 hF11 (by
    rw [hBmem, hAmem, hm, ← hsl4, hlb, Nat.mod_eq_of_lt hlw]) (by
    rw [hBmem, hAmem, hm, ← hsl8, htg, Nat.mod_eq_of_lt htagW])
  obtain ⟨hC10, hC3, hC11, hCmem, hCfr⟩ := hIC
  -- ### chunk ID: `r12 = 1024`
  set st4 : RAMState := runBlock decCandID E st3 with hst4
  obtain ⟨hD12, hDmem, hDfr⟩ := decCandID_spec E st3 hbig
  have hcode : runBlock decCandInit E st = st4 := by
    rw [decCandInit_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3, ← hst4]
  have h4mem : st4.mem = st.mem := by
    rw [hst4, hDmem, hst3, hCmem, hst2, hBmem, hst1, hAmem]
  -- ### the ten registers of the invariant
  have hr0 : st4.regs r0 = 0 :=
    (hDfr r0 (by decide)).trans ((hCfr r0 (by decide) (by decide) (by decide) (by decide)).trans
      ((hBfr r0 (by decide) (by decide)).trans hA0))
  have hr2 : st4.regs r2 = 0 :=
    (hDfr r2 (by decide)).trans ((hCfr r2 (by decide) (by decide) (by decide) (by decide)).trans
      ((hBfr r2 (by decide) (by decide)).trans hA2))
  have hr3 : st4.regs r3 = tag := (hDfr r3 (by decide)).trans hC3
  have hr4 : st4.regs r4 = s.val :=
    (hDfr r4 (by decide)).trans ((hCfr r4 (by decide) (by decide) (by decide) (by decide)).trans
      ((hBfr r4 (by decide) (by decide)).trans
        ((hAfr r4 (by decide) (by decide) (by decide) (by decide)).trans h4)))
  have hr7 : st4.regs r7 = cr23M t :=
    (hDfr r7 (by decide)).trans ((hCfr r7 (by decide) (by decide) (by decide) (by decide)).trans
      ((hBfr r7 (by decide) (by decide)).trans hA7))
  have hr8 : st4.regs r8 = cr23Lb N + 1 :=
    (hDfr r8 (by decide)).trans
      ((hCfr r8 (by decide) (by decide) (by decide) (by decide)).trans hB8)
  have hr10 : st4.regs r10 = cr23Lb N := (hDfr r10 (by decide)).trans hC10
  have hr11 : st4.regs r11 = 1 := (hDfr r11 (by decide)).trans hC11
  have hr12 : st4.regs r12 = 1024 := hD12
  have hr14 : st4.regs r14 = cr23DecFrame N t :=
    (hDfr r14 (by decide)).trans ((hCfr r14 (by decide) (by decide) (by decide) (by decide)).trans
      ((hBfr r14 (by decide) (by decide)).trans
        ((hAfr r14 (by decide) (by decide) (by decide) (by decide)).trans h14)))
  rw [hcode]
  refine ⟨hr0, hr2, hr3, hr4, hr7, hr8, hr10, hr11, hr12, hr14, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- the stored list is empty
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact List.nodup_nil
  · rfl
  · -- no entry to bound
    intro i hi
    exact absurd hi (by simp)
  · -- the tag array holds `tag` exactly on `[]`, which is empty
    intro v hv
    have hne : st4.mem (decTagBase N t + v) ≠ tag := by
      rw [h4mem, hm]
      exact ne_of_lt (htaglt v hv)
    constructor
    · intro h
      exact absurd h hne
    · intro h
      exact absurd h (by simp)
  · -- every tag cell of the region is `≤ tag`: the round head's cells are `< tag`
    intro v hv
    rw [h4mem, hm]
    exact le_of_lt (htaglt v hv)
  · -- the prefix set clause is empty at `b = 0`
    intro v
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨-, j, hj, -⟩
      exact absurd hj (Nat.not_lt_zero j.val)
  · -- the payload is untouched
    intro a ha
    rw [h4mem, hm]
    exact hpay a ha
  · rw [h4mem, hm]; exact hNv
  · rw [h4mem, hm]; exact hcb
  · rw [h4mem, hm]; exact htb
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
/-- The symmetric difference of two finite sets of numbers: one round of body (d) toggles a single
value into the running parity set, which is exactly this operation. -/
def decSymm (A B : Finset ℕ) : Finset ℕ := (A \ B) ∪ (B \ A)
theorem decSymm_singleton_self (A : Finset ℕ) (x : ℕ) : x ∈ decSymm A {x} ↔ x ∉ A := by
  simp only [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  tauto
theorem decSymm_singleton_ne (A : Finset ℕ) {x w : ℕ} (h : w ≠ x) :
    w ∈ decSymm A {x} ↔ w ∈ A := by
  simp only [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  tauto
theorem decSymm_empty (A : Finset ℕ) : decSymm A ∅ = A := by
  simp [decSymm]
/-- **The toggle**: a `0/1` bit flips exactly when the value enters the symmetric difference. -/
theorem dec_toggle (A : Finset ℕ) (x : ℕ) :
    1 - (if x ∈ A then 1 else 0) = if x ∈ decSymm A {x} then 1 else 0 := by
  have hiff : x ∈ decSymm A {x} ↔ x ∉ A := decSymm_singleton_self A x
  by_cases h : x ∈ A
  · have h' : ¬ x ∈ decSymm A {x} := fun hh => (hiff.mp hh) h
    rw [if_pos h, if_neg h', Nat.sub_self]
  · have h' : x ∈ decSymm A {x} := hiff.mpr h
    rw [if_neg h, if_pos h', Nat.sub_zero]
theorem dec_le_add_r (a b : ℕ) : a ≤ a + b := by omega
theorem dec_getD_append_lt (l₁ l₂ : List ℕ) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := List.getD_append l₁ l₂ 0 i hi
theorem dec_getD_append_add (l₁ l₂ : List ℕ) {k : ℕ} (hk : k < l₂.length) :
    (l₁ ++ l₂).getD (l₁.length + k) 0 = l₂.getD k 0 := by
  rw [List.getD_append_right l₁ l₂ 0 (l₁.length + k) (by omega), Nat.add_sub_cancel_left]
/-- The `j`-th entry of a list is a member. -/
theorem dec_getD_mem {l : List ℕ} {j : ℕ} (hj : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem l 0 hj]
  exact List.getElem_mem hj
/-- Every member of a list is its `k`-th entry for some `k`. -/
theorem dec_mem_getD {l : List ℕ} {v : ℕ} (h : v ∈ l) :
    ∃ k, k < l.length ∧ l.getD k 0 = v := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, hk, by rw [List.getD_eq_getElem l 0 hk, hget]⟩
/-- **Splitting the master clause**: the two halves give the clause for `mst ++ l`. -/
theorem dec_mst_concat (m : ℕ → ℕ) (base : ℕ) (mst l : List ℕ)
    (h1 : ∀ i, i < mst.length → m (base + i) = mst.getD i 0)
    (h2 : ∀ k, k < l.length → m (base + (mst.length + k)) = l.getD k 0) :
    ∀ i, i < (mst ++ l).length → m (base + i) = (mst ++ l).getD i 0 := by
  intro i hi
  rcases lt_or_ge i mst.length with hlt | hge
  · rw [dec_getD_append_lt mst l hlt]
    exact h1 i hlt
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < l.length ∧ i = mst.length + k := by
      refine ⟨i - mst.length, ?_, by omega⟩
      simp only [List.length_append] at hi
      omega
    rw [dec_getD_append_add mst l hk]
    exact h2 k hk
theorem dec_upd_same (m : ℕ → ℕ) (A v : ℕ) : (Function.update m A v) A = v := by simp
theorem dec_upd_ne {m : ℕ → ℕ} {A a v : ℕ} (h : a ≠ A) :
    (Function.update m A v) a = m a :=
  Function.update_of_ne h v m
theorem dec_upd2_ne {m : ℕ → ℕ} {A B a v w : ℕ} (hA : a ≠ A) (hB : a ≠ B) :
    (Function.update (Function.update m A v) B w) a = m a := by
  rw [dec_upd_ne hB, dec_upd_ne hA]
/-- Two writes at `A` and `B` with `a` below both. -/
theorem dec_upd2_lt (m : ℕ → ℕ) (A B v w a : ℕ) (hAB : B < A) (ha : a < B) :
    (Function.update (Function.update m A v) B w) a = m a :=
  dec_upd2_ne (show a ≠ A from by omega) (show a ≠ B from by omega)
theorem dec_upd2_fst {m : ℕ → ℕ} {A B v w : ℕ} (h : B ≠ A) :
    (Function.update (Function.update m A v) B w) A = v := by
  rw [dec_upd_ne (show A ≠ B from fun hh => h hh.symm), dec_upd_same]
theorem dec_upd2_snd (m : ℕ → ℕ) (A B v w : ℕ) :
    (Function.update (Function.update m A v) B w) B = w :=
  dec_upd_same _ B w
theorem dec_ne_of_lt {a b : ℕ} (h : a < b) : a ≠ b := ne_of_lt h
theorem dec_ne_of_lt' {a b : ℕ} (h : a < b) : b ≠ a := (ne_of_lt h).symm
theorem dec_ne_add_l {a b c : ℕ} (h : b ≠ c) : a + b ≠ a + c :=
  fun hh => h (Nat.add_left_cancel hh)
theorem dec_nodup_concat (l : List ℕ) (x : ℕ) (h : l.Nodup) (hx : x ∉ l) :
    (l ++ [x]).Nodup := by
  refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact fun hab => hx (hab ▸ ha)
theorem decParInit_split :
    decParInit = decParIA ++ decParIB ++ decParIC ++ decParID := rfl
theorem decParBody_split : decParBody = decParBA ++ decParBB := rfl
theorem decSlot_nine (N t : ℕ) : decSlot N t 9 = cr23DecFrame N t + 10 := rfl
theorem decSlot_eleven (N t : ℕ) : decSlot N t 11 = cr23DecFrame N t + 12 := rfl
theorem decSlot_twelve (N t : ℕ) : decSlot N t 12 = cr23DecFrame N t + 13 := rfl
theorem decSlot_thirteen (N t : ℕ) : decSlot N t 13 = cr23DecFrame N t + 14 := rfl
theorem decSlot_fourteen (N t : ℕ) : decSlot N t 14 = cr23DecFrame N t + 15 := rfl
theorem dec_1024_lt_word (N : ℕ) : 1024 < 2 ^ cr23Word N := by
  have h1 : (1024 : ℕ) = 2 ^ 10 := by norm_num
  rw [h1]
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  simp only [cr23Word]
  have := cr23Lb_succ_pos N
  omega
theorem dec_frame_add_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {c : ℕ} (hc : c ≤ 16) :
    cr23DecFrame N t + c < 2 ^ cr23Word N :=
  cr23_frame_add_lt_word N t hN htN (by omega)
theorem dec_candBase_le_mstBase (N t : ℕ) : decCandBase N t ≤ decMstBase N t :=
  le_trans (decCandBase_le_tagBase N t) (decTagBase_le_mstBase N t)
theorem decParBase_le_outBase (N t : ℕ) : decParBase N t ≤ decOutBase N t := by
  simp only [decOutBase]
  exact dec_le_add_r _ _
theorem decOutBase_le_end (N t : ℕ) : decOutBase N t ≤ cr23DecEnd N t := by
  simp only [cr23DecEnd]
  exact dec_le_add_r _ _
theorem decTagBase_le_end (N t : ℕ) : decTagBase N t ≤ cr23DecEnd N t :=
  le_trans (decTagBase_le_mstBase N t)
    (le_trans (decMstBase_le_parBase N t)
      (le_trans (decParBase_le_outBase N t) (decOutBase_le_end N t)))
theorem decSlot_lt_mstBase (N t : ℕ) {k : ℕ} (hk : k < 15) : decSlot N t k < decMstBase N t :=
  lt_of_lt_of_le (decSlot_lt_candBase N t hk) (dec_candBase_le_mstBase N t)
/-- The candidate pointer stays a legal word: `candBase + j < 2^W` for `j ≤ 2t+1`. -/
theorem dec_cand_add_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {j : ℕ}
    (hj : j ≤ 2 * t + 1) : decCandBase N t + j < 2 ^ cr23Word N := by
  have h1 : decCandBase N t + (2 * t + 1) = decTagBase N t := by simp only [decTagBase]
  have h2 : decTagBase N t ≤ cr23DecEnd N t := decTagBase_le_end N t
  calc decCandBase N t + j ≤ decCandBase N t + (2 * t + 1) := Nat.add_le_add_left hj _
    _ = decTagBase N t := h1
    _ ≤ cr23DecEnd N t := h2
    _ < 2 ^ cr23Word N := cr23DecEnd_lt_word N t hN htN
/-- The parity pointer stays a legal word: `parBase + v < 2^W` for `v < 2^(lb+1)`. -/
theorem dec_par_add_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {v : ℕ}
    (hv : v < 2 ^ (cr23Lb N + 1)) : decParBase N t + v < 2 ^ cr23Word N := by
  have h1 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by simp only [decOutBase]
  have h2 : decOutBase N t ≤ cr23DecEnd N t := decOutBase_le_end N t
  calc decParBase N t + v < decParBase N t + 2 ^ (cr23Lb N + 1) := Nat.add_lt_add_left hv _
    _ = decOutBase N t := h1
    _ ≤ cr23DecEnd N t := h2
    _ < 2 ^ cr23Word N := cr23DecEnd_lt_word N t hN htN
/-- The output pointer stays a legal word: `outBase + j < 2^W` for `j ≤ 2t+1`. -/
theorem dec_out_add_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) {j : ℕ}
    (hj : j ≤ 2 * t + 1) : decOutBase N t + j < 2 ^ cr23Word N := by
  have ht : t ≤ 2 ^ cr23Lb N := le_trans htN (cr23_le_pow_lb N)
  have hE := cr23DecEnd_le N t hN htN
  have h1 : decOutBase N t + (t + 1) = cr23DecEnd N t := by simp only [cr23DecEnd]
  have h2 : 2 ^ cr23Lb N ≤ 2 ^ (3 * cr23Lb N + 83) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : decOutBase N t + (2 * t + 1) = cr23DecEnd N t + t := by
    have h4 : decOutBase N t + (2 * t + 1) = decOutBase N t + (t + 1) + t := by ring
    rw [h4, h1]
  have h5 : decOutBase N t + (2 * t + 1) ≤ 2 ^ (3 * cr23Lb N + 100) := by
    rw [h3]
    calc cr23DecEnd N t + t ≤ 2 ^ (3 * cr23Lb N + 83) + 2 ^ (3 * cr23Lb N + 83) :=
          Nat.add_le_add hE (le_trans ht h2)
      _ = 2 * 2 ^ (3 * cr23Lb N + 83) := by ring
      _ = 2 ^ (3 * cr23Lb N + 84) := by
          rw [show 3 * cr23Lb N + 84 = (3 * cr23Lb N + 83) + 1 from by ring, pow_succ]
          ring
      _ ≤ 2 ^ (3 * cr23Lb N + 100) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc decOutBase N t + j ≤ decOutBase N t + (2 * t + 1) := Nat.add_le_add_left hj _
    _ ≤ 2 ^ (3 * cr23Lb N + 100) := h5
    _ < 2 ^ cr23Word N := cr23_lt_word_frame N hN (le_refl _)
/-- The master pointer stays below the parity bitmap: `mstBase + mstLen + j < parBase`. -/
theorem dec_mst_add_lt_parBase (N t : ℕ) {mstLen j : ℕ} (hj : mstLen + j < 2 * t + 1) :
    decMstBase N t + mstLen + j < decParBase N t := by
  have h1 : decMstBase N t + (2 * t + 1) = decParBase N t := by simp only [decParBase]
  have h2 : decMstBase N t + (mstLen + j) < decMstBase N t + (2 * t + 1) :=
    Nat.add_lt_add_left hj _
  have h3 : decMstBase N t + (mstLen + j) = decMstBase N t + mstLen + j := by ring
  rw [h3] at h2
  rw [h1] at h2
  exact h2
/-- The candidate list lives below the master list. -/
theorem dec_cand_add_lt_tag (N t : ℕ) {j : ℕ} (hj : j < 2 * t + 1) :
    decCandBase N t + j < decTagBase N t := by
  have h1 : decCandBase N t + (2 * t + 1) = decTagBase N t := by simp only [decTagBase]
  have h2 : decCandBase N t + j < decCandBase N t + (2 * t + 1) := Nat.add_lt_add_left hj _
  rw [h1] at h2
  exact h2
theorem dec_mstBase_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    decMstBase N t < 2 ^ cr23Word N := by
  have h := dec_par_add_lt_word N t hN htN (v := 0) (by simp)
  have h2 := decMstBase_le_parBase N t
  omega
theorem dec_candBase_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    decCandBase N t < 2 ^ cr23Word N := by
  have h := dec_cand_add_lt_word N t hN htN (j := 0) (by omega)
  simpa using h
theorem dec_parBase_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    decParBase N t < 2 ^ cr23Word N := by
  have h := dec_par_add_lt_word N t hN htN (v := 0) (by simp)
  simpa using h
/-- `2t+1` is a legal word (the output pointer never leaves the frame). -/
theorem dec_two_t_lt_word (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N) :
    2 * t + 1 < 2 ^ cr23Word N := by
  have h := dec_out_add_lt_word N t hN htN (j := 2 * t + 1) (le_refl _)
  omega
theorem decParIA_mem (E : RAMEnv) (st : RAMState) : (runBlock decParIA E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decParIA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decParIB_mem (E : RAMEnv) (st : RAMState) : (runBlock decParIB E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decParIB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decParIC_mem (E : RAMEnv) (st : RAMState) : (runBlock decParIC E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decParIC, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [iImm, iAdd, iLd, iBor]
theorem decParID_mem (E : RAMEnv) (st : RAMState) : (runBlock decParID E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decParID, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl <;> simp [iImm]
theorem decParInit_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decParInit E st).mem = st.mem := by
  rw [decParInit_split, runBlock_append, runBlock_append, runBlock_append, decParID_mem,
    decParIC_mem, decParIB_mem, decParIA_mem]
/-- The 16-instruction initialisation, read out through the slots. -/
theorem decParInit_regs (E : RAMEnv) (st : RAMState) (F cb pb mb ml len : ℕ)
    (h14 : st.regs r14 = F) (h2 : st.regs r2 = len)
    (hW1 : 1 < 2 ^ E.W) (hW10 : 10 < 2 ^ E.W) (hW12 : 12 < 2 ^ E.W) (hW13 : 13 < 2 ^ E.W)
    (hW15 : 15 < 2 ^ E.W) (hW0 : 0 < 2 ^ E.W)
    (hF10 : F + 10 < 2 ^ E.W) (hF12 : F + 12 < 2 ^ E.W) (hF13 : F + 13 < 2 ^ E.W)
    (hF15 : F + 15 < 2 ^ E.W)
    (hm10 : st.mem (F + 10) = cb) (hm12 : st.mem (F + 12) = mb) (hm13 : st.mem (F + 13) = pb)
    (hm15 : st.mem (F + 15) = ml)
    (hcb : cb < 2 ^ E.W) (hpb : pb < 2 ^ E.W) (hmb : mb < 2 ^ E.W) (hml : ml < 2 ^ E.W)
    (hsum : mb + ml < 2 ^ E.W) (hlen : len < 2 ^ E.W) :
    (runBlock decParInit E st).regs r0 = 0 ∧ (runBlock decParInit E st).regs r1 = len ∧
      (runBlock decParInit E st).regs r4 = 1 ∧ (runBlock decParInit E st).regs r5 = cb ∧
      (runBlock decParInit E st).regs r6 = pb ∧ (runBlock decParInit E st).regs r7 = mb + ml := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [decParInit, decParIA, decParIB, decParIC, decParID, runBlock_append, h14, h2, hm10,
      hm12, hm13, hm15, Nat.mod_eq_of_lt hW1, Nat.mod_eq_of_lt hW10, Nat.mod_eq_of_lt hW12,
      Nat.mod_eq_of_lt hW13, Nat.mod_eq_of_lt hW15, Nat.mod_eq_of_lt hW0,
      Nat.mod_eq_of_lt hF10, Nat.mod_eq_of_lt hF12, Nat.mod_eq_of_lt hF13,
      Nat.mod_eq_of_lt hF15, Nat.mod_eq_of_lt hcb, Nat.mod_eq_of_lt hpb, Nat.mod_eq_of_lt hmb,
      Nat.mod_eq_of_lt hml, Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hlen]
theorem decParBA_spec (E : RAMEnv) (st : RAMState) (cb pb i v old : ℕ) (hW : 1 < 2 ^ E.W)
    (h4 : st.regs r4 = 1) (h5 : st.regs r5 = cb) (h0 : st.regs r0 = i) (h6 : st.regs r6 = pb)
    (hm : st.mem (cb + i) = v) (hci : cb + i < 2 ^ E.W) (hv : v < 2 ^ E.W)
    (hold : st.mem (pb + v) = old) (ho1 : old ≤ 1) (hpv : pb + v < 2 ^ E.W) :
    (runBlock decParBA E st).regs r2 = v ∧ (runBlock decParBA E st).regs r3 = 1 - old ∧
      (runBlock decParBA E st).regs r9 = pb + v := by
  have hoW : old < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decParBA, h4, h5, h0, h6, hm, hold, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hci,
      Nat.mod_eq_of_lt hoW, Nat.mod_eq_of_lt hpv, dec_one_sub E.W old ho1 hW]
theorem decParBB_spec (E : RAMEnv) (st : RAMState) (pb mp v bit j : ℕ)
    (h9 : st.regs r9 = pb) (h3 : st.regs r3 = bit) (h7 : st.regs r7 = mp) (h2 : st.regs r2 = v)
    (h4 : st.regs r4 = 1) (h0 : st.regs r0 = j) (hmp : mp + 1 < 2 ^ E.W) (hj : j + 1 < 2 ^ E.W) :
    (runBlock decParBB E st).mem = Function.update (Function.update st.mem pb bit) mp v ∧
      (runBlock decParBB E st).regs r7 = mp + 1 ∧
      (runBlock decParBB E st).regs r0 = j + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decParBB, h9, h3, h7, h2, h4, h0, Nat.mod_eq_of_lt hmp, Nat.mod_eq_of_lt hj]
/-- `decParBA` writes only `r9`, `r2`, `r3`. -/
theorem decParBA_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (h9 : d ≠ r9) (h2 : d ≠ r2) (h3 : d ≠ r3) : (runBlock decParBA E st).regs d = st.regs d := by
  refine runBlock_regs_frame decParBA E st d ?_
  intro i hi hdest
  simp only [decParBA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simp only [Instr.dest?] at hdest; exact h9 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h2 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h9 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h3 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h3 (Option.some.inj hdest).symm
/-- `decParBB` writes only `r7`, `r0` (besides the two memory words). -/
theorem decParBB_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (h7 : d ≠ r7) (h0 : d ≠ r0) : (runBlock decParBB E st).regs d = st.regs d := by
  refine runBlock_regs_frame decParBB E st d ?_
  intro i hi hdest
  simp only [decParBB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact nomatch hdest
  · exact nomatch hdest
  · simp only [Instr.dest?] at hdest; exact h7 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h0 (Option.some.inj hdest).symm
theorem decParIA_noBranch : NoBranch decParIA := by simp [decParIA]
theorem decParIB_noBranch : NoBranch decParIB := by simp [decParIB]
theorem decParIC_noBranch : NoBranch decParIC := by simp [decParIC]
theorem decParID_noBranch : NoBranch decParID := by simp [decParID]
theorem decParBA_noBranch : NoBranch decParBA := by simp [decParBA]
theorem decParBB_noBranch : NoBranch decParBB := by simp [decParBB]
theorem decParBody_noBranch : NoBranch decParBody := by
  rw [decParBody_split]
  simp [decParBA_noBranch, decParBB_noBranch]
theorem decParInit_noBranch : NoBranch decParInit := by
  rw [decParInit_split]
  simp [decParIA_noBranch, decParIB_noBranch, decParIC_noBranch, decParID_noBranch]
theorem decParInit_len : decParInit.length = 16 := by
  simp [decParInit, decParIA, decParIB, decParIC, decParID]
theorem decParBody_len : decParBody.length = 9 := by
  simp [decParBody, decParBA, decParBB]
/-- **`DecParInv`** — the loop-head invariant of body (d) at step `j`: the parity bitmap holds the
set `S j` (the round's initial parity set toggled by the first `j` candidate values), the candidate
list is intact, and the master list has received `l[0..j)`. -/
def DecParInv (N t : ℕ) (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ)
    (st : RAMState) : Prop :=
  st.regs r0 = j ∧
  st.regs r1 = l.length ∧
  st.regs r4 = 1 ∧
  st.regs r5 = decCandBase N t ∧
  st.regs r6 = decParBase N t ∧
  st.regs r7 = decMstBase N t + mstLen + j ∧
  (∀ i, i < l.length → st.mem (decCandBase N t + i) = l.getD i 0) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S j then 1 else 0) ∧
  (∀ a, a < decMstBase N t → st.mem a = mb a) ∧
  (∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0) ∧
  (∀ k, k < j → st.mem (decMstBase N t + mstLen + k) = l.getD k 0)
/-- `DecParInv` never looks at the program counter. -/
theorem DecParInv_pc (N t : ℕ) (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ)
    (mb : ℕ → ℕ) (p : ℕ) (st : RAMState) (h : DecParInv N t S l mst mstLen j mb st) :
    DecParInv N t S l mst mstLen j mb { st with pc := p } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
/-- **The initialisation establishes the invariant at `j = 0`**: the four frame slots are read out
of the round-head memory `mb`, which is what `DecData` provides. -/
theorem decParInit_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (h14 : st.regs r14 = cr23DecFrame N t) (h2 : st.regs r2 = l.length)
    (hcand : ∀ i, i < l.length → mb (decCandBase N t + i) = l.getD i 0)
    (hbelow : ∀ b, b < decMstBase N t → st.mem b = mb b)
    (hsl9 : mb (decSlot N t 9) = decCandBase N t)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl14 : mb (decSlot N t 14) = mstLen)
    (hmst : ∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0)
    (hcap : mstLen + l.length ≤ 2 * t + 1)
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0) :
    DecParInv N t S l mst mstLen 0 mb (runBlock decParInit E st) := by
  have hW1 : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hbig : 1024 < 2 ^ E.W := by rw [hEW]; exact dec_1024_lt_word N
  have hW10 : 10 < 2 ^ E.W := by omega
  have hW12 : 12 < 2 ^ E.W := by omega
  have hW13 : 13 < 2 ^ E.W := by omega
  have hW15 : 15 < 2 ^ E.W := by omega
  have hW0 : 0 < 2 ^ E.W := by omega
  have hF10 : cr23DecFrame N t + 10 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF12 : cr23DecFrame N t + 12 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF13 : cr23DecFrame N t + 13 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF15 : cr23DecFrame N t + 15 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hcb : decCandBase N t < 2 ^ E.W := by rw [hEW]; exact dec_candBase_lt_word N t hN htN
  have hpb : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
  have hmb : decMstBase N t < 2 ^ E.W := by rw [hEW]; exact dec_mstBase_lt_word N t hN htN
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hml : mstLen < 2 ^ E.W := by omega
  have hlenW : l.length < 2 ^ E.W := by omega
  have hsum : decMstBase N t + mstLen < 2 ^ E.W := by
    have h1 : decMstBase N t + mstLen ≤ decMstBase N t + (2 * t + 1) :=
      Nat.add_le_add_left (by omega) _
    have h2 : decMstBase N t + (2 * t + 1) = decParBase N t := by simp only [decParBase]
    omega
  have hslot : ∀ (k : ℕ) (_ : k < 15) (val : ℕ), mb (decSlot N t k) = val →
      st.mem (decSlot N t k) = val := by
    intro k hk val hv
    rw [hbelow _ (decSlot_lt_mstBase N t hk)]
    exact hv
  have hc10 : st.mem (cr23DecFrame N t + 10) = decCandBase N t := by
    have := hslot 9 (by norm_num) _ hsl9
    rwa [decSlot_nine] at this
  have hc12 : st.mem (cr23DecFrame N t + 12) = decMstBase N t := by
    have := hslot 11 (by norm_num) _ hsl11
    rwa [decSlot_eleven] at this
  have hc13 : st.mem (cr23DecFrame N t + 13) = decParBase N t := by
    have := hslot 12 (by norm_num) _ hsl12
    rwa [decSlot_twelve] at this
  have hc15 : st.mem (cr23DecFrame N t + 15) = mstLen := by
    have := hslot 14 (by norm_num) _ hsl14
    rwa [decSlot_fourteen] at this
  obtain ⟨hr0, hr1, hr4, hr5, hr6, hr7⟩ :=
    decParInit_regs E st (cr23DecFrame N t) (decCandBase N t) (decParBase N t)
      (decMstBase N t) mstLen (l.length) h14 h2 hW1 hW10 hW12 hW13 hW15 hW0 hF10 hF12 hF13 hF15
      hc10 hc12 hc13 hc15 hcb hpb hmb hml hsum hlenW
  have hmem : (runBlock decParInit E st).mem = st.mem := decParInit_mem E st
  refine ⟨hr0, hr1, hr4, hr5, hr6, hr7, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi2 : i < 2 * t + 1 := by omega
    have hcm : decCandBase N t + i < decMstBase N t :=
      lt_of_lt_of_le (dec_cand_add_lt_tag N t hi2) (decTagBase_le_mstBase N t)
    rw [hmem, hbelow _ hcm]
    exact hcand i hi
  · intro v hv
    rw [hmem]
    exact hpar0 v hv
  · intro b hb
    rw [hmem]
    exact hbelow b hb
  · intro i hi
    rw [hmem]
    exact hmst i hi
  · intro k hk
    omega
theorem decParBody_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hj : j < l.length) (hcap : mstLen + l.length ≤ 2 * t + 1)
    (hlN : ∀ i ∈ l, i < N) (hS : S (j + 1) = decSymm (S j) {l.getD j 0})
    (hI : DecParInv N t S l mst mstLen j mb st) :
    DecParInv N t S l mst mstLen (j + 1) mb (runBlock decParBody E st) := by
  obtain ⟨h0, h1, h4, h5, h6, h7, hcand, hpar, hbelow, hmst, hnew⟩ := hI
  set x : ℕ := l.getD j 0 with hx
  set o : ℕ := if x ∈ S j then 1 else 0 with ho
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hxmem : x ∈ l := by rw [hx]; exact dec_getD_mem hj
  have hxN : x < N := hlN x hxmem
  have hexp : cr23Lb N + 1 ≤ cr23Word N := by
    simp only [cr23Word]
    have := cr23Lb_succ_pos N
    omega
  have hxLb : x < 2 ^ (cr23Lb N + 1) := by
    have h1 : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    have h2 : 2 ^ cr23Lb N ≤ 2 ^ (cr23Lb N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxW : x < 2 ^ E.W := by
    rw [hEW]
    exact lt_of_lt_of_le hxLb (Nat.pow_le_pow_right (by norm_num) hexp)
  have ho1 : o ≤ 1 := by rw [ho]; split_ifs <;> omega
  have hlt2t : j < 2 * t + 1 := by omega
  have hci : decCandBase N t + j < 2 ^ E.W := by
    rw [hEW]; exact dec_cand_add_lt_word N t hN htN (by omega)
  have hpv : decParBase N t + x < 2 ^ E.W := by
    rw [hEW]; exact dec_par_add_lt_word N t hN htN hxLb
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hjW : j + 1 < 2 ^ E.W := by omega
  have hcap2 : mstLen + j < 2 * t + 1 := by omega
  have hmpPar : decMstBase N t + mstLen + j < decParBase N t :=
    dec_mst_add_lt_parBase N t hcap2
  have hmpPar' : decMstBase N t + mstLen + j < decParBase N t + x :=
    lt_of_lt_of_le hmpPar (dec_le_add_r _ _)
  have hmpLt : decMstBase N t + mstLen + j < 2 ^ E.W := by
    have h2 : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
    exact lt_trans hmpPar h2
  have hmp1 : decMstBase N t + mstLen + j + 1 < 2 ^ E.W := by omega
  have hmstLt : decMstBase N t ≤ decParBase N t := decMstBase_le_parBase N t
  have hbelow' : decMstBase N t ≤ decMstBase N t + mstLen + j := by omega
  -- every candidate lives below the master list
  have hcm : ∀ i, i < l.length → decCandBase N t + i < decMstBase N t := by
    intro i hi
    have hi2 : i < 2 * t + 1 := by omega
    exact lt_of_lt_of_le (dec_cand_add_lt_tag N t hi2) (decTagBase_le_mstBase N t)
  have hcandx : st.mem (decCandBase N t + j) = x := by
    rw [hx]; exact hcand j hj
  have hparx : st.mem (decParBase N t + x) = o := by
    rw [ho]; exact hpar x hxLb
  -- chunk A
  set st1 : RAMState := runBlock decParBA E st with hst1
  have hBA := decParBA_spec E st (decCandBase N t) (decParBase N t) j x o hW h4 h5 h0 h6 hcandx
    hci hxW hparx ho1 hpv
  have hA2 : st1.regs r2 = x := hBA.1
  have hA3 : st1.regs r3 = 1 - o := hBA.2.1
  have hA9 : st1.regs r9 = decParBase N t + x := hBA.2.2
  have hA0 : st1.regs r0 = j := by
    rw [hst1]; exact (decParBA_frame E st r0 (by decide) (by decide) (by decide)).trans h0
  have hA4 : st1.regs r4 = 1 := by
    rw [hst1]; exact (decParBA_frame E st r4 (by decide) (by decide) (by decide)).trans h4
  have hA5 : st1.regs r5 = decCandBase N t := by
    rw [hst1]; exact (decParBA_frame E st r5 (by decide) (by decide) (by decide)).trans h5
  have hA6 : st1.regs r6 = decParBase N t := by
    rw [hst1]; exact (decParBA_frame E st r6 (by decide) (by decide) (by decide)).trans h6
  have hA7 : st1.regs r7 = decMstBase N t + mstLen + j := by
    rw [hst1]; exact (decParBA_frame E st r7 (by decide) (by decide) (by decide)).trans h7
  -- chunk B
  have hBB := decParBB_spec E st1 (decParBase N t + x) (decMstBase N t + mstLen + j) x (1 - o) j
    hA9 hA3 hA7 hA2 hA4 hA0 hmp1 hjW
  have hB7 : (runBlock decParBody E st).regs r7 = decMstBase N t + mstLen + j + 1 := by
    rw [decParBody_split, runBlock_append, ← hst1]
    exact hBB.2.1
  have hB0 : (runBlock decParBody E st).regs r0 = j + 1 := by
    rw [decParBody_split, runBlock_append, ← hst1]
    exact hBB.2.2
  have hBmem : (runBlock decParBody E st).mem
      = Function.update (Function.update st.mem (decParBase N t + x) (1 - o))
          (decMstBase N t + mstLen + j) x := by
    rw [decParBody_split, runBlock_append, ← hst1]
    exact hBB.1
  have hrest : ∀ d : Fin 16, d ≠ r9 → d ≠ r2 → d ≠ r3 → d ≠ r7 → d ≠ r0 →
      (runBlock decParBody E st).regs d = st.regs d := by
    intro d h9 h2 h3 h7' h0'
    rw [decParBody_split, runBlock_append, ← hst1]
    exact (decParBB_frame E (runBlock decParBA E st) d h7' h0').trans
      (decParBA_frame E st d h9 h2 h3)
  refine ⟨hB0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrest r1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1
  · rw [hrest r4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
  · rw [hrest r5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
  · rw [hrest r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
  · rw [hB7]; omega
  · intro i hi
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
      (decCandBase N t + i) hmpPar' (lt_of_lt_of_le (hcm i hi) hbelow')]
    exact hcand i hi
  · intro v hv
    rw [hS]
    by_cases hvx : v = x
    · subst hvx
      rw [hBmem, dec_upd2_fst (show decMstBase N t + mstLen + j ≠ decParBase N t + x from by omega),
        ho, dec_toggle]
    · have hiff : (v ∈ decSymm (S j) {x}) ↔ v ∈ S j := decSymm_singleton_ne (S j) hvx
      rw [hBmem, dec_upd2_ne
        (show decParBase N t + v ≠ decParBase N t + x from fun h => hvx (by omega))
        (show decParBase N t + v ≠ decMstBase N t + mstLen + j from by omega), hpar v hv]
      by_cases hm : v ∈ S j
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
      · rw [if_neg hm, if_neg (fun hh => hm (hiff.mp hh))]
  · intro a ha
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x a
      hmpPar' (lt_of_lt_of_le ha hbelow')]
    exact hbelow a ha
  · intro i hi
    have h1 : decMstBase N t + i < decMstBase N t + mstLen := Nat.add_lt_add_left hi _
    have h2 : decMstBase N t + mstLen ≤ decMstBase N t + mstLen + j := dec_le_add_r _ _
    rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
      (decMstBase N t + i) hmpPar' (lt_of_lt_of_le h1 h2)]
    exact hmst i hi
  · intro k hk
    by_cases hk' : k = j
    · subst hk'
      rw [hBmem, dec_upd2_snd, ← hx]
    · have h1 : decMstBase N t + mstLen + k < decMstBase N t + mstLen + j :=
        Nat.add_lt_add_left (by omega) _
      rw [hBmem, dec_upd2_lt st.mem (decParBase N t + x) (decMstBase N t + mstLen + j) (1 - o) x
        (decMstBase N t + mstLen + k) hmpPar' h1]
      exact hnew k (by omega)
theorem decEmitInit_split :
    decEmitInit = decEmitEA ++ decEmitEB ++ decEmitEC ++ decEmitED ++ decEmitEE := rfl
theorem decEmitBody_split : decEmitBody = decEmitBA ++ decEmitBB := rfl
/-- The output-counter increment of one emit step. -/
def decEmitSel (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) : ℕ :=
  if x ∈ P \ lacc.toFinset then 1 else 0
/-- The emitted list after one emit step. -/
def decEmitApp (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) : List ℕ :=
  if x ∈ P \ lacc.toFinset then lacc ++ [x] else lacc
theorem decEmitSel_le (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) : decEmitSel P lacc x ≤ 1 := by
  simp only [decEmitSel]
  split_ifs <;> omega
theorem decEmitSel_one (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) :
    decEmitSel P lacc x = 1 ↔ x ∈ P \ lacc.toFinset := by
  simp only [decEmitSel]
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd hh h⟩
theorem decEmitApp_pos (P : Finset ℕ) (lacc : List ℕ) {x : ℕ} (h : x ∈ P \ lacc.toFinset) :
    decEmitApp P lacc x = lacc ++ [x] := by
  simp only [decEmitApp]
  rw [if_pos h]
theorem decEmitApp_neg (P : Finset ℕ) (lacc : List ℕ) {x : ℕ} (h : x ∉ P \ lacc.toFinset) :
    decEmitApp P lacc x = lacc := by
  simp only [decEmitApp]
  rw [if_neg h]
/-- Adding an element to a list does not change the remaining set of the other values. -/
theorem dec_sdiff_concat (P : Finset ℕ) (lacc : List ℕ) {x w : ℕ} (hwx : w ≠ x) :
    (w ∈ P \ (lacc ++ [x]).toFinset) ↔ (w ∈ P \ lacc.toFinset) := by
  have hset : (lacc ++ [x]).toFinset = lacc.toFinset ∪ {x} := by
    rw [List.toFinset_append]
    simp
  rw [hset, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => h2 (Or.inl hh)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => hh.elim h2 (fun h3 => absurd h3 hwx)⟩
theorem decEmitEA_mem (E : RAMEnv) (st : RAMState) : (runBlock decEmitEA E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decEmitEA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decEmitEB_mem (E : RAMEnv) (st : RAMState) : (runBlock decEmitEB E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decEmitEB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decEmitEC_mem (E : RAMEnv) (st : RAMState) : (runBlock decEmitEC E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decEmitEC, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decEmitED_mem (E : RAMEnv) (st : RAMState) : (runBlock decEmitED E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decEmitED, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [iImm, iAdd, iLd]
theorem decEmitEE_mem (E : RAMEnv) (st : RAMState) : (runBlock decEmitEE E st).mem = st.mem := by
  refine runBlock_mem_frame _ _ _ ?_
  intro i hi a v
  simp only [decEmitEE, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [iImm]
theorem decEmitInit_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decEmitInit E st).mem = st.mem := by
  rw [decEmitInit_split, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
    decEmitEE_mem, decEmitED_mem, decEmitEC_mem, decEmitEB_mem, decEmitEA_mem]
theorem decEmitBA_spec (E : RAMEnv) (st : RAMState) (MB PB j x sel : ℕ)
    (h8 : st.regs r8 = MB) (h9 : st.regs r9 = PB) (h0 : st.regs r0 = j) (h11 : st.regs r11 = 0)
    (hW : 1 < 2 ^ E.W) (hMB : MB + j < 2 ^ E.W) (hm : st.mem (MB + j) = x) (hxW : x < 2 ^ E.W)
    (hPB : PB + x < 2 ^ E.W) (hp : st.mem (PB + x) = sel) (hsel1 : sel ≤ 1) :
    (runBlock decEmitBA E st).regs r3 = x ∧ (runBlock decEmitBA E st).regs r4 = sel ∧
      (runBlock decEmitBA E st).mem = Function.update st.mem (PB + x) 0 := by
  have hselW : sel % 2 ^ E.W = sel := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decEmitBA, h8, h9, h0, h11, hm, hp, hselW, Nat.mod_eq_of_lt hMB,
      Nat.mod_eq_of_lt hxW, Nat.mod_eq_of_lt hPB]
theorem decEmitBB_spec (E : RAMEnv) (st : RAMState) (OB cnt x sel j : ℕ)
    (h10 : st.regs r10 = OB) (h1 : st.regs r1 = cnt) (h3 : st.regs r3 = x) (h4 : st.regs r4 = sel)
    (h6 : st.regs r6 = 1) (h0 : st.regs r0 = j)
    (hOB : OB + cnt < 2 ^ E.W) (hcs : cnt + sel < 2 ^ E.W) (hj : j + 1 < 2 ^ E.W) :
    (runBlock decEmitBB E st).mem = Function.update st.mem (OB + cnt) x ∧
      (runBlock decEmitBB E st).regs r0 = j + 1 ∧
      (runBlock decEmitBB E st).regs r1 = cnt + sel := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decEmitBB, h10, h1, h3, h4, h6, h0, Nat.mod_eq_of_lt hOB, Nat.mod_eq_of_lt hcs,
      Nat.mod_eq_of_lt hj]
/-- `decEmitBA` writes only `r5`, `r3`, `r4` (besides the memory word). -/
theorem decEmitBA_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (h5 : d ≠ r5) (h3 : d ≠ r3) (h4 : d ≠ r4) : (runBlock decEmitBA E st).regs d = st.regs d := by
  refine runBlock_regs_frame decEmitBA E st d ?_
  intro i hi hdest
  simp only [decEmitBA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simp only [Instr.dest?] at hdest; exact h5 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h3 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h5 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h4 (Option.some.inj hdest).symm
  · exact nomatch hdest
/-- `decEmitBB` writes only `r5`, `r0`, `r1` (besides the memory word). -/
theorem decEmitBB_frame (E : RAMEnv) (st : RAMState) (d : Fin 16)
    (h5 : d ≠ r5) (h0 : d ≠ r0) (h1 : d ≠ r1) : (runBlock decEmitBB E st).regs d = st.regs d := by
  refine runBlock_regs_frame decEmitBB E st d ?_
  intro i hi hdest
  simp only [decEmitBB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [Instr.dest?] at hdest; exact h5 (Option.some.inj hdest).symm
  · exact nomatch hdest
  · simp only [Instr.dest?] at hdest; exact h0 (Option.some.inj hdest).symm
  · simp only [Instr.dest?] at hdest; exact h1 (Option.some.inj hdest).symm
theorem decEmitPost_spec (E : RAMEnv) (st : RAMState) (OB : ℕ)
    (h10 : st.regs r10 = OB) (hOB : OB < 2 ^ E.W) :
    (runBlock decEmitPost E st).regs r0 = OB := by
  simp [decEmitPost, h10, Nat.mod_eq_of_lt hOB]
theorem decEmitInit_noBranch : NoBranch decEmitInit := by
  simp [decEmitInit, decEmitEA, decEmitEB, decEmitEC, decEmitED, decEmitEE]
theorem decEmitBA_noBranch : NoBranch decEmitBA := by simp [decEmitBA]
theorem decEmitBB_noBranch : NoBranch decEmitBB := by simp [decEmitBB]
theorem decEmitPost_noBranch : NoBranch decEmitPost := by simp [decEmitPost]
theorem decEmitBody_noBranch : NoBranch decEmitBody := by
  rw [decEmitBody_split]
  simp [decEmitBA_noBranch, decEmitBB_noBranch]
theorem decEmitInit_len : decEmitInit.length = 16 := by
  simp [decEmitInit, decEmitEA, decEmitEB, decEmitEC, decEmitED, decEmitEE]
theorem decEmitBody_len : decEmitBody.length = 9 := by
  simp [decEmitBody, decEmitBA, decEmitBB]
theorem decEmitPost_len : decEmitPost.length = 1 := by
  simp [decEmitPost]
/-- **`DecEmitInv`** — the loop-head invariant of body (e) at step `j`: the output words spell the
duplicate-free list `lacc`, the parity bitmap holds the *remaining* set `P \ lacc`, and every entry
of `mst` before `j` that lies in `P` has already been emitted. -/
def DecEmitInv (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (st : RAMState) : Prop :=
  st.regs r0 = j ∧
  st.regs r1 = cnt ∧
  st.regs r2 = mst.length ∧
  st.regs r6 = 1 ∧
  st.regs r8 = decMstBase N t ∧
  st.regs r9 = decParBase N t ∧
  st.regs r10 = decOutBase N t ∧
  st.regs r11 = 0 ∧
  cnt ≤ j ∧
  (∀ k, k < cnt → st.mem (decOutBase N t + k) = lacc.getD k 0) ∧
  lacc.Nodup ∧ lacc.length = cnt ∧
  (∀ v, v ∈ lacc → v ∈ P) ∧
  (∀ k, k < j → mst.getD k 0 ∈ P → mst.getD k 0 ∈ lacc) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ P \ lacc.toFinset then 1 else 0) ∧
  (∀ a, a < decParBase N t → st.mem a = mb a)
/-- `DecEmitInv` never looks at the program counter. -/
theorem DecEmitInv_pc (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (p : ℕ) (st : RAMState) (h : DecEmitInv N t P mst j cnt lacc mb st) :
    DecEmitInv N t P mst j cnt lacc mb { st with pc := p } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩
/-- At the end of the pass the emitted list is exactly the parity set. -/
theorem DecEmitInv_set (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (cnt : ℕ) (lacc : List ℕ)
    (mb : ℕ → ℕ) (st : RAMState) (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h : DecEmitInv N t P mst mst.length cnt lacc mb st) : lacc.toFinset = P := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsubP, hseen, -, -⟩ := h
  ext v
  constructor
  · intro hv
    exact hsubP v (List.mem_toFinset.mp hv)
  · intro hvP
    obtain ⟨k, hk, hget⟩ := dec_mem_getD (hsub v hvP)
    have hkP : mst.getD k 0 ∈ P := by rw [hget]; exact hvP
    rw [← hget]
    exact List.mem_toFinset.mpr (hseen k hk hkP)
theorem decEmitInit_regs (E : RAMEnv) (st : RAMState) (F MB PB OB ML : ℕ)
    (h14 : st.regs r14 = F)
    (hW1 : 1 < 2 ^ E.W) (hW12 : 12 < 2 ^ E.W) (hW13 : 13 < 2 ^ E.W) (hW14 : 14 < 2 ^ E.W)
    (hW15 : 15 < 2 ^ E.W) (hW0 : 0 < 2 ^ E.W)
    (hF12 : F + 12 < 2 ^ E.W) (hF13 : F + 13 < 2 ^ E.W) (hF14 : F + 14 < 2 ^ E.W)
    (hF15 : F + 15 < 2 ^ E.W)
    (hm12 : st.mem (F + 12) = MB) (hm13 : st.mem (F + 13) = PB) (hm14 : st.mem (F + 14) = OB)
    (hm15 : st.mem (F + 15) = ML)
    (hMB : MB < 2 ^ E.W) (hPB : PB < 2 ^ E.W) (hOB : OB < 2 ^ E.W) (hML : ML < 2 ^ E.W) :
    (runBlock decEmitInit E st).regs r0 = 0 ∧ (runBlock decEmitInit E st).regs r1 = 0 ∧
      (runBlock decEmitInit E st).regs r2 = ML ∧ (runBlock decEmitInit E st).regs r6 = 1 ∧
      (runBlock decEmitInit E st).regs r8 = MB ∧ (runBlock decEmitInit E st).regs r9 = PB ∧
      (runBlock decEmitInit E st).regs r10 = OB ∧ (runBlock decEmitInit E st).regs r11 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [decEmitInit, decEmitEA, decEmitEB, decEmitEC, decEmitED, decEmitEE, runBlock_append,
      h14, hm12, hm13, hm14, hm15, Nat.mod_eq_of_lt hW1, Nat.mod_eq_of_lt hW12,
      Nat.mod_eq_of_lt hW13, Nat.mod_eq_of_lt hW14, Nat.mod_eq_of_lt hW15, Nat.mod_eq_of_lt hW0,
      Nat.mod_eq_of_lt hF12, Nat.mod_eq_of_lt hF13, Nat.mod_eq_of_lt hF14, Nat.mod_eq_of_lt hF15,
      Nat.mod_eq_of_lt hMB, Nat.mod_eq_of_lt hPB, Nat.mod_eq_of_lt hOB, Nat.mod_eq_of_lt hML]
theorem decEmitInit_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (h14 : st.regs r14 = cr23DecFrame N t)
    (hbelow : ∀ b, b < decParBase N t → st.mem b = mb b)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl13 : mb (decSlot N t 13) = decOutBase N t)
    (hsl14 : mb (decSlot N t 14) = mst.length)
    (hcap : mst.length ≤ 2 * t + 1)
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ P then 1 else 0) :
    DecEmitInv N t P mst 0 0 [] mb (runBlock decEmitInit E st) := by
  have hbig : 1024 < 2 ^ E.W := by rw [hEW]; exact dec_1024_lt_word N
  have hW1 : 1 < 2 ^ E.W := by omega
  have hW12 : 12 < 2 ^ E.W := by omega
  have hW13 : 13 < 2 ^ E.W := by omega
  have hW14 : 14 < 2 ^ E.W := by omega
  have hW15 : 15 < 2 ^ E.W := by omega
  have hW0 : 0 < 2 ^ E.W := by omega
  have hF12 : cr23DecFrame N t + 12 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF13 : cr23DecFrame N t + 13 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF14 : cr23DecFrame N t + 14 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hF15 : cr23DecFrame N t + 15 < 2 ^ E.W := by
    rw [hEW]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have hmbW : decMstBase N t < 2 ^ E.W := by rw [hEW]; exact dec_mstBase_lt_word N t hN htN
  have hpbW : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
  have hobW : decOutBase N t < 2 ^ E.W := by
    have h := dec_out_add_lt_word N t hN htN (j := 0) (by omega)
    rw [hEW]
    omega
  have hmlW : mst.length < 2 ^ E.W := by
    have h2t := dec_two_t_lt_word N t hN htN
    rw [hEW]
    omega
  have hslot : ∀ (k : ℕ) (_ : k < 15) (val : ℕ), mb (decSlot N t k) = val →
      st.mem (decSlot N t k) = val := by
    intro k hk val hv
    rw [hbelow _ (lt_of_lt_of_le (decSlot_lt_mstBase N t hk) (decMstBase_le_parBase N t))]
    exact hv
  have hc12 : st.mem (cr23DecFrame N t + 12) = decMstBase N t := by
    have := hslot 11 (by norm_num) _ hsl11
    rwa [decSlot_eleven] at this
  have hc13 : st.mem (cr23DecFrame N t + 13) = decParBase N t := by
    have := hslot 12 (by norm_num) _ hsl12
    rwa [decSlot_twelve] at this
  have hc14 : st.mem (cr23DecFrame N t + 14) = decOutBase N t := by
    have := hslot 13 (by norm_num) _ hsl13
    rwa [decSlot_thirteen] at this
  have hc15 : st.mem (cr23DecFrame N t + 15) = mst.length := by
    have := hslot 14 (by norm_num) _ hsl14
    rwa [decSlot_fourteen] at this
  obtain ⟨hr0, hr1, hr2, hr6, hr8, hr9, hr10, hr11⟩ :=
    decEmitInit_regs E st (cr23DecFrame N t) (decMstBase N t) (decParBase N t)
      (decOutBase N t) (mst.length) h14 hW1 hW12 hW13 hW14 hW15 hW0 hF12 hF13 hF14 hF15 hc12 hc13
      hc14 hc15 hmbW hpbW hobW hmlW
  have hmem : (runBlock decEmitInit E st).mem = st.mem := decEmitInit_mem E st
  refine ⟨hr0, hr1, hr2, hr6, hr8, hr9, hr10, hr11, by omega, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro k hk
    omega
  · exact List.nodup_nil
  · intro v hv
    exact absurd hv (by simp)
  · intro k hk
    omega
  · intro v hv
    rw [hmem]
    have h : P \ ([] : List ℕ).toFinset = P := by simp
    rw [h]
    exact hpar0 v hv
  · intro b hb
    rw [hmem]
    exact hbelow b hb
theorem decEmitApp_getD (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) {k : ℕ}
    (hk : k < lacc.length) : (decEmitApp P lacc x).getD k 0 = lacc.getD k 0 := by
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc h]
    exact dec_getD_append_lt lacc [x] hk
  · rw [decEmitApp_neg P lacc h]
theorem decEmitApp_nodup (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) (h : lacc.Nodup) :
    (decEmitApp P lacc x).Nodup := by
  by_cases hx : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc hx]
    exact dec_nodup_concat lacc x h
      (fun hh => (Finset.mem_sdiff.mp hx).2 (List.mem_toFinset.mpr hh))
  · rw [decEmitApp_neg P lacc hx]
    exact h
theorem decEmitApp_length (P : Finset ℕ) (lacc : List ℕ) (x : ℕ) :
    (decEmitApp P lacc x).length = lacc.length + decEmitSel P lacc x := by
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc h, decEmitSel, if_pos h]
    simp
  · rw [decEmitApp_neg P lacc h, decEmitSel, if_neg h]
    simp
theorem decEmitApp_sub (P : Finset ℕ) (lacc : List ℕ) (x : ℕ)
    (hsub : ∀ v, v ∈ lacc → v ∈ P) :
    ∀ v, v ∈ decEmitApp P lacc x → v ∈ P := by
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc h]
    intro v hv
    rcases List.mem_append.mp hv with hv' | hv'
    · exact hsub v hv'
    · rw [List.mem_singleton.mp hv']
      exact (Finset.mem_sdiff.mp h).1
  · rw [decEmitApp_neg P lacc h]
    exact hsub
theorem decEmitApp_seen (P : Finset ℕ) (lacc : List ℕ) (mst : List ℕ) (j : ℕ) (x : ℕ)
    (hx : x = mst.getD j 0)
    (hseen : ∀ k, k < j → mst.getD k 0 ∈ P → mst.getD k 0 ∈ lacc) :
    ∀ k, k < j + 1 → mst.getD k 0 ∈ P → mst.getD k 0 ∈ decEmitApp P lacc x := by
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc h]
    intro k hk hkP
    rcases lt_or_eq_of_le (by omega : k ≤ j) with hkj | hkj
    · exact List.mem_append_left _ (hseen k hkj hkP)
    · subst hkj
      exact List.mem_append_right _ (by rw [List.mem_singleton]; exact hx.symm)
  · rw [decEmitApp_neg P lacc h]
    intro k hk hkP
    rcases lt_or_eq_of_le (by omega : k ≤ j) with hkj | hkj
    · exact hseen k hkj hkP
    · subst hkj
      have hxP : x ∈ P := by rw [hx]; exact hkP
      have hxl' : x ∈ lacc := by
        by_contra hc
        exact h (Finset.mem_sdiff.mpr ⟨hxP, fun hh => hc (List.mem_toFinset.mp hh)⟩)
      rw [← hx]
      exact hxl'
theorem decEmitApp_sdiff (P : Finset ℕ) (lacc : List ℕ) {x w : ℕ} (hwx : w ≠ x) :
    (w ∈ P \ (decEmitApp P lacc x).toFinset) ↔ (w ∈ P \ lacc.toFinset) := by
  by_cases h : x ∈ P \ lacc.toFinset
  · rw [decEmitApp_pos P lacc h]
    exact dec_sdiff_concat P lacc hwx
  · rw [decEmitApp_neg P lacc h]
theorem decEmitApp_self (P : Finset ℕ) (lacc : List ℕ) {x : ℕ}
    (h : x ∈ P \ lacc.toFinset) : x ∉ P \ (decEmitApp P lacc x).toFinset := by
  rw [decEmitApp_pos P lacc h]
  intro hh
  exact (Finset.mem_sdiff.mp hh).2 (by
    rw [List.toFinset_append]
    exact Finset.mem_union_right _ (by simp))
theorem decEmitApp_self_neg (P : Finset ℕ) (lacc : List ℕ) {x : ℕ}
    (h : x ∉ P \ lacc.toFinset) : x ∉ P \ (decEmitApp P lacc x).toFinset := by
  rw [decEmitApp_neg P lacc h]
  exact h
theorem decEmitBody_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hj : j < mst.length) (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (hI : DecEmitInv N t P mst j cnt lacc mb st) :
    DecEmitInv N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
      (decEmitApp P lacc (mst.getD j 0)) mb (runBlock decEmitBody E st) := by
  obtain ⟨h0, h1, h2, h6, h8, h9, h10, h11, hcj, hout, hnd, hlen, hsubP, hseen, hpar,
    hbelow⟩ := hI
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  set x : ℕ := mst.getD j 0 with hx
  set sel : ℕ := decEmitSel P lacc x with hsel
  have hxmem : x ∈ mst := by rw [hx]; exact dec_getD_mem hj
  have hxN : x < N := hmstN x hxmem
  have hxl : x < 2 ^ (cr23Lb N + 1) := by
    have h1' : N ≤ 2 ^ cr23Lb N := cr23_le_pow_lb N
    have h2' : 2 ^ cr23Lb N ≤ 2 ^ (cr23Lb N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxW : x < 2 ^ E.W := by
    have hexp : cr23Lb N + 1 ≤ cr23Word N := by
      simp only [cr23Word]
      have := cr23Lb_succ_pos N
      omega
    rw [hEW]
    exact lt_of_lt_of_le hxl (Nat.pow_le_pow_right (by norm_num) hexp)
  have hsel1 : sel ≤ 1 := by rw [hsel]; exact decEmitSel_le P lacc x
  have h2t : 2 * t + 1 < 2 ^ E.W := by rw [hEW]; exact dec_two_t_lt_word N t hN htN
  have hjW : j + 1 < 2 ^ E.W := by omega
  have hparOut : decParBase N t ≤ decOutBase N t := decParBase_le_outBase N t
  have hmstjPar : decMstBase N t + j < decParBase N t := by
    have h2' : decMstBase N t + mst.length ≤ decMstBase N t + (2 * t + 1) :=
      Nat.add_le_add_left hcap _
    have h3 : decMstBase N t + (2 * t + 1) = decParBase N t := by simp only [decParBase]
    have h1' : decMstBase N t + j < decMstBase N t + mst.length := Nat.add_lt_add_left hj _
    omega
  have hlenW : decMstBase N t + j < 2 ^ E.W := by
    have h5 : decParBase N t < 2 ^ E.W := by rw [hEW]; exact dec_parBase_lt_word N t hN htN
    omega
  have hparxW : decParBase N t + x < 2 ^ E.W := by
    rw [hEW]; exact dec_par_add_lt_word N t hN htN hxl
  have houtcW : decOutBase N t + cnt < 2 ^ E.W := by
    have h4 := dec_out_add_lt_word N t hN htN (j := 2 * t + 1) (le_refl _)
    rw [hEW]
    omega
  have hcsW : cnt + sel < 2 ^ E.W := by omega
  have hAx : decParBase N t + x < decOutBase N t := by
    have h3 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by simp only [decOutBase]
    have h4 : decParBase N t + x < decParBase N t + 2 ^ (cr23Lb N + 1) :=
      Nat.add_lt_add_left hxl _
    omega
  have hxmem' : st.mem (decMstBase N t + j) = x := by
    rw [hbelow _ hmstjPar, hx]
    exact hmstm j hj
  have hparx : st.mem (decParBase N t + x) = sel := by
    rw [hsel]
    exact hpar x hxl
  -- chunk A
  set st1 : RAMState := runBlock decEmitBA E st with hst1
  have hBA := decEmitBA_spec E st (decMstBase N t) (decParBase N t) j x sel h8 h9 h0 h11
    hW hlenW hxmem' hxW hparxW hparx hsel1
  have hA0 : st1.regs r0 = j := by
    rw [hst1]; exact (decEmitBA_frame E st r0 (by decide) (by decide) (by decide)).trans h0
  have hA1 : st1.regs r1 = cnt := by
    rw [hst1]; exact (decEmitBA_frame E st r1 (by decide) (by decide) (by decide)).trans h1
  have hA3 : st1.regs r3 = x := hBA.1
  have hA4 : st1.regs r4 = sel := hBA.2.1
  have hA6 : st1.regs r6 = 1 := by
    rw [hst1]; exact (decEmitBA_frame E st r6 (by decide) (by decide) (by decide)).trans h6
  have hA10 : st1.regs r10 = decOutBase N t := by
    rw [hst1]; exact (decEmitBA_frame E st r10 (by decide) (by decide) (by decide)).trans h10
  have hAmem : st1.mem = Function.update st.mem (decParBase N t + x) 0 := hBA.2.2
  -- chunk B
  have hBB := decEmitBB_spec E st1 (decOutBase N t) cnt x sel j hA10 hA1 hA3 hA4 hA6 hA0 houtcW
    hcsW hjW
  have hB0 : (runBlock decEmitBody E st).regs r0 = j + 1 := by
    rw [decEmitBody_split, runBlock_append, ← hst1]; exact hBB.2.1
  have hB1 : (runBlock decEmitBody E st).regs r1 = cnt + sel := by
    rw [decEmitBody_split, runBlock_append, ← hst1]; exact hBB.2.2
  have hBmem : (runBlock decEmitBody E st).mem
      = Function.update (Function.update st.mem (decParBase N t + x) 0)
          (decOutBase N t + cnt) x := by
    rw [decEmitBody_split, runBlock_append, ← hst1, hBB.1, hAmem]
  have hrest : ∀ d : Fin 16, d ≠ r5 → d ≠ r3 → d ≠ r4 → d ≠ r0 → d ≠ r1 →
      (runBlock decEmitBody E st).regs d = st.regs d := by
    intro d h5 h3 h4 h0' h1'
    rw [decEmitBody_split, runBlock_append, ← hst1]
    exact (decEmitBB_frame E (runBlock decEmitBA E st) d h5 h0' h1').trans
      (decEmitBA_frame E st d h5 h3 h4)
  refine ⟨hB0, hB1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrest r2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2
  · rw [hrest r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
  · rw [hrest r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
  · rw [hrest r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
  · rw [hrest r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · rw [hrest r11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · omega
  · -- the output words
    intro k hk
    rcases lt_or_eq_of_le (by omega : k ≤ cnt) with hkc | hkc
    · rw [hBmem, dec_upd2_ne
        (dec_ne_of_lt' (lt_of_lt_of_le hAx (dec_le_add_r _ _)))
        (dec_ne_add_l (ne_of_lt hkc)), decEmitApp_getD P lacc x (by omega)]
      exact hout k hkc
    · subst hkc
      have hpos : x ∈ P \ lacc.toFinset := by
        rw [← decEmitSel_one, ← hsel]
        omega
      rw [hBmem, dec_upd2_snd, decEmitApp_pos P lacc hpos, ← hlen]
      exact (dec_getD_append_add lacc [x] (k := 0) (by simp)).symm
  · -- `Nodup`
    exact decEmitApp_nodup P lacc x hnd
  · -- the length
    rw [decEmitApp_length P lacc x, hlen, hsel]
  · -- emitted values lie in `P`
    exact decEmitApp_sub P lacc x hsubP
  · -- every `P`-entry of the master list up to `j+1` is emitted
    exact decEmitApp_seen P lacc mst j x hx hseen
  · -- the parity bitmap
    intro w hw
    by_cases hwx : w = x
    · subst hwx
      rw [hBmem, dec_upd2_fst (dec_ne_of_lt' (lt_of_lt_of_le hAx (dec_le_add_r _ _)))]
      by_cases hsel : x ∈ P \ lacc.toFinset
      · rw [if_neg (decEmitApp_self P lacc hsel)]
      · rw [if_neg (decEmitApp_self_neg P lacc hsel)]
    · have hAw : decParBase N t + w < decOutBase N t := by
        have h3 : decParBase N t + 2 ^ (cr23Lb N + 1) = decOutBase N t := by
          simp only [decOutBase]
        have h4 : decParBase N t + w < decParBase N t + 2 ^ (cr23Lb N + 1) :=
          Nat.add_lt_add_left hw _
        omega
      rw [hBmem, dec_upd2_ne (dec_ne_add_l hwx)
        (dec_ne_of_lt (lt_of_lt_of_le hAw (dec_le_add_r _ _))), hpar w hw]
      by_cases hwP : w ∈ P \ lacc.toFinset
      · rw [if_pos hwP, if_pos ((decEmitApp_sdiff P lacc hwx).mpr hwP)]
      · rw [if_neg hwP, if_neg (fun hh => hwP ((decEmitApp_sdiff P lacc hwx).mp hh))]
  · -- the frame below the parity bitmap
    intro a ha
    rw [hBmem, dec_upd2_ne
      (dec_ne_of_lt (lt_of_lt_of_le ha (dec_le_add_r _ _)))
      (dec_ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le ha hparOut) (dec_le_add_r _ _)))]
    exact hbelow a ha
/-- **One iteration of the emit pass**: the test, the `jz`, the 9-instruction body and the `jmp`. -/
theorem decEmit_bodyIter (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (j cnt : ℕ) (lacc : List ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAtBody : At Pgm (a + (Cond.lt r13 r0 r2).code.length + 1) decEmitBody)
    (hjmpAt : Pgm[(a + (Cond.lt r13 r0 r2).code.length + 1) + decEmitBody.length]? =
      some (iJmp a))
    (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r13 r0 r2).code.length + 1)
    (hR : DecEmitInv N t P mst j cnt lacc mb st) (hj : j < mst.length) :
    Sem Pgm E (a + (Cond.lt r13 r0 r2).code.length + 1) a
      { st with pc := a + (Cond.lt r13 r0 r2).code.length + 1 }
      (fun k s' => k = decEmitBody.length + 1 ∧
        DecEmitInv N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
          (decEmitApp P lacc (mst.getD j 0)) mb s' ∧ s'.pc = a) := by
  set b : ℕ := a + (Cond.lt r13 r0 r2).code.length + 1 with hb
  have hblk : Sem Pgm E b (b + decEmitBody.length) { st with pc := b }
      (fun k s' => k = decEmitBody.length ∧ s' = runBlock decEmitBody E { st with pc := b }) :=
    Sem.block Pgm E b decEmitBody { st with pc := b } hAtBody decEmitBody_noBranch rfl
  have hpcB : (runBlock decEmitBody E { st with pc := b }).pc = b + decEmitBody.length := by
    rw [runBlock_pc decEmitBody E _ decEmitBody_noBranch]
  have hjmpSem : Sem Pgm E (b + decEmitBody.length) a
      (runBlock decEmitBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock decEmitBody E { st with pc := b } with pc := a }) :=
    Sem.exec Pgm E (b + decEmitBody.length) a _ (iJmp a) hjmpAt hpcB rfl
  refine Sem.mono (Sem.trans hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨rfl, DecEmitInv_pc N t P mst (j + 1) (cnt + decEmitSel P lacc (mst.getD j 0))
    (decEmitApp P lacc (mst.getD j 0)) mb a _
    (decEmitBody_data N t hN htN E hEW P mst j cnt lacc mb { st with pc := b } hj hcap hmstN
      hmstm hR), rfl⟩
/-- **The emit loop**: `mst.length` iterations, then the failing test. -/
theorem decEmit_loop (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) a))
    (hcap : mst.length ≤ 2 * t + 1) (hmstN : ∀ v ∈ mst, v < N)
    (hmstm : ∀ i, i < mst.length → mb (decMstBase N t + i) = mst.getD i 0)
    (st : RAMState) (hpc : st.pc = a) (hR : DecEmitInv N t P mst 0 0 [] mb st) :
    Sem Pgm E a (a + (Cond.lt r13 r0 r2).code.length + (Stmt.code decEmitBody).len + 2) st
      (fun k s' => k ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc mb s') ∧
        s'.pc = a + (Cond.lt r13 r0 r2).code.length + (Stmt.code decEmitBody).len + 2) := by
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have htrans : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → ∀ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s →
        DecEmitInv N t P mst j cnt lacc mb s' := by
    rintro j s s' hd hm' cnt lacc h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hd r0 (by decide)]; exact a1
    · rw [← hd r1 (by decide)]; exact a2
    · rw [← hd r2 (by decide)]; exact a3
    · rw [← hd r6 (by decide)]; exact a4
    · rw [← hd r8 (by decide)]; exact a5
    · rw [← hd r9 (by decide)]; exact a6
    · rw [← hd r10 (by decide)]; exact a7
    · rw [← hd r11 (by decide)]; exact a8
    · exact a9
    · intro k hk; rw [← hm']; exact a10 k hk
    · exact a11
    · exact a12
    · exact a13
    · exact a14
    · intro v hv; rw [← hm']; exact a15 v hv
    · intro b hb; rw [← hm']; exact a16 b hb
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → (∃ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s) →
        (∃ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s') := by
    rintro j s s' hd hm' ⟨cnt, lacc, h⟩
    exact ⟨cnt, lacc, htrans j s s' hd hm' cnt lacc h⟩
  have hgo : ∀ j, j < mst.length → ∀ s, (∃ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s) →
      (Cond.lt r13 r0 r2).eval s := by
    rintro j hj s ⟨cnt, lacc, h⟩
    obtain ⟨h0, -, h2, -⟩ := h
    show s.regs r0 < s.regs r2
    rw [h0, h2]; exact hj
  have hstop : ∀ s, (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc mb s) →
      ¬ (Cond.lt r13 r0 r2).eval s := by
    rintro s ⟨cnt, lacc, h⟩
    obtain ⟨h0, -, h2, -⟩ := h
    show ¬ (s.regs r0 < s.regs r2)
    rw [h0, h2]; omega
  have hstep : ∀ j, j < mst.length → ∀ s, s.pc = a →
      (∃ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s) →
      Sem Pgm E (a + (Cond.lt r13 r0 r2).code.length + 1) a
        { runBlock (Cond.lt r13 r0 r2).code E s with
          pc := a + (Cond.lt r13 r0 r2).code.length + 1 }
        (fun k s' => k ≤ decEmitBody.length + 1 ∧
          (∃ cnt lacc, DecEmitInv N t P mst (j + 1) cnt lacc mb s') ∧ s'.pc = a) := by
    rintro j hj s hpc' ⟨cnt, lacc, hRs⟩
    obtain ⟨-, hjz, hbody, hjmp⟩ := at_loop hAt
    have hlen : (Stmt.code decEmitBody).len = decEmitBody.length := rfl
    have hbody' : At Pgm (a + (Cond.lt r13 r0 r2).code.length + 1) decEmitBody := hbody
    have hjmpAt : Pgm[(a + (Cond.lt r13 r0 r2).code.length + 1) + decEmitBody.length]? =
        some (iJmp a) := by
      rw [← hlen]
      exact hjmp
    have hR' : DecEmitInv N t P mst j cnt lacc mb
        { runBlock (Cond.lt r13 r0 r2).code E s with
          pc := a + (Cond.lt r13 r0 r2).code.length + 1 } :=
      htrans j (runBlock (Cond.lt r13 r0 r2).code E s) s
        (fun d hd => runBlock_cond_regs (Cond.lt r13 r0 r2) E s d hd)
        (runBlock_cond_mem (Cond.lt r13 r0 r2) E s) cnt lacc hRs
    refine Sem.mono (decEmit_bodyIter N t hN htN E hEW P mst j cnt lacc mb Pgm a hbody' hjmpAt
      hcap hmstN hmstm { runBlock (Cond.lt r13 r0 r2).code E s with
        pc := a + (Cond.lt r13 r0 r2).code.length + 1 } rfl hR' hj) ?_
    intro k s' hk
    exact ⟨le_of_eq hk.1, ⟨_, _, hk.2.1⟩, hk.2.2⟩
  have hloop := Sem.loopPredLe Pgm E a (Cond.lt r13 r0 r2) (Stmt.code decEmitBody) hAt hW
    mst.length (fun j s => ∃ cnt lacc, DecEmitInv N t P mst j cnt lacc mb s)
    (fun _ => decEmitBody.length + 1) hirr hgo hstop hstep st hpc ⟨0, [], hR⟩
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1, h.2.2⟩)
  obtain ⟨h1, h2, h3⟩ := h
  have hsum : (∑ j ∈ Finset.range mst.length,
        ((Cond.lt r13 r0 r2).code.length + 1 + (decEmitBody.length + 1)))
      = 12 * mst.length := by
    simp [Finset.sum_const, Finset.card_range, Cond.code, decEmitBody_len, Nat.mul_comm]
  rw [hsum] at h1
  have hcl : (Cond.lt r13 r0 r2).code.length = 1 := rfl
  rw [hcl] at h1
  omega
/-- The loop's final invariant, read as the output-list facts. -/
theorem decEmit_final (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ) (st : RAMState)
    (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h : ∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc mb st) :
    ∃ lacc : List ℕ, lacc.Nodup ∧ st.regs r1 = lacc.length ∧
      (∀ k, k < lacc.length → st.mem (decOutBase N t + k) = lacc.getD k 0) ∧
      lacc.toFinset = P := by
  obtain ⟨cnt, lacc, hI⟩ := h
  have hcopy := hI
  obtain ⟨-, h1, -, -, -, -, -, -, -, hout, hnd, hlen, -, -, -, -⟩ := hI
  exact ⟨lacc, hnd, by rw [h1, hlen], by rw [hlen]; exact hout,
    DecEmitInv_set N t P mst cnt lacc mb st hsub hcopy⟩
/-- **Output plumbing** (from `_wram_lib.lean.txt` §6, renamed so that the round loop can cite it
without a name clash): the word count in register 1 and the words at the address in register 0 spell
a duplicate-free list of exactly the support of `x`. -/
theorem decOutputsSupport_of_mem {n : ℕ} (s : RAMState) (x : Fin n → ZMod 2) (base L : ℕ)
    (l : List ℕ) (hbase : s.regs 0 = base) (hlen : s.regs 1 = L) (hlen' : l.length = L)
    (hmem : ∀ k, k < L → s.mem (base + k) = l.getD k 0)
    (hnd : l.Nodup) (hls : ∀ v : ℕ, v ∈ l ↔ ∃ i : Fin n, i.val = v ∧ x i = 1) :
    OutputsSupport s x := by
  have hout : outList s = l := by
    unfold outList
    rw [hlen, hbase]
    apply List.ext_getElem
    · simp [hlen']
    · intro k h1 h2
      have hk : k < L := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [hmem k hk]
      exact List.getD_eq_getElem l 0 (by omega)
  refine ⟨?_, ?_⟩
  · rw [hout]
    exact hnd
  · intro v
    rw [hout]
    exact hls v
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
/-- **Support is additive**: `supp (x + y) = supp x Δ supp y`, spelled as `cr23_shrink` spells it. -/
theorem cr23Supp_add {N : ℕ} (x y : Fin N → ZMod 2) :
    cr23Supp (x + y) = (cr23Supp x \ cr23Supp y) ∪ (cr23Supp y \ cr23Supp x) := by
  ext v
  simp only [cr23Supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_sdiff, Pi.add_apply]
  rcases cr23_zmod2_cases (x v) with hx | hx <;> rcases cr23_zmod2_cases (y v) with hy | hy <;>
    rw [hx, hy] <;> decide
/-- `l` read as a subset of `[N]`: the numbers it names that are coordinates.  This is the type the
support lives in, so it is the type the one-hot sum's support has to be compared in. -/
def cr23LstSet (N : ℕ) (l : List ℕ) : Finset (Fin N) :=
  univ.filter (fun v => v.val ∈ l)
theorem cr23LstSet_mem (N : ℕ) (l : List ℕ) (v : Fin N) :
    v ∈ cr23LstSet N l ↔ v.val ∈ l := by
  simp only [cr23LstSet, Finset.mem_filter, Finset.mem_univ, true_and]
/-- **The support of a sum of one-hots**: if `f` is injective on `s`, the one-hot sum over `s` has
support the range of `f` on `s` — no cancellation can happen, and every hit coordinate carries a
single `1`.  This is the general form; the round loop instantiates it at `s = range l.length`,
`f = decLstFin N l` (see `cr23Supp_decLstVec`). -/
theorem cr23Supp_sum_single {N : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Fin N)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j) :
    cr23Supp (∑ i ∈ s, (Pi.single (f i) (1 : ZMod 2) : Fin N → ZMod 2)) = s.image f := by
  classical
  ext v
  simp only [cr23Supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_apply]
  have hterm : ∀ i ∈ s,
      (Pi.single (f i) (1 : ZMod 2) : Fin N → ZMod 2) v
        = (if f i = v then (1 : ZMod 2) else 0) := by
    intro i _
    by_cases h : f i = v
    · have h2 : v = f i := h.symm
      rw [Pi.single_apply, if_pos h2, if_pos h]
    · have h2 : ¬ (v = f i) := fun hh => h hh.symm
      rw [Pi.single_apply, if_neg h2, if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, cr23_zmod2_eq_one_iff]
  have hcard : (s.filter (fun i => f i = v)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  have hodd : Odd (s.filter (fun i => f i = v)).card ↔
      (s.filter (fun i => f i = v)).card = 1 := by
    constructor
    · rintro ⟨c, hc⟩
      omega
    · intro h
      rw [h]
      exact odd_one
  rw [hodd]
  constructor
  · intro h
    rw [Finset.card_eq_one] at h
    obtain ⟨a, ha⟩ := h
    have ha' : a ∈ s.filter (fun i => f i = v) := by rw [ha]; simp
    obtain ⟨has, hav⟩ := Finset.mem_filter.mp ha'
    exact Finset.mem_image.mpr ⟨a, has, hav⟩
  · intro hv
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_filter.mpr ⟨ha, hav⟩, ?_⟩
    intro b hb
    obtain ⟨hbs, hbv⟩ := Finset.mem_filter.mp hb
    exact hinj b hbs a ha (hbv.trans hav.symm)
/-- Two indices below `l.length` that `getD` cannot tell apart are equal — the list is duplicate-free,
so its entries are too. -/
theorem dec_getD_inj {l : List ℕ} (h : l.Nodup) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : l.getD i 0 = l.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at hij
  exact (List.Nodup.getElem_inj_iff h).mp hij
/-- The coordinate a list index names, as a *total* function: an index whose entry is not a
coordinate is mapped to `0` (its one-hot is `0` anyway, so `decLstVec` never sees it). -/
def decLstFin (N : ℕ) (hN : 1 ≤ N) (l : List ℕ) : ℕ → Fin N :=
  fun k => if h : l.getD k 0 < N then ⟨l.getD k 0, h⟩ else ⟨0, hN⟩
theorem decLstFin_of_lt (N : ℕ) (hN : 1 ≤ N) (l : List ℕ) {k : ℕ} (h : l.getD k 0 < N) :
    decLstFin N hN l k = ⟨l.getD k 0, h⟩ := by
  simp only [decLstFin, dif_pos h]
/-- **The hidden vector one round adds**: the sum of the one-hots of the entries `0, …, i-1` of the
candidate list.  Its definition is deliberately the mirror image of `decLstDelta` — the same
`range`/`getD`/`dif` shape — so that `cr23Sketch_decLstVec` below is the statement that the machine's
payload update is this vector's sketch. -/
def decLstVec (N : ℕ) (l : List ℕ) (i : ℕ) : Fin N → ZMod 2 :=
  ∑ k ∈ Finset.range i,
    (if h : l.getD k 0 < N then Pi.single (⟨l.getD k 0, h⟩ : Fin N) (1 : ZMod 2) else 0)
theorem decLstVec_eq_sum_fin (N : ℕ) (hN : 1 ≤ N) (l : List ℕ) (hlt : ∀ v ∈ l, v < N)
    {i : ℕ} (hi : i ≤ l.length) :
    decLstVec N l i
      = ∑ k ∈ Finset.range i, (Pi.single (decLstFin N hN l k) (1 : ZMod 2) : Fin N → ZMod 2) := by
  simp only [decLstVec]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < l.length := by
    have := Finset.mem_range.mp hk
    omega
  have h : l.getD k 0 < N := hlt _ (dec_getD_mem hk')
  rw [dif_pos h, decLstFin_of_lt N hN l h]
/-- **The support of the round's vector is the candidate list's entry set.**  This is item 1
specialised to the `range`/`getD` shape the decoder actually uses. -/
theorem cr23Supp_decLstVec (N : ℕ) (hN : 1 ≤ N) (l : List ℕ) (hnd : l.Nodup)
    (hlt : ∀ v ∈ l, v < N) :
    cr23Supp (decLstVec N l l.length) = cr23LstSet N l := by
  rw [decLstVec_eq_sum_fin N hN l hlt (le_refl _)]
  have hinj : ∀ i ∈ Finset.range l.length, ∀ j ∈ Finset.range l.length,
      decLstFin N hN l i = decLstFin N hN l j → i = j := by
    intro i hi j hj hij
    have hi' : i < l.length := Finset.mem_range.mp hi
    have hj' : j < l.length := Finset.mem_range.mp hj
    have h1 : l.getD i 0 < N := hlt _ (dec_getD_mem hi')
    have h2 : l.getD j 0 < N := hlt _ (dec_getD_mem hj')
    have e1 : decLstFin N hN l i = (⟨l.getD i 0, h1⟩ : Fin N) := decLstFin_of_lt N hN l h1
    have e2 : decLstFin N hN l j = (⟨l.getD j 0, h2⟩ : Fin N) := decLstFin_of_lt N hN l h2
    rw [e1, e2] at hij
    exact dec_getD_inj hnd hi' hj' (congrArg Fin.val hij)
  rw [cr23Supp_sum_single (Finset.range l.length) (decLstFin N hN l) hinj]
  ext v
  rw [cr23LstSet_mem, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < l.length := Finset.mem_range.mp hk
    have h : l.getD k 0 < N := hlt _ (dec_getD_mem hk')
    rw [decLstFin_of_lt N hN l h]
    exact dec_getD_mem hk'
  · intro hv
    obtain ⟨k, hk, hget⟩ := dec_mem_getD hv
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    have h : l.getD k 0 < N := hlt _ (dec_getD_mem hk)
    refine Fin.ext ?_
    rw [decLstFin_of_lt N hN l h]
    exact hget
/-- **The payload of the round is the sketch of `decLstVec`**: `cr23Delta_full` at every level,
pushed through the linearity of `cr23Sketch`.  Together with `decXor_delta_step` this says that the
machine's `y + decLstDelta l i` is `cr23Sketch (z + decLstVec l i)` whenever `cr23Sketch z = y`. -/
theorem cr23Sketch_decLstVec (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (l : List ℕ) (i : ℕ) :
    cr23Sketch N t C (decLstVec N l i) = decLstDelta N t C l i := by
  unfold decLstVec decLstDelta
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : l.getD k 0 < N
  · rw [dif_pos h, dif_pos h, cr23Delta_full]
  · rw [dif_neg h, dif_neg h, map_zero]
/-- **The machine's candidate set is the list's entry set.**  Body (b)'s exit invariant
(`DecCandInv`) stores the candidate as the *numbers* in `l`; `cr23Cand` is the same set read as
coordinates.  This is the bridge that lets the support identity below be stated against
`cr23Cand`, i.e. in exactly the form `cr23_shrink` consumes. -/
theorem cr23Cand_eq_lstSet {N t : ℕ} (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (S : Finset (Fin N)) (s : Fin (cr23D N)) (l : List ℕ)
    (hl : l.toFinset
      = ((cr23OddB C S s).image (fun b => cr23XorLbl C S s b)).filter (fun v => v < N)) :
    cr23Cand C S s = cr23LstSet N l := by
  ext v
  simp only [cr23Cand, cr23LstSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← List.mem_toFinset, hl, Finset.mem_filter]
  exact ⟨fun h => ⟨h, v.isLt⟩, fun h => h.1⟩
/-- **One round of the loop, closed.**  Given the hidden vector `z` (whose sketch is the payload the
round started from) and the candidate list `l` that body (b) produced from `z`'s sketch:

* the new hidden vector `z + decLstVec l l.length` has payload `cr23Sketch z + decLstDelta l
  l.length` — exactly what body (c) leaves (`decXorStmt_spec`), so `y` can be replaced by it;
* its support is `supp z Δ cr23Cand C (supp z) s` — exactly the set `cr23_shrink` certifies shrinks
  fourfold (for the seed it returns).

Both conclusions are stated with `cr23Supp z` in place of `S`, so `cr23_shrink`'s hypothesis
`(cr23Supp z).card ≤ t` is the only side condition of the level step. -/
theorem cr23_round_residual (N t : ℕ) (hN : 1 ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (l : List ℕ) (hnd : l.Nodup) (hlt : ∀ v ∈ l, v < N) (s : Fin (cr23D N))
    (hl : l.toFinset
      = ((cr23OddB C (cr23Supp z) s).image (fun b => cr23XorLbl C (cr23Supp z) s b)).filter
          (fun v => v < N)) :
    cr23Sketch N t C (z + decLstVec N l l.length)
        = cr23Sketch N t C z + decLstDelta N t C l l.length ∧
      cr23Supp (z + decLstVec N l l.length)
        = (cr23Supp z \ cr23Cand C (cr23Supp z) s) ∪
            (cr23Cand C (cr23Supp z) s \ cr23Supp z) := by
  constructor
  · rw [map_add, cr23Sketch_decLstVec]
  · rw [cr23Supp_add, cr23Supp_decLstVec N hN l hnd hlt,
      ← cr23Cand_eq_lstSet C (cr23Supp z) s l hl]
/-- A vector of empty support is the zero vector. -/
theorem cr23Supp_eq_zero_of_supp_eq_empty {N : ℕ} {x : Fin N → ZMod 2}
    (h : cr23Supp x = ∅) : x = 0 := by
  funext v
  by_contra hv
  have h1 : x v = 1 := by
    rcases cr23_zmod2_cases (x v) with h0 | h1
    · exact absurd h0 hv
    · exact h1
  have hmem : v ∈ cr23Supp x := Finset.mem_filter.mpr ⟨Finset.mem_univ v, h1⟩
  rw [h] at hmem
  exact absurd hmem (by simp)
/-- The number set of a set of coordinates: what body (d)'s parity bitmap stores. -/
def cr23NumSet {N : ℕ} (S : Finset (Fin N)) : Finset ℕ := S.image Fin.val
theorem cr23NumSet_mem {N : ℕ} (S : Finset (Fin N)) (v : ℕ) :
    v ∈ cr23NumSet S ↔ ∃ i ∈ S, i.val = v := by
  simp only [cr23NumSet, Finset.mem_image]
theorem cr23NumSet_lt {N : ℕ} (S : Finset (Fin N)) {v : ℕ} (h : v ∈ cr23NumSet S) : v < N := by
  obtain ⟨i, -, rfl⟩ := (cr23NumSet_mem S v).mp h
  exact i.isLt
/-- Below `N` a number names exactly one coordinate, so `cr23NumSet` is injective there: the lemma
that makes every set operation commute with it. -/
theorem cr23NumSet_mem_iff {N : ℕ} (S : Finset (Fin N)) {v : ℕ} (hv : v < N) :
    v ∈ cr23NumSet S ↔ (⟨v, hv⟩ : Fin N) ∈ S := by
  rw [cr23NumSet_mem]
  constructor
  · rintro ⟨i, hi, hiv⟩
    have h : i = ⟨v, hv⟩ := Fin.ext hiv
    rwa [h] at hi
  · intro h
    exact ⟨⟨v, hv⟩, h, rfl⟩
/-- **`cr23NumSet` commutes with the symmetric difference**, in `decSymm`'s spelling (which is
body (d)'s). -/
theorem cr23NumSet_symm {N : ℕ} (A B : Finset (Fin N)) :
    cr23NumSet ((A \ B) ∪ (B \ A)) = decSymm (cr23NumSet A) (cr23NumSet B) := by
  ext v
  by_cases hv : v < N
  · have hm : ∀ S : Finset (Fin N), v ∈ cr23NumSet S ↔ (⟨v, hv⟩ : Fin N) ∈ S :=
      fun S => cr23NumSet_mem_iff S hv
    rw [cr23NumSet_mem_iff _ hv]
    simp only [decSymm, Finset.mem_union, Finset.mem_sdiff, hm] <;> tauto
  · have h1 : v ∉ cr23NumSet ((A \ B) ∪ (B \ A)) := fun h => absurd (cr23NumSet_lt _ h) hv
    have h2 : v ∉ decSymm (cr23NumSet A) (cr23NumSet B) := by
      intro h
      rw [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at h
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd (cr23NumSet_lt _ h) hv
      · exact absurd (cr23NumSet_lt _ h) hv
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
/-- A candidate list, read as numbers, is its `toFinset` (all its entries are coordinates). -/
theorem cr23NumSet_lstSet {N : ℕ} (l : List ℕ) (hlt : ∀ v ∈ l, v < N) :
    cr23NumSet (cr23LstSet N l) = l.toFinset := by
  ext v
  rw [cr23NumSet_mem, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rwa [cr23LstSet_mem] at hi
  · intro hv
    refine ⟨⟨v, hlt v hv⟩, ?_, rfl⟩
    rw [cr23LstSet_mem]
    exact hv
/-- **`cr23NumSet (cr23Supp w)` is `w`'s support as a set of numbers** — exactly the shape of
`decEmit_outputsSupport`'s hypothesis. -/
theorem cr23NumSet_supp_mem {N : ℕ} (w : Fin N → ZMod 2) (v : ℕ) :
    v ∈ cr23NumSet (cr23Supp w) ↔ ∃ i : Fin N, i.val = v ∧ w i = 1 := by
  rw [cr23NumSet_mem]
  constructor
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, hiv, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hiv, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, hiv⟩
/-- **Empty support iff the zero vector.**  This is the direction the round loop needs at its exit:
`cr23Supp z K = ∅` *is* `z K = 0`. -/
theorem cr23Supp_eq_empty_iff {N : ℕ} (z : Fin N → ZMod 2) : cr23Supp z = ∅ ↔ z = 0 := by
  constructor
  · exact cr23Supp_eq_zero_of_supp_eq_empty
  · rintro rfl
    simp [cr23Supp]
/-- `ZMod 2`-vectors are of exponent two. -/
theorem cr23_add_self_eq_zero {N : ℕ} (w : Fin N → ZMod 2) : w + w = 0 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by
    intro a
    rcases cr23_zmod2_cases a with h | h
    · rw [h, zero_add]
    · rw [h]
      decide
  funext i
  exact h (w i)
/-- **One round preserves the parity invariant.**  If the parity set is the support of the error
`x + z`, and the round adds `decLstVec N l l.length` (item 2), then toggling the candidate list's
entry set into `P` — exactly the master-list append body (d) performs — gives the support of the new
error `x + (z + vec)`. -/
theorem cr23Parity_step {N : ℕ} (hN : 1 ≤ N) (x z : Fin N → ZMod 2) (l : List ℕ) (P : Finset ℕ)
    (hnd : l.Nodup) (hlt : ∀ v ∈ l, v < N)
    (hP : P = cr23NumSet (cr23Supp (x + z))) :
    decSymm P l.toFinset
      = cr23NumSet (cr23Supp (x + (z + decLstVec N l l.length))) := by
  have hassoc : x + (z + decLstVec N l l.length) = (x + z) + decLstVec N l l.length := by
    rw [add_assoc]
  rw [hassoc, cr23Supp_add (x + z) (decLstVec N l l.length),
    cr23Supp_decLstVec N hN l hnd hlt, cr23NumSet_symm, cr23NumSet_lstSet l hlt, hP]
/-- **The round loop's exit condition**: if the parity set is the support of the error `x + z K` and
the final residual has empty support, then the parity set *is* the support of `x` — exactly the
hypothesis `decEmit_outputsSupport` needs, as a `∀ v` clause. -/
theorem decRounds_final_support {N : ℕ} (x zK : Fin N → ZMod 2) (P : Finset ℕ)
    (hP : P = cr23NumSet (cr23Supp (x + zK))) (hK : cr23Supp zK = ∅) :
    ∀ v : ℕ, v ∈ P ↔ ∃ i : Fin N, i.val = v ∧ x i = 1 := by
  have hz : zK = 0 := (cr23Supp_eq_empty_iff zK).mp hK
  intro v
  rw [hP, hz, add_zero]
  exact cr23NumSet_supp_mem x v
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
theorem decAdvance_len : decAdvance.length = 17 := by decide
theorem decLoadW_len : decLoadW.length = 3 := by decide
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
/-- **Body (a), end to end, at an arbitrary address**: `decScanStmt_spec` is stated at address `0`
because it was the first body to be built; the round loop needs it at `a`. -/
theorem decScanStmt_spec_at (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (w : ℕ)
    (m₀ : ℕ → ℕ) (P : Program) (a : ℕ) (hAt : At P a (Stmt.compile decScanStmt a))
    (st : RAMState) (hpc : st.pc = a)
    (hm : st.mem = m₀) (h9 : st.regs r9 = w) (h14 : st.regs r14 = cr23DecFrame N t)
    (hD : m₀ (decSlot N t 0) = cr23D N) (hM : m₀ (decSlot N t 2) = cr23M t)
    (hL : m₀ (decSlot N t 3) = cr23Lb N + 1) (hlb : m₀ (decSlot N t 4) = cr23Lb N)
    (hmem : ∀ b, b < wordsOf (cr23Word N) (cr23R N t) →
      m₀ b = packMem (cr23Word N) (cr23Sketch N t C z) b) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      ((a + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decScanBody).len + 2) st
      (fun k s' => k ≤ (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) ∧
        DecScanInv N t C z w (cr23D N * cr23M t) m₀ s' ∧
        s'.pc = ((a + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
          + (Stmt.code decScanBody).len + 2)) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hcs : decScanStmt
      = Stmt.seq (Stmt.code decScanInit) (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decScanBody)) :=
    rfl
  have hAt' : At P a (decScanInit
      ++ Stmt.compile (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decScanBody))
        (a + (Stmt.code decScanInit).len)) := by
    rw [hcs] at hAt
    simpa only [Stmt.compile, Stmt.len] using hAt
  obtain ⟨hAtInit, hAtLoop⟩ := At.append.mp hAt'
  have hinit : Sem P E a (a + decScanInit.length) st
      (fun k s' => k = decScanInit.length ∧ s' = runBlock decScanInit E st) :=
    Sem.block P E a decScanInit st hAtInit decScanInit_noBranch hpc
  have hpc21 : (runBlock decScanInit E st).pc = a + decScanInit.length := by
    rw [runBlock_pc decScanInit E st decScanInit_noBranch, hpc]
  refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' => k1 = (Stmt.code decScanInit).len ∧
    (k2 ≤ 2 + 30 * (cr23D N * cr23M t) ∧
      DecScanInv N t C z w (cr23D N * cr23M t) m₀ s' ∧
      s'.pc = (a + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decScanBody).len + 2)) hinit ?_) ?_
  · intro k1 s1 h1
    obtain ⟨rfl, rfl⟩ := h1
    have hR0 : DecScanInv N t C z w 0 m₀ (runBlock decScanInit E st) :=
      decScanInit_data N t hN htN C z w m₀ st hm h9 h14 (by rw [hm]; exact hD)
        (by rw [hm]; exact hM) (by rw [hm]; exact hL) (by rw [hm]; exact hlb)
    refine Sem.mono (decScan_loop N t hN ht htN C z w m₀ P _ hAtLoop hmem _
      (by rw [hpc21]) hR0) ?_
    intro k s' hk
    exact ⟨rfl, hk⟩
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3, h4⟩ := h
    exact ⟨by omega, h3, h4⟩
/-- **Body (a)'s result at an arbitrary counter value `w`**: `decScan_result` is stated at `w = 0`
(it only reads the argmax clauses of the invariant), which the round loop cannot supply. -/
theorem decScan_result' (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2) (w : ℕ) (m₀ : ℕ → ℕ)
    (s' : RAMState) (h : DecScanInv N t C z w (cr23D N * cr23M t) m₀ s') :
    (∀ s : Fin (cr23D N), (cr23OddB C (cr23Supp z) s).card ≤ s'.regs r3) ∧
      ∃ s : Fin (cr23D N), s'.regs r4 = s.val ∧
        (cr23OddB C (cr23Supp z) s).card = s'.regs r3 := by
  obtain ⟨-, -, -, -, h3, h4, -, -, -, -, -, -, -, -, -⟩ := h
  obtain ⟨hA, ⟨s, hs, hB⟩⟩ := decScan_correct N t hN ht htN C z
  refine ⟨fun u => ?_, ⟨s, ?_, ?_⟩⟩
  · rw [h3]; exact hA u
  · rw [h4]; exact hs
  · rw [h3]; exact hB
theorem cr23_shrink_argmax {N' t' : ℕ} {eps : ℝ}
    (C : Fin N' → Fin (cr23D N') → Fin (cr23M t'))
    (hexp : IsLayeredExpander C (2 * t') eps) (heps : 16 * eps ≤ 1)
    (S : Finset (Fin N')) (hS : S.card ≤ t') (hD : 0 < cr23D N')
    (s : Fin (cr23D N'))
    (hmax : ∀ s' : Fin (cr23D N'), (cr23OddB C S s').card ≤ (cr23OddB C S s).card) :
    4 * ((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card ≤ S.card := by
  classical
  have hDpos : (0 : ℝ) < (cr23D N' : ℝ) := by exact_mod_cast hD
  have hs0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  have hsum : (cr23D N' : ℝ) * ((1 - 2 * eps) * (S.card : ℝ))
      ≤ ∑ s : Fin (cr23D N'), ((cr23OddB C S s).card : ℝ) := by
    have hneigh : (1 - eps) * ((cr23D N' : ℝ) * (S.card : ℝ))
        ≤ ∑ s : Fin (cr23D N'), ((cr23Neigh C S s : ℕ) : ℝ) := hexp S (by omega)
    have h3 : ∀ s : Fin (cr23D N'),
        2 * ((cr23Neigh C S s : ℕ) : ℝ) - (S.card : ℝ) ≤ ((cr23Alone C S s : ℕ) : ℝ) := by
      intro s
      have h := cr23_alone_bound C S s
      have h' : 2 * ((cr23Neigh C S s : ℕ) : ℝ)
          ≤ (S.card : ℝ) + ((cr23Alone C S s : ℕ) : ℝ) := by
        exact_mod_cast h
      linarith only [h']
    have h4 : 2 * (∑ s : Fin (cr23D N'), ((cr23Neigh C S s : ℕ) : ℝ))
          - (cr23D N' : ℝ) * (S.card : ℝ)
        ≤ ∑ s : Fin (cr23D N'), ((cr23Alone C S s : ℕ) : ℝ) := by
      have heq : 2 * (∑ s : Fin (cr23D N'), ((cr23Neigh C S s : ℕ) : ℝ))
            - (cr23D N' : ℝ) * (S.card : ℝ)
          = ∑ s : Fin (cr23D N'),
              (2 * ((cr23Neigh C S s : ℕ) : ℝ) - (S.card : ℝ)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [heq]
      exact Finset.sum_le_sum (fun s _ => h3 s)
    have h5 : ∀ s : Fin (cr23D N'),
        ((cr23Alone C S s : ℕ) : ℝ) ≤ ((cr23OddB C S s).card : ℝ) := by
      intro s
      exact_mod_cast cr23Alone_le_odd C S s
    have h6 : (∑ s : Fin (cr23D N'), ((cr23Alone C S s : ℕ) : ℝ))
        ≤ ∑ s : Fin (cr23D N'), ((cr23OddB C S s).card : ℝ) :=
      Finset.sum_le_sum (fun s _ => h5 s)
    nlinarith only [hneigh, h4, h6]
  have hmax' : (1 - 2 * eps) * (S.card : ℝ) ≤ ((cr23OddB C S s).card : ℝ) := by
    have hsum2 : (∑ s' : Fin (cr23D N'), ((cr23OddB C S s').card : ℝ))
        ≤ (cr23D N' : ℝ) * ((cr23OddB C S s).card : ℝ) := by
      have hle : (∑ s' : Fin (cr23D N'), ((cr23OddB C S s').card : ℝ))
          ≤ ∑ _s' : Fin (cr23D N'), ((cr23OddB C S s).card : ℝ) := by
        refine Finset.sum_le_sum (fun s' _ => ?_)
        exact_mod_cast hmax s'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      exact hle
    exact le_of_mul_le_mul_left (by linarith only [hsum, hsum2]) hDpos
  have hA : (((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card : ℝ)
      + 2 * ((cr23Alone C S s : ℕ) : ℝ)
      ≤ (S.card : ℝ) + ((cr23OddB C S s).card : ℝ) := by
    have h := cr23Cand_diff_add C S s
    exact_mod_cast h
  have hB : 3 * ((cr23OddB C S s).card : ℝ)
      ≤ 2 * ((cr23Alone C S s : ℕ) : ℝ) + (S.card : ℝ) := by
    have h := cr23_alone_odd C S s
    exact_mod_cast h
  have hfin : (4 : ℝ) * (((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card : ℝ)
      ≤ (S.card : ℝ) := by
    nlinarith only [hA, hB, hmax', heps, hs0]
  have hcast : ((4 * ((S \ cr23Cand C S s) ∪ (cr23Cand C S s \ S)).card : ℕ) : ℝ)
      ≤ (S.card : ℝ) := by
    push_cast
    linarith only [hfin]
  exact_mod_cast hcast
/-- `DecData` with the parity bitmap read as the number set `P`. -/
def DecDataN (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w tag mstLen : ℕ) (P : Finset ℕ) (mst : List ℕ) (s : RAMState) : Prop :=
  s.mem (decSlot N t 0) = cr23D N ∧
  s.mem (decSlot N t 1) = N ∧
  s.mem (decSlot N t 2) = cr23M t ∧
  s.mem (decSlot N t 3) = cr23Lb N + 1 ∧
  s.mem (decSlot N t 4) = cr23Lb N ∧
  s.mem (decSlot N t 5) = 2 ^ (cr23Lb N + 1) ∧
  s.mem (decSlot N t 6) = t ∧
  s.mem (decSlot N t 7) = w ∧
  s.mem (decSlot N t 8) = tag ∧
  s.mem (decSlot N t 9) = decCandBase N t ∧
  s.mem (decSlot N t 10) = decTagBase N t ∧
  s.mem (decSlot N t 11) = decMstBase N t ∧
  s.mem (decSlot N t 12) = decParBase N t ∧
  s.mem (decSlot N t 13) = decOutBase N t ∧
  s.mem (decSlot N t 14) = mstLen ∧
  (∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C z) a) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → s.mem (decTagBase N t + v) < tag) ∧
  (∀ v, v < 2 ^ (cr23Lb N + 1) → (s.mem (decParBase N t + v) = 1 ↔ v ∈ P)) ∧
  (∀ i, i < mstLen → s.mem (decMstBase N t + i) = mst.getD i 0)
/-- **`DecDataN` at a round head, with `mstLen = mst.length` and `P ⊆ mst`** — the shape the round
loop carries.  Bundling the side conditions the emit pass needs keeps the loop invariant small. -/
def DecHead (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState) : Prop :=
  DecDataN N t C z w tag mst.length P mst st ∧
  st.regs r14 = cr23DecFrame N t ∧
  P = cr23NumSet (cr23Supp (x + z)) ∧
  (∀ v, v ∈ P → v ∈ mst) ∧
  mst.length + 2 * w ≤ 2 * t + 1 ∧
  (cr23Supp z).card ≤ w
/-- A `DecCandInv`'s candidate list has at most `w` entries whenever the residual's support does. -/
theorem decCandLen_le_w (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState)
    (hR : DecCandInv N t C x s tag b len l st) :
    len ≤ (cr23Supp x).card := by
  obtain ⟨-, -, -, hnodup, hlen, -, -, -, hset⟩ := hR
  have hsub : l.toFinset ⊆
      ((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
        (fun v => v < N) := by
    intro v hv
    rw [hset] at hv
    exact hv
  have h1 : l.toFinset.card ≤
      (((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
        (fun v => v < N)).card := Finset.card_le_card hsub
  have h2 : (((cr23OddB C (cr23Supp x) s).image (fun b => cr23XorLbl C (cr23Supp x) s b)).filter
      (fun v => v < N)).card ≤ (cr23OddB C (cr23Supp x) s).card :=
    le_trans (Finset.card_filter_le _ _) Finset.card_image_le
  have h3 : (cr23OddB C (cr23Supp x) s).card ≤ (cr23Supp x).card :=
    cr23OddB_card_le C (cr23Supp x) s
  have h4 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  omega
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
/-- Body (c) writes only inside the packed payload. -/
def DecXorFrame (N t : ℕ) (st s : RAMState) : Prop :=
  ∀ b, wordsOf (cr23Word N) (cr23R N t) ≤ b → s.mem b = st.mem b
/-- **One iteration of body (c)'s outer loop, with the frame.** -/
theorem decXor_bodyIter_fr (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2)
    (l : List ℕ) (len j : ℕ) (P : Program) (a : ℕ)
    (hAtBody : At P (a + (Cond.lt r8 r1 r2).code.length + 1)
      (Stmt.compile decXorBody (a + (Cond.lt r8 r1 r2).code.length + 1)))
    (hjmpAt : P[a + (Cond.lt r8 r1 r2).code.length + 1 + decXorBody.len]? = some (iJmp a))
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r8 r1 r2).code.length + 1)
    (hR : DecXorInv N t C y l len j st) (hj : j < len) (hlen : len ≤ 2 * t + 1) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C))
      (a + (Cond.lt r8 r1 r2).code.length + 1) a
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }
      (fun k s' => k ≤ cr23D N * 10 + 22 ∧ DecXorInv N t C y l len (j + 1) s' ∧
        DecXorFrame N t st s' ∧ s'.pc = a) := by
  obtain ⟨h1, h2, h14, hsl0, hsl1, hlst, hlt, hpay⟩ := hR
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hW1 : 1 < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23_one_lt_word N hN
  have hv : l.getD j 0 < N := hlt j hj
  set v : Fin N := ⟨l.getD j 0, hv⟩ with hvdef
  have hvval : v.val = l.getD j 0 := rfl
  have hvN : v.val < N := v.isLt
  have hDW : cr23D N < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23D_lt_word N hN
  have hfrW : cr23DecFrame N t + 1 < 2 ^ E.W := by
    simp only [hE, detEnv]; exact cr23_frame_add_lt_word N t hN htN (c := 1) (by norm_num)
  have hvW : v.val + 1 < 2 ^ E.W := by
    have hNw : N < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23N_lt_word N hN
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hvN) hNw
  have hBv : upBase N v.val < 2 ^ E.W := by simp only [hE, detEnv]; exact upBase_lt N hN v
  have hB1v : upBase N v.val + 1 < 2 ^ E.W := by
    have h := upBase_end_lt N hN v
    have hD : 0 < cr23D N := cr23D_pos N hN
    simp only [hE, detEnv] at h ⊢
    omega
  have h2W : 2 < 2 ^ E.W := by
    have h32 := cr23_32_lt_word N
    simp only [hE, detEnv] at h32 ⊢
    omega
  have hE2v : upBase N v.val + 2 * cr23D N < 2 ^ E.W := by
    simp only [hE, detEnv]; exact upBase_end_lt N hN v
  have h32 : 32 < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23_32_lt_word N
  have hvalW : l.getD j 0 < 2 ^ E.W := by
    have hNw : N < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23N_lt_word N hN
    exact lt_of_lt_of_le hv (le_of_lt hNw)
  have hjW : j + 1 < 2 ^ E.W := by
    have hend : cr23DecEnd N t < 2 ^ E.W := by
      simp only [hE, detEnv]; exact cr23DecEnd_lt_word N t hN htN
    have hle1 : j + 1 ≤ 2 * t + 1 := by omega
    exact lt_of_le_of_lt (le_trans hle1 (cr23DecEnd_ge_two N t)) hend
  have hframeW : cr23DecFrame N t + 32 + j < 2 ^ E.W := by
    have hend : cr23DecEnd N t < 2 ^ E.W := by
      simp only [hE, detEnv]; exact cr23DecEnd_lt_word N t hN htN
    exact lt_of_lt_of_le (cr23DecEnd_ge_cand N t j (lt_of_lt_of_le hj hlen)) (le_of_lt hend)
  obtain ⟨hAtLoad, hAtPre, hAtInner, hAtPost⟩ := decXorBody_at hAtBody
  have hnoL : NoBranch decXorLoad := by simp [decXorLoad, decXorL1, decXorL2]
  have hnoP : NoBranch decXorPre := by simp [decXorPre]
  have hnoQ : NoBranch decXorPost := by simp [decXorPost]
  have hload : Sem P E (a + (Cond.lt r8 r1 r2).code.length + 1)
      (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length)
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }
      (fun k s' => k = decXorLoad.length ∧
        s' = runBlock decXorLoad E { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }) :=
    Sem.block P E (a + (Cond.lt r8 r1 r2).code.length + 1) decXorLoad _
      hAtLoad hnoL rfl
  have hpre : Sem P E (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length)
      (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length)
      (runBlock decXorLoad E { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })
      (fun k s' => k = decXorPre.length ∧
        s' = runBlock decXorPre E
          (runBlock decXorLoad E { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })) :=
    Sem.block P E _ decXorPre _ hAtPre hnoP (by rw [runBlock_pc decXorLoad E _ hnoL])
  have hLP : Sem P E (a + (Cond.lt r8 r1 r2).code.length + 1)
      (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length)
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }
      (fun k s' => k = decXorLoad.length + decXorPre.length ∧
        s' = runBlock decXorPre E
          (runBlock decXorLoad E { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })) :=
    Sem.trans hload hpre
  have hld := decXorLoad_data E { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }
    N t j l h1 h14 (hlst j hj) h32 hframeW hvalW
  have hT0 : (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }).regs r0 = v.val := hld.1
  have hTmem : (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }).mem = st.mem := hld.2
  have hT14 : (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }).regs r14 = cr23DecFrame N t := by
    rw [decXorLoad_frame E _ r14 (by decide)]
    exact h14
  have hTD : (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }).mem (decSlot N t 0) = cr23D N := by
    rw [hTmem]; exact hsl0
  have hTpay : ∀ addr, addr < wordsOf (cr23Word N) (cr23R N t) →
      (runBlock decXorLoad E
        { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }).mem addr
        = packMem (cr23Word N) (y + decLstDelta N t C l j) addr := by
    intro addr ha
    rw [hTmem]; exact hpay addr ha
  have hbase : E.det (v.val + 1) = upBase N v.val := by
    simp only [hE, detEnv]
    rw [Nat.add_comm]
    exact cr23DecDet_base N t C hN v
  obtain ⟨hUp, hPreMem, hPre0, hPre1, hPre2, hPre14⟩ :=
    decXorPre_data E (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }) N t C y l j v
      hT0 hT14 hTD hbase hTpay hW1 hDW hfrW hvW hBv hB1v h2W hE2v
  have hL1 : (runBlock decXorPre E (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })).regs r1 = j := by
    rw [hPre1, decXorLoad_frame E _ r1 (by decide)]
    exact h1
  have hL2 : (runBlock decXorPre E (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })).regs r2 = len := by
    rw [hPre2, decXorLoad_frame E _ r2 (by decide)]
    exact h2
  have hL14 : (runBlock decXorPre E (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })).regs r14 = cr23DecFrame N t := by
    rw [hPre14, decXorLoad_frame E _ r14 (by decide)]
    exact h14
  have hloopI := decXorLoop_frame N t hN htN C (y + decLstDelta N t C l j) v P
    (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length) hAtInner
    (runBlock decXorPre E (runBlock decXorLoad E
      { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }))
    (by rw [runBlock_pc decXorPre E _ hnoP, runBlock_pc decXorLoad E _ hnoL]) hUp
  have hejmp : a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
      + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2 + decXorPost.length
      = a + (Cond.lt r8 r1 r2).code.length + 1 + decXorBody.len := by
    have e1 : decXorLoad.length = 4 := decXorLoad_len
    have e2 : decXorPre.length = 14 := decXorPre_len
    have e3 : decXorPost.length = 2 := decXorPost_len
    have e4 : decXorBody.len = 30 := decXorBody_len
    have e5 : (Cond.neqz r6).code.length = 0 := rfl
    have e6 : (Stmt.code progUpBody).len = 8 := by decide
    have e7 : (Cond.lt r8 r1 r2).code.length = 1 := rfl
    rw [e1, e2, e3, e4, e5, e6, e7]
  have hTail : Sem P E
      (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length) a
      (runBlock decXorPre E (runBlock decXorLoad E
        { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }))
      (fun k s' => k ≤ (cr23D N * 10 + 1) + (decXorPost.length + 1) ∧
        DecXorInv N t C y l len (j + 1) s' ∧ DecXorFrame N t st s' ∧ s'.pc = a) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k s' => k ≤ cr23D N * 10 + 1 ∧
        DecXorPay.UpData N t C (y + decLstDelta N t C l j) v 0 s' ∧
        DecXorSame N t (runBlock decXorPre E (runBlock decXorLoad E
          { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 })) s' ∧
        s'.pc = a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
          + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2)
      (Q₂ := fun k₂ k₃ s' => k₂ ≤ cr23D N * 10 + 1 ∧ k₃ ≤ decXorPost.length + 1 ∧
        DecXorInv N t C y l len (j + 1) s' ∧ DecXorFrame N t st s' ∧ s'.pc = a) hloopI ?_) ?_
    · intro k₂ s₂ h₂
      obtain ⟨hk₂, hU0, hSame2, hpc₂⟩ := h₂
      have hpost : Sem P E
          (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
            + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2)
          (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
            + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2 + decXorPost.length)
          s₂ (fun k s' => k = decXorPost.length ∧ s' = runBlock decXorPost E s₂) :=
        Sem.block P E _ decXorPost s₂ hAtPost hnoQ hpc₂
      have hje : P[a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
          + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2 + decXorPost.length]?
          = some (iJmp a) := by
        rw [hejmp]; exact hjmpAt
      have hpcT : (runBlock decXorPost E s₂).pc
          = a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
            + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2 + decXorPost.length := by
        rw [runBlock_pc decXorPost E s₂ hnoQ, hpc₂]
      have hjmp : Sem P E
          (a + (Cond.lt r8 r1 r2).code.length + 1 + decXorLoad.length + decXorPre.length
            + (Cond.neqz r6).code.length + (Stmt.code progUpBody).len + 2 + decXorPost.length) a
          (runBlock decXorPost E s₂)
          (fun k s' => k = 1 ∧ s' = { runBlock decXorPost E s₂ with pc := a }) :=
        Sem.exec P E _ a _ (iJmp a) hje hpcT rfl
      refine Sem.mono (Sem.trans hpost hjmp) ?_
      intro k₃ s₃ h₃
      obtain ⟨rfl, rfl⟩ := h₃
      have hpost_spec := decXorPost_spec E s₂ j (by rw [hSame2.1, hL1]) hW1 hjW
      obtain ⟨hpr1, hprMem, hpr2, hpr14⟩ := hpost_spec
      have hbig : ∀ d : ℕ, cr23DecFrame N t ≤ d → wordsOf (cr23Word N) (cr23R N t) ≤ d :=
        fun d hd => le_trans (cr23_wordsOf_le_frame N t hN) hd
      have hsr1 : ({ runBlock decXorPost E s₂ with pc := a } : RAMState).regs r1 = j + 1 := by
        show (runBlock decXorPost E s₂).regs r1 = j + 1
        exact hpr1
      have hsr2 : ({ runBlock decXorPost E s₂ with pc := a } : RAMState).regs r2 = len := by
        show (runBlock decXorPost E s₂).regs r2 = len
        rw [hpr2, hSame2.2.1, hL2]
      have hsr14 : ({ runBlock decXorPost E s₂ with pc := a } : RAMState).regs r14
          = cr23DecFrame N t := by
        show (runBlock decXorPost E s₂).regs r14 = cr23DecFrame N t
        rw [hpr14, hSame2.2.2.1, hL14]
      have hsm0 : ({ runBlock decXorPost E s₂ with pc := a } : RAMState).mem
          (decSlot N t 0) = cr23D N := by
        show s₂.mem (decSlot N t 0) = cr23D N
        rw [hSame2.2.2.2 _ (hbig _ (by simp only [decSlot]; omega)), hPreMem, hld.2]
        exact hsl0
      have hsm1 : ({ runBlock decXorPost E s₂ with pc := a } : RAMState).mem
          (decSlot N t 1) = N := by
        show s₂.mem (decSlot N t 1) = N
        rw [hSame2.2.2.2 _ (hbig _ (by simp only [decSlot]; omega)), hPreMem, hld.2]
        exact hsl1
      refine ⟨hk₂, le_rfl, ?_, ?_, rfl⟩
      · refine ⟨hsr1, hsr2, hsr14, hsm0, hsm1, ?_, hlt, ?_⟩
        · intro k hk
          show s₂.mem (decCandBase N t + k) = l.getD k 0
          rw [hSame2.2.2.2 _ (hbig _ (by simp only [decCandBase]; omega)), hPreMem, hld.2]
          exact hlst k hk
        · intro addr ha
          show s₂.mem addr = packMem (cr23Word N) (y + decLstDelta N t C l (j + 1)) addr
          rw [DecXorPay.body_result N t C (y + decLstDelta N t C l j) v s₂ hU0 addr ha]
          rw [decXor_delta_step N t C y l j v hvval]
      · intro b hb
        show s₂.mem b = st.mem b
        rw [hSame2.2.2.2 b hb, hPreMem, hld.2]
    · intro k s' h
      obtain ⟨k₂, k₃, hk, hb1, hb2, hInv, hfr, hpc⟩ := h
      exact ⟨by omega, hInv, hfr, hpc⟩
  refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = decXorLoad.length + decXorPre.length ∧
      s' = runBlock decXorPre E (runBlock decXorLoad E
        { st with pc := a + (Cond.lt r8 r1 r2).code.length + 1 }))
    (Q₂ := fun k₁ k₂ s' => k₁ = decXorLoad.length + decXorPre.length ∧
      k₂ ≤ (cr23D N * 10 + 1) + (decXorPost.length + 1) ∧
      DecXorInv N t C y l len (j + 1) s' ∧ DecXorFrame N t st s' ∧ s'.pc = a) hLP ?_) ?_
  · intro k₁ s₁ h₁
    obtain ⟨hk₁, rfl⟩ := h₁
    exact Sem.mono hTail (fun k s' h => ⟨hk₁, h.1, h.2.1, h.2.2⟩)
  · intro k s' h
    obtain ⟨k₁, k₂, hk, h18, hb, hInv, hfr, hpc⟩ := h
    have h18' : decXorLoad.length + decXorPre.length = 18 := by
      rw [decXorLoad_len, decXorPre_len]
    have hpl : decXorPost.length = 2 := decXorPost_len
    exact ⟨by omega, hInv, hfr, hpc⟩
/-- **Body (c), end to end, with the frame.** -/
theorem decXorStmt_specF (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (y : Fin (cr23R N t) → ZMod 2)
    (l : List ℕ) (len : ℕ) (P : Program) (a : ℕ) (hAt : At P a (Stmt.compile decXorStmt a))
    (st : RAMState) (hpc : st.pc = a) (hR : DecXorInv N t C y l len 0 st)
    (hlen : len ≤ 2 * t + 1) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2) st
      (fun k s' => k ≤ 2 + len * (cr23D N * 10 + 24) ∧ DecXorInv N t C y l len len s' ∧
        DecXorFrame N t st s' ∧
        s'.pc = a + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2) := by
  rw [decXorStmt_eq] at hAt
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hW : 1 < 2 ^ E.W := by simp only [hE, detEnv]; exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r8 → s.regs d = s'.regs d) →
      s.mem = s'.mem → (DecXorInv N t C y l len j s ∧ DecXorFrame N t st s) →
      (DecXorInv N t C y l len j s' ∧ DecXorFrame N t st s') := by
    intro j s s' hd hm h
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := h.1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, k7, ?_⟩, ?_⟩
    · rw [← hd r1 (by decide)]; exact k1
    · rw [← hd r2 (by decide)]; exact k2
    · rw [← hd r14 (by decide)]; exact k3
    · rw [← hm]; exact k4
    · rw [← hm]; exact k5
    · intro i hi; rw [← hm]; exact k6 i hi
    · intro addr ha; rw [← hm]; exact k8 addr ha
    · intro b hb; rw [← hm]; exact h.2 b hb
  have hgo : ∀ j, j < len → ∀ s, (DecXorInv N t C y l len j s ∧ DecXorFrame N t st s) →
      (Cond.lt r8 r1 r2).eval s := by
    intro j hj s h
    show s.regs r1 < s.regs r2
    rw [h.1.1, h.1.2.1]
    exact hj
  have hstop : ∀ s, (DecXorInv N t C y l len len s ∧ DecXorFrame N t st s) →
      ¬ (Cond.lt r8 r1 r2).eval s := by
    intro s h
    show ¬ (s.regs r1 < s.regs r2)
    rw [h.1.1, h.1.2.1]
    omega
  have hstep : ∀ j, j < len → ∀ s, s.pc = a →
      (DecXorInv N t C y l len j s ∧ DecXorFrame N t st s) →
      Sem P E (a + (Cond.lt r8 r1 r2).code.length + 1) a
        { runBlock (Cond.lt r8 r1 r2).code E s with
          pc := a + (Cond.lt r8 r1 r2).code.length + 1 }
        (fun k s' => k ≤ cr23D N * 10 + 22 ∧
          (DecXorInv N t C y l len (j + 1) s' ∧ DecXorFrame N t st s') ∧ s'.pc = a) := by
    intro j hj s hpc' hRj
    obtain ⟨hInv, hFr⟩ := hRj
    obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hAt
    have hFr' : DecXorFrame N t st
        { runBlock (Cond.lt r8 r1 r2).code E s with
          pc := a + (Cond.lt r8 r1 r2).code.length + 1 } := by
      intro b hb
      show (runBlock (Cond.lt r8 r1 r2).code E s).mem b = st.mem b
      rw [runBlock_cond_mem]
      exact hFr b hb
    have hInv' : DecXorInv N t C y l len j
        { runBlock (Cond.lt r8 r1 r2).code E s with
          pc := a + (Cond.lt r8 r1 r2).code.length + 1 } :=
      hirr j _ s (fun d hd => runBlock_cond_regs (Cond.lt r8 r1 r2) E s d hd)
        (runBlock_cond_mem (Cond.lt r8 r1 r2) E s) ⟨hInv, hFr⟩ |>.1
    refine Sem.mono (decXor_bodyIter_fr N t hN htN C y l len j P a hbodyAt hjmp
      { runBlock (Cond.lt r8 r1 r2).code E s with
        pc := a + (Cond.lt r8 r1 r2).code.length + 1 } rfl hInv' hj hlen) ?_
    intro k s' h
    obtain ⟨hk, hInv2, hfr, hpc2⟩ := h
    exact ⟨hk, ⟨hInv2, fun b hb => (hfr b hb).trans (hFr' b hb)⟩, hpc2⟩
  have hloop := Sem.loopPredLe P E a (Cond.lt r8 r1 r2) decXorBody hAt hW len
    (fun j s => DecXorInv N t C y l len j s ∧ DecXorFrame N t st s) (fun _ => cr23D N * 10 + 22)
    hirr hgo hstop hstep st hpc ⟨hR, fun b _ => rfl⟩
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1.1, h.2.1.2, h.2.2⟩)
  obtain ⟨hk, -, -⟩ := h
  have hterm : ∀ j ∈ Finset.range len,
      ((Cond.lt r8 r1 r2).code.length + 1 + (cr23D N * 10 + 22)) = (cr23D N * 10 + 24) := by
    intro j hj
    have hcl : (Cond.lt r8 r1 r2).code.length = 1 := rfl
    rw [hcl]
    omega
  have hsum : (∑ j ∈ Finset.range len, (cr23D N * 10 + 24)) = len * (cr23D N * 10 + 24) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hcl : (Cond.lt r8 r1 r2).code.length = 1 := rfl
  rw [Finset.sum_congr rfl hterm, hsum, hcl] at hk
  exact hk
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
/-- **The write set of body (b)'s body.**  Every store of the 36-instruction candidate body is at
`decCandBase + len` (chunk `BE`) or at `decTagBase + lbl` (chunk `BH`); both lie in
`[decCandBase, decMstBase)`.  Hence the memory below `decCandBase` (the frame slots, in particular
`slot 0`, `slot 11`, `slot 12`, `slot 14`) and at or above `decMstBase` (the master list, the parity
bitmap and the output area) is exactly what it was at the loop head. -/
theorem decCandBody_frame (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag b len : ℕ) (l : List ℕ) (st : RAMState)
    (jj : Fin (cr23M t)) (hsup : (cr23Supp x).card ≤ t) (htagW : tag < 2 ^ cr23Word N)
    (hjb : jj.val = b) (hbM : b < cr23M t)
    (hR : DecCandInvP N t C x s tag b len l st)
    {a : ℕ} (ha : a < decCandBase N t ∨ decMstBase N t ≤ a) :
    (runBlock decCandBody (detEnv (cr23Word N) (cr23DecDet N t C)) st).mem a = st.mem a := by
  have hR0 := hR
  obtain ⟨hq0, hq2, hq3, hq4, hq7, hq8, hq10, hq11, hq12, hq14, hlist, hnodup, hlen, hentries,
    htagarr, htagbound, hset, hpay, hslot1, hslot9, hslot10⟩ := hR
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hW0 : 0 < 2 ^ E.W := by omega
  have hDMw : cr23D N * cr23M t < 2 ^ E.W := by rw [hEW]; exact cr23DM_lt_word N t hN htN
  have hNw : N < 2 ^ E.W := by rw [hEW]; exact cr23N_lt_word N hN
  have h2lbw : 2 ^ cr23Lb N < 2 ^ E.W := by
    rw [hEW]
    calc 2 ^ cr23Lb N ≤ 2 ^ (2 * cr23Lb N + 20) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ cr23Word N := cr23_pow_lt_word N hN
  have hF11 : cr23DecFrame N t + 11 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 11) (by norm_num)
  have hfrW : cr23DecFrame N t < 2 ^ E.W := by
    rw [hEW]; simpa using cr23_frame_add_lt_word N t hN htN (c := 0) (by norm_num)
  have h1024 : 1024 ≤ 2 ^ E.W := by
    rw [hEW]
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ cr23Word N := le_of_lt (cr23_pow_lt_word N hN)
  have hMs : cr23M t * s.val < 2 ^ E.W := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (le_of_lt s.isLt)) ?_
    rw [Nat.mul_comm (cr23M t) (cr23D N)]
    exact hDMw
  have hqDM : cr23M t * s.val + b < cr23D N * cr23M t := by
    have h1 : cr23M t * s.val + b < cr23M t * (s.val + 1) := by
      rw [show cr23M t * (s.val + 1) = cr23M t * s.val + cr23M t from by ring]
      exact Nat.add_lt_add_left hbM _
    have h3 : cr23M t * (s.val + 1) ≤ cr23D N * cr23M t := by
      calc cr23M t * (s.val + 1) ≤ cr23M t * cr23D N := Nat.mul_le_mul_left _ (by omega)
        _ = cr23D N * cr23M t := Nat.mul_comm _ _
    omega
  have hqW : cr23M t * s.val + b < 2 ^ E.W := lt_trans hqDM hDMw
  have hqw : (cr23M t * s.val + b) / 1024 < 2 ^ E.W :=
    lt_of_lt_of_le (decScanWordLt N t hN hqDM)
      (le_trans (cr23_wordsOf_le_frame N t hN) (le_of_lt hfrW))
  have hoff : (cr23M t * s.val + b) % 1024 * (cr23Lb N + 1) < 2 ^ E.W := by
    rw [hEW]
    apply cr23_lt_word N hN
    have h1 : (cr23M t * s.val + b) % 1024 ≤ 1023 := by
      have := Nat.mod_lt (cr23M t * s.val + b) (by norm_num : 0 < 1024)
      omega
    calc (cr23M t * s.val + b) % 1024 * (cr23Lb N + 1)
        ≤ 1023 * (cr23Lb N + 1) := Nat.mul_le_mul_right _ h1
      _ ≤ 1023 * (cr23Lb N + 1) + (cr23Lb N + 1) := by omega
      _ = 1024 * (cr23Lb N + 1) := by ring
      _ ≤ 1024 * 2 ^ (cr23Lb N + 1) :=
          Nat.mul_le_mul_left _ (le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ 10 * 2 ^ (cr23Lb N + 1) := by norm_num
      _ = 2 ^ (cr23Lb N + 11) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (2 * cr23Lb N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1W : b + 1 < 2 ^ E.W := by
    have h1 : b < cr23M t := hbM
    have h2 : cr23M t ≤ cr23D N * cr23M t := by
      calc cr23M t = 1 * cr23M t := (Nat.one_mul _).symm
        _ ≤ cr23D N * cr23M t := Nat.mul_le_mul_right _ (by have := cr23D_pos N hN; omega)
    omega
  have hlenle : len ≤ t := decCandLen_le N t hN ht C x hsup s tag b len l st hR0
  have hlenlt : len < 2 * t + 1 := by omega
  have hcbtb : decCandBase N t + len < decTagBase N t := decCand_cand_lt_tag N t len hlenlt
  have hclW : decCandBase N t + len < 2 ^ E.W := by
    rw [hEW]; exact decCand_candAddr_lt_word N t hN htN hlenlt
  have hcbW : decCandBase N t < 2 ^ E.W := by
    rw [hEW]; exact decCand_candAddr_lt_word N t hN htN (j := 0) (by omega)
  have htbW : decTagBase N t < 2 ^ E.W := by
    rw [hEW]; exact decCand_tagBase_lt_word N t hN htN
  have hlen1W : len + 1 < 2 ^ E.W := by
    have h1 : len + 1 ≤ 2 * t + 1 := by omega
    have h2 : 2 * t + 1 ≤ cr23D N * cr23M t := by
      have h3 : 2 * t + 1 ≤ cr23M t := by simp only [cr23M]; omega
      calc 2 * t + 1 ≤ cr23M t := h3
        _ = 1 * cr23M t := (Nat.one_mul _).symm
        _ ≤ cr23D N * cr23M t := Nat.mul_le_mul_right _ (by have := cr23D_pos N hN; omega)
    exact lt_of_le_of_lt (le_trans h1 h2) hDMw
  have hsl1 : st.mem (cr23DecFrame N t + 2) = N := by
    simpa only [decSlot] using hslot1
  have hsl9 : st.mem (cr23DecFrame N t + 10) = decCandBase N t := by
    simpa only [decSlot] using hslot9
  have hsl10 : st.mem (cr23DecFrame N t + 11) = decTagBase N t := by
    simpa only [decSlot] using hslot10
  have hcbLen : cr23DecFrame N t + 11 ≠ decCandBase N t + len := by
    have h := decSlot_lt_candBase N t (k := 10) (by norm_num)
    simp only [decSlot] at h
    omega
  have htagW' : tag < 2 ^ E.W := by rw [hEW]; exact htagW
  -- ### chunk A: q = M·s* + b, its payload word and q % 1024
  set st1 : RAMState := runBlock decCandBA E st with hst1
  have hA := decCandBA_spec E st (cr23M t) s.val b hq7 hq4 hq0 hq12 h1024 hMs hqW hqw
  have hA5 : st1.regs r5 = st.mem ((cr23M t * s.val + b) / 1024) % 2 ^ E.W := hA.1
  have hA6 : st1.regs r6 = (cr23M t * s.val + b) % 1024 := hA.2.1
  have hAmem : st1.mem = st.mem := hA.2.2.1
  have hAfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r5 → st1.regs d = st.regs d := hA.2.2.2
  have hkeep1 : ∀ d : Fin 16, d ≠ r5 → d ≠ r6 → st1.regs d = st.regs d := by
    intro d k5 k6
    exact hAfr d k6 k5
  have hword : st1.regs r5 < 2 ^ E.W := by rw [hA5]; exact Nat.mod_lt _ hW0
  -- ### chunk B: the field `word >>> off`, `2^lb` and `field / 2^lb`
  set st2 : RAMState := runBlock decCandBB E st1 with hst2
  have hoff' : st1.regs r6 * (cr23Lb N + 1) < 2 ^ E.W := by rw [hA6]; exact hoff
  have hB := decCandBB_spec E st1 (st1.regs r5) (st1.regs r6) (cr23Lb N + 1) (cr23Lb N)
    rfl rfl
    ((hkeep1 r8 (by decide) (by decide)).trans hq8)
    ((hkeep1 r11 (by decide) (by decide)).trans hq11)
    ((hkeep1 r10 (by decide) (by decide)).trans hq10)
    hword hoff' h2lbw
  have hB5 : st2.regs r5 = st1.regs r5 / 2 ^ (st1.regs r6 * (cr23Lb N + 1)) := hB.1
  have hB1 : st2.regs r1 = 2 ^ cr23Lb N := hB.2.1
  have hB15 : st2.regs r15
      = st1.regs r5 / 2 ^ (st1.regs r6 * (cr23Lb N + 1)) / 2 ^ cr23Lb N := hB.2.2.1
  have hBmem : st2.mem = st1.mem := hB.2.2.2.1
  have hBfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r5 → d ≠ r1 → d ≠ r15 →
      st2.regs d = st1.regs d := hB.2.2.2.2
  have hkeep2 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st2.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hBfr d k6 k5 k1 k15, hkeep1 d k5 k6]
  have hword2 : st2.regs r5 < 2 ^ E.W := by
    rw [hB5]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hword
  -- ### chunk C: par, lbl and N
  set st3 : RAMState := runBlock decCandBC E st2 with hst3
  have hNm2 : st2.mem (cr23DecFrame N t + 2) % 2 ^ E.W = N := by
    rw [hBmem, hAmem, hsl1, Nat.mod_eq_of_lt hNw]
  have hC := decCandBC_spec E st2 (st2.regs r15) (st2.regs r5) (cr23Lb N) (cr23DecFrame N t) N
    rfl rfl hB1
    ((hkeep2 r11 (by decide) (by decide) (by decide) (by decide)).trans hq11)
    ((hkeep2 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hword2 hF11 hNm2
  have hC15 : st3.regs r15 = st2.regs r15 % 2 := hC.1
  have hC5 : st3.regs r5 = st2.regs r5 % 2 ^ cr23Lb N := hC.2.1
  have hC6 : st3.regs r6 = N := hC.2.2.1
  have hCmem : st3.mem = st2.mem := hC.2.2.2.1
  have hCfr : ∀ d : Fin 16, d ≠ r15 → d ≠ r6 → d ≠ r5 → st3.regs d = st2.regs d :=
    hC.2.2.2.2
  have hkeep3 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st3.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hCfr d k15 k6 k5, hkeep2 d k1 k5 k6 k15]
  -- ### chunk D: sN = (lbl < N), ps = par·sN, the candidate base
  set st4 : RAMState := runBlock decCandBD E st3 with hst4
  have hCB2 : st3.mem (cr23DecFrame N t + 10) % 2 ^ E.W = decCandBase N t := by
    rw [hCmem, hBmem, hAmem, hsl9, Nat.mod_eq_of_lt hcbW]
  have hpar1 : st3.regs r15 ≤ 1 := by
    rw [hC15]
    have := Nat.mod_lt (st2.regs r15) (by norm_num : 0 < 2)
    omega
  have hD := decCandBD_spec E st3 (st2.regs r5 % 2 ^ cr23Lb N) N (st3.regs r15)
    (cr23DecFrame N t) (decCandBase N t)
    hC6 hC5 rfl
    ((hkeep3 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hpar1 hW hF11 hCB2
  have hD1 : st4.regs r1 = decCandBase N t := hD.2.2.1
  have hDmem : st4.mem = st3.mem := hD.2.2.2.1
  have hDfr : ∀ d : Fin 16, d ≠ r6 → d ≠ r15 → d ≠ r1 → st4.regs d = st3.regs d :=
    hD.2.2.2.2
  have hkeep4 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st4.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hDfr d k6 k15 k1, hkeep3 d k1 k5 k6 k15]
  -- ### chunk E: the unconditional candidate store and the tag base
  set st5 : RAMState := runBlock decCandBE E st4 with hst5
  have hneCand : cr23DecFrame N t + 11 ≠ decCandBase N t + len := hcbLen
  have hE5 := decCandBE_spec E st4 (decCandBase N t) len (st2.regs r5 % 2 ^ cr23Lb N)
    (cr23DecFrame N t) hD1
    ((hkeep4 r2 (by decide) (by decide) (by decide) (by decide)).trans hq2)
    ((hDfr r5 (by decide) (by decide) (by decide)).trans hC5)
    ((hkeep4 r14 (by decide) (by decide) (by decide) (by decide)).trans hq14)
    hclW hF11 hneCand
  have hE5r1 : st5.regs r1 = decTagBase N t := by
    rw [hE5.1, hDmem, hCmem, hBmem, hAmem, hsl10, Nat.mod_eq_of_lt htbW]
  have hE5mem : st5.mem = Function.update st4.mem (decCandBase N t + len)
      (st2.regs r5 % 2 ^ cr23Lb N) := hE5.2.1
  have hE5fr : ∀ d : Fin 16, d ≠ r1 → st5.regs d = st4.regs d := hE5.2.2
  have hkeep5 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r15 → st5.regs d = st.regs d := by
    intro d k1 k5 k6 k15
    rw [hE5fr d k1, hkeep4 d k1 k5 k6 k15]
  -- ### chunk F: the tag address, `old`, and the two comparison masks
  set st6 : RAMState := runBlock decCandBF E st5 with hst6
  have hneAddr : decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) ≠ decCandBase N t + len := by
    omega
  have hlbLb1 : st2.regs r5 % 2 ^ cr23Lb N < 2 ^ (cr23Lb N + 1) := by
    have h1 : st2.regs r5 % 2 ^ cr23Lb N < 2 ^ cr23Lb N := Nat.mod_lt _ (by positivity)
    calc st2.regs r5 % 2 ^ cr23Lb N < 2 ^ cr23Lb N := h1
      _ ≤ 2 ^ (cr23Lb N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htlW : decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) < 2 ^ E.W := by
    rw [hEW]; exact decCand_tagAddr_lt_word N t hN htN hlbLb1
  have holdW : st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) < 2 ^ E.W := by
    refine lt_of_le_of_lt (htagbound _ hlbLb1) htagW'
  have hold5 : st5.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) % 2 ^ E.W
      = st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) := by
    rw [hE5mem, Function.update_of_ne hneAddr, hDmem, hCmem, hBmem, hAmem,
      Nat.mod_eq_of_lt holdW]
  have hF := decCandBF_spec E st5 (decTagBase N t) (st2.regs r5 % 2 ^ cr23Lb N) tag
    (st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N))) hE5r1
    ((hE5fr r5 (by decide)).trans hC5)
    ((hkeep5 r3 (by decide) (by decide) (by decide) (by decide)).trans hq3)
    hW htlW hold5
  have hF1 : st6.regs r1 = decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) := hF.1
  have hF6 : st6.regs r6 = st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) := hF.2.1
  have hF5 : st6.regs r5
      = (if st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) < tag then 1 else 0)
        + (if tag < st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) then 1 else 0) :=
    hF.2.2.2.1
  have hFmem : st6.mem = st5.mem := hF.2.2.2.2.1
  have hFfr : ∀ d : Fin 16, d ≠ r1 → d ≠ r6 → d ≠ r13 → d ≠ r5 → st6.regs d = st5.regs d :=
    hF.2.2.2.2.2
  have hkeep6 : ∀ d : Fin 16, d ≠ r1 → d ≠ r5 → d ≠ r6 → d ≠ r13 → d ≠ r15 →
      st6.regs d = st.regs d := by
    intro d k1 k5 k6 k13 k15
    rw [hFfr d k1 k6 k13 k5, hkeep5 d k1 k5 k6 k15]
  -- ### chunk G: sel, len and the tag store value
  set st7 : RAMState := runBlock decCandBG E st6 with hst7
  have hps1 : st4.regs r15 ≤ 1 := by
    rw [hD.2.1]
    have h1 : (if st2.regs r5 % 2 ^ cr23Lb N < N then 1 else 0) ≤ 1 := by split_ifs <;> omega
    exact dec_mul_le_one hpar1 h1
  have hne1 : (if st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) < tag then 1 else 0)
      + (if tag < st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) then 1 else 0) ≤ 1 :=
    decCand_ind_add _ _
  have hlen2 : st6.regs r2 = len :=
    (hkeep6 r2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq2
  have hG := decCandBG_spec E st6 (st4.regs r15)
    ((if st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) < tag then 1 else 0)
      + (if tag < st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) then 1 else 0))
    len tag (st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)))
    ((hFfr r15 (by decide) (by decide) (by decide) (by decide)).trans
      (hE5fr r15 (by decide)))
    hF5 hlen2
    ((hkeep6 r3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq3)
    hF6 hps1 hne1 hlen1W
  have hG2 : st7.regs r2 = len + st4.regs r15
      * ((if st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) < tag then 1 else 0)
        + (if tag < st.mem (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) then 1 else 0)) :=
    hG.2.1
  have hGmem : st7.mem = st6.mem := hG.2.2.2.1
  have hGfr : ∀ d : Fin 16, d ≠ r15 → d ≠ r2 → d ≠ r5 → d ≠ r13 → d ≠ r6 →
      st7.regs d = st6.regs d := hG.2.2.2.2
  have hkeep7 : ∀ d : Fin 16, d ≠ r1 → d ≠ r2 → d ≠ r5 → d ≠ r6 → d ≠ r13 → d ≠ r15 →
      st7.regs d = st.regs d := by
    intro d k1 k2 k5 k6 k13 k15
    rw [hGfr d k15 k2 k5 k13 k6, hkeep6 d k1 k5 k6 k13 k15]
  -- ### chunk H: the tag store and the bucket counter
  set st8 : RAMState := runBlock decCandBH E st7 with hst8
  have hH := decCandBH_spec E st7 (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N))
    (st7.regs r6) b
    ((hGfr r1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hF1)
    rfl
    ((hkeep7 r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq0)
    ((hkeep7 r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hq11)
    hb1W
  have hHmem : st8.mem = Function.update st7.mem
      (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) (st7.regs r6) := hH.2.1
  -- ### the memory of the end state
  have hm8 : st8.mem = Function.update (Function.update st.mem (decCandBase N t + len)
      (st2.regs r5 % 2 ^ cr23Lb N))
      (decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N)) (st7.regs r6) := by
    rw [hHmem, hGmem, hFmem, hE5mem, hDmem, hCmem, hBmem, hAmem]
  have hout : ∀ a : ℕ, a ≠ decCandBase N t + len →
      a ≠ decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) → st8.mem a = st.mem a := by
    intro a h1 h2
    rw [hm8]
    exact decCand_mem_ne h2 h1
  have hbody : runBlock decCandBody E st = st8 := by
    rw [decCandBody_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3, ← hst4, ← hst5, ← hst6, ← hst7, ← hst8]
  rw [hbody]
  refine hout a ?_ ?_
  · rcases ha with h | h
    · omega
    · have h2 : decCandBase N t + len < decMstBase N t :=
        lt_of_lt_of_le hcbtb (decTagBase_le_mstBase N t)
      omega
  · rcases ha with h | h
    · have h2 : a < decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) := by
        have h3 := decCandBase_le_tagBase N t
        omega
      omega
    · have h2 : decTagBase N t + (st2.regs r5 % 2 ^ cr23Lb N) < decMstBase N t := by
        simp only [decMstBase]; omega
      omega
/-- **The memory contract between body (b) and the rest of the round**: the frame slots (below
`decCandBase`) and the master list / parity bitmap / output area (at or above `decMstBase`) are
exactly the round head's. -/
def DecCandFrame (N t : ℕ) (m₀ : ℕ → ℕ) (st : RAMState) : Prop :=
  ∀ b, b < decCandBase N t ∨ decMstBase N t ≤ b → st.mem b = m₀ b
/-- The candidate initialisation writes no memory at all. -/
theorem decCandInit_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decCandInit E st).mem = st.mem := by
  have hA : ∀ u : RAMState, (runBlock decCandIA E u).mem = u.mem := fun u => by simp [decCandIA]
  have hB : ∀ u : RAMState, (runBlock decCandIB E u).mem = u.mem := fun u => by simp [decCandIB]
  have hC : ∀ u : RAMState, (runBlock decCandIC E u).mem = u.mem := fun u => by simp [decCandIC]
  have hD : ∀ u : RAMState, (runBlock decCandID E u).mem = u.mem := fun u => by simp [decCandID]
  rw [decCandInit_split, runBlock_append, runBlock_append, runBlock_append, hD, hC, hB, hA]
/-- The candidate initialisation never writes `r14` or `r4` (it only loads into `r0`, `r2`, `r3`,
`r6`, `r7`, `r8`, `r10`, `r11`, `r12`). -/
theorem decCandInit_regs14 (E : RAMEnv) (st : RAMState) :
    (runBlock decCandInit E st).regs r14 = st.regs r14 := by
  simp [decCandInit, decCandIA, decCandIB, decCandIC, decCandID, runBlock_append]
theorem decCandInit_regs4 (E : RAMEnv) (st : RAMState) :
    (runBlock decCandInit E st).regs r4 = st.regs r4 := by
  simp [decCandInit, decCandIA, decCandIB, decCandIC, decCandID, runBlock_append]
/-- **The candidate scan, with the prefix invariant *and* the frame kept at the exit.**  The existing
`decCand_loop` throws `DecCandInvP` away (`decCandInvP_final` only keeps nine of its twenty-one
clauses), which loses the payload, the slot values and — through `decCandBody_frame` — the memory
outside the candidate/tag region.  The round loop needs all three. -/
theorem decCand_loopP (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag len : ℕ) (l : List ℕ) (m₀ : ℕ → ℕ)
    (hsup : (cr23Supp x).card ≤ t) (htagW : tag < 2 ^ cr23Word N)
    (P : Program) (a : ℕ)
    (hAt : At P a (Stmt.compile (Stmt.loop (Cond.lt r15 r0 r7) (Stmt.code decCandBody)) a))
    (st : RAMState) (hpc : st.pc = a) (hm : st.mem = m₀)
    (hR : DecCandInvP N t C x s tag 0 len l st) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + (Cond.lt r15 r0 r7).code.length + (Stmt.code decCandBody).len + 2) st
      (fun k s' => k ≤ 2 + 39 * cr23M t ∧
        (∃ len' l', DecCandInvP N t C x s tag (cr23M t) len' l' s' ∧
          DecCandFrame N t m₀ s') ∧
        s'.pc = a + (Cond.lt r15 r0 r7).code.length + (Stmt.code decCandBody).len + 2) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hW : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hF0 : DecCandFrame N t m₀ st := by
    intro b _
    rw [hm]
  have hirr : ∀ (j : ℕ) (st₁ st₂ : RAMState),
      (∀ d : Fin 16, d ≠ r15 → st₁.regs d = st₂.regs d) → st₁.mem = st₂.mem →
      (∃ len l, DecCandInvP N t C x s tag j len l st₁ ∧ DecCandFrame N t m₀ st₁) →
      (∃ len l, DecCandInvP N t C x s tag j len l st₂ ∧ DecCandFrame N t m₀ st₂) := by
    rintro j st₁ st₂ hd hm' ⟨len, l, h, hf⟩
    exact ⟨len, l, decCandInvP_irr N t C x s tag j len l st₁ st₂ hd hm' h,
      fun b hb => by rw [← hm']; exact hf b hb⟩
  have hgo : ∀ j, j < cr23M t →
      ∀ st₁, (∃ len l, DecCandInvP N t C x s tag j len l st₁ ∧ DecCandFrame N t m₀ st₁) →
      (Cond.lt r15 r0 r7).eval st₁ := by
    rintro j hj st₁ ⟨len, l, hP, -⟩
    have h0 : st₁.regs r0 = j := hP.1
    have h7 : st₁.regs r7 = cr23M t := hP.2.2.2.2.1
    show st₁.regs r0 < st₁.regs r7
    rw [h0, h7]; exact hj
  have hstop : ∀ st₁, (∃ len l, DecCandInvP N t C x s tag (cr23M t) len l st₁ ∧
      DecCandFrame N t m₀ st₁) → ¬ (Cond.lt r15 r0 r7).eval st₁ := by
    rintro st₁ ⟨len, l, hP, -⟩
    have h0 : st₁.regs r0 = cr23M t := hP.1
    have h7 : st₁.regs r7 = cr23M t := hP.2.2.2.2.1
    show ¬ (st₁.regs r0 < st₁.regs r7)
    rw [h0, h7]; omega
  have hstep : ∀ j, j < cr23M t → ∀ st₁, st₁.pc = a →
      (∃ len l, DecCandInvP N t C x s tag j len l st₁ ∧ DecCandFrame N t m₀ st₁) →
      Sem P E (a + (Cond.lt r15 r0 r7).code.length + 1) a
        { runBlock (Cond.lt r15 r0 r7).code E st₁ with
          pc := a + (Cond.lt r15 r0 r7).code.length + 1 }
        (fun k s' => k ≤ decCandBody.length + 1 ∧
          (∃ len l, DecCandInvP N t C x s tag (j + 1) len l s' ∧
            DecCandFrame N t m₀ s') ∧ s'.pc = a) := by
    rintro j hj st₁ hpc₁ ⟨len, l, hP, hF⟩
    obtain ⟨-, -, hbody, hjmp⟩ := at_loop hAt
    have hlen : (Stmt.code decCandBody).len = decCandBody.length := rfl
    have hjmpAt : P[(a + (Cond.lt r15 r0 r7).code.length + 1) + decCandBody.length]? =
        some (iJmp a) := by rw [← hlen]; exact hjmp
    have hP0 : DecCandInvP N t C x s tag j len l
        (runBlock (Cond.lt r15 r0 r7).code E st₁) :=
      decCandInvP_irr N t C x s tag j len l st₁
        (runBlock (Cond.lt r15 r0 r7).code E st₁)
        (fun d hd => (runBlock_cond_regs (Cond.lt r15 r0 r7) E st₁ d hd).symm)
        (runBlock_cond_mem (Cond.lt r15 r0 r7) E st₁).symm hP
    have hP' : DecCandInvP N t C x s tag j len l
        { runBlock (Cond.lt r15 r0 r7).code E st₁ with
          pc := a + (Cond.lt r15 r0 r7).code.length + 1 } :=
      DecCandInvP_pc N t C x s tag j len l _ _ hP0
    have hF' : DecCandFrame N t m₀
        { runBlock (Cond.lt r15 r0 r7).code E st₁ with
          pc := a + (Cond.lt r15 r0 r7).code.length + 1 } := by
      intro b hb
      rw [runBlock_cond_mem]
      exact hF b hb
    set st₂ : RAMState := { runBlock (Cond.lt r15 r0 r7).code E st₁ with
      pc := a + (Cond.lt r15 r0 r7).code.length + 1 } with hst₂
    have hblk : Sem P E (a + (Cond.lt r15 r0 r7).code.length + 1)
        (a + (Cond.lt r15 r0 r7).code.length + 1 + decCandBody.length) st₂
        (fun k s' => k = decCandBody.length ∧ s' = runBlock decCandBody E st₂) :=
      Sem.block P E _ decCandBody st₂ hbody decCandBody_noBranch rfl
    have hjmpSem : Sem P E (a + (Cond.lt r15 r0 r7).code.length + 1 + decCandBody.length) a
        (runBlock decCandBody E st₂)
        (fun k s' => k = 1 ∧ s' = { runBlock decCandBody E st₂ with pc := a }) :=
      Sem.exec P E _ a _ (iJmp a) hjmpAt
        (by rw [runBlock_pc decCandBody E st₂ decCandBody_noBranch]) rfl
    refine Sem.mono (Sem.trans hblk hjmpSem) ?_
    intro k s' hk
    obtain ⟨rfl, rfl⟩ := hk
    have hdata := decCandBody_data N t hN ht htN C x s tag j len l st₂ ⟨j, hj⟩ hsup htagW
      rfl hj hP'
    obtain ⟨len', l', hInv⟩ : ∃ len' l', DecCandInvP N t C x s tag (j + 1) len' l'
        (runBlock decCandBody E st₂) := ⟨_, _, hdata⟩
    refine ⟨by omega, ⟨len', l', ?_, ?_⟩, rfl⟩
    · exact DecCandInvP_pc N t C x s tag (j + 1) len' l' a _ hInv
    · intro b hb
      show (runBlock decCandBody E st₂).mem b = m₀ b
      exact (decCandBody_frame N t hN ht htN C x s tag j len l st₂ ⟨j, hj⟩ hsup htagW rfl hj
        hP' hb).trans (hF' b hb)
  have hloop := Sem.loopPredLe P E a (Cond.lt r15 r0 r7) (Stmt.code decCandBody) hAt hW
    (cr23M t)
    (fun j st₁ => ∃ len l, DecCandInvP N t C x s tag j len l st₁ ∧ DecCandFrame N t m₀ st₁)
    (fun _ => decCandBody.length + 1) hirr hgo hstop hstep st hpc ⟨len, l, hR, hF0⟩
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1, h.2.2⟩)
  · obtain ⟨h1, -, -⟩ := h
    have hsum : (∑ j ∈ Finset.range (cr23M t),
        ((Cond.lt r15 r0 r7).code.length + 1 + (decCandBody.length + 1)))
        = 39 * cr23M t := by
      simp [Finset.sum_const, Finset.card_range, Cond.code, decCandBody_len, Nat.mul_comm]
    have hcl : (Cond.lt r15 r0 r7).code.length = 1 := rfl
    rw [hsum] at h1
    rw [hcl] at h1
    omega
/-- **Body (b) end to end, with `DecCandInvP` and the frame at the exit.** -/
theorem decCandStmtP_spec (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag : ℕ) (m₀ : ℕ → ℕ) (P : Program) (a : ℕ)
    (hAt : At P a (Stmt.compile decCandStmtFull a)) (st : RAMState) (hpc : st.pc = a)
    (hm : st.mem = m₀) (h4 : st.regs r4 = s.val) (h14 : st.regs r14 = cr23DecFrame N t)
    (hMv : m₀ (decSlot N t 2) = cr23M t)
    (hLv : m₀ (decSlot N t 3) = cr23Lb N + 1)
    (hlb : m₀ (decSlot N t 4) = cr23Lb N)
    (htg : m₀ (decSlot N t 8) = tag)
    (hNv : m₀ (decSlot N t 1) = N)
    (hcb : m₀ (decSlot N t 9) = decCandBase N t)
    (htb : m₀ (decSlot N t 10) = decTagBase N t)
    (hsup : (cr23Supp x).card ≤ t) (htagW : tag < 2 ^ cr23Word N)
    (htaglt : ∀ v, v < 2 ^ (cr23Lb N + 1) → m₀ (decTagBase N t + v) < tag)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      m₀ a = packMem (cr23Word N) (cr23Sketch N t C x) a) :
    Sem P (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + (Stmt.code decCandInit).len + (Cond.lt r15 r0 r7).code.length
        + (Stmt.code decCandBody).len + 2) st
      (fun k s' => k ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) ∧
        (∃ len' l', DecCandInvP N t C x s tag (cr23M t) len' l' s' ∧
          DecCandFrame N t m₀ s') ∧
        s'.pc = a + (Stmt.code decCandInit).len + (Cond.lt r15 r0 r7).code.length
          + (Stmt.code decCandBody).len + 2) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hcs : decCandStmtFull
      = Stmt.seq (Stmt.code decCandInit) (Stmt.loop (Cond.lt r15 r0 r7) (Stmt.code decCandBody)) :=
    rfl
  have hAt' : At P a (decCandInit
      ++ Stmt.compile (Stmt.loop (Cond.lt r15 r0 r7) (Stmt.code decCandBody))
        (a + (Stmt.code decCandInit).len)) := by
    rw [hcs] at hAt
    simpa only [Stmt.compile, Stmt.len] using hAt
  obtain ⟨hAtInit, hAtLoop⟩ := At.append.mp hAt'
  have hinit : Sem P E a (a + decCandInit.length) st
      (fun k s' => k = decCandInit.length ∧ s' = runBlock decCandInit E st) :=
    Sem.block P E a decCandInit st hAtInit decCandInit_noBranch hpc
  have hpc16 : (runBlock decCandInit E st).pc = a + decCandInit.length := by
    rw [runBlock_pc decCandInit E st decCandInit_noBranch, hpc]
  have hminit : (runBlock decCandInit E st).mem = m₀ := by
    rw [decCandInit_mem]; exact hm
  have hfr14 : (runBlock decCandInit E st).regs r14 = cr23DecFrame N t := by
    rw [decCandInit_regs14]; exact h14
  have hfr4 : (runBlock decCandInit E st).regs r4 = s.val := by
    rw [decCandInit_regs4]; exact h4
  refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' => k1 = (Stmt.code decCandInit).len ∧
    (k2 ≤ 2 + 39 * cr23M t ∧
      (∃ len' l', DecCandInvP N t C x s tag (cr23M t) len' l' s' ∧
        DecCandFrame N t m₀ s') ∧
      s'.pc = a + (Stmt.code decCandInit).len + (Cond.lt r15 r0 r7).code.length
        + (Stmt.code decCandBody).len + 2)) hinit ?_) ?_
  · intro k1 s1 h1
    obtain ⟨rfl, rfl⟩ := h1
    have hR0 : DecCandInvP N t C x s tag 0 0 [] (runBlock decCandInit E st) :=
      decCandInit_data N t hN htN E hEW C x s tag m₀ st hminit hfr14 hfr4
        hMv hLv hlb htg hNv hcb htb (by rw [hEW]; exact htagW) htaglt hpay
    refine Sem.mono (decCand_loopP N t hN ht htN C x s tag 0 [] m₀ hsup htagW P
      (a + (Stmt.code decCandInit).len) hAtLoop (runBlock decCandInit E st) hpc16 hminit
      hR0) ?_
    intro k s' hk
    exact ⟨rfl, hk⟩
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3, h4⟩ := h
    exact ⟨by omega, h3, h4⟩
/-- Chunk W of `decAdvance`: `mem (slot 7) := mem (slot 7) / 4`, leaving `w / 4` in `r9` for the
next round's seed scan (`r9` is the loop counter). -/
def advW : List Instr :=
  [iImm r15 8, iAdd r15 r14 r15, iLd r9 r15, iImm r12 4, iDiv r9 r9 r12, iSt r15 r9]
/-- Chunk T of `decAdvance`: `mem (slot 8) := mem (slot 8) + 1` (the round tag). -/
def advT : List Instr :=
  [iImm r15 9, iAdd r15 r14 r15, iLd r6 r15, iImm r5 1, iAdd r6 r6 r5, iSt r15 r6]
/-- Chunk M of `decAdvance`: `mem (slot 14) := mem (slot 14) + r1` (the master length). -/
def advM : List Instr :=
  [iImm r15 15, iAdd r15 r14 r15, iLd r6 r15, iAdd r6 r6 r1, iSt r15 r6]
theorem decAdvance_split : decAdvance = advW ++ advT ++ advM := rfl
theorem advW_data (E : RAMEnv) (st : RAMState) (F : ℕ)
    (h14 : st.regs r14 = F) (hF8 : F + 8 < 2 ^ E.W) (hW : 1 < 2 ^ E.W)
    (hvw : st.mem (F + 8) < 2 ^ E.W) :
    (runBlock advW E st).mem = Function.update st.mem (F + 8) (st.mem (F + 8) / 4) ∧
    (runBlock advW E st).regs r9 = st.mem (F + 8) / 4 ∧
    (runBlock advW E st).regs r15 = F + 8 ∧
    (∀ d : Fin 16, d ≠ r9 → d ≠ r12 → d ≠ r15 → (runBlock advW E st).regs d = st.regs d) := by
  have hb8 : (8 : ℕ) % 2 ^ E.W = 8 := Nat.mod_eq_of_lt (by omega)
  have hb4 : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by omega)
  have hF8m : (F + 8) % 2 ^ E.W = F + 8 := Nat.mod_eq_of_lt hF8
  have hdv : st.mem (F + 8) / 4 % 2 ^ E.W = st.mem (F + 8) / 4 :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hvw)
  have hvm : st.mem (F + 8) % 2 ^ E.W = st.mem (F + 8) := Nat.mod_eq_of_lt hvw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [advW, h14, hb8, hb4, hF8m, hdv, hvm]
  · simp [advW, h14, hb8, hb4, hF8m, hdv, hvm]
  · simp [advW, h14, hb8, hb4, hF8m, hdv, hvm]
  · intro d h9 h12 h15
    simp [advW, h9, h12, h15]
theorem advT_data (E : RAMEnv) (st : RAMState) (F : ℕ)
    (h14 : st.regs r14 = F) (hF9 : F + 9 < 2 ^ E.W) (hW : 1 < 2 ^ E.W)
    (hvw : st.mem (F + 9) + 1 < 2 ^ E.W) :
    (runBlock advT E st).mem = Function.update st.mem (F + 9) (st.mem (F + 9) + 1) ∧
    (runBlock advT E st).regs r6 = st.mem (F + 9) + 1 ∧
    (runBlock advT E st).regs r15 = F + 9 ∧
    (∀ d : Fin 16, d ≠ r5 → d ≠ r6 → d ≠ r15 → (runBlock advT E st).regs d = st.regs d) := by
  have hb9 : (9 : ℕ) % 2 ^ E.W = 9 := Nat.mod_eq_of_lt (by omega)
  have hb1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hF9m : (F + 9) % 2 ^ E.W = F + 9 := Nat.mod_eq_of_lt hF9
  have hsum : (st.mem (F + 9) + 1) % 2 ^ E.W = st.mem (F + 9) + 1 :=
    Nat.mod_eq_of_lt hvw
  have hvm : st.mem (F + 9) % 2 ^ E.W = st.mem (F + 9) := by
    refine Nat.mod_eq_of_lt (lt_of_lt_of_le ?_ (le_of_lt hvw))
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [advT, h14, hb9, hb1, hF9m, hsum, hvm]
  · simp [advT, h14, hb9, hb1, hF9m, hsum, hvm]
  · simp [advT, h14, hb9, hb1, hF9m, hsum, hvm]
  · intro d h5 h6 h15
    simp [advT, h5, h6, h15]
theorem advM_data (E : RAMEnv) (st : RAMState) (F : ℕ)
    (h14 : st.regs r14 = F) (hF15 : F + 15 < 2 ^ E.W) (hW : 1 < 2 ^ E.W)
    (hvw : st.mem (F + 15) + st.regs r1 < 2 ^ E.W) (h1v : st.regs r1 < 2 ^ E.W) :
    (runBlock advM E st).mem = Function.update st.mem (F + 15) (st.mem (F + 15) + st.regs r1) ∧
    (runBlock advM E st).regs r6 = st.mem (F + 15) + st.regs r1 ∧
    (runBlock advM E st).regs r15 = F + 15 ∧
    (∀ d : Fin 16, d ≠ r6 → d ≠ r15 → (runBlock advM E st).regs d = st.regs d) := by
  have hb15 : (15 : ℕ) % 2 ^ E.W = 15 := Nat.mod_eq_of_lt (by omega)
  have hF15m : (F + 15) % 2 ^ E.W = F + 15 := Nat.mod_eq_of_lt hF15
  have hsum : (st.mem (F + 15) + st.regs r1) % 2 ^ E.W = st.mem (F + 15) + st.regs r1 :=
    Nat.mod_eq_of_lt hvw
  have hvm : st.mem (F + 15) % 2 ^ E.W = st.mem (F + 15) :=
    Nat.mod_eq_of_lt (by omega)
  have h1m : st.regs r1 % 2 ^ E.W = st.regs r1 := Nat.mod_eq_of_lt h1v
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [advM, h14, hb15, hF15m, hsum, hvm, h1m]
  · simp [advM, h14, hb15, hF15m, hsum, hvm, h1m]
  · simp [advM, h14, hb15, hF15m, hsum, hvm, h1m]
  · intro d h6 h15
    simp [advM, h6, h15]
/-- **The round's bookkeeping, end to end**: `slot 7 := w/4` (and `r9` carries it), `slot 8 :=
tag+1`, `slot 14 := mstLen + len` (`len` is in `r1`), and **nothing else in memory moves**. -/
theorem decAdvance_data (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C' : Fin N → Fin (cr23D N) → Fin (cr23M t)) (st : RAMState)
    (h14 : st.regs r14 = cr23DecFrame N t)
    (h7 : st.mem (decSlot N t 7) < 2 ^ cr23Word N)
    (h8 : st.mem (decSlot N t 8) + 1 < 2 ^ cr23Word N)
    (h14v : st.mem (decSlot N t 14) + st.regs r1 < 2 ^ cr23Word N)
    (h1v : st.regs r1 < 2 ^ cr23Word N) :
    (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).mem (decSlot N t 7)
        = st.mem (decSlot N t 7) / 4 ∧
      (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).mem (decSlot N t 8)
        = st.mem (decSlot N t 8) + 1 ∧
      (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).mem (decSlot N t 14)
        = st.mem (decSlot N t 14) + st.regs r1 ∧
      (∀ a, a ≠ decSlot N t 7 → a ≠ decSlot N t 8 → a ≠ decSlot N t 14 →
        (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).mem a = st.mem a) ∧
      (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).regs r9
        = st.mem (decSlot N t 7) / 4 ∧
      (runBlock decAdvance (detEnv (cr23Word N) (cr23DecDet N t C')) st).regs r14
        = cr23DecFrame N t := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C') with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hF8 : cr23DecFrame N t + 8 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 8) (by norm_num)
  have hF9 : cr23DecFrame N t + 9 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 9) (by norm_num)
  have hF15 : cr23DecFrame N t + 15 < 2 ^ E.W := by
    rw [hEW]; exact cr23_frame_add_lt_word N t hN htN (c := 15) (by norm_num)
  have h7' : st.mem (cr23DecFrame N t + 8) < 2 ^ E.W := by rw [hEW]; simpa only [decSlot] using h7
  have h8' : st.mem (cr23DecFrame N t + 9) + 1 < 2 ^ E.W := by
    rw [hEW]; simpa only [decSlot] using h8
  have h14' : st.mem (cr23DecFrame N t + 15) + st.regs r1 < 2 ^ E.W := by
    rw [hEW]; simpa only [decSlot] using h14v
  have h1' : st.regs r1 < 2 ^ E.W := by rw [hEW]; exact h1v
  set st1 : RAMState := runBlock advW E st with hst1
  set st2 : RAMState := runBlock advT E st1 with hst2
  set st3 : RAMState := runBlock advM E st2 with hst3
  obtain ⟨hm1, hr9, hr15, hfr1⟩ := advW_data E st (cr23DecFrame N t) h14 hF8 hW h7'
  have hm1' : st1.mem = Function.update st.mem (cr23DecFrame N t + 8)
      (st.mem (cr23DecFrame N t + 8) / 4) := hm1
  have hr9' : st1.regs r9 = st.mem (cr23DecFrame N t + 8) / 4 := hr9
  have hr15a : st1.regs r15 = cr23DecFrame N t + 8 := hr15
  have hfr1' : ∀ d : Fin 16, d ≠ r9 → d ≠ r12 → d ≠ r15 → st1.regs d = st.regs d := hfr1
  have h1m9 : st1.mem (cr23DecFrame N t + 9) = st.mem (cr23DecFrame N t + 9) := by
    rw [hm1']; exact dec_upd_ne (by omega)
  have h1m15 : st1.mem (cr23DecFrame N t + 15) = st.mem (cr23DecFrame N t + 15) := by
    rw [hm1']; exact dec_upd_ne (by omega)
  have h1r14 : st1.regs r14 = cr23DecFrame N t :=
    (hfr1' r14 (by decide) (by decide) (by decide)).trans h14
  obtain ⟨hm2, hr6, hr15a, hfr2⟩ := advT_data E st1 (cr23DecFrame N t) h1r14 hF9 hW
    (by rw [h1m9]; exact h8')
  have hm2' : st2.mem = Function.update st1.mem (cr23DecFrame N t + 9)
      (st1.mem (cr23DecFrame N t + 9) + 1) := hm2
  have hfr2' : ∀ d : Fin 16, d ≠ r5 → d ≠ r6 → d ≠ r15 → st2.regs d = st1.regs d := hfr2
  have h2m15 : st2.mem (cr23DecFrame N t + 15) = st1.mem (cr23DecFrame N t + 15) := by
    rw [hm2']; exact dec_upd_ne (by omega)
  have h2r1 : st2.regs r1 = st.regs r1 :=
    (hfr2' r1 (by decide) (by decide) (by decide)).trans
      (hfr1' r1 (by decide) (by decide) (by decide))
  have h2r14 : st2.regs r14 = cr23DecFrame N t :=
    (hfr2' r14 (by decide) (by decide) (by decide)).trans h1r14
  obtain ⟨hm3, hr6', hr15b, hfr3⟩ := advM_data E st2 (cr23DecFrame N t) h2r14 hF15 hW
    (by rw [h2m15, h1m15]; exact h14') (by rw [h2r1]; exact h1')
  have hm3' : st3.mem = Function.update st2.mem (cr23DecFrame N t + 15)
      (st2.mem (cr23DecFrame N t + 15) + st2.regs r1) := hm3
  have hfr3' : ∀ d : Fin 16, d ≠ r6 → d ≠ r15 → st3.regs d = st2.regs d := hfr3
  have hbody : runBlock decAdvance E st = st3 := by
    rw [decAdvance_split]
    simp only [runBlock_append]
    rw [← hst1, ← hst2, ← hst3]
  have hv7 : st3.mem (cr23DecFrame N t + 8) = st.mem (cr23DecFrame N t + 8) / 4 := by
    rw [hm3', dec_upd_ne (by omega), hm2', dec_upd_ne (by omega), hm1']
    exact dec_upd_same _ _ _
  have hv8 : st3.mem (cr23DecFrame N t + 9) = st.mem (cr23DecFrame N t + 9) + 1 := by
    rw [hm3', dec_upd_ne (by omega), hm2', dec_upd_same, h1m9]
  have hv15 : st3.mem (cr23DecFrame N t + 15)
      = st.mem (cr23DecFrame N t + 15) + st.regs r1 := by
    rw [hm3', dec_upd_same, h2m15, h1m15, h2r1]
  have hout : ∀ a, a ≠ cr23DecFrame N t + 8 → a ≠ cr23DecFrame N t + 9 →
      a ≠ cr23DecFrame N t + 15 → st3.mem a = st.mem a := by
    intro a ha8 ha9 ha15
    rw [hm3', dec_upd_ne ha15, hm2', dec_upd_ne ha9, hm1', dec_upd_ne ha8]
  have hr9'' : st3.regs r9 = st.mem (cr23DecFrame N t + 8) / 4 :=
    (hfr3' r9 (by decide) (by decide)).trans
      ((hfr2' r9 (by decide) (by decide) (by decide)).trans hr9')
  have hr14'' : st3.regs r14 = cr23DecFrame N t :=
    (hfr3' r14 (by decide) (by decide)).trans h2r14
  have hs7 : decSlot N t 7 = cr23DecFrame N t + 8 := by simp only [decSlot]
  have hs8 : decSlot N t 8 = cr23DecFrame N t + 9 := by simp only [decSlot]
  have hs14 : decSlot N t 14 = cr23DecFrame N t + 15 := by simp only [decSlot]
  rw [hbody]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs7]; exact hv7
  · rw [hs8]; exact hv8
  · rw [hs14]; exact hv15
  · intro a h1 h2 h3
    exact hout a (fun hh => h1 (by rw [hs7]; exact hh)) (fun hh => h2 (by rw [hs8]; exact hh))
      (fun hh => h3 (by rw [hs14]; exact hh))
  · rw [hs7]; exact hr9''
  · exact hr14''
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
/-- **A symmetric difference against an insertion**: if `x` is new for `B`, inserting it into the
right-hand set is the same as toggling `{x}` *after* the toggle by `B`. -/
theorem decSymm_insert (A B : Finset ℕ) {x : ℕ} (hx : x ∉ B) :
    decSymm A (insert x B) = decSymm (decSymm A B) {x} := by
  ext v
  by_cases hvx : v = x
  · rw [hvx]
    have hB : x ∈ decSymm A B ↔ x ∈ A := by
      simp only [decSymm, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd h hx
      · intro h
        exact Or.inl ⟨h, hx⟩
    rw [decSymm_singleton_self, hB]
    simp only [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, true_or, not_true, and_false, false_or, true_and, and_true]
  · have hv : v ≠ x := hvx
    have hL : v ∈ decSymm A (insert x B) ↔ (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
      simp only [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, fun hb => h2 (Or.inr hb)⟩
        · rcases h1 with h | h
          · exact absurd h hv
          · exact Or.inr ⟨h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, fun h => by rcases h with h' | h'; exacts [hv h', h2 h']⟩
        · exact Or.inr ⟨Or.inr h1, h2⟩
    have hR : v ∈ decSymm (decSymm A B) {x} ↔ (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
      rw [decSymm_singleton_ne (decSymm A B) hv]
      simp only [decSymm, Finset.mem_union, Finset.mem_sdiff]
    rw [hL, hR]
/-- One more entry: `l.take (j+1)` is `l.take j` with `l.getD j 0` appended. -/
theorem dec_take_succ (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j 0] := by
  have hopt : l[j]? = some (l.getD j 0) := by
    rw [List.getD_eq_getElem _ 0 hj, List.getElem?_eq_getElem hj]
  rw [List.take_add_one, hopt]
  rfl
/-- **The entry set of a prefix**: `(l.take (j+1)).toFinset = insert (l.getD j 0) (l.take j).toFinset`. -/
theorem dec_take_toFinset (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).toFinset = insert (l.getD j 0) (l.take j).toFinset := by
  rw [dec_take_succ l hj, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty, Finset.insert_eq, Finset.union_comm]
/-- A duplicate-free list does not contain its own `j`-th entry earlier. -/
theorem dec_getD_not_mem_take {l : List ℕ} (hnd : l.Nodup) {j : ℕ} (hj : j < l.length) :
    l.getD j 0 ∉ l.take j := by
  have hnd1 : (l.take (j + 1)).Nodup := hnd.take
  rw [dec_take_succ l hj] at hnd1
  have h2 := (List.nodup_append.mp hnd1).2.2
  intro hm
  exact h2 _ hm _ (by simp) rfl
/-- **The parity-set family of the round loop**: `k` toggles of the first `k` candidates. -/
def decParSet (P : Finset ℕ) (l : List ℕ) : ℕ → Finset ℕ :=
  fun k => decSymm P (l.take k).toFinset
/-- **The family steps correctly**: this is the `hS` hypothesis of `decParStmt_spec`. -/
theorem decParFamily {l : List ℕ} (hnd : l.Nodup) (P : Finset ℕ) :
    ∀ j, j < l.length → decParSet P l (j + 1) = decSymm (decParSet P l j) {l.getD j 0} := by
  intro j hj
  have h := dec_take_toFinset l hj
  have hx : l.getD j 0 ∉ (l.take j).toFinset := by
    rw [List.mem_toFinset]
    exact dec_getD_not_mem_take hnd hj
  show decSymm P (l.take (j + 1)).toFinset
      = decSymm (decSymm P (l.take j).toFinset) {l.getD j 0}
  rw [h]
  exact decSymm_insert P (l.take j).toFinset hx
/-- The family starts at `P`: `S 0` is the round head's parity set. -/
theorem decParFamily_zero (P : Finset ℕ) (l : List ℕ) : decParSet P l 0 = P := by
  show decSymm P (l.take 0).toFinset = P
  rw [List.take_zero, List.toFinset_nil, decSymm_empty]
theorem progDecPreC_noBranch : NoBranch progDecPreC := by simp [progDecPreC]
theorem progDecPreS_noBranch : NoBranch progDecPreS := by simp [progDecPreS]
theorem progDecPre_noBranch : NoBranch progDecPre := by
  rw [progDecPre, noBranch_append]
  exact ⟨progDecPreC_noBranch, progDecPreS_noBranch⟩
/-- **The store half never writes `r14`.**  `decFrame_of_dests` cannot state this — the block has
fifteen `store`s, whose `Instr.dest?` is `none`, so a `List (Fin 16)` destination list cannot match.
The destination *test* of the whole block is one closed `Bool` computation, and
`runBlock_regs_frame` is happy with `dest? = none`. -/
theorem progDecPreS_r14 : ∀ i ∈ progDecPreS, i.dest? ≠ some r14 := by
  have h : (progDecPreS.map (fun i => i.dest? != some r14)).all id = true := by decide
  intro i hi
  have hmem : (i.dest? != some r14) ∈ progDecPreS.map (fun i => i.dest? != some r14) :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  have h1 : (i.dest? != some r14) = true := (List.all_eq_true.mp h) _ hmem
  rwa [bne_iff_ne] at h1
/-- **The prologue's frame register**: the store half does not touch `r14`, and the computation half
computes `cr23DecFrame` into it (`decPreC_data`). -/
theorem decPreState_regs14 (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0) :
    (decPreState N t C s).regs r14 = cr23DecFrame N t := by
  obtain ⟨-, -, -, -, -, -, -, -, g14, -, -⟩ := decPreC_data N t hN htN C s h0
  rw [decPreState, runBlock_regs_frame _ _ _ _ progDecPreS_r14]
  exact g14
/-- The `r1 := 0` reset: one instruction. -/
theorem decReset1_spec (E : RAMEnv) (st : RAMState) :
    (runBlock [iImm r1 0] E st).regs r1 = 0 ∧
      (runBlock [iImm r1 0] E st).mem = st.mem ∧
      (∀ d : Fin 16, d ≠ r1 → (runBlock [iImm r1 0] E st).regs d = st.regs d) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro d hd
    simp [hd]
theorem decReset1_noBranch : NoBranch [iImm r1 0] := by simp
/-- **The (b) → (c) seam.**  Body (b)'s exit invariant and its memory frame, together with the round
head's `DecDataN` facts (`slot 0`, and the payload of the residual), give body (c)'s entry invariant on
the state after `r1 := 0` — with `y := cr23Sketch N t C x`, so that the payload body (c) starts from is
*the* sketch of the residual. -/
theorem decXorInv_of_cand (N t : ℕ) (hN : 1 ≤ N) (_ht : 1 ≤ t) (_htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag len : ℕ) (l : List ℕ) (m₀ : ℕ → ℕ) (st : RAMState)
    (hR : DecCandInvP N t C x s tag (cr23M t) len l st)
    (hF : DecCandFrame N t m₀ st)
    (h0 : m₀ (decSlot N t 0) = cr23D N)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      m₀ a = packMem (cr23Word N) (cr23Sketch N t C x) a) :
    DecXorInv N t C (cr23Sketch N t C x) l len 0
      (runBlock [iImm r1 0] (detEnv (cr23Word N) (cr23DecDet N t C)) st) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  obtain ⟨-, h2, -, -, -, -, -, -, -, h14, hlist, hnod, hlen, hentries, -, -, -, -, hsl1, -,
    -⟩ := hR
  have hres := decReset1_spec E st
  have hr1 : (runBlock [iImm r1 0] E st).regs r1 = 0 := hres.1
  have hmem : (runBlock [iImm r1 0] E st).mem = st.mem := hres.2.1
  have hnot1 := hres.2.2
  refine ⟨hr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnot1 r2 (by decide)]
    exact h2
  · rw [hnot1 r14 (by decide)]
    exact h14
  · rw [hmem]
    have hfr : decSlot N t 0 < decCandBase N t := by
      simp only [decSlot, decCandBase]
      omega
    exact (hF _ (Or.inl hfr)).trans h0
  · rw [hmem]
    exact hsl1
  · intro k hk
    rw [hmem]
    exact hlist k hk
  · intro k hk
    exact hentries _ (dec_getD_mem (by rw [← hlen]; exact hk))
  · intro addr ha
    rw [hmem]
    have hfr : addr < decCandBase N t := by
      have h1 := cr23_wordsOf_le_frame N t hN
      simp only [decCandBase]
      omega
    rw [hF addr (Or.inl hfr)]
    have hz : decLstDelta N t C l 0 = 0 := by simp [decLstDelta]
    rw [hz, add_zero]
    exact hpay addr ha
/-- The candidate list's length is at most the residual's support — the `DecCandInvP` form of
`decCandLen_le_w`, which is what the parity pass's cap uses. -/
theorem decCandLen_le_wP (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (s : Fin (cr23D N)) (tag len : ℕ) (l : List ℕ) (st : RAMState)
    (hR : DecCandInvP N t C x s tag (cr23M t) len l st) :
    len ≤ (cr23Supp x).card :=
  decCandLen_le_w N t hN ht C x s tag (cr23M t) len l st
    (decCandInvP_final N t C x s tag len l st hR)
theorem decWordsOf_le_slot (N t : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    wordsOf (cr23Word N) (cr23R N t) ≤ decSlot N t k :=
  le_trans (cr23_wordsOf_le_frame N t hN) (by simp only [decSlot]; omega)
theorem decWordsOf_le_candBase (N t : ℕ) (hN : 1 ≤ N) :
    wordsOf (cr23Word N) (cr23R N t) ≤ decCandBase N t :=
  le_trans (cr23_wordsOf_le_frame N t hN) (by simp only [decCandBase]; omega)
theorem decWordsOf_le_tagBase (N t : ℕ) (hN : 1 ≤ N) :
    wordsOf (cr23Word N) (cr23R N t) ≤ decTagBase N t :=
  le_trans (decWordsOf_le_candBase N t hN) (decCandBase_le_tagBase N t)
theorem decWordsOf_le_mstBase (N t : ℕ) (hN : 1 ≤ N) :
    wordsOf (cr23Word N) (cr23R N t) ≤ decMstBase N t :=
  le_trans (decWordsOf_le_tagBase N t hN) (decTagBase_le_mstBase N t)
theorem decWordsOf_le_parBase (N t : ℕ) (hN : 1 ≤ N) :
    wordsOf (cr23Word N) (cr23R N t) ≤ decParBase N t :=
  le_trans (decWordsOf_le_mstBase N t hN) (decMstBase_le_parBase N t)
/-- **The parity bitmap is a bitmap.**  Body (d)'s initialisation (`decParInit_data`) wants its input
bit as `if v ∈ S 0 then 1 else 0`, i.e. *total*, while `DecDataN`'s parity clause is only the `iff`
"`mem = 1 ↔ v ∈ P`".  The two differ exactly on the cells that are neither `0` nor `1`, so the loop
has to carry "every parity cell is at most one" as well — this lemma is the bridge, and it is the
second interface gap of this kind the round loop has to pay for (the first was `DecCandStmt_spec`'s
unrestricted `htaglt`, see `_cr23_roundf.lean.txt` §1). -/
theorem decPar_if_form (N t : ℕ) (P : Finset ℕ) (m : ℕ → ℕ)
    (hb : ∀ v, v < 2 ^ (cr23Lb N + 1) → m (decParBase N t + v) ≤ 1)
    (h : ∀ v, v < 2 ^ (cr23Lb N + 1) → (m (decParBase N t + v) = 1 ↔ v ∈ P)) :
    ∀ v, v < 2 ^ (cr23Lb N + 1) → m (decParBase N t + v) = if v ∈ P then 1 else 0 := by
  intro v hv
  have h1 := hb v hv
  have h2 := h v hv
  by_cases hP : v ∈ P
  · rw [if_pos hP]
    exact h2.mpr hP
  · rw [if_neg hP]
    have hne : m (decParBase N t + v) ≠ 1 := fun he => hP (h2.mp he)
    omega
/-- The same bridge, read off `DecDataN`. -/
theorem decDataN_par_if (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (z : Fin N → ZMod 2)
    (w tag mstLen : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState)
    (h : DecDataN N t C z w tag mstLen P mst st)
    (hb : ∀ v, v < 2 ^ (cr23Lb N + 1) → st.mem (decParBase N t + v) ≤ 1) :
    ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ P then 1 else 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := h
  exact decPar_if_form N t P st.mem hb hpar
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
/-- The parity body never writes `r14`. -/
theorem decParBody_frame14 (E : RAMEnv) (st : RAMState) :
    (runBlock decParBody E st).regs r14 = st.regs r14 := by
  rw [decParBody, runBlock_append]
  rw [decParBB_frame _ _ r14 (by decide) (by decide)]
  exact decParBA_frame _ _ r14 (by decide) (by decide) (by decide)
/-- The parity initialisation never writes `r14`. -/
theorem decParInit_frame14 (E : RAMEnv) (st : RAMState) :
    (runBlock decParInit E st).regs r14 = st.regs r14 := by
  simp [decParInit, decParIA, decParIB, decParIC, decParID, runBlock_append]
/-- **One iteration of the parity pass, with the frame register.**  `decPar_bodyIter` plus the
observation that the body's block leaves `r14` alone. -/
theorem decPar_bodyIter_r14 (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen j : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAtBody : At Pgm (a + (Cond.lt r13 r0 r1).code.length + 1) decParBody)
    (hjmpAt : Pgm[(a + (Cond.lt r13 r0 r1).code.length + 1) + decParBody.length]? =
      some (iJmp a))
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : S (j + 1) = decSymm (S j) {l.getD j 0})
    (st : RAMState) (hpc : st.pc = a + (Cond.lt r13 r0 r1).code.length + 1)
    (hR : DecParInv N t S l mst mstLen j mb st) (hj : j < l.length) :
    Sem Pgm E (a + (Cond.lt r13 r0 r1).code.length + 1) a
      { st with pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
      (fun k s' => k = decParBody.length + 1 ∧
        DecParInv N t S l mst mstLen (j + 1) mb s' ∧ s'.pc = a ∧
        s'.regs r14 = st.regs r14) := by
  set b : ℕ := a + (Cond.lt r13 r0 r1).code.length + 1 with hb
  have hblk : Sem Pgm E b (b + decParBody.length) { st with pc := b }
      (fun k s' => k = decParBody.length ∧ s' = runBlock decParBody E { st with pc := b }) :=
    Sem.block Pgm E b decParBody { st with pc := b } hAtBody decParBody_noBranch rfl
  have hpcB : (runBlock decParBody E { st with pc := b }).pc = b + decParBody.length := by
    rw [runBlock_pc decParBody E _ decParBody_noBranch]
  have hjmpSem : Sem Pgm E (b + decParBody.length) a
      (runBlock decParBody E { st with pc := b })
      (fun k s' => k = 1 ∧ s' = { runBlock decParBody E { st with pc := b } with pc := a }) :=
    Sem.exec Pgm E (b + decParBody.length) a _ (iJmp a) hjmpAt hpcB rfl
  refine Sem.mono (Sem.trans hblk hjmpSem) ?_
  intro k s' hk
  obtain ⟨rfl, rfl⟩ := hk
  have hfr : (runBlock decParBody E { st with pc := b }).regs r14 = st.regs r14 := by
    simpa using decParBody_frame14 E { st with pc := b }
  exact ⟨rfl, DecParInv_pc N t S l mst mstLen (j + 1) mb a _
    (decParBody_data N t hN htN E hEW S l mst mstLen j mb { st with pc := b } hj hcap hlN hS
      hR), rfl, hfr⟩
/-- **The parity loop, with the frame register.**  `DecParInv ∧ r14 = F` is the loop invariant. -/
theorem decPar_loop_r14 (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ) (F : ℕ)
    (hAt : At Pgm a (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) a))
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0})
    (st : RAMState) (hpc : st.pc = a) (hF : st.regs r14 = F)
    (hR : DecParInv N t S l mst mstLen 0 mb st) :
    Sem Pgm E a (a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len + 2) st
      (fun k s' => k ≤ 2 + 12 * l.length ∧
        DecParInv N t S l mst mstLen l.length mb s' ∧
        s'.pc = a + (Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len + 2 ∧
        s'.regs r14 = F) := by
  have hW : 1 < 2 ^ E.W := by rw [hEW]; exact cr23_one_lt_word N hN
  have hirr : ∀ (j : ℕ) (s s' : RAMState), (∀ d : Fin 16, d ≠ r13 → s.regs d = s'.regs d) →
      s.mem = s'.mem → (DecParInv N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
        (DecParInv N t S l mst mstLen j mb s' ∧ s'.regs r14 = F) := by
    intro j s s' hd hm' h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [← hd r0 (by decide)]; exact a1
    · rw [← hd r1 (by decide)]; exact a2
    · rw [← hd r4 (by decide)]; exact a3
    · rw [← hd r5 (by decide)]; exact a4
    · rw [← hd r6 (by decide)]; exact a5
    · rw [← hd r7 (by decide)]; exact a6
    · intro i hi; rw [← hm']; exact a7 i hi
    · intro v hv; rw [← hm']; exact a8 v hv
    · intro b hb; rw [← hm']; exact a9 b hb
    · intro i hi; rw [← hm']; exact a10 i hi
    · intro k hk; rw [← hm']; exact a11 k hk
    · rw [← hd r14 (by decide)]; exact h2
  have hgo : ∀ j, j < l.length → ∀ s, (DecParInv N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
      (Cond.lt r13 r0 r1).eval s := by
    intro j hj s h
    obtain ⟨h1, -⟩ := h
    obtain ⟨h0, h1', -⟩ := h1
    show s.regs r0 < s.regs r1
    rw [h0, h1']; exact hj
  have hstop : ∀ s, (DecParInv N t S l mst mstLen l.length mb s ∧ s.regs r14 = F) →
      ¬ (Cond.lt r13 r0 r1).eval s := by
    intro s h
    obtain ⟨h1, -⟩ := h
    obtain ⟨h0, h1', -⟩ := h1
    show ¬ (s.regs r0 < s.regs r1)
    rw [h0, h1']; omega
  have hstep : ∀ j, j < l.length → ∀ s, s.pc = a →
      (DecParInv N t S l mst mstLen j mb s ∧ s.regs r14 = F) →
      Sem Pgm E (a + (Cond.lt r13 r0 r1).code.length + 1) a
        { runBlock (Cond.lt r13 r0 r1).code E s with
          pc := a + (Cond.lt r13 r0 r1).code.length + 1 }
        (fun k s' => k ≤ decParBody.length + 1 ∧
          (DecParInv N t S l mst mstLen (j + 1) mb s' ∧ s'.regs r14 = F) ∧ s'.pc = a) := by
    intro j hj s hpc' hRs
    obtain ⟨hRj, hFrj⟩ := hRs
    obtain ⟨-, hjz, hbody, hjmp⟩ := at_loop hAt
    have hlen : (Stmt.code decParBody).len = decParBody.length := rfl
    have hbody' : At Pgm (a + (Cond.lt r13 r0 r1).code.length + 1) decParBody := hbody
    have hjmpAt : Pgm[(a + (Cond.lt r13 r0 r1).code.length + 1) + decParBody.length]? =
        some (iJmp a) := by
      rw [← hlen]
      exact hjmp
    have hR' : DecParInv N t S l mst mstLen j mb
        { runBlock (Cond.lt r13 r0 r1).code E s with
          pc := a + (Cond.lt r13 r0 r1).code.length + 1 } :=
      (hirr j (runBlock (Cond.lt r13 r0 r1).code E s) s
        (fun d hd => runBlock_cond_regs (Cond.lt r13 r0 r1) E s d hd)
        (runBlock_cond_mem (Cond.lt r13 r0 r1) E s) ⟨hRj, hFrj⟩).1
    have hFr' : (runBlock (Cond.lt r13 r0 r1).code E s).regs r14 = F := by
      rw [runBlock_cond_regs (Cond.lt r13 r0 r1) E s r14 (by decide)]
      exact hFrj
    refine Sem.mono (decPar_bodyIter_r14 N t hN htN E hEW S l mst mstLen j mb Pgm a hbody' hjmpAt
      hcap hlN (hS j hj) { runBlock (Cond.lt r13 r0 r1).code E s with
        pc := a + (Cond.lt r13 r0 r1).code.length + 1 } rfl hR' hj) ?_
    intro k s' hk
    obtain ⟨hk1, hInv, hpc, hfr⟩ := hk
    exact ⟨le_of_eq hk1, ⟨hInv, by rw [hfr]; exact hFr'⟩, hpc⟩
  have hloop := Sem.loopPredLe Pgm E a (Cond.lt r13 r0 r1) (Stmt.code decParBody) hAt hW
    l.length (fun j s => DecParInv N t S l mst mstLen j mb s ∧ s.regs r14 = F)
    (fun _ => decParBody.length + 1) hirr hgo hstop hstep st hpc ⟨hR, hF⟩
  refine Sem.mono hloop (fun k s' h => ⟨?_, h.2.1.1, h.2.2, h.2.1.2⟩)
  obtain ⟨h1, h2⟩ := h
  have hsum : (∑ j ∈ Finset.range l.length,
        ((Cond.lt r13 r0 r1).code.length + 1 + (decParBody.length + 1)))
      = 12 * l.length := by
    simp [Finset.sum_const, Finset.card_range, Cond.code, decParBody_len, Nat.mul_comm]
  rw [hsum] at h1
  have hcl : (Cond.lt r13 r0 r1).code.length = 1 := rfl
  rw [hcl] at h1
  omega
/-- **Body (d), end to end, with the frame register.**  `decParStmt_spec`'s statement plus
`s'.regs r14 = cr23DecFrame N t`. -/
theorem decParStmt_spec_r14 (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (E : RAMEnv) (hEW : E.W = cr23Word N)
    (S : ℕ → Finset ℕ) (l mst : List ℕ) (mstLen : ℕ) (mb : ℕ → ℕ)
    (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile decParStmt a))
    (st : RAMState) (hpc : st.pc = a)
    (h14 : st.regs r14 = cr23DecFrame N t) (h2 : st.regs r2 = l.length)
    (hcand : ∀ i, i < l.length → mb (decCandBase N t + i) = l.getD i 0)
    (hbelow : ∀ b, b < decMstBase N t → st.mem b = mb b)
    (hsl9 : mb (decSlot N t 9) = decCandBase N t)
    (hsl11 : mb (decSlot N t 11) = decMstBase N t)
    (hsl12 : mb (decSlot N t 12) = decParBase N t)
    (hsl14 : mb (decSlot N t 14) = mstLen)
    (hmst : ∀ i, i < mstLen → st.mem (decMstBase N t + i) = mst.getD i 0)
    (hcap : mstLen + l.length ≤ 2 * t + 1) (hlN : ∀ i ∈ l, i < N)
    (hS : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0})
    (hpar0 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
      st.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0) :
    Sem Pgm E a (a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2) st
      (fun k s' => k ≤ (Stmt.code decParInit).len + (2 + 12 * l.length) ∧
        DecParInv N t S l mst mstLen l.length mb s' ∧
        s'.pc = a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
          + (Stmt.code decParBody).len + 2 ∧
        s'.regs r14 = cr23DecFrame N t) := by
  have hcs : decParStmt = Stmt.seq (Stmt.code decParInit)
      (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) := rfl
  have hAt' : At Pgm a (decParInit ++ Stmt.compile
      (Stmt.loop (Cond.lt r13 r0 r1) (Stmt.code decParBody)) (a + (Stmt.code decParInit).len)) := by
    rw [hcs] at hAt
    simpa only [Stmt.compile, Stmt.len] using hAt
  obtain ⟨hAtInit, hAtLoop⟩ := At.append.mp hAt'
  have hinit : Sem Pgm E a (a + decParInit.length) st
      (fun k s' => k = decParInit.length ∧ s' = runBlock decParInit E st) :=
    Sem.block Pgm E a decParInit st hAtInit decParInit_noBranch hpc
  have hpcI : (runBlock decParInit E st).pc = a + decParInit.length := by
    rw [runBlock_pc decParInit E st decParInit_noBranch, hpc]
  refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' => k1 = (Stmt.code decParInit).len ∧
    (k2 ≤ 2 + 12 * l.length ∧
      DecParInv N t S l mst mstLen l.length mb s' ∧
      s'.pc = a + (Stmt.code decParInit).len + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2 ∧
      s'.regs r14 = cr23DecFrame N t)) hinit ?_) ?_
  · intro k1 s1 h1
    obtain ⟨rfl, rfl⟩ := h1
    have hR0 : DecParInv N t S l mst mstLen 0 mb (runBlock decParInit E st) :=
      decParInit_data N t hN htN E hEW S l mst mstLen mb st h14 h2 hcand hbelow hsl9 hsl11 hsl12
        hsl14 hmst (by omega) hpar0
    have hF0 : (runBlock decParInit E st).regs r14 = cr23DecFrame N t := by
      rw [decParInit_frame14]; exact h14
    refine Sem.mono (decPar_loop_r14 N t hN htN E hEW S l mst mstLen mb Pgm _
      (cr23DecFrame N t) hAtLoop hcap hlN hS _ (by rw [hpcI]) hF0 hR0) ?_
    intro k s' hk
    exact ⟨rfl, hk⟩
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩ := h
    exact ⟨by omega, h3, h4, h5⟩
/-- `DecHead` plus the parity-bitmap bound.  `DecDataN` states the bitmap only as
`mem = 1 ↔ v ∈ P`; body (d)'s initialisation wants `mem = if v ∈ P then 1 else 0`, and the two
differ exactly on cells that are neither `0` nor `1`.

The third conjunct is the master-list address bound: the emit pass reads `mst` back as
`mem (mstBase + i)` and uses its entries as indices into the parity bitmap, so every entry must be
`< N`.  `DecHead`/`DecDataN` describe a single round only and cannot carry it. -/
def DecHead1 (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState) : Prop :=
  DecHead N t C x z w tag P mst st ∧
    (∀ v, v ∈ mst → v < N) ∧
    (∀ v, v < 2 ^ (cr23Lb N + 1) → st.mem (decParBase N t + v) ≤ 1)
theorem decSlot_ne (N t k j : ℕ) (h : k ≠ j) : decSlot N t k ≠ decSlot N t j := by
  intro hh; simp only [decSlot] at hh; omega
theorem decSlot_ne_ge (N t k b : ℕ) (hk : k < 15) (hb : decCandBase N t ≤ b) :
    b ≠ decSlot N t k := by
  have h1 := decSlot_lt_candBase N t hk
  omega
theorem decSlot_ne_lt (N t k a : ℕ) (ha : a < wordsOf (cr23Word N) (cr23R N t))
    (hN : 1 ≤ N) : a ≠ decSlot N t k := by
  have h1 := cr23_wordsOf_le_frame N t hN
  have h2 : wordsOf (cr23Word N) (cr23R N t) ≤ decSlot N t k :=
    le_trans h1 (by simp only [decSlot]; omega)
  omega
/-- The uniform cost of one round: each leg's bound with the candidate length replaced by its
cap `2t + 1`. -/
def decRoundCost (N t : ℕ) : ℕ :=
  (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) +
    ((Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
      (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
        ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length))))
theorem decAdvance_noBranch : NoBranch decAdvance := by simp [decAdvance, NoBranch]
/-- **One round**: from a round head at `(w, tag, P, mst)` the five legs reach a round head at
`(w/4, tag+1, decSymm P l.toFinset, mst ++ l)` for the candidate list `l` the scan produced. -/
theorem decRoundBody_spec (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (Pgm : Program) (b : ℕ) (hAt : At Pgm b (Stmt.compile decRoundBody b))
    (st : RAMState) (hpc : st.pc = b) (hR : DecHead1 N t C x z w tag P mst st)
    (h9 : st.regs r9 = w)
    (hwW : w < 2 ^ cr23Word N) (htagW : tag + 1 < 2 ^ cr23Word N)
    (h2tW : 2 * t + 1 < 2 ^ cr23Word N) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) b (b + decRoundBody.len) st
      (fun k s' => k ≤ decRoundCost N t ∧
        (∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
        s'.pc = b + decRoundBody.len) := by
  obtain ⟨hHead, hmstN, hpar1⟩ := hR
  obtain ⟨hD, h14, hP, hsub, hcap, hcard⟩ := hHead
  have hDp : DecDataN N t C z w tag mst.length P mst st := hD
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9s, h10s, h11s, h12s, h13s, h14s, hpay, htaglt,
    hpar, hmst⟩ := hD
  have hsup : (cr23Supp z).card ≤ t := by omega
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := by rw [hE]; rfl
  -- flatten the compile, one leg at a time
  have hcs : decRoundBody = decScanStmt.seq
      ((decCandStmtFull.seq (Stmt.code [iImm r1 0])).seq
        (decXorStmt.seq (decParStmt.seq (Stmt.code decAdvance)))) := rfl
  have h1' : At Pgm b (Stmt.compile decRoundBody b) := hAt
  rw [hcs] at h1'
  simp only [Stmt.compile, Stmt.length_compile, Stmt.len, List.append_assoc, List.length_cons,
    List.length_nil] at h1'
  obtain ⟨hAtS, h1'⟩ := At.append.mp h1'
  simp only [Stmt.length_compile] at h1'
  obtain ⟨hAtC, h1'⟩ := At.append.mp h1'
  simp only [Stmt.length_compile] at h1'
  obtain ⟨hAtR, h1'⟩ := At.append.mp h1'
  simp only [List.length_cons, List.length_nil] at h1'
  obtain ⟨hAtX, h1'⟩ := At.append.mp h1'
  simp only [Stmt.length_compile] at h1'
  obtain ⟨hAtP, h1'⟩ := At.append.mp h1'
  simp only [Stmt.length_compile] at h1'
  set b1 : ℕ := b + decScanStmt.len with hb1def
  set b2 : ℕ := b1 + decCandStmtFull.len with hb2def
  set b3 : ℕ := b2 + 1 with hb3def
  set b4 : ℕ := b3 + decXorStmt.len with hb4def
  set b5 : ℕ := b4 + decParStmt.len with hb5def
  set b6 : ℕ := b5 + decAdvance.length with hb6def
  have hAtA : At Pgm b5 decAdvance := h1'
  have hb1end : b1 = (b + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
      + (Stmt.code decScanBody).len + 2 := by
    rw [hb1def]
    show b + ((Stmt.code decScanInit).len +
        (((Cond.lt r13 r0 r1).code.length + (Stmt.code decScanBody).len) + 2))
      = (b + (Stmt.code decScanInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decScanBody).len + 2
    omega
  have hb2end : b2 = (b1 + (Stmt.code decCandInit).len) + (Cond.lt r15 r0 r7).code.length
      + (Stmt.code decCandBody).len + 2 := by
    rw [hb2def, hb1def]
    show (b + decScanStmt.len) + ((Stmt.code decCandInit).len +
        (((Cond.lt r15 r0 r7).code.length + (Stmt.code decCandBody).len) + 2))
      = ((b + decScanStmt.len) + (Stmt.code decCandInit).len) + (Cond.lt r15 r0 r7).code.length
        + (Stmt.code decCandBody).len + 2
    omega
  have hb4end : b4 = b3 + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2 := by
    rw [hb4def, hb3def]
    show b3 + (((Cond.lt r8 r1 r2).code.length + decXorBody.len) + 2)
      = b3 + (Cond.lt r8 r1 r2).code.length + decXorBody.len + 2
    omega
  have hb5end : b5 = (b4 + (Stmt.code decParInit).len) + (Cond.lt r13 r0 r1).code.length
      + (Stmt.code decParBody).len + 2 := by
    rw [hb5def, hb4def, hb3def]
    show b3 + decXorStmt.len + ((Stmt.code decParInit).len +
        (((Cond.lt r13 r0 r1).code.length + (Stmt.code decParBody).len) + 2))
      = ((b3 + decXorStmt.len) + (Stmt.code decParInit).len) + (Cond.lt r13 r0 r1).code.length
        + (Stmt.code decParBody).len + 2
    omega
  have hb6 : b6 = b + decRoundBody.len := by
    have hlen6 : decRoundBody.len = decScanStmt.len +
        ((decCandStmtFull.len + 1) + (decXorStmt.len + (decParStmt.len + decAdvance.length))) := rfl
    rw [hb6def, hb5def, hb4def, hb3def, hb2def, hb1def, hlen6]
    omega
  -- leg (a)
  have hscan : Sem Pgm E b b1 st
      (fun k s' => k ≤ (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) ∧
        DecScanInv N t C z w (cr23D N * cr23M t) st.mem s' ∧ s'.pc = b1) := by
    have h := decScanStmt_spec_at N t hN ht htN C z w st.mem Pgm b hAtS st hpc rfl h9 h14
      h0 h2 h3 h4 hpay
    rw [← hb1end] at h
    exact h
  refine Sem.mono (Sem.seq (Q₂ := fun k1 k2 s' =>
      k1 ≤ (Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t)) ∧
      (k2 ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
          (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
            ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length))) ∧
        ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
          s'.pc = b6))) hscan ?_) ?_
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    obtain ⟨hmaxAll, sstar, h4s, h3s⟩ := decScan_result' N t hN ht htN C z w st.mem s1 hInv1
    obtain ⟨hmem1, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr10, hr11, hr12, hr9, hr14⟩ := hInv1
    have hmax : ∀ s' : Fin (cr23D N), (cr23OddB C (cr23Supp z) s').card ≤
        (cr23OddB C (cr23Supp z) sstar).card := by
      intro s'; rw [h3s]; exact hmaxAll s'
    have hcand := decCandStmtP_spec N t hN ht htN C z sstar tag st.mem Pgm b1 hAtC s1 hpc1
      hmem1 h4s hr14 h2 h3 h4 h8 h1 h9s h10s hsup (by omega) htaglt hpay
    rw [← hb2end] at hcand
    have hInner1 : Sem Pgm E b1 b6 s1
        (fun k s' => k ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
            (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length))) ∧
          ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
            s'.pc = b6)) := by
      refine Sem.mono (Sem.seq (Q₂ := fun k2 k3 s' =>
          k2 ≤ (Stmt.code decCandInit).len + (2 + 39 * cr23M t) ∧
          (k3 ≤ 1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)) ∧
            ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
              s'.pc = b6))) hcand ?_) ?_
      · intro k2 s2 hQ2
        obtain ⟨hk2, ⟨len, l, hInvP, hFrame⟩, hpc2⟩ := hQ2
        have hci := decCandInvP_final N t C z sstar tag len l s2 hInvP
        obtain ⟨-, -, -, hciNodup, hciLen, hciEntries, -, -, hciSet⟩ := hci
        have hcle : len ≤ (cr23Supp z).card := decCandLen_le_wP N t hN ht C z sstar tag len l s2 hInvP
        have hInvP0 : DecCandInvP N t C z sstar tag (cr23M t) len l s2 := hInvP
        obtain ⟨hc0, hc2, hc3, hc4, hc7, hc8, hc10, hc11, hc12, hc14, hcList, hcNodup, hcLen,
          hcEntries, hcTagEq, hcTagLe, hcSet, hcPay, hcS1, hcS9, hcS10⟩ := hInvP
        have hreset : Sem Pgm E b2 b3 s2
            (fun k s' => k = 1 ∧ s' = runBlock [iImm r1 0] E s2) := by
          have h := Sem.block Pgm E b2 [iImm r1 0] s2 hAtR decReset1_noBranch hpc2
          simpa only [List.length_cons, List.length_nil] using h
        have hpc3 : (runBlock [iImm r1 0] E s2).pc = b3 := by
          rw [runBlock_pc [iImm r1 0] E s2 decReset1_noBranch, hpc2]; rfl
        have h13mem : (runBlock [iImm r1 0] E s2).mem = s2.mem := (decReset1_spec E s2).2.1
        have hXorInv : DecXorInv N t C (cr23Sketch N t C z) l len 0
            (runBlock [iImm r1 0] E s2) :=
          decXorInv_of_cand N t hN ht htN C z sstar tag len l st.mem s2 hInvP0 hFrame h0 hpay
        have hlen2t : len ≤ 2 * t + 1 := by omega
        have hl2 : l.length ≤ 2 * t + 1 := by rw [← hcLen]; exact hlen2t
        have hxor := decXorStmt_specF N t hN htN C (cr23Sketch N t C z) l len Pgm b3 hAtX
          (runBlock [iImm r1 0] E s2) hpc3 hXorInv hlen2t
        rw [← hb4end] at hxor
        have hxc : 2 + len * (cr23D N * 10 + 24) ≤
            2 + (2 * t + 1) * (cr23D N * 10 + 24) := by
          have := Nat.mul_le_mul_right (cr23D N * 10 + 24) hlen2t
          omega
        have hInner2 : Sem Pgm E b2 b6 s2
            (fun k s' => k ≤ 1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
                ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)) ∧
              ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                s'.pc = b6)) := by
          refine Sem.mono (Sem.seq (Q₂ := fun k3 k4 s' => k3 = 1 ∧
              (k4 ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) +
                  ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length) ∧
                ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                  s'.pc = b6))) hreset ?_) ?_
          · intro k3 s3 hQ3
            obtain ⟨hk3, rfl⟩ := hQ3
            have hInner3 : Sem Pgm E b3 b6 (runBlock [iImm r1 0] E s2)
                (fun k s' => k ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) +
                    ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length) ∧
                  ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                    s'.pc = b6)) := by
              refine Sem.mono (Sem.seq (Q₂ := fun k4 k5 s' =>
                  k4 ≤ 2 + (2 * t + 1) * (cr23D N * 10 + 24) ∧
                  (k5 ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length ∧
                    ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                      s'.pc = b6))) hxor ?_) ?_
              · intro k4 s4 hQ4
                obtain ⟨hk4, hXI, hXF, hpc4⟩ := hQ4
                set S : ℕ → Finset ℕ := decParSet P l with hSdef
                have hS0 : S 0 = P := by rw [hSdef]; exact decParFamily_zero P l
                have hSstep : ∀ j, j < l.length → S (j + 1) = decSymm (S j) {l.getD j 0} :=
                  decParFamily hcNodup P
                have hSlen : S l.length = decSymm P l.toFinset := by
                  rw [hSdef]; simp only [decParSet, List.take_length]
                have hsl9 : s4.mem (decSlot N t 9) = decCandBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 9), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 9) (by norm_num)))]
                  exact h9s
                have hsl11 : s4.mem (decSlot N t 11) = decMstBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 11), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 11) (by norm_num)))]
                  exact h11s
                have hsl12 : s4.mem (decSlot N t 12) = decParBase N t := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 12), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 12) (by norm_num)))]
                  exact h12s
                have hsl14 : s4.mem (decSlot N t 14) = mst.length := by
                  rw [hXF _ (decWordsOf_le_slot N t hN 14), h13mem]
                  rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 14) (by norm_num)))]
                  exact h14s
                have hmst4 : ∀ i, i < mst.length → s4.mem (decMstBase N t + i) = mst.getD i 0 := by
                  intro i hi
                  rw [hXF _ (le_trans (decWordsOf_le_mstBase N t hN) (by omega)), h13mem]
                  rw [hFrame _ (Or.inr (by simp only [decMstBase, decTagBase]; omega))]
                  exact hmst i hi
                have hpar04 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                    s4.mem (decParBase N t + v) = if v ∈ S 0 then 1 else 0 := by
                  intro v hv
                  rw [hS0]
                  rw [hXF _ (le_trans (decWordsOf_le_parBase N t hN) (by omega)), h13mem]
                  rw [hFrame _ (Or.inr (by simp only [decMstBase, decParBase]; omega))]
                  exact decDataN_par_if N t C z w tag mst.length P mst st hDp hpar1 v hv
                have hcapP : mst.length + l.length ≤ 2 * t + 1 := by
                  have h1 : l.length ≤ w := by
                    rw [← hcLen]
                    exact le_trans hcle hcard
                  omega
                have hpar := decParStmt_spec_r14 N t hN htN E hEW S l mst mst.length s4.mem Pgm b4 hAtP s4 hpc4
                  hXI.2.2.1 (by rw [hXI.2.1, hcLen])
                  (fun i hi => hXI.2.2.2.2.2.1 i (by omega))
                  (fun _ _ => rfl) hsl9 hsl11 hsl12 hsl14 hmst4
                  hcapP hcEntries hSstep hpar04
                rw [← hb5end] at hpar
                have hInner4 : Sem Pgm E b4 b6 s4
                    (fun k s' => k ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1))
                        + decAdvance.length ∧
                      ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                        s'.pc = b6)) := by
                  refine Sem.mono (Sem.seq (Q₂ := fun k5 k6 s' =>
                      k5 ≤ (Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) ∧
                      (k6 ≤ decAdvance.length ∧
                        ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                          s'.pc = b6))) hpar ?_) ?_
                  · intro k5 s5 hQ5
                    obtain ⟨hk5, hPI, hpc5', h14s5'⟩ := hQ5
                    obtain ⟨hp0, hp1, hp4, hp5, hp6, hp7, hpcand5, hppar5, hpbelow, hpmst5, hpnew5⟩ := hPI
                    have hs5_7 : s5.mem (decSlot N t 7) = w := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 7), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 7) (by norm_num)))]
                      exact h7
                    have hs5_8 : s5.mem (decSlot N t 8) = tag := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 8), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 8) (by norm_num)))]
                      exact h8
                    have hs5_14 : s5.mem (decSlot N t 14) = mst.length := by
                      rw [hpbelow _ (decSlot_lt_mstBase N t (by norm_num))]
                      rw [hXF _ (decWordsOf_le_slot N t hN 14), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t (k := 14) (by norm_num)))]
                      exact h14s
                    have h1lt : s5.regs r1 < 2 ^ cr23Word N := by
                      rw [hp1]; exact lt_of_le_of_lt (by omega) h2tW
                    have h14vlt : s5.mem (decSlot N t 14) + s5.regs r1 < 2 ^ cr23Word N := by
                      rw [hs5_14, hp1]; exact lt_of_le_of_lt hcapP h2tW
                    have hAdv := decAdvance_data N t hN htN C s5 h14s5'
                      (by rw [hs5_7]; exact hwW)
                      (by rw [hs5_8]; exact htagW)
                      h14vlt h1lt
                    have hadv : Sem Pgm E b5 b6 s5
                        (fun k s' => k = decAdvance.length ∧ s' = runBlock decAdvance E s5) := by
                      have h := Sem.block Pgm E b5 decAdvance s5 hAtA decAdvance_noBranch hpc5'
                      simpa using h
                    have hres := cr23_round_residual N t hN C z l hcNodup hcEntries sstar hciSet
                    have hshrink := cr23_shrink_argmax C hexp heps (cr23Supp z) hsup (cr23D_pos N hN) sstar hmax
                    have hcard' : (cr23Supp (z + decLstVec N l l.length)).card ≤ w / 4 := by
                      have h1 : 4 * (cr23Supp (z + decLstVec N l l.length)).card ≤ (cr23Supp z).card := by
                        rw [hres.2]; exact hshrink
                      have h2 : 4 * (cr23Supp (z + decLstVec N l l.length)).card ≤ w := le_trans h1 hcard
                      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by omega)
                    have hcap' : (mst ++ l).length + 2 * (w / 4) ≤ 2 * t + 1 := by
                      rw [List.length_append]
                      have hlw : l.length ≤ w := by
                        rw [← hcLen]
                        exact le_trans hcle hcard
                      have hdiv : 2 * (w / 4) ≤ w := by
                        have h4 := Nat.div_mul_le_self w 4
                        omega
                      omega
                    have hsub' : ∀ v ∈ decSymm P l.toFinset, v ∈ mst ++ l := by
                      intro v hv
                      rw [decSymm, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hv
                      rcases hv with ⟨hvP, -⟩ | ⟨hvl, -⟩
                      · exact List.mem_append.mpr (Or.inl (hsub v hvP))
                      · exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hvl))
                    have hP' : decSymm P l.toFinset
                        = cr23NumSet (cr23Supp (x + (z + decLstVec N l l.length))) :=
                      cr23Parity_step hN x z l P hcNodup hcEntries hP
                    have hslot : ∀ k, k < 15 → k ≠ 7 → k ≠ 8 → k ≠ 14 →
                        (runBlock decAdvance E s5).mem (decSlot N t k) = st.mem (decSlot N t k) := by
                      intro k hk h7' h8' h14'
                      rw [hAdv.2.2.2.1 _ (decSlot_ne N t k 7 h7') (decSlot_ne N t k 8 h8')
                        (decSlot_ne N t k 14 h14')]
                      rw [hpbelow _ (decSlot_lt_mstBase N t hk)]
                      rw [hXF _ (decWordsOf_le_slot N t hN k), h13mem]
                      rw [hFrame _ (Or.inl (decSlot_lt_candBase N t hk))]
                    have hmem6 : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
                        (runBlock decAdvance E s5).mem a
                          = packMem (cr23Word N) (cr23Sketch N t C (z + decLstVec N l l.length)) a := by
                      intro a ha
                      rw [hAdv.2.2.2.1 a
                        (decSlot_ne_lt N t 7 a ha hN) (decSlot_ne_lt N t 8 a ha hN)
                        (decSlot_ne_lt N t 14 a ha hN)]
                      rw [hpbelow a (by have h1 := cr23_wordsOf_le_frame N t hN; simp only [decMstBase, decTagBase, decCandBase] at h1 ⊢; omega)]
                      rw [hXI.2.2.2.2.2.2.2 a ha]
                      rw [hres.1, hcLen]
                    have htag6 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        (runBlock decAdvance E s5).mem (decTagBase N t + v) < tag + 1 := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decTagBase N t + v)
                        (decSlot_ne_ge N t 7 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 8 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 14 (decTagBase N t + v) (by norm_num) (by simp only [decTagBase, decCandBase]; omega))]
                      rw [hpbelow _ (by simp only [decMstBase]; omega)]
                      rw [hXF _ (le_trans (decWordsOf_le_tagBase N t hN) (by omega)), h13mem]
                      have h := hcTagLe v hv
                      omega
                    have hpar6 : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        ((runBlock decAdvance E s5).mem (decParBase N t + v) = 1
                          ↔ v ∈ decSymm P l.toFinset) := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decParBase N t + v)
                        (decSlot_ne_ge N t 7 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 8 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 14 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))]
                      rw [hppar5 v hv, hSlen]
                      by_cases hvP : v ∈ decSymm P l.toFinset <;> simp [hvP]
                    have hpar6le : ∀ v, v < 2 ^ (cr23Lb N + 1) →
                        (runBlock decAdvance E s5).mem (decParBase N t + v) ≤ 1 := by
                      intro v hv
                      rw [hAdv.2.2.2.1 (decParBase N t + v)
                        (decSlot_ne_ge N t 7 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 8 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))
                        (decSlot_ne_ge N t 14 (decParBase N t + v) (by norm_num) (by simp only [decParBase, decTagBase, decCandBase, decMstBase]; omega))]
                      rw [hppar5 v hv, hSlen]
                      by_cases hvP : v ∈ decSymm P l.toFinset <;> simp [hvP]
                    have hmst6 : ∀ i, i < (mst ++ l).length →
                        (runBlock decAdvance E s5).mem (decMstBase N t + i) = (mst ++ l).getD i 0 := by
                      intro i hi
                      rw [hAdv.2.2.2.1 (decMstBase N t + i)
                        (decSlot_ne_ge N t 7 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 8 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))
                        (decSlot_ne_ge N t 14 (decMstBase N t + i) (by norm_num) (by simp only [decMstBase, decTagBase, decCandBase]; omega))]
                      exact dec_mst_concat s5.mem (decMstBase N t) mst l hpmst5 (fun k hk => by rw [← Nat.add_assoc]; exact hpnew5 k hk) i hi
                    have hmst6N : ∀ v, v ∈ mst ++ l → v < N := by
                      intro v hv
                      rw [List.mem_append] at hv
                      rcases hv with hv | hv
                      · exact hmstN v hv
                      · exact hcEntries v hv
                    have hHead1 : DecHead1 N t C x (z + decLstVec N l l.length) (w / 4) (tag + 1)
                        (decSymm P l.toFinset) (mst ++ l) (runBlock decAdvance E s5) := by
                      refine ⟨⟨?_, hAdv.2.2.2.2.2, hP', hsub', hcap', hcard'⟩, hmst6N, hpar6le⟩
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem6, htag6,
                        hpar6, hmst6⟩
                      · rw [hslot 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h0
                      · rw [hslot 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h1
                      · rw [hslot 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h2
                      · rw [hslot 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h3
                      · rw [hslot 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h4
                      · rw [hslot 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h5
                      · rw [hslot 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h6
                      · rw [hAdv.1, hs5_7]
                      · rw [hAdv.2.1, hs5_8]
                      · rw [hslot 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h9s
                      · rw [hslot 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h10s
                      · rw [hslot 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h11s
                      · rw [hslot 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h12s
                      · rw [hslot 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h13s
                      · rw [hAdv.2.2.1, hs5_14, hp1, List.length_append]
                    have hpc6 : (runBlock decAdvance E s5).pc = b6 := by
                      rw [runBlock_pc decAdvance E s5 decAdvance_noBranch, hpc5']
                    have hInner5 : Sem Pgm E b5 b6 s5
                        (fun k s' => k ≤ decAdvance.length ∧
                          ((∃ z' P' mst', DecHead1 N t C x z' (w / 4) (tag + 1) P' mst' s') ∧ s'.regs r9 = w / 4 ∧
                            s'.pc = b6)) := by
                      have hr9 : (runBlock decAdvance E s5).regs r9 = w / 4 := by
                        rw [hAdv.2.2.2.2.1, hs5_7]
                      refine Sem.mono hadv (fun k s' hk => ?_)
                      obtain ⟨rfl, rfl⟩ := hk
                      exact ⟨le_rfl, ⟨_, _, _, hHead1⟩, hr9, hpc6⟩
                    exact Sem.mono hInner5 (fun k s' h => ⟨by have h12 := Nat.mul_le_mul_left 12 hl2; omega, h⟩)
                  · intro k s' h
                    obtain ⟨k5, k6, hk, h1, h2, h3⟩ := h
                    exact ⟨by omega, h3⟩
                exact Sem.mono hInner4 (fun k s' h => ⟨le_trans hk4 hxc, h⟩)
              · intro k s' h
                obtain ⟨k4, k5, hk, h1, h2, h3⟩ := h
                exact ⟨by omega, h3⟩
            exact Sem.mono hInner3 (fun k s' h => ⟨hk3, h⟩)
          · intro k s' h
            obtain ⟨k3, k4, hk, h1, h2, h3⟩ := h
            exact ⟨by omega, h3⟩
        exact Sem.mono hInner2 (fun k s' h => ⟨hk2, h⟩)
      · intro k s' h
        obtain ⟨k2, k3, hk, h1, h2, h3⟩ := h
        exact ⟨by omega, h3⟩
    exact Sem.mono hInner1 (fun k s' h => ⟨hk1, h⟩)
  · intro k s' h
    obtain ⟨k1, k2, hk, h1, h2, h3⟩ := h
    have hcost : decRoundCost N t
        = ((Stmt.code decScanInit).len + (2 + 30 * (cr23D N * cr23M t))) +
          ((Stmt.code decCandInit).len + (2 + 39 * cr23M t) +
            (1 + ((2 + (2 * t + 1) * (cr23D N * 10 + 24)) +
              ((Stmt.code decParInit).len + (2 + 12 * (2 * t + 1)) + decAdvance.length)))) := rfl
    refine ⟨?_, h3⟩
    rw [hcost]; omega
def DecLoopInv (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (j : ℕ) (st : RAMState) : Prop :=
  ∃ z P mst, DecHead1 N t C x z (t / 4 ^ j) (1 + j) P mst st ∧ st.regs r9 = t / 4 ^ j
theorem DecDataN_congr {N t : ℕ} {C : Fin N → Fin (cr23D N) → Fin (cr23M t)}
    {z : Fin N → ZMod 2} {w tag mstLen : ℕ} {P : Finset ℕ} {mst : List ℕ} {s s' : RAMState}
    (hm : s.mem = s'.mem) (h : DecDataN N t C z w tag mstLen P mst s) :
    DecDataN N t C z w tag mstLen P mst s' := by
  unfold DecDataN at h ⊢
  simpa only [hm] using h
theorem DecHead1_congr {N t : ℕ} {C : Fin N → Fin (cr23D N) → Fin (cr23M t)}
    {x z : Fin N → ZMod 2} {w tag : ℕ} {P : Finset ℕ} {mst : List ℕ} {s s' : RAMState}
    (hm : s.mem = s'.mem) (hr : s.regs r14 = s'.regs r14)
    (h : DecHead1 N t C x z w tag P mst s) : DecHead1 N t C x z w tag P mst s' := by
  obtain ⟨⟨hD, h14, hP, hsub, hcap, hcard⟩, hmstN, hpar1⟩ := h
  refine ⟨⟨?_, ?_, hP, hsub, hcap, hcard⟩, hmstN, ?_⟩
  · exact DecDataN_congr hm hD
  · rw [← hr]; exact h14
  · intro v hv; rw [← hm]; exact hpar1 v hv
/-- **The loop rule for `.neqz r`**: `Sem.loopPredLe` with the test-register insensitivity replaced
by program-counter insensitivity (the `neqz` test code is empty). -/
theorem Sem.loopPredLe_neqz (P : Program) (E : RAMEnv) (a : ℕ) (r : Fin 16) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop (Cond.neqz r) b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (R : ℕ → RAMState → Prop) (cost : ℕ → ℕ),
      (∀ (j : ℕ) (s : RAMState) (p : ℕ), R j s → R j { s with pc := p }) →
      (∀ j, j < n → ∀ s, R j s → s.regs r ≠ 0) →
      (∀ s, R n s → s.regs r = 0) →
      (∀ j, j < n → ∀ s, s.pc = a → R j s →
        Sem P E (a + (Cond.neqz r).code.length + 1) a
          { runBlock (Cond.neqz r).code E s with pc := a + (Cond.neqz r).code.length + 1 }
          (fun k s' => k ≤ cost j ∧ R (j + 1) s' ∧ s'.pc = a)) →
      ∀ s, s.pc = a → R 0 s →
        Sem P E a (a + (Cond.neqz r).code.length + b.len + 2) s
          (fun k s' => k ≤ (Cond.neqz r).code.length + 1 +
              ∑ j ∈ Finset.range n, ((Cond.neqz r).code.length + 1 + cost j) ∧
            R n s' ∧ s'.pc = a + (Cond.neqz r).code.length + b.len + 2) := by
  intro n
  induction n with
  | zero =>
      intro R cost hpcirr hgo hstop hstep s hpc hR
      have hne : ¬ (Cond.neqz r).eval s := fun h => h (hstop s hR)
      refine Sem.mono (Sem.loopExit P E a (Cond.neqz r) b s hAt hW hpc hne) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, ?_, rfl⟩
      have h := hpcirr 0 s (a + (Cond.neqz r).code.length + b.len + 2) hR
      simpa only [Cond.code, runBlock_nil] using h
  | succ n ih =>
      intro R cost hpcirr hgo hstop hstep s hpc hR
      have hgo0 : (Cond.neqz r).eval s := hgo 0 (by omega) s hR
      have hfirst := Sem.loopStepPredLe P E a (Cond.neqz r) b s (R 1) (cost 0) hAt hW hpc hgo0
        (hstep 0 (by omega) s hpc hR)
      have hpcirr' : ∀ (j : ℕ) (s : RAMState) (p : ℕ),
          (fun j => R (j + 1)) j s → (fun j => R (j + 1)) j { s with pc := p } :=
        fun j s p h => hpcirr (j + 1) s p h
      have hgo' : ∀ j, j < n → ∀ s, (fun j => R (j + 1)) j s → s.regs r ≠ 0 :=
        fun j hj s h => hgo (j + 1) (by omega) s h
      have hstop' : ∀ s, (fun j => R (j + 1)) n s → s.regs r = 0 :=
        fun s h => hstop s h
      have hstep' : ∀ j, j < n → ∀ s, s.pc = a → (fun j => R (j + 1)) j s →
          Sem P E (a + (Cond.neqz r).code.length + 1) a
            { runBlock (Cond.neqz r).code E s with pc := a + (Cond.neqz r).code.length + 1 }
            (fun k s' => k ≤ (fun j => cost (j + 1)) j ∧
              (fun j => R (j + 1)) (j + 1) s' ∧ s'.pc = a) :=
        fun j hj s hp hs => hstep (j + 1) (by omega) s hp hs
      refine Sem.mono (Sem.seq (Q₁ := fun k s' => k ≤ ((Cond.neqz r).code.length + 1) + cost 0 ∧
          R 1 s' ∧ s'.pc = a)
        (Q₂ := fun k₁ k₂ s' => k₁ ≤ ((Cond.neqz r).code.length + 1) + cost 0 ∧
          (k₂ ≤ ((Cond.neqz r).code.length + 1) +
              ∑ j ∈ Finset.range n, ((Cond.neqz r).code.length + 1 + cost (j + 1)) ∧
            R (n + 1) s' ∧ s'.pc = a + (Cond.neqz r).code.length + b.len + 2)) hfirst ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨hk₁, hR1, hpc1⟩ := hQ₁
        exact Sem.mono (ih (fun j => R (j + 1)) (fun j => cost (j + 1)) hpcirr' hgo' hstop' hstep'
          s₁ hpc1 hR1) (fun k s' h => ⟨hk₁, h⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, hk, h1, h2, h3, h4⟩ := h
        rw [Finset.sum_range_succ']
        exact ⟨by omega, h3, h4⟩
/-- **The round loop**: `Nat.clog 4 (t+1)` rounds, then the failing test on `r9 = w = 0`. -/
theorem decRoundStmt_spec (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (Pgm : Program) (a : ℕ) (hAt : At Pgm a (Stmt.compile decRoundStmt a))
    (st : RAMState) (hpc : st.pc = a)
    (hR : DecHead1 N t C x x t 1 ∅ [] st) (h9 : st.regs r9 = t) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) a
      (a + decRoundBody.len + 2) st
      (fun k s' => k ≤ 1 + Nat.clog 4 (t + 1) * (decRoundCost N t + 2) ∧
        DecLoopInv N t C x (Nat.clog 4 (t + 1)) s' ∧
        s'.pc = a + decRoundBody.len + 2) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set n : ℕ := Nat.clog 4 (t + 1) with hn
  have hW : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hnL : n ≤ cr23Lb N := by
    rw [hn, Nat.clog_le_iff_le_pow (by norm_num : 1 < 4)]
    calc t + 1 ≤ N + 1 := by omega
      _ ≤ 2 ^ cr23Lb N := Nat.le_pow_clog (by norm_num : 1 < 2) (N + 1)
      _ ≤ 4 ^ cr23Lb N := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpcirr : ∀ (j : ℕ) (s : RAMState) (p : ℕ),
      DecLoopInv N t C x j s → DecLoopInv N t C x j { s with pc := p } := by
    intro j s p h
    obtain ⟨z, P, mst, hH, h9'⟩ := h
    exact ⟨z, P, mst, hH, h9'⟩
  have hgo : ∀ j, j < n → ∀ s, DecLoopInv N t C x j s → s.regs r9 ≠ 0 := by
    intro j hj s h
    obtain ⟨z, P, mst, hH, h9'⟩ := h
    rw [h9']
    have hpow : ¬ (t + 1 ≤ 4 ^ j) := by
      intro hp
      have h1 : Nat.clog 4 (t + 1) ≤ j :=
        (Nat.clog_le_iff_le_pow (by norm_num : 1 < 4)).mpr hp
      rw [← hn] at h1
      omega
    have h4j : 4 ^ j ≤ t := by omega
    exact Nat.pos_iff_ne_zero.mp (Nat.div_pos h4j (pow_pos (by norm_num) j))
  have hstop : ∀ s, DecLoopInv N t C x n s → s.regs r9 = 0 := by
    intro s h
    obtain ⟨z, P, mst, hH, h9'⟩ := h
    rw [h9']
    apply Nat.div_eq_of_lt
    have hlt : t < 4 ^ n := by
      have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
      rw [← hn] at h
      omega
    omega
  have hstep : ∀ j, j < n → ∀ s, s.pc = a → DecLoopInv N t C x j s →
      Sem Pgm E (a + (Cond.neqz r9).code.length + 1) a
        { runBlock (Cond.neqz r9).code E s with pc := a + (Cond.neqz r9).code.length + 1 }
        (fun k s' => k ≤ decRoundCost N t + 1 ∧ DecLoopInv N t C x (j + 1) s' ∧ s'.pc = a) := by
    intro j hj s hp hRj
    obtain ⟨z, P, mst, hHead, h9eq⟩ := hRj
    obtain ⟨-, -, hAtBody, hjmp⟩ := at_loop hAt
    have hsup : (cr23Supp z).card ≤ t := by
      obtain ⟨hD, -⟩ := hHead
      obtain ⟨-, -, -, -, hcap, hcard⟩ := hD
      have hdw : t / 4 ^ j ≤ t := Nat.div_le_self _ _
      omega
    have hwW : t / 4 ^ j < 2 ^ cr23Word N :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt htN (cr23N_lt_word N hN))
    have htagW : (1 + j) + 1 < 2 ^ cr23Word N := by
      have h1 : 1 + j + 1 ≤ cr23Lb N + 1 := by omega
      exact lt_of_le_of_lt h1 (cr23_lb1_lt_word N hN)
    have h2tW : 2 * t + 1 < 2 ^ cr23Word N := dec_two_t_lt_word N t hN htN
    refine Sem.jmp_append hjmp ?_
    refine Sem.mono (decRoundBody_spec N t hN ht htN C x z (t / 4 ^ j) (1 + j) P mst eps hexp
      heps Pgm (a + (Cond.neqz r9).code.length + 1) hAtBody
      { runBlock (Cond.neqz r9).code E s with pc := a + (Cond.neqz r9).code.length + 1 }
      rfl hHead h9eq hwW htagW h2tW) ?_
    intro k s' h
    obtain ⟨hk, ⟨z', P', mst', hHead'⟩, hr9, hpc6⟩ := h
    have hw' : (t / 4 ^ j) / 4 = t / 4 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have ht' : 1 + j + 1 = 1 + (j + 1) := by omega
    rw [hw', ht'] at hHead'
    rw [hw'] at hr9
    exact ⟨by omega, ⟨z', P', mst', hHead', hr9⟩, rfl⟩
  have hR0 : DecLoopInv N t C x 0 st := by
    refine ⟨x, ∅, [], ?_, ?_⟩
    · simpa only [pow_zero, Nat.div_one, Nat.add_zero] using hR
    · simpa only [pow_zero, Nat.div_one] using h9
  have hloop := Sem.loopPredLe_neqz Pgm E a r9 decRoundBody hAt hW n (DecLoopInv N t C x)
    (fun _ => decRoundCost N t + 1) hpcirr hgo hstop hstep st hpc hR0
  refine Sem.mono hloop ?_
  intro k s' h
  obtain ⟨hk, hInv, hpc'⟩ := h
  have hsum : (∑ j ∈ Finset.range n, ((Cond.neqz r9).code.length + 1 + (decRoundCost N t + 1)))
      = n * (decRoundCost N t + 2) := by
    have hcl : (Cond.neqz r9).code.length = 0 := rfl
    rw [hcl]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [Nat.cast_id]
    ring
  have hk' : k ≤ 1 + n * (decRoundCost N t + 2) := by
    rw [hsum] at hk
    have hcl2 : (Cond.neqz r9).code.length = 0 := rfl
    rw [hcl2] at hk
    omega
  exact ⟨hk', hInv, hpc'⟩
/-- Outside the fifteen slots, the prologue's store half leaves memory alone. -/
theorem decPreState_mem_out (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0)
    {a : ℕ} (ha : ∀ k < 15, a ≠ decSlot N t k) :
    (decPreState N t C s).mem a = s.mem a := by
  rw [decPreS_data N t hN htN C s h0]
  refine writeList_out s.mem (decSlotList N t) a ?_
  intro p hp hpa
  rw [decSlotList] at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact ha k (List.mem_range.mp hk) hpa.symm
/-- **Every parity cell starts at zero** (it is above the payload and is not a slot). -/
theorem decPreState_par_zero (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (s : RAMState) (h0 : s.regs r0 = 0)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → s.mem a = 0) (v : ℕ) :
    (decPreState N t C s).mem (decParBase N t + v) = 0 := by
  rw [decPreState_mem_out N t hN htN C s h0 (fun k hk => ?_)]
  · exact hzero _ (le_trans (cr23_wordsOf_le_frame N t hN)
      (le_trans (decFrame_le_parBase N t) (dec_le_add_self _ v)))
  · exact ne_of_gt (lt_of_lt_of_le (decSlot_lt_candBase N t hk)
      (le_trans (decCandBase_le_tagBase N t)
        (le_trans (decTagBase_le_mstBase N t)
          (le_trans (decMstBase_le_parBase N t) (dec_le_add_self _ v)))))
/-- **The prologue establishes `DecHead1`** at `(z = x, w = t, tag = 1, P = ∅, mst = [])`. -/
theorem decPrologueDecHead (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t) (s : RAMState) (h0 : s.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      s.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → s.mem a = 0) :
    DecHead1 N t C x x t 1 ∅ [] (decPreState N t C s) := by
  have hD := decPrepare N t hN htN C x s h0 hpay hzero
  have h14D := decPreState_regs14 N t hN htN C s h0
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hD
  have hDN' : DecDataN N t C x t 1 ([] : List ℕ).length (∅ : Finset ℕ) []
      (decPreState N t C s) := by
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ?_, a19⟩
    intro v hv
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ := (a18 v hv).mp h
      exact absurd hi (by simp)
    · intro h
      exact absurd h (by simp)
  refine ⟨⟨hDN', ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact h14D
  · rw [cr23_add_self_eq_zero]
    simp [cr23Supp, cr23NumSet]
  · intro v hv
    simp at hv
  · simp only [List.length_nil]
    omega
  · exact hsup
  · intro v hv
    simp at hv
  · intro v hv
    rw [decPreState_par_zero N t hN htN C s h0 hzero v]
    omega
/-- **The prologue block**, as a `Sem` from `0` to `progDecPre.length`. -/
theorem decPrologue_spec (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2)
    (hsup : (cr23Supp x).card ≤ t) (Pgm : Program) (hAt : At Pgm 0 progDecPre)
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre.length st
      (fun k s' => k = progDecPre.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t) := by
  refine Sem.mono (Sem.block Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 progDecPre st hAt
    progDecPre_noBranch hpc) ?_
  rintro k s' ⟨rfl, rfl⟩
  exact ⟨rfl, decPrologueDecHead N t hN htN C x hsup st h0 hpay hzero,
    decPreState_regs14 N t hN htN C st h0⟩
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
theorem progDecPreC_len : progDecPreC.length = 22 := by decide
theorem progDecPreS_len : progDecPreS.length = 41 := by decide
theorem progDecPre_len : progDecPre.length = 63 := by decide
/-- `decRoundStmt.len`, in terms of the body: the `.neqz` test contributes no code. -/
theorem decRoundStmt_len_form : decRoundStmt.len = decRoundBody.len + 2 := by
  simp [decRoundStmt, Stmt.len, Cond.code]
theorem decEmitStmt_len_form : decEmitStmt.len = 29 := by
  rw [decEmitStmt]
  simp only [Stmt.len, decEmitInit_len, decEmitBody_len, decEmitPost_len, Cond.code,
    List.length_cons, List.length_nil]
theorem decLoadW_noBranch : NoBranch decLoadW := by
  simp [decLoadW, NoBranch]
/-- `decStmt.len`, in terms of its four pieces (definitional). -/
theorem decStmt_len_form : decStmt.len
    = progDecPreC.length + (progDecPreS.length +
        (decLoadW.length + (decRoundStmt.len + decEmitStmt.len))) := rfl
theorem decSlot_seven (N t : ℕ) : decSlot N t 7 = cr23DecFrame N t + 8 := rfl
/-- `decStmt` unfolded once: the `At` split below peels one `Stmt.compile` step at a time, so that no
definitional-equality check ever unfolds a whole `Stmt.compile decStmt 0`. -/
theorem decStmt_eq1 : decStmt = Stmt.seq (Stmt.code progDecPreC)
    (Stmt.seq (Stmt.code progDecPreS)
      (Stmt.seq (Stmt.code decLoadW) (Stmt.seq decRoundStmt decEmitStmt))) := rfl
theorem decLoadW_spec (E : RAMEnv) (st : RAMState) (F : ℕ)
    (hW : 1 < 2 ^ E.W) (h14 : st.regs r14 = F) (hF : F + 8 < 2 ^ E.W) :
    (runBlock decLoadW E st).regs r9 = st.mem (F + 8) % 2 ^ E.W ∧
      (runBlock decLoadW E st).mem = st.mem ∧
      (runBlock decLoadW E st).pc = st.pc + 3 ∧
      (∀ d : Fin 16, d ≠ r9 → d ≠ r15 → (runBlock decLoadW E st).regs d = st.regs d) := by
  have h8 : (8 : ℕ) < 2 ^ E.W := by omega
  have h8' : 8 % 2 ^ E.W = 8 := Nat.mod_eq_of_lt h8
  have hF' : (F + 8) % 2 ^ E.W = F + 8 := Nat.mod_eq_of_lt hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [decLoadW, h14, h8', hF']
  · simp [decLoadW, h14, h8', hF']
  · simp [decLoadW, h14, h8', hF']
  · intro d h9 h15
    simp [decLoadW, h14, h8', hF', h9, h15]
theorem decPar_if_eq (N t : ℕ) (P : Finset ℕ) (s : RAMState)
    (h1 : ∀ v, v < 2 ^ (cr23Lb N + 1) → s.mem (decParBase N t + v) ≤ 1)
    (h2 : ∀ v, v < 2 ^ (cr23Lb N + 1) → (s.mem (decParBase N t + v) = 1 ↔ v ∈ P)) :
    ∀ v, v < 2 ^ (cr23Lb N + 1) → s.mem (decParBase N t + v) = if v ∈ P then 1 else 0 := by
  intro v hv
  have hle := h1 v hv
  by_cases hP : v ∈ P
  · rw [if_pos hP]
    exact (h2 v hv).mpr hP
  · rw [if_neg hP]
    have hne : s.mem (decParBase N t + v) ≠ 1 := fun hc => hP ((h2 v hv).mp hc)
    omega
/-- The cost of the emit pass: `16` initialisation, `≤ 2 + 12·(2t+1)` for the walk, `1` postlude. -/
def decEmitStmtCost (N t : ℕ) : ℕ :=
  decEmitInit.length + (2 + 12 * (2 * t + 1)) + decEmitPost.length
theorem decEmitStmtCost_le (N t : ℕ) (mst : List ℕ) (hcap : mst.length ≤ 2 * t + 1) :
    decEmitInit.length + (2 + 12 * mst.length) + decEmitPost.length ≤ decEmitStmtCost N t := by
  rw [decEmitStmtCost]
  omega
theorem decEmitPost_mem (E : RAMEnv) (st : RAMState) :
    (runBlock decEmitPost E st).mem = st.mem := rfl
theorem decEmitPost_frame (E : RAMEnv) (st : RAMState) (d : Fin 16) (h : d ≠ r0) :
    (runBlock decEmitPost E st).regs d = st.regs d := by
  simp [decEmitPost, h]
/-- The output reading, with the invariant taken on the state *before* the postlude and the
`r0`/`r1`/memory facts taken after it. -/
theorem decEmit_outputsSupport_post (N t : ℕ) (P : Finset ℕ) (mst : List ℕ) (mb : ℕ → ℕ)
    (s1 s : RAMState) (x z : Fin N → ZMod 2)
    (hP : P = cr23NumSet (cr23Supp (x + z))) (hK : cr23Supp z = ∅)
    (hsub : ∀ v, v ∈ P → v ∈ mst)
    (h0 : s.regs r0 = decOutBase N t) (hmem : s.mem = s1.mem) (h1 : s.regs r1 = s1.regs r1)
    (hInv : ∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc mb s1) :
    OutputsSupport s x := by
  obtain ⟨lacc, hnd, hlen, hout, hset⟩ := decEmit_final N t P mst mb s1 hsub hInv
  refine decOutputsSupport_of_mem s x (decOutBase N t) lacc.length lacc h0 ?_ rfl ?_ hnd ?_
  · rw [h1, hlen]
  · intro k hk
    rw [hmem, hout k hk]
  · intro v
    rw [← List.mem_toFinset, hset]
    exact decRounds_final_support x z P hP hK v
/-- **The emit pass, end to end.**  From a round head at `w = 0` (the round loop has stopped) and a
residual of empty support, the pass writes the support of `x` into the output area. -/
theorem decEmitStmt_spec (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState) (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile decEmitStmt a))
    (hpc : st.pc = a) (hw : w = 0)
    (hH : DecHead1 N t C x z w tag P mst st) (hK : cr23Supp z = ∅) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) a (a + decEmitStmt.len) st
      (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x) := by
  subst hw
  obtain ⟨hHead, hmstN, hpar1⟩ := hH
  obtain ⟨hD, h14, hP', hsub, hcap0, hcard⟩ := hHead
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h11s, h12s, h13s, h14s, -, -, hpar, hmst⟩ := hD
  have hcap : mst.length ≤ 2 * t + 1 := by
    have h := hcap0
    omega
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := rfl
  have hpar0 := decPar_if_eq N t P st hpar1 hpar
  have hbel : ∀ b, b < decParBase N t → st.mem b = st.mem b := fun _ _ => rfl
  have hsl11 : st.mem (decSlot N t 11) = decMstBase N t := h11s
  have hsl12 : st.mem (decSlot N t 12) = decParBase N t := h12s
  have hsl13 : st.mem (decSlot N t 13) = decOutBase N t := h13s
  have hsl14 : st.mem (decSlot N t 14) = mst.length := h14s
  -- split the compile: init · (loop · post)
  have hAtAll : At Pgm a (decEmitInit ++ (Stmt.compile
      (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) (a + decEmitInit.length)
        ++ decEmitPost)) := hAt
  obtain ⟨hAtI, hAtAll⟩ := At.append.mp hAtAll
  obtain ⟨hAtL0, hAtP0⟩ := At.append.mp hAtAll
  have hlooplen : (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody))
      (a + decEmitInit.length)).length = 12 := by
    rw [Stmt.length_compile]
    simp only [Stmt.len, Cond.code, decEmitBody_len, List.length_cons, List.length_nil]
  have hAtPost : At Pgm (a + decEmitInit.length + 12) decEmitPost := by
    have h := hAtP0
    rw [hlooplen] at h
    exact h
  -- the initialisation
  have hInitInv : DecEmitInv N t P mst 0 0 [] st.mem (runBlock decEmitInit E st) :=
    decEmitInit_data N t hN htN E hEW P mst st.mem st h14 hbel hsl11 hsl12 hsl13 hsl14 hcap hpar0
  have hInitPc : (runBlock decEmitInit E st).pc = a + decEmitInit.length := by
    rw [runBlock_pc decEmitInit E st decEmitInit_noBranch, hpc]
  -- the walk
  have hLoop := decEmit_loop N t hN htN E hEW P mst st.mem Pgm (a + decEmitInit.length) hAtL0
    hcap hmstN hmst (runBlock decEmitInit E st) hInitPc hInitInv
  have hLoopP : Sem Pgm E (a + decEmitInit.length) (a + decEmitInit.length + 12)
      (runBlock decEmitInit E st)
      (fun k s' => k ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s') ∧
        s'.pc = a + decEmitInit.length + 12) :=
    Sem.mono hLoop (fun k s' h => ⟨h.1, h.2.1, h.2.2⟩)
  -- the postlude
  have hOutW : decOutBase N t < 2 ^ E.W := by
    rw [hEW]; exact dec_out_add_lt_word N t hN htN (j := 0) (by omega)
  have hPostSem : ∀ (s1 : RAMState),
      (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s1) →
      s1.pc = a + decEmitInit.length + 12 →
      Sem Pgm E (a + decEmitInit.length + 12)
        (a + decEmitInit.length + 12 + decEmitPost.length) s1
        (fun k s' => k = decEmitPost.length ∧ s'.regs r0 = decOutBase N t ∧
          s'.mem = s1.mem ∧ s'.regs r1 = s1.regs r1) := by
    intro s1 hInv1 hpc1
    obtain ⟨cnt, lacc, hI1⟩ := hInv1
    obtain ⟨-, -, -, -, -, -, h10, -, -, -, -, -, -, -, -, -⟩ := hI1
    refine Sem.mono (Sem.block Pgm E (a + decEmitInit.length + 12) decEmitPost s1 hAtPost
      decEmitPost_noBranch hpc1) ?_
    rintro k s' ⟨hk, rfl⟩
    exact ⟨hk, decEmitPost_spec E s1 (decOutBase N t) h10 hOutW,
      decEmitPost_mem E s1, decEmitPost_frame E s1 r1 (by decide)⟩
  -- init · (loop · post)
  refine Sem.mono (Sem.seq
    (Q₁ := fun k0 s0 => k0 = decEmitInit.length ∧ s0 = runBlock decEmitInit E st)
    (Q₂ := fun k0 k' s' => ∃ k1 k2, k' = k1 + k2 ∧ k0 = decEmitInit.length ∧
      k1 ≤ 2 + 12 * mst.length ∧ k2 = decEmitPost.length ∧ OutputsSupport s' x)
    (Sem.block Pgm E a decEmitInit st hAtI decEmitInit_noBranch hpc) ?_) ?_
  · intro k0 s0 hQ0
    obtain ⟨hk0, rfl⟩ := hQ0
    refine Sem.seq
      (Q₁ := fun k1 s1 => k1 ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s1) ∧
        s1.pc = a + decEmitInit.length + 12)
      (Q₂ := fun k1 k2 s' => k0 = decEmitInit.length ∧ k1 ≤ 2 + 12 * mst.length ∧
        k2 = decEmitPost.length ∧ OutputsSupport s' x) hLoopP ?_
    intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    refine Sem.mono (hPostSem s1 hInv1 hpc1) (fun k s' hh => ⟨hk0, hk1, hh.1, ?_⟩)
    exact decEmit_outputsSupport_post N t P mst st.mem s1 s' x z hP' hK hsub
      hh.2.1 hh.2.2.1 hh.2.2.2 hInv1
  · rintro k s' ⟨k0, k', hk, k1, k2, hk', h16, hk1, hk2, hout⟩
    refine ⟨?_, hout⟩
    have hle := decEmitStmtCost_le N t mst hcap
    omega
/-- The closed step bound of `decStmt`. -/
def decStmtCost (N t : ℕ) : ℕ :=
  progDecPre.length + 3 + (1 + Nat.clog 4 (t + 1) * (decRoundCost N t + 2)) +
    decEmitStmtCost N t
theorem decStmtCost_le (N t k1 k2 : ℕ)
    (h1 : k1 ≤ 63 + decLoadW.length + (1 + Nat.clog 4 (t + 1) * (decRoundCost N t + 2)))
    (h2 : k2 ≤ decEmitStmtCost N t) : k1 + k2 ≤ decStmtCost N t := by
  rw [decLoadW_len] at h1
  rw [decStmtCost, progDecPre_len]
  omega
/-- `Sem` is insensitive to the spelling of its end address. -/
theorem Sem.end_congr {P : Program} {E : RAMEnv} {a b b' : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} (h : Sem P E a b s Q) (hbb : b = b') : Sem P E a b' s Q := by
  obtain ⟨hpc, k, s', hs, hb, hQ⟩ := h
  exact ⟨hpc, k, s', hs, hbb ▸ hb, hQ⟩
/-- Add the program counter to a `Sem` postcondition. -/
theorem Sem.add_pc {P : Program} {E : RAMEnv} {a b : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} (h : Sem P E a b s Q) :
    Sem P E a b s (fun k s' => Q k s' ∧ s'.pc = b) := by
  obtain ⟨hpc, k, s', hs, hb, hQ⟩ := h
  exact ⟨hpc, k, s', hs, hb, hQ, hb⟩
/-- **The decoder, end to end.** -/
theorem decStmt_sem (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (Pgm : Program) (hAt : At Pgm 0 (Stmt.compile decStmt 0))
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len st
      (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set n : ℕ := Nat.clog 4 (t + 1) with hn
  -- the compile, peeled one `Stmt.compile` step at a time
  have h1 : At Pgm 0 (Stmt.compile decStmt 0) := hAt
  rw [decStmt_eq1] at h1
  obtain ⟨hAtC0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreC_len, Nat.zero_add] at h1
  obtain ⟨hAtS0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreS_len, Nat.zero_add] at h1
  obtain ⟨hAtL0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, decLoadW_len, Nat.zero_add] at h1
  obtain ⟨hAtR, hAtE0⟩ := At.append.mp h1
  have hAtC : At Pgm 0 progDecPreC := hAtC0
  have hAtS : At Pgm 22 progDecPreS := hAtS0
  have hAtL63 : At Pgm 63 decLoadW := hAtL0
  have hAtPre : At Pgm 0 progDecPre := by
    rw [progDecPre]
    exact At.append.mpr ⟨hAtC, hAtS⟩
  have hpre : progDecPre.length = 63 := progDecPre_len
  have hAtE : At Pgm (66 + decRoundBody.len + 2)
      (Stmt.compile decEmitStmt (66 + decRoundBody.len + 2)) := by
    have h := hAtE0
    simp only [Stmt.length_compile, decRoundStmt_len_form, Nat.zero_add] at h
    exact h
  have hW1 : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hF8 : cr23DecFrame N t + 8 < 2 ^ E.W := by
    rw [hE]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have htW : t < 2 ^ E.W := by
    rw [hE]; exact lt_of_le_of_lt htN (cr23N_lt_word N hN)
  -- leg 1: the prologue
  have hProl : Sem Pgm E 0 63 st
      (fun k s' => (k = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t) ∧ s'.pc = 63) := by
    have h := decPrologue_spec N t hN htN C x hsup Pgm hAtPre st hpc h0 hpay hzero
    rw [hpre] at h
    exact Sem.add_pc h
  -- leg 2: the counter reload
  have hL2 : ∀ (s1 : RAMState), s1.pc = 63 → DecHead1 N t C x x t 1 ∅ [] s1 →
      s1.regs r14 = cr23DecFrame N t →
      Sem Pgm E 63 66 s1
        (fun k s' => k = decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
          s'.regs r9 = t ∧ s'.pc = 66) := by
    intro s1 hpc1 hH1 h141
    have hblk := Sem.block Pgm E 63 decLoadW s1 hAtL63 decLoadW_noBranch hpc1
    have hspec := decLoadW_spec E s1 (cr23DecFrame N t) hW1 h141 hF8
    obtain ⟨h9, hmem, hpc3, hframe⟩ := hspec
    have h7 : s1.mem (cr23DecFrame N t + 8) = t := by
      obtain ⟨hD0, -, -⟩ := hH1
      obtain ⟨hD1, -, -, -, -, -⟩ := hD0
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19⟩ := hD1
      have h := a8
      rwa [decSlot_seven] at h
    have h9' : (runBlock decLoadW E s1).regs r9 = t := by
      rw [h9, h7, Nat.mod_eq_of_lt htW]
    have hH1' : DecHead1 N t C x x t 1 ∅ [] (runBlock decLoadW E s1) :=
      DecHead1_congr hmem.symm (hframe r14 (by decide) (by decide)).symm hH1
    refine Sem.mono hblk (fun k s' hh => ?_)
    obtain ⟨hk, rfl⟩ := hh
    exact ⟨hk, hH1', h9', by rw [hpc3, hpc1]⟩
  -- leg 3: the round loop
  have hL3 : ∀ (s2 : RAMState), s2.pc = 66 → DecHead1 N t C x x t 1 ∅ [] s2 →
      s2.regs r9 = t →
      Sem Pgm E 66 (66 + decRoundBody.len + 2) s2
        (fun k s' => k ≤ 1 + n * (decRoundCost N t + 2) ∧
          DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    intro s2 hpc2 hH2 h92
    exact decRoundStmt_spec N t hN ht htN C x eps hexp heps Pgm 66 hAtR s2 hpc2 hH2 h92
  -- leg 4: the emit pass
  have hw0 : t / 4 ^ n = 0 := by
    rw [hn]
    refine Nat.div_eq_of_lt ?_
    have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
    omega
  have hL4 : ∀ (s3 : RAMState), s3.pc = (66 + decRoundBody.len + 2) →
      DecLoopInv N t C x n s3 →
      Sem Pgm E (66 + decRoundBody.len + 2)
        (66 + decRoundBody.len + 2 + decEmitStmt.len) s3
        (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x) := by
    intro s3 hpc3 hInv
    obtain ⟨z, P, mst, hH3, -⟩ := hInv
    rw [hw0] at hH3
    have hH3' := hH3
    obtain ⟨⟨-, -, -, -, -, hwc⟩, -, -⟩ := hH3'
    have hK : cr23Supp z = ∅ := Finset.card_eq_zero.mp (by omega)
    exact decEmitStmt_spec N t hN htN C x z 0 (1 + n) P mst s3 Pgm (66 + decRoundBody.len + 2)
      hAtE hpc3 rfl hH3 hK
  -- 1 · 2
  have h12 : Sem Pgm E 0 66 st
      (fun k s' => k = 63 + decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r9 = t ∧ s'.pc = 66) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => (k1 = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s1 ∧
        s1.regs r14 = cr23DecFrame N t) ∧ s1.pc = 63)
      (Q₂ := fun k1 k2 s' => k1 = 63 ∧ k2 = decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s' ∧ s'.regs r9 = t ∧ s'.pc = 66) hProl ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨⟨hk1, hH1, h141⟩, hpc1⟩ := hQ1
      exact Sem.mono (hL2 s1 hpc1 hH1 h141)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩
      exact ⟨by omega, h3, h4, h5⟩
  -- (1 · 2) · 3
  have h123 : Sem Pgm E 0 (66 + decRoundBody.len + 2) st
      (fun k s' => k ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
        DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => k1 = 63 + decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s1 ∧ s1.regs r9 = t ∧ s1.pc = 66)
      (Q₂ := fun k1 k2 s' => k1 = 63 + decLoadW.length ∧
        k2 ≤ 1 + n * (decRoundCost N t + 2) ∧ DecLoopInv N t C x n s' ∧
        s'.pc = (66 + decRoundBody.len + 2)) h12 ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨hk1, hH1, h91, hpc1⟩ := hQ1
      exact Sem.mono (hL3 s1 hpc1 hH1 h91)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
      exact ⟨by omega, h3, h4⟩
  -- everything
  have htotal : (66 + decRoundBody.len + 2 + decEmitStmt.len) = decStmt.len := by
    rw [decStmt_len_form, progDecPreC_len, progDecPreS_len, decLoadW_len, decRoundStmt_len_form,
      decEmitStmt_len_form]
    omega
  refine Sem.end_congr (Sem.mono (Sem.seq
    (Q₁ := fun k1 s1 => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      DecLoopInv N t C x n s1 ∧ s1.pc = (66 + decRoundBody.len + 2))
    (Q₂ := fun k1 k2 s' => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      k2 ≤ decEmitStmtCost N t ∧ OutputsSupport s' x) h123 ?_) ?_) htotal
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    exact Sem.mono (hL4 s1 hpc1 hInv1) (fun k s' hh => ⟨hk1, hh.1, hh.2⟩)
  · rintro k s' ⟨k1, k2, hk, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have hle := decStmtCost_le N t k1 k2 h1 h2
    omega
theorem decoderStart_cr23_pc (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) :
    (decoderStart (cr23Word N) (cr23Sketch N t C x) ([] : List ℕ)).pc = 0 := rfl
theorem decoderStart_cr23_r0 (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) :
    (decoderStart (cr23Word N) (cr23Sketch N t C x) ([] : List ℕ)).regs r0 = 0 := by
  simp [decoderStart, initState]
theorem decoderStart_cr23_pay (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) :
    ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      (decoderStart (cr23Word N) (cr23Sketch N t C x) ([] : List ℕ)).mem a
        = packMem (cr23Word N) (cr23Sketch N t C x) a := by
  intro a ha
  simp [decoderStart, initState, hintMem, ha]
theorem decoderStart_cr23_zero (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (x : Fin N → ZMod 2) :
    ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a →
      (decoderStart (cr23Word N) (cr23Sketch N t C x) ([] : List ℕ)).mem a = 0 := by
  intro a ha
  simp [decoderStart, initState, hintMem, Nat.not_lt.mpr ha]
theorem progDec_at_main : At progDec 0 (Stmt.compile decStmt 0) := by
  have h : At progDec 0 (Stmt.compile decStmt 0 ++ [iHalt]) := At.self progDec
  exact (At.append.mp h).1
theorem progDec_at_halt : progDec[decStmt.len]? = some iHalt := by
  have hlen : (Stmt.compile decStmt 0).length = decStmt.len := Stmt.length_compile _ _
  have h : progDec = Stmt.compile decStmt 0 ++ [iHalt] := rfl
  rw [h, List.getElem?_append_right (by rw [hlen])]
  have h0 : decStmt.len - (Stmt.compile decStmt 0).length = 0 := by
    rw [hlen]; exact Nat.sub_self _
  rw [h0]
  rfl
/-- **Proposition 2.3's decoding conjunct, at the explicit cost `decStmtCost + 1`.** -/
theorem decStmt_halts (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1)
        (decoderStart (cr23Word N) (cr23Sketch N t C x) []) s' ∧
        OutputsSupport s' x := by
  have hsem := decStmt_sem N t hN ht htN C x eps hexp heps hsup progDec progDec_at_main
    (decoderStart (cr23Word N) (cr23Sketch N t C x) [])
    (decoderStart_cr23_pc N t C x) (decoderStart_cr23_r0 N t C x)
    (decoderStart_cr23_pay N t C x) (decoderStart_cr23_zero N t C x)
  refine halts_of_run progDec (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len
    (decoderStart (cr23Word N) (cr23Sketch N t C x) [])
    ((decStmtCost N t : ℝ) + 1)
    (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x)
    (fun s' => OutputsSupport s' x) progDec_at_halt hsem ?_
  rintro k s' ⟨hk, hout⟩
  refine ⟨?_, hout⟩
  have hk' : (k : ℝ) ≤ (decStmtCost N t : ℝ) := by exact_mod_cast hk
  linarith
/-- `⌈log₂ m⌉ ≤ log₂ m + 1` for `m ≥ 2` (`Nat.pow_pred_clog_lt_self` + monotonicity of `logb`). -/
theorem decClog_two_le_lg {m : ℕ} (hm : 2 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ lg (m : ℝ) + 1 := by
  have hb : 1 < 2 := by norm_num
  have hk : 0 < Nat.clog 2 m := Nat.clog_pos hb (by omega)
  have h1 : 2 ^ (Nat.clog 2 m).pred < m := Nat.pow_pred_clog_lt_self hb (by omega)
  have hcast : ((2 ^ (Nat.clog 2 m).pred : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.clog 2 m).pred := by
    push_cast
    ring
  have h2 : (2 : ℝ) ^ (Nat.clog 2 m).pred < (m : ℝ) := by
    rw [← hcast]
    exact_mod_cast h1
  have h3 : lg ((2 : ℝ) ^ (Nat.clog 2 m).pred) < lg (m : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by positivity) h2
  have h3' : ((Nat.clog 2 m).pred : ℝ) < lg (m : ℝ) := by
    have h := h3
    rw [lg, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    exact h
  have h4 : ((Nat.clog 2 m).pred : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub hk, Nat.cast_one]
  rw [h4] at h3'
  linarith
/-- `lg` of a natural at least `2` is at least `1`. -/
theorem decOne_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ lg (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hn : (2 : ℝ) ≤ (n : ℝ))
  have h2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  rw [h2] at h
  exact h
theorem cr23Lb_le_lg_add_one (N : ℕ) (hN : 1 ≤ N) :
    (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := by
  have h := decClog_two_le_lg (m := N + 1) (by omega)
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  have hmono : lg ((N : ℝ) + 1) ≤ lg ((N : ℝ) + 2) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (by linarith)
  show (Nat.clog 2 (N + 1) : ℝ) ≤ lg ((N : ℝ) + 2) + 1
  linarith
/-- `clog 4 (t+1) ≤ lg (t+2)` for `t ≥ 1`. -/
theorem decClog_four_le_lg {t : ℕ} (ht : 1 ≤ t) :
    (Nat.clog 4 (t + 1) : ℝ) ≤ lg ((t : ℝ) + 2) := by
  have hb : 1 < 4 := by norm_num
  have hk : 0 < Nat.clog 4 (t + 1) := Nat.clog_pos hb (by omega)
  have h1 : 4 ^ (Nat.clog 4 (t + 1)).pred < t + 1 := Nat.pow_pred_clog_lt_self hb (by omega)
  have hcast : ((4 ^ (Nat.clog 4 (t + 1)).pred : ℕ) : ℝ) = (4 : ℝ) ^ (Nat.clog 4 (t + 1)).pred := by
    push_cast
    ring
  have h2 : (4 : ℝ) ^ (Nat.clog 4 (t + 1)).pred < ((t : ℝ) + 1) := by
    rw [← hcast]
    have ht1 : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    rw [← ht1]
    exact_mod_cast h1
  have h3 : lg ((4 : ℝ) ^ (Nat.clog 4 (t + 1)).pred) < lg ((t : ℝ) + 1) :=
    Real.logb_lt_logb (by norm_num) (by positivity) h2
  have h4 : lg ((4 : ℝ) ^ (Nat.clog 4 (t + 1)).pred)
      = 2 * ((Nat.clog 4 (t + 1)).pred : ℝ) := by
    rw [lg, Real.logb_pow]
    have h44 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h44]
    ring
  rw [h4] at h3
  have h5 : ((Nat.clog 4 (t + 1)).pred : ℝ) = (Nat.clog 4 (t + 1) : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub hk, Nat.cast_one]
  rw [h5] at h3
  have h6 : lg ((t : ℝ) + 1) ≤ lg ((t : ℝ) + 2) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (by linarith)
  by_cases hcase : (2 : ℝ) ≤ lg ((t : ℝ) + 2)
  · linarith
  · push Not at hcase
    have ht1 : t = 1 := by
      have hlt : ((t : ℝ) + 2) < 4 := by
        by_contra hc
        push Not at hc
        have h4' : Real.logb 2 (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          norm_num
        have hle := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hc
        rw [h4'] at hle
        have hle2 : (2 : ℝ) ≤ lg ((t : ℝ) + 2) := hle
        linarith
      have hlt2 : (t : ℝ) < 2 := by linarith
      have hlt2' : t < 2 := by exact_mod_cast hlt2
      omega
    subst ht1
    have hval : Nat.clog 4 (1 + 1) = 1 := by decide
    rw [hval]
    have h3' : (1 : ℝ) ≤ lg ((3 : ℕ) : ℝ) := decOne_le_lg (by norm_num)
    norm_num at h3' ⊢
    exact h3'
/-- **The step bound, expanded** (all lengths at their numerals). -/
theorem decStmtCost_nat_le (N t : ℕ) :
    decStmtCost N t = 86 + Nat.clog 4 (t + 1) *
      (81 + 30 * (cr23D N * cr23M t) + 39 * cr23M t +
        (2 * t + 1) * (10 * cr23D N + 24) + 12 * (2 * t + 1)) +
      12 * (2 * t + 1) := by
  simp only [decStmtCost, decEmitStmtCost, decRoundCost, Stmt.len, progDecPre_len,
    decAdvance_len, decEmitInit_len, decEmitPost_len, decScanInit_len, decCandInit_len,
    decParInit_len]
  ring
/-- **The step bound as a real inequality.** -/
theorem decStmtCost_real_le (N t : ℕ) :
    (decStmtCost N t : ℝ) + 1 ≤ 87 + 12 * (2 * (t : ℝ) + 1) +
      (Nat.clog 4 (t + 1) : ℝ) *
        (81 + 30 * ((cr23D N : ℝ) * (cr23M t : ℝ)) + 39 * (cr23M t : ℝ) +
          (2 * (t : ℝ) + 1) * (10 * (cr23D N : ℝ) + 24) + 12 * (2 * (t : ℝ) + 1)) := by
  have h := decStmtCost_nat_le N t
  have h' : ((decStmtCost N t : ℕ) : ℝ) ≤
      ((86 + Nat.clog 4 (t + 1) * (81 + 30 * (cr23D N * cr23M t) + 39 * cr23M t +
        (2 * t + 1) * (10 * cr23D N + 24) + 12 * (2 * t + 1)) +
        12 * (2 * t + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_of_eq h
  push_cast at h'
  linarith
/-- **`K = 2^85` suffices.** -/
theorem decStmtCost_le_K (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) :
    (decStmtCost N t : ℝ) + 1 ≤
      (2 : ℝ) ^ 85 * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) := by
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hT2 : (2 : ℝ) ≤ (t : ℝ) + 2 := by linarith
  have hN1 : (1 : ℝ) ≤ lg ((N : ℝ) + 2) := by
    have h := decOne_le_lg (n := N + 2) (by omega)
    push_cast at h
    exact h
  have hT1 : (1 : ℝ) ≤ lg ((t : ℝ) + 2) := by
    have h := decOne_le_lg (n := t + 2) (by omega)
    push_cast at h
    exact h
  have hN0 : (0 : ℝ) < lg ((N : ℝ) + 2) := by linarith
  have hT0 : (0 : ℝ) < lg ((t : ℝ) + 2) := by linarith
  have hlb : (cr23Lb N : ℝ) ≤ lg ((N : ℝ) + 2) + 1 := cr23Lb_le_lg_add_one N hN
  have hn : (Nat.clog 4 (t + 1) : ℝ) ≤ lg ((t : ℝ) + 2) := decClog_four_le_lg ht
  have hn0 : (0 : ℝ) ≤ (Nat.clog 4 (t + 1) : ℝ) := by positivity
  -- monotonicity of the bound in `t`
  have hmono1 : (t : ℝ) ≤ (t : ℝ) * lg ((t : ℝ) + 2) := by
    calc (t : ℝ) = (t : ℝ) * 1 := by ring
      _ ≤ (t : ℝ) * lg ((t : ℝ) + 2) := mul_le_mul_of_nonneg_left hT1 ht0
  have hmono2 : (t : ℝ) ≤ (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    calc (t : ℝ) ≤ (t : ℝ) * lg ((t : ℝ) + 2) := hmono1
      _ = ((t : ℝ) * lg ((t : ℝ) + 2)) * 1 := by ring
      _ ≤ ((t : ℝ) * lg ((t : ℝ) + 2)) * lg ((N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hN1 (by positivity)
  have hTle : lg ((t : ℝ) + 2) ≤ (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    have h1 : lg ((t : ℝ) + 2) ≤ (t : ℝ) * lg ((t : ℝ) + 2) := by
      calc lg ((t : ℝ) + 2) = 1 * lg ((t : ℝ) + 2) := by ring
        _ ≤ (t : ℝ) * lg ((t : ℝ) + 2) := mul_le_mul_of_nonneg_right htR hT0.le
    calc lg ((t : ℝ) + 2) ≤ (t : ℝ) * lg ((t : ℝ) + 2) := h1
      _ = ((t : ℝ) * lg ((t : ℝ) + 2)) * 1 := by ring
      _ ≤ ((t : ℝ) * lg ((t : ℝ) + 2)) * lg ((N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hN1 (by positivity)
  -- the monomial bounds
  have hp1 : (Nat.clog 4 (t + 1) : ℝ) * (cr23Lb N : ℝ)
      ≤ 2 * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    have h1 : (Nat.clog 4 (t + 1) : ℝ) * (cr23Lb N : ℝ)
        ≤ lg ((t : ℝ) + 2) * (lg ((N : ℝ) + 2) + 1) :=
      mul_le_mul hn hlb (by linarith) (by linarith)
    have h2 : lg ((t : ℝ) + 2) * (lg ((N : ℝ) + 2) + 1)
        ≤ 2 * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
      have h5 : lg ((N : ℝ) + 2) + 1 ≤ 2 * lg ((N : ℝ) + 2) := by linarith
      calc lg ((t : ℝ) + 2) * (lg ((N : ℝ) + 2) + 1)
          ≤ lg ((t : ℝ) + 2) * (2 * lg ((N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left h5 hT0.le
        _ = 2 * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by ring
    exact le_trans h1 h2
  have hA : (Nat.clog 4 (t + 1) : ℝ) * (t : ℝ) * (cr23Lb N : ℝ)
      ≤ 2 * (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    have h := mul_le_mul_of_nonneg_right hp1 ht0
    nlinarith [h]
  have hB : (Nat.clog 4 (t + 1) : ℝ) * (t : ℝ) ≤ (t : ℝ) * lg ((t : ℝ) + 2) := by
    have h := mul_le_mul_of_nonneg_right hn ht0
    linarith
  have hD : (Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1)
      ≤ 3 * (t : ℝ) * lg ((t : ℝ) + 2) := by
    have h1 : (2 * (t : ℝ) + 1) ≤ 3 * (t : ℝ) := by linarith
    have h := mul_le_mul hn h1 (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ) + 1) (by linarith)
    nlinarith [h]
  have hC : (Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1) * (cr23Lb N : ℝ)
      ≤ 6 * (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    have h2 : (Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1) * (cr23Lb N : ℝ)
        ≤ (3 * (t : ℝ) * lg ((t : ℝ) + 2)) * (lg ((N : ℝ) + 2) + 1) :=
      mul_le_mul hD hlb (by linarith) (by positivity)
    have h3 : (3 * (t : ℝ) * lg ((t : ℝ) + 2)) * (lg ((N : ℝ) + 2) + 1)
        ≤ 6 * (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
      have h5 : lg ((N : ℝ) + 2) + 1 ≤ 2 * lg ((N : ℝ) + 2) := by linarith
      have h4 : (0 : ℝ) ≤ 3 * (t : ℝ) * lg ((t : ℝ) + 2) := by positivity
      calc (3 * (t : ℝ) * lg ((t : ℝ) + 2)) * (lg ((N : ℝ) + 2) + 1)
          ≤ (3 * (t : ℝ) * lg ((t : ℝ) + 2)) * (2 * lg ((N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left h5 h4
        _ = 6 * (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by ring
    exact le_trans h2 h3
  have hmax : max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2))
      = (t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2) := by
    refine max_eq_right ?_
    exact le_trans htR hmono2
  rw [hmax]
  have hcost := decStmtCost_real_le N t
  have hD' : (cr23D N : ℝ) = 1024 * (cr23Lb N : ℝ) := by
    rw [cr23D]; push_cast; ring
  have hM' : (cr23M t : ℝ) = 2 ^ 68 * (t : ℝ) := by
    rw [cr23M]; push_cast; ring
  have h68 : ((2 : ℝ) ^ 68) = 295147905179352825856 := by norm_num
  rw [hD', hM', h68] at hcost
  -- expand the cost into the monomials
  have hexp : (decStmtCost N t : ℝ) + 1 ≤ 87 + 12 * (2 * (t : ℝ) + 1)
      + 81 * (Nat.clog 4 (t + 1) : ℝ)
      + 9066943647109718810296320 * ((Nat.clog 4 (t + 1) : ℝ) * (t : ℝ) * (cr23Lb N : ℝ))
      + 11510768301994760208384 * ((Nat.clog 4 (t + 1) : ℝ) * (t : ℝ))
      + 10240 * ((Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1) * (cr23Lb N : ℝ))
      + 36 * ((Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1)) := by
    nlinarith [hcost]
  have hfinal : 87 + 12 * (2 * (t : ℝ) + 1)
      + 81 * (Nat.clog 4 (t + 1) : ℝ)
      + 9066943647109718810296320 * ((Nat.clog 4 (t + 1) : ℝ) * (t : ℝ) * (cr23Lb N : ℝ))
      + 11510768301994760208384 * ((Nat.clog 4 (t + 1) : ℝ) * (t : ℝ))
      + 10240 * ((Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1) * (cr23Lb N : ℝ))
      + 36 * ((Nat.clog 4 (t + 1) : ℝ) * (2 * (t : ℝ) + 1))
      ≤ 18145398062521432380862776 * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) := by
    nlinarith [hA, hB, hC, hD, hn, hmono2, hTle, hN1, hT1, htR]
  refine le_trans (le_trans hexp hfinal) ?_
  have : (18145398062521432380862776 : ℝ) ≤ 2 ^ 85 := by norm_num
  calc (18145398062521432380862776 : ℝ) * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2))
      ≤ 2 ^ 85 * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = 2 ^ 85 * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) := rfl
/-- **Proposition 2.3's decoding conjunct**, with `K = 2 ^ 85`. -/
theorem cr23_decoding_proof (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1) :
    ∀ x : Fin N → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ t →
      ∃ s' : RAMState,
        HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
          ((2 : ℝ) ^ 85 * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)))
          (decoderStart (cr23Word N) (cr23Sketch N t C x) []) s' ∧
          OutputsSupport s' x := by
  intro x hx
  obtain ⟨s', hhalt, hout⟩ :=
    decStmt_halts N t hN ht htN C x eps hexp heps hx
  refine ⟨s', ?_, hout⟩
  obtain ⟨k, hk, hstep, hstop⟩ := hhalt
  exact ⟨k, le_trans hk (decStmtCost_le_K N t hN ht htN), hstep, hstop⟩
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option maxRecDepth 8000
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
end LinearSetReconciliation327.Main
open LinearSetReconciliation327.Main in
theorem solution (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1) :
    ∀ x : Fin N → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ t →
      ∃ s' : RAMState,
        HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
          ((2 : ℝ) ^ 85 * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)))
          (decoderStart (cr23Word N) (cr23Sketch N t C x) []) s' ∧
          OutputsSupport s' x :=
  cr23_decoding_proof N t hN ht htN C eps hexp heps
