-- Prove2me | solution 1 for NSWApxHard.Reduction.reduction_encode_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T08:50:13.323928+00:00
-- url     : https://prove2.me/submissions/1b547067-ba7a-4d23-be55-affe9b19b859

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare
import Definitions.Def_NSWApxHard_Reduction_CubicVC
import Definitions.Def_NSWApxHard_Reduction_Instance

set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

inductive Key
  | inp | out | D | Bn | F | Nu | sc | T | Q | A | U | UA | Ts | Ec | Kk | AN | R | E1 | E2 | C1 | C2 | Nn | Mm | Bnn | Bnm | X | X2 | Y | Z | Cy | O | Vd | Vr | OH | CF | RF | S1 | Ed | Er | Wa | Wb
  deriving DecidableEq

instance : Fintype Key :=
  ⟨⟨([.inp, .out, .D, .Bn, .F, .Nu, .sc, .T, .Q, .A, .U, .UA, .Ts, .Ec, .Kk, .AN, .R, .E1, .E2, .C1, .C2, .Nn, .Mm, .Bnn, .Bnm, .X, .X2, .Y, .Z, .Cy, .O, .Vd, .Vr, .OH, .CF, .RF, .S1, .Ed, .Er, .Wa, .Wb] : List Key), by decide⟩, by intro x; cases x <;> decide⟩

structure Regs where
  inp : List Bool
  out : List Bool
  D : List Bool
  Bn : List Bool
  F : List Bool
  Nu : List Bool
  sc : List Bool
  T : List Bool
  Q : List Bool
  A : List Bool
  U : List Bool
  UA : List Bool
  Ts : List Bool
  Ec : List Bool
  Kk : List Bool
  AN : List Bool
  R : List Bool
  E1 : List Bool
  E2 : List Bool
  C1 : List Bool
  C2 : List Bool
  Nn : List Bool
  Mm : List Bool
  Bnn : List Bool
  Bnm : List Bool
  X : List Bool
  X2 : List Bool
  Y : List Bool
  Z : List Bool
  Cy : List Bool
  O : List Bool
  Vd : List Bool
  Vr : List Bool
  OH : List Bool
  CF : List Bool
  RF : List Bool
  S1 : List Bool
  Ed : List Bool
  Er : List Bool
  Wa : List Bool
  Wb : List Bool

namespace Regs

def get (σ : Regs) : Key → List Bool
  | .inp => σ.inp
  | .out => σ.out
  | .D => σ.D
  | .Bn => σ.Bn
  | .F => σ.F
  | .Nu => σ.Nu
  | .sc => σ.sc
  | .T => σ.T
  | .Q => σ.Q
  | .A => σ.A
  | .U => σ.U
  | .UA => σ.UA
  | .Ts => σ.Ts
  | .Ec => σ.Ec
  | .Kk => σ.Kk
  | .AN => σ.AN
  | .R => σ.R
  | .E1 => σ.E1
  | .E2 => σ.E2
  | .C1 => σ.C1
  | .C2 => σ.C2
  | .Nn => σ.Nn
  | .Mm => σ.Mm
  | .Bnn => σ.Bnn
  | .Bnm => σ.Bnm
  | .X => σ.X
  | .X2 => σ.X2
  | .Y => σ.Y
  | .Z => σ.Z
  | .Cy => σ.Cy
  | .O => σ.O
  | .Vd => σ.Vd
  | .Vr => σ.Vr
  | .OH => σ.OH
  | .CF => σ.CF
  | .RF => σ.RF
  | .S1 => σ.S1
  | .Ed => σ.Ed
  | .Er => σ.Er
  | .Wa => σ.Wa
  | .Wb => σ.Wb

def set (σ : Regs) : Key → List Bool → Regs
  | .inp, l => { σ with inp := l }
  | .out, l => { σ with out := l }
  | .D, l => { σ with D := l }
  | .Bn, l => { σ with Bn := l }
  | .F, l => { σ with F := l }
  | .Nu, l => { σ with Nu := l }
  | .sc, l => { σ with sc := l }
  | .T, l => { σ with T := l }
  | .Q, l => { σ with Q := l }
  | .A, l => { σ with A := l }
  | .U, l => { σ with U := l }
  | .UA, l => { σ with UA := l }
  | .Ts, l => { σ with Ts := l }
  | .Ec, l => { σ with Ec := l }
  | .Kk, l => { σ with Kk := l }
  | .AN, l => { σ with AN := l }
  | .R, l => { σ with R := l }
  | .E1, l => { σ with E1 := l }
  | .E2, l => { σ with E2 := l }
  | .C1, l => { σ with C1 := l }
  | .C2, l => { σ with C2 := l }
  | .Nn, l => { σ with Nn := l }
  | .Mm, l => { σ with Mm := l }
  | .Bnn, l => { σ with Bnn := l }
  | .Bnm, l => { σ with Bnm := l }
  | .X, l => { σ with X := l }
  | .X2, l => { σ with X2 := l }
  | .Y, l => { σ with Y := l }
  | .Z, l => { σ with Z := l }
  | .Cy, l => { σ with Cy := l }
  | .O, l => { σ with O := l }
  | .Vd, l => { σ with Vd := l }
  | .Vr, l => { σ with Vr := l }
  | .OH, l => { σ with OH := l }
  | .CF, l => { σ with CF := l }
  | .RF, l => { σ with RF := l }
  | .S1, l => { σ with S1 := l }
  | .Ed, l => { σ with Ed := l }
  | .Er, l => { σ with Er := l }
  | .Wa, l => { σ with Wa := l }
  | .Wb, l => { σ with Wb := l }

lemma get_set (σ : Regs) (k j : Key) (l : List Bool) :
    (σ.set k l).get j = if j = k then l else σ.get j := by
  cases k <;> cases j <;> rfl

lemma update_get (σ : Regs) (k : Key) (l : List Bool) :
    Function.update σ.get k l = (σ.set k l).get := by
  funext j
  rw [get_set, Function.update_apply]

@[simp] lemma get_set_self (σ : Regs) (k : Key) (l : List Bool) : (σ.set k l).get k = l := by
  simp [get_set]

lemma get_set_ne (σ : Regs) {k j : Key} (h : j ≠ k) (l : List Bool) : (σ.set k l).get j = σ.get j := by
  simp [get_set, h]

lemma ext_get {σ τ : Regs} (h : σ.get = τ.get) : σ = τ := by
  cases σ; cases τ
  simp only [Regs.mk.injEq]
  exact ⟨congrFun h .inp, congrFun h .out, congrFun h .D, congrFun h .Bn, congrFun h .F, congrFun h .Nu, congrFun h .sc, congrFun h .T, congrFun h .Q, congrFun h .A, congrFun h .U, congrFun h .UA, congrFun h .Ts, congrFun h .Ec, congrFun h .Kk, congrFun h .AN, congrFun h .R, congrFun h .E1, congrFun h .E2, congrFun h .C1, congrFun h .C2, congrFun h .Nn, congrFun h .Mm, congrFun h .Bnn, congrFun h .Bnm, congrFun h .X, congrFun h .X2, congrFun h .Y, congrFun h .Z, congrFun h .Cy, congrFun h .O, congrFun h .Vd, congrFun h .Vr, congrFun h .OH, congrFun h .CF, congrFun h .RF, congrFun h .S1, congrFun h .Ed, congrFun h .Er, congrFun h .Wa, congrFun h .Wb⟩

lemma set_get (σ : Regs) (k : Key) : σ.set k (σ.get k) = σ := by
  cases k <;> rfl

end Regs

def Regs.empty : Regs :=
  ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩


abbrev Prog := StackProg Key Bool

/-- the tops of a register file -/
def hd (σ : Regs) : Key → Option Bool := fun k => (σ.get k).head?

/-- `p` runs from `σ` to `τ` within `B` steps. -/
def Runs (p : Prog) (σ τ : Regs) (B : ℕ) : Prop := ∃ n ≤ B, p.Exec σ.get τ.get n

/-! ## Combinators -/

lemma Runs.mono {p : Prog} {σ τ : Regs} {B B' : ℕ} (h : Runs p σ τ B) (hB : B ≤ B') :
    Runs p σ τ B' := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨n, le_trans hn hB, e⟩

lemma Runs.congr {p : Prog} {σ τ τ' : Regs} {B : ℕ} (h : Runs p σ τ B) (e : τ = τ') :
    Runs p σ τ' B := e ▸ h

lemma Runs.seq {p q : Prog} {σ τ υ : Regs} {B1 B2 : ℕ} (h1 : Runs p σ τ B1)
    (h2 : Runs q τ υ B2) : Runs (.seq p q) σ υ (B1 + 1 + B2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e e'⟩

lemma Runs.brT {t : (Key → Option Bool) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = true) (h : Runs p σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchTrue ht e⟩

lemma Runs.brF {t : (Key → Option Bool) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = false) (h : Runs q σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchFalse ht e⟩

lemma Runs.loopT {t : (Key → Option Bool) → Bool} {body : Prog} {σ σ' τ : Regs} {B1 B2 : ℕ}
    (ht : t (hd σ) = true) (h1 : Runs body σ σ' B1) (h2 : Runs (.loop t body) σ' τ B2) :
    Runs (.loop t body) σ τ (B1 + B2 + 2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, StackProg.Exec.loopTrue ht e e'⟩

lemma Runs.loopF {t : (Key → Option Bool) → Bool} {body : Prog} {σ : Regs}
    (ht : t (hd σ) = false) : Runs (.loop t body) σ σ 1 :=
  ⟨1, le_rfl, StackProg.Exec.loopFalse ht⟩

/-- a loop driven by an explicit sequence of register files -/
lemma Runs.loopU (t : (Key → Option Bool) → Bool) (body : Prog) (h : ℕ → Regs) (B m : ℕ)
    (hstep : ∀ j < m, t (hd (h j)) = true ∧ Runs body (h j) (h (j + 1)) B)
    (hstop : t (hd (h m)) = false) :
    Runs (.loop t body) (h 0) (h m) (m * (B + 2) + 1) := by
  have key : ∀ i, i ≤ m → Runs (.loop t body) (h (m - i)) (h m) (i * (B + 2) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨1, by simp, by simpa using StackProg.Exec.loopFalse hstop⟩
    | succ i ih =>
      intro hi
      obtain ⟨ht, n, hn, e⟩ := hstep (m - (i + 1)) (by omega)
      obtain ⟨n', hn', e'⟩ := ih (by omega)
      have hidx : m - (i + 1) + 1 = m - i := by omega
      rw [hidx] at e
      refine ⟨1 + n + 1 + n', ?_, StackProg.Exec.loopTrue ht e e'⟩
      have : (i + 1) * (B + 2) + 1 = i * (B + 2) + 1 + (B + 2) := by ring
      omega
  simpa using key m le_rfl

/-- `loopU` with the start and end states given up to equality -/
lemma Runs.loopU' (t : (Key → Option Bool) → Bool) (body : Prog) (h : ℕ → Regs) (B m : ℕ)
    {σ τ : Regs} (h0 : h 0 = σ) (hm : h m = τ)
    (hstep : ∀ j < m, t (hd (h j)) = true ∧ Runs body (h j) (h (j + 1)) B)
    (hstop : t (hd (h m)) = false) {C : ℕ} (hC : m * (B + 2) + 1 ≤ C) :
    Runs (.loop t body) σ τ C := by
  subst h0; subst hm
  exact (Runs.loopU t body h B m hstep hstop).mono hC

/-! ## Primitive programs -/

lemma runs_push (k : Key) (a : Bool) (σ : Regs) :
    Runs (pushProg k a) σ (σ.set k (a :: σ.get k)) 1 :=
  ⟨1, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).1 a⟩

lemma runs_pop (k : Key) (σ : Regs) : Runs (popProg k) σ (σ.set k (σ.get k).tail) 1 :=
  ⟨1, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).2.1⟩

lemma runs_clear (k : Key) (σ : Regs) :
    Runs (clearProg k) σ (σ.set k []) (3 * (σ.get k).length + 1) :=
  ⟨_, le_rfl, by rw [← Regs.update_get]; exact (stack_basic_macros k σ.get).2.2⟩

lemma runs_copy (a b c : Key) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (σ : Regs)
    (hc : σ.get c = []) :
    Runs (copyProg a b c) σ (σ.set b (σ.get a ++ σ.get b)) (6 * (σ.get a).length + 3) :=
  ⟨_, le_rfl, by rw [← Regs.update_get]; exact stack_copy a b c hab hac hbc σ.get hc⟩

def mvProg (a b : Key) : Prog := transferProg a (fun k => decide (k = b))

lemma runs_mv (a b : Key) (hab : a ≠ b) (σ : Regs) :
    Runs (mvProg a b) σ ((σ.set a []).set b ((σ.get a).reverse ++ σ.get b))
      (3 * (σ.get a).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_transfer a (fun k => decide (k = b)) σ.get
  unfold mvProg
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [transferStore]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab]
  · by_cases h2 : k = a
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma runs_syncpop (i j : Key) (hij : i ≠ j) (σ : Regs) :
    Runs (syncPopProg i j) σ
      ((σ.set i ((σ.get i).drop (min (σ.get i).length (σ.get j).length))).set j
        ((σ.get j).drop (min (σ.get i).length (σ.get j).length)))
      (3 * min (σ.get i).length (σ.get j).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_sync_pop i j hij σ.get
  simp only at e
  convert e using 1
  rw [← Regs.update_get, ← Regs.update_get]

def emb4 (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Key :=
  ⟨![a, b, c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

/-- `b := (a repeated |c| times) ++ b`, consuming `c` (scratch `d`) -/
def repProg (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Prog :=
  repeatCopyProg (emb4 a b c d hab hac had hbc hbd hcd)

lemma runs_rep (a b c d : Key) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (σ : Regs) (hd0 : σ.get d = []) :
    Runs (repProg a b c d hab hac had hbc hbd hcd) σ
      ((σ.set c []).set b ((List.replicate (σ.get c).length (σ.get a)).flatten ++ σ.get b))
      ((6 * (σ.get a).length + 7) * (σ.get c).length + 1) := by
  refine ⟨_, le_rfl, ?_⟩
  have e := stack_repeat_copy (emb4 a b c d hab hac had hbc hbd hcd) σ.get hd0
  rw [← Regs.update_get, ← Regs.update_get]
  exact e

/-- a no-op -/
def skipP : Prog := .act (fun _ _ => .keep)

lemma runs_skip (σ : Regs) : Runs skipP σ σ 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (fun (_ : Key → Option Bool) (_ : Key) => (StackAct.keep : StackAct Bool)) σ.get
  have : StackProg.applyAct (fun (_ : Key → Option Bool) (_ : Key) => (StackAct.keep : StackAct Bool)) σ.get = σ.get := by
    funext k; rfl
  rw [this] at e; exact e

/-- a general atomic step -/
lemma runs_act (f : (Key → Option Bool) → Key → StackAct Bool) (σ τ : Regs)
    (h : ∀ k, (f (hd σ) k).apply (σ.get k) = τ.get k) : Runs (.act f) σ τ 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act f σ.get
  convert e using 1
  funext k
  exact (h k).symm

/-- move the top of `a` onto `b` (one step) -/
def mv1 (a b : Key) : Prog := .act (transferAct a (fun k => decide (k = b)))

lemma runs_mv1 (a b : Key) (hab : a ≠ b) (σ : Regs) (x : Bool) (l : List Bool)
    (h : σ.get a = x :: l) : Runs (mv1 a b) σ ((σ.set a l).set b (x :: σ.get b)) 1 := by
  refine runs_act _ _ _ (fun k => ?_)
  rw [Regs.get_set, Regs.get_set]
  simp only [transferAct, hd]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, h, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [h, StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

lemma runs_mv1_nil (a b : Key) (σ : Regs) (h : σ.get a = []) : Runs (mv1 a b) σ σ 1 := by
  refine runs_act _ _ _ (fun k => ?_)
  simp only [transferAct, hd]
  by_cases h2 : k = a
  · subst h2; simp [h, StackAct.apply]
  · by_cases h1 : k = b
    · subst h1; simp [h, h2, StackAct.apply]
    · simp [h1, h2, StackAct.apply]

/-! ## drain: pop `a` completely, pushing a constant onto `b` -/

def ppAct (a b : Key) (y : Bool) : (Key → Option Bool) → Key → StackAct Bool :=
  fun _ k => if k = a then .pop else if k = b then .push y else .keep

lemma runs_pp (a b : Key) (hab : a ≠ b) (y : Bool) (σ : Regs) :
    Runs (.act (ppAct a b y)) σ ((σ.set a (σ.get a).tail).set b (y :: σ.get b)) 1 := by
  refine runs_act _ _ _ (fun k => ?_)
  rw [Regs.get_set, Regs.get_set]
  simp only [ppAct]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

def drainProg (a b : Key) (y : Bool) : Prog :=
  .loop (fun h => (h a).isSome) (.act (ppAct a b y))

lemma runs_drain (a b : Key) (hab : a ≠ b) (y : Bool) :
    ∀ (n : ℕ) (σ : Regs), (σ.get a).length = n →
      Runs (drainProg a b y) σ ((σ.set a []).set b (List.replicate n y ++ σ.get b)) (3 * n + 1) := by
  intro n
  induction n with
  | zero =>
    intro σ hσ
    have h0 : σ.get a = [] := List.length_eq_zero_iff.mp hσ
    have : (σ.set a []).set b (List.replicate 0 y ++ σ.get b) = σ := by
      simp only [List.replicate_zero, List.nil_append]
      rw [← h0, Regs.set_get, Regs.set_get]
    rw [this]
    unfold drainProg
    exact Runs.loopF (by simp [hd, h0])
  | succ n ih =>
    intro σ hσ
    obtain ⟨x, l, hxl⟩ : ∃ x l, σ.get a = x :: l := by
      cases h : σ.get a with
      | nil => rw [h] at hσ; simp at hσ
      | cons x l => exact ⟨x, l, rfl⟩
    have e1 := runs_pp a b hab y σ
    set σ1 := (σ.set a (σ.get a).tail).set b (y :: σ.get b) with hσ1
    have h1 : (σ1.get a).length = n := by
      rw [hσ1, Regs.get_set_ne _ hab, Regs.get_set_self, hxl]
      rw [hxl] at hσ; simpa using hσ
    have e2 := ih σ1 h1
    have hres : (σ1.set a []).set b (List.replicate n y ++ σ1.get b) =
        (σ.set a []).set b (List.replicate (n + 1) y ++ σ.get b) := by
      apply Regs.ext_get; funext i
      simp only [hσ1, Regs.get_set]
      split_ifs <;> simp_all [List.replicate_succ']
    rw [← hres]
    unfold drainProg
    exact (Runs.loopT (by simp [hd, hxl]) e1 e2).mono (by omega)

/-! ## emission of constant blocks onto `O` -/

def emitC : List Bool → Prog
  | [] => skipP
  | b :: l => .seq (pushProg .O b) (emitC l)

lemma runs_emitC : ∀ (l : List Bool) (σ : Regs),
    Runs (emitC l) σ (σ.set .O (l.reverse ++ σ.O)) (2 * l.length + 1)
  | [], σ => by
      have : σ.set .O ([].reverse ++ σ.O) = σ := by cases σ; rfl
      rw [this]; exact runs_skip σ
  | b :: l, σ => by
      have e1 := runs_push .O b σ
      have e2 := runs_emitC l (σ.set .O (b :: σ.get .O))
      have : (σ.set .O (b :: σ.get .O)).set .O (l.reverse ++ (σ.set .O (b :: σ.get .O)).O) =
          σ.set .O ((b :: l).reverse ++ σ.O) := by
        cases σ; simp [Regs.set, Regs.get]
      rw [this] at e2
      refine (e1.seq e2).mono ?_
      simp; omega

/-- emit block `l` once for every symbol of counter `C` (consuming it) -/
def repEmit (C : Key) (l : List Bool) : Prog :=
  .loop (fun h => (h C).isSome) (.seq (popProg C) (emitC l))

lemma runs_repEmit (C : Key) (hC : C ≠ .O) (l : List Bool) :
    ∀ (n : ℕ) (σ : Regs), (σ.get C).length = n →
      Runs (repEmit C l) σ ((σ.set C []).set .O ((List.replicate n l).flatten.reverse ++ σ.O))
        (n * (2 * l.length + 5) + 1) := by
  intro n
  induction n with
  | zero =>
    intro σ hσ
    have h0 : σ.get C = [] := List.length_eq_zero_iff.mp hσ
    have : (σ.set C []).set .O ((List.replicate 0 l).flatten.reverse ++ σ.O) = σ := by
      simp only [List.replicate_zero, List.flatten_nil, List.reverse_nil, List.nil_append]
      rw [← h0, Regs.set_get]; cases σ; rfl
    rw [this]
    unfold repEmit
    exact (Runs.loopF (by simp [hd, h0])).mono (by omega)
  | succ n ih =>
    intro σ hσ
    obtain ⟨x, r, hxl⟩ : ∃ x r, σ.get C = x :: r := by
      cases h : σ.get C with
      | nil => rw [h] at hσ; simp at hσ
      | cons x r => exact ⟨x, r, rfl⟩
    have e1 := runs_pop C σ
    have e2 := runs_emitC l (σ.set C (σ.get C).tail)
    set σ1 := (σ.set C (σ.get C).tail).set .O (l.reverse ++ (σ.set C (σ.get C).tail).O) with hσ1
    have h1 : (σ1.get C).length = n := by
      rw [hσ1, Regs.get_set_ne _ hC, Regs.get_set_self, hxl]
      rw [hxl] at hσ; simpa using hσ
    have e3 := ih σ1 h1
    have hO : (σ.set C (σ.get C).tail).O = σ.O := by
      have := Regs.get_set_ne σ (Ne.symm hC) (σ.get C).tail
      simpa [Regs.get] using this
    have hres : (σ1.set C []).set .O ((List.replicate n l).flatten.reverse ++ σ1.O) =
        (σ.set C []).set .O ((List.replicate (n + 1) l).flatten.reverse ++ σ.O) := by
      have hσ1O : σ1.O = l.reverse ++ σ.O := by
        rw [hσ1, hO]; cases σ; cases C <;> rfl
      rw [hσ1O]
      apply Regs.ext_get; funext i
      simp only [hσ1, Regs.get_set]
      split_ifs <;> simp_all [List.replicate_succ]
    rw [← hres]
    unfold repEmit
    refine (Runs.loopT (by simp [hd, hxl]) (e1.seq e2) e3).mono ?_
    nlinarith

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## Binary numerals (least significant bit first) -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

lemma bits_eq_nil_iff' (k : ℕ) : Nat.bits k = [] ↔ k = 0 := by
  constructor
  · intro h
    induction k using Nat.binaryRec' with
    | zero => rfl
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hn] at h
      simp at h
  · rintro rfl; simp

lemma bval_bits (n : ℕ) : bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval, ih]

lemma bits_bval (l : List Bool) (h : l.getLast? ≠ some false) : Nat.bits (bval l) = l := by
  induction l with
  | nil => simp [bval]
  | cons b t ih =>
    by_cases ht : t = []
    · subst ht
      have hb : b = true := by cases b <;> simp_all
      subst hb
      exact Nat.bits_append_bit 0 true (fun _ => rfl)
    · have h' : t.getLast? ≠ some false := by
        cases t with
        | nil => exact absurd rfl ht
        | cons x t' => simpa [List.getLast?_cons_cons] using h
      have ih' := ih h'
      have hne : bval t ≠ 0 := by
        intro h0; rw [h0] at ih'; simp at ih'; exact absurd ih'.symm (Ne.symm ht)
      simp only [bval]
      rw [Nat.bits_append_bit _ _ (fun h0 => absurd h0 hne), ih']

lemma bits_getLast (n : ℕ) : (Nat.bits n).getLast? ≠ some false := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; have := hn rfl; subst this; simp
    · have hne : Nat.bits n ≠ [] := fun h => h0 ((bits_eq_nil_iff' n).1 h)
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hne] at *
      simpa using ih

lemma bval_append (l l' : List Bool) : bval (l ++ l') = bval l + 2 ^ l.length * bval l' := by
  induction l with
  | nil => simp [bval]
  | cons b l ih =>
    simp only [List.cons_append, bval, ih, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> ring

lemma bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons b l ih =>
    simp only [bval, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> omega

lemma len_bits_le_of_lt (n m : ℕ) (h : n < 2 ^ m) : (Nat.bits n).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

lemma len_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma len_bits_le (x : ℕ) : (Nat.bits x).length ≤ x := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self)

/-! ## increment and decrement -/

def incL : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incL r

def decL : List Bool → List Bool
  | [] => []
  | true :: r => if r = [] then [] else false :: r
  | false :: r => true :: decL r

lemma incL_bits (k : ℕ) : incL (Nat.bits k) = Nat.bits (k + 1) := by
  induction k using Nat.binaryRec' with
  | zero => simp [incL]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b
    · have hn0 : n ≠ 0 := fun h => by simpa using hn h
      simp only [incL]
      have : Nat.bit false n + 1 = Nat.bit true n := by
        first | (simp [Nat.bit]; done) | (simp [Nat.bit]; omega)
      rw [this]; exact (Nat.bits_append_bit n true (fun _ => rfl)).symm
    · simp only [incL, ih]
      have : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
        first | (simp [Nat.bit]; done) | (simp [Nat.bit]; omega)
      rw [this]; exact (Nat.bits_append_bit (n + 1) false (fun h => absurd h (Nat.succ_ne_zero n))).symm

lemma bit_ne_zero_aux (b : Bool) (n : ℕ) (h : n = 0 → b = true) : Nat.bit b n ≠ 0 := by
  cases b
  · have : n ≠ 0 := fun h0 => by simpa using h h0
    simp [Nat.bit]; omega
  · simp [Nat.bit]

lemma decL_bits (k : ℕ) : decL (Nat.bits k) = Nat.bits (k - 1) := by
  induction k using Nat.binaryRec' with
  | zero => simp [decL]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b
    · have hn0 : n ≠ 0 := fun h => by simpa using hn h
      simp only [decL, ih]
      have : Nat.bit false n - 1 = Nat.bit true (n - 1) := by simp [Nat.bit]; omega
      rw [this, Nat.bits_append_bit _ _ (fun _ => rfl)]
    · simp only [decL]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg (by rw [bits_eq_nil_iff']; exact h0)]
        have : Nat.bit true n - 1 = Nat.bit false n := by simp [Nat.bit]
        rw [this, Nat.bits_append_bit _ _ (by simp [h0])]

/-- a canonical nonempty bit list has a `true` after its leading zeros -/
lemma bits_split_false (k : ℕ) (hk : k ≠ 0) :
    ∃ c r, Nat.bits k = List.replicate c false ++ true :: r := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨b, n, rfl⟩ : ∃ b n, k = Nat.bit b n := ⟨k.bodd, k.div2, (Nat.bit_bodd_div2 k).symm⟩
    by_cases hc : n = 0 → b = true
    · rw [Nat.bits_append_bit _ _ hc]
      cases b
      · have hn0 : n ≠ 0 := fun h => by simpa using hc h
        obtain ⟨c, r, hr⟩ := ih n (by simp [Nat.bit]; omega) hn0
        exact ⟨c + 1, r, by rw [hr]; simp [List.replicate_succ]⟩
      · exact ⟨0, Nat.bits n, by simp⟩
    · push Not at hc
      obtain ⟨rfl, hb⟩ := hc
      simp at hb; subst hb; simp [Nat.bit] at hk

lemma split_true (l : List Bool) :
    ∃ c rest, l = List.replicate c true ++ rest ∧ rest.head? ≠ some true := by
  induction l with
  | nil => exact ⟨0, [], by simp⟩
  | cons b l ih =>
    cases b
    · exact ⟨0, false :: l, by simp⟩
    · obtain ⟨c, rest, h1, h2⟩ := ih
      exact ⟨c + 1, rest, by rw [h1]; simp [List.replicate_succ], h2⟩

lemma incL_rep (c : ℕ) (rest : List Bool) :
    incL (List.replicate c true ++ rest) = List.replicate c false ++ incL rest := by
  induction c with
  | zero => simp
  | succ c ih => simp [List.replicate_succ, incL, ih]

lemma decL_rep (c : ℕ) (r : List Bool) :
    decL (List.replicate c false ++ true :: r) =
      List.replicate c true ++ (if r = [] then [] else false :: r) := by
  induction c with
  | zero => simp [decL]
  | succ c ih => simp [List.replicate_succ, decL, ih]

/-! ## pop-and-push loops -/

/-- while the top of `a` is `x`: pop `a`, push `y` onto `b` -/
def whilePP (a b : Key) (x y : Bool) : Prog :=
  .loop (fun h => decide (h a = some x)) (.act (ppAct a b y))

lemma runs_whilePP (a b : Key) (hab : a ≠ b) (x y : Bool) :
    ∀ (c : ℕ) (r : List Bool) (σ : Regs), σ.get a = List.replicate c x ++ r → r.head? ≠ some x →
      Runs (whilePP a b x y) σ ((σ.set a r).set b (List.replicate c y ++ σ.get b)) (3 * c + 1) := by
  intro c
  induction c with
  | zero =>
    intro r σ ha hr
    simp only [List.replicate_zero, List.nil_append] at ha ⊢
    rw [← ha, Regs.set_get, Regs.set_get]
    unfold whilePP
    exact Runs.loopF (by simp [hd, ha, hr])
  | succ c ih =>
    intro r σ ha hr
    have e1 := runs_pp a b hab y σ
    set σ1 := (σ.set a (σ.get a).tail).set b (y :: σ.get b) with hσ1
    have h1 : σ1.get a = List.replicate c x ++ r := by
      rw [hσ1, Regs.get_set_ne _ hab, Regs.get_set_self, ha]; simp [List.replicate_succ]
    have e2 := ih r σ1 h1 hr
    have hres : (σ1.set a r).set b (List.replicate c y ++ σ1.get b) =
        (σ.set a r).set b (List.replicate (c + 1) y ++ σ.get b) := by
      apply Regs.ext_get; funext i
      simp only [hσ1, Regs.get_set]
      split_ifs <;> simp_all [List.replicate_succ']
    rw [← hres]
    unfold whilePP
    exact (Runs.loopT (by simp [hd, ha, List.replicate_succ]) e1 e2).mono (by omega)

/-- increment the counter `X` (scratch `T`, empty before and after) -/
def incProg (X T : Key) : Prog :=
  .seq (whilePP X T true false)
    (.seq (.branch (fun h => decide (h X = some false)) (popProg X) skipP)
      (.seq (pushProg X true) (mvProg T X)))

lemma runs_inc (X T : Key) (hXT : X ≠ T) (σ : Regs) (l : List Bool)
    (hX : σ.get X = l) (hT : σ.get T = []) :
    Runs (incProg X T) σ (σ.set X (incL l)) (6 * l.length + 10) := by
  obtain ⟨c, rest, hl, hrest⟩ := split_true l
  subst hl
  have e1 := runs_whilePP X T hXT true false c rest σ hX hrest
  set σ1 := (σ.set X rest).set T (List.replicate c false ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = rest := by rw [hσ1, Regs.get_set_ne _ hXT, Regs.get_set_self]
  have hσ1T : σ1.get T = List.replicate c false := by rw [hσ1, Regs.get_set_self, hT]; simp
  obtain ⟨σ2, rest', e2, hσ2, hrest'⟩ : ∃ σ2 rest', Runs (.branch (fun h => decide (h X = some false)) (popProg X) skipP) σ1 σ2 2 ∧
      σ2 = σ1.set X rest' ∧ incL rest = true :: rest' := by
    cases rest with
    | nil =>
      refine ⟨σ1, [], (runs_skip σ1).brF (by simp [hd, hσ1X]), ?_, by simp [incL]⟩
      rw [← hσ1X, Regs.set_get]
    | cons b r =>
      cases b
      · have hb : Runs (.branch (fun h => decide (h X = some false)) (popProg X) skipP) σ1
            (σ1.set X (σ1.get X).tail) 2 := (runs_pop X σ1).brT (by simp [hd, hσ1X])
        have ht : (σ1.get X).tail = r := by rw [hσ1X]; rfl
        rw [ht] at hb
        exact ⟨σ1.set X r, r, hb, rfl, by simp [incL]⟩
      · simp at hrest
  have e3 := runs_push X true σ2
  set σ3 := σ2.set X (true :: σ2.get X) with hσ3
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have h3T : σ3.get T = List.replicate c false := by
    rw [hσ3, Regs.get_set_ne _ (Ne.symm hXT), hσ2, Regs.get_set_ne _ (Ne.symm hXT), hσ1T]
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (incL (List.replicate c true ++ rest)) := by
    rw [incL_rep, hrest']
    have h3X : σ3.get X = true :: rest' := by
      rw [hσ3, Regs.get_set_self, hσ2, Regs.get_set_self]
    rw [h3T, h3X]
    apply Regs.ext_get; funext i
    simp only [hσ3, hσ2, hσ1, Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  rw [h3T]; simp; omega

/-- decrement the counter `X` holding a nonzero canonical value (scratch `T`) -/
def decProg (X T : Key) : Prog :=
  .seq (whilePP X T false true)
    (.seq (popProg X)
      (.seq (.branch (fun h => (h X).isSome) (pushProg X false) skipP) (mvProg T X)))

lemma runs_dec (X T : Key) (hXT : X ≠ T) (σ : Regs) (c : ℕ) (r : List Bool)
    (hX : σ.get X = List.replicate c false ++ true :: r) (hT : σ.get T = []) :
    Runs (decProg X T) σ (σ.set X (decL (List.replicate c false ++ true :: r)))
      (6 * c + 10) := by
  have e1 := runs_whilePP X T hXT false true c (true :: r) σ hX (by simp)
  set σ1 := (σ.set X (true :: r)).set T (List.replicate c true ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = true :: r := by
    rw [hσ1, Regs.get_set_ne _ hXT, Regs.get_set_self]
  have e2 := runs_pop X σ1
  set σ2 := σ1.set X (σ1.get X).tail with hσ2
  have hσ2X : σ2.get X = r := by rw [hσ2, Regs.get_set_self, hσ1X]; rfl
  obtain ⟨σ3, e3, hσ3⟩ : ∃ σ3, Runs (.branch (fun h => (h X).isSome) (pushProg X false) skipP) σ2 σ3 2 ∧
      σ3 = σ2.set X (if r = [] then [] else false :: r) := by
    by_cases hr : r = []
    · subst hr
      refine ⟨σ2, (runs_skip σ2).brF (by simp [hd, hσ2X]), ?_⟩
      simp only [if_true]; rw [← hσ2X, Regs.set_get]
    · have hb : Runs (.branch (fun h => (h X).isSome) (pushProg X false) skipP) σ2
          (σ2.set X (false :: σ2.get X)) 2 := (runs_push X false σ2).brT (by
          cases r with
          | nil => exact absurd rfl hr
          | cons b r => simp [hd, hσ2X])
      refine ⟨_, hb, ?_⟩
      rw [if_neg hr, hσ2X]
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have h3T : σ3.get T = List.replicate c true := by
    rw [hσ3, Regs.get_set_ne _ (Ne.symm hXT), hσ2, Regs.get_set_ne _ (Ne.symm hXT), hσ1,
      Regs.get_set_self, hT]; simp
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (decL (List.replicate c false ++ true :: r)) := by
    rw [decL_rep, h3T]
    have h3X : σ3.get X = (if r = [] then [] else false :: r) := by
      rw [hσ3, Regs.get_set_self]
    rw [h3X]
    apply Regs.ext_get; funext i
    simp only [hσ3, hσ2, hσ1, Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  rw [h3T]; simp; omega

lemma runs_dec_bits (X T : Key) (hXT : X ≠ T) (σ : Regs) (k : ℕ) (hk : k ≠ 0)
    (hX : σ.get X = Nat.bits k) (hT : σ.get T = []) :
    Runs (decProg X T) σ (σ.set X (Nat.bits (k - 1))) (6 * (Nat.bits k).length + 10) := by
  obtain ⟨c, r, hr⟩ := bits_split_false k hk
  rw [hr] at hX
  have := runs_dec X T hXT σ c r hX hT
  rw [← hr, decL_bits] at this
  refine this.mono ?_
  have : c ≤ (Nat.bits k).length := by rw [hr]; simp
  omega

lemma runs_inc_bits (X T : Key) (hXT : X ≠ T) (σ : Regs) (k : ℕ)
    (hX : σ.get X = Nat.bits k) (hT : σ.get T = []) :
    Runs (incProg X T) σ (σ.set X (Nat.bits (k + 1))) (6 * (Nat.bits k).length + 10) := by
  have := runs_inc X T hXT σ (Nat.bits k) hX hT
  rwa [incL_bits] at this

/-! ## addition -/

def maj (x y c : Bool) : Bool := (x && y) || (x && c) || (y && c)

lemma addL_meas (c : Bool) (xs ys : List Bool) (h : ¬(xs = [] ∧ ys = [] ∧ c = false)) :
    xs.tail.length + ys.tail.length + (maj (xs.headD false) (ys.headD false) c).toNat <
      xs.length + ys.length + c.toNat := by
  rcases xs with _ | ⟨x, xs⟩ <;> rcases ys with _ | ⟨y, ys⟩ <;> cases c <;>
    (try cases x) <;> (try cases y) <;> simp_all [maj] <;> omega

def addL (c : Bool) (xs ys : List Bool) : List Bool :=
  if xs = [] ∧ ys = [] ∧ c = false then [] else
    (xs.headD false ^^ ys.headD false ^^ c) ::
      addL (maj (xs.headD false) (ys.headD false) c) xs.tail ys.tail
termination_by xs.length + ys.length + c.toNat
decreasing_by exact addL_meas c xs ys (by assumption)

lemma addL_eq (c : Bool) (xs ys : List Bool) : addL c xs ys =
    if xs = [] ∧ ys = [] ∧ c = false then [] else
    (xs.headD false ^^ ys.headD false ^^ c) ::
      addL (maj (xs.headD false) (ys.headD false) c) xs.tail ys.tail := by
  rw [addL]

lemma addL_val : ∀ (n : ℕ) (c : Bool) (xs ys : List Bool),
    xs.length + ys.length + c.toNat = n →
    bval (addL c xs ys) = bval xs + bval ys + c.toNat := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c xs ys hn
    rw [addL_eq]
    by_cases h : xs = [] ∧ ys = [] ∧ c = false
    · rw [if_pos h]; obtain ⟨rfl, rfl, rfl⟩ := h; simp [bval]
    · rw [if_neg h]
      have key := ih (xs.tail.length + ys.tail.length +
          (maj (xs.headD false) (ys.headD false) c).toNat) (by rw [← hn]; exact addL_meas c xs ys h)
          (maj (xs.headD false) (ys.headD false) c) xs.tail ys.tail rfl
      simp only [bval, key]
      rcases xs with _ | ⟨x, xs⟩ <;> rcases ys with _ | ⟨y, ys⟩ <;>
        cases c <;> (try cases x) <;> (try cases y) <;> simp_all [bval, maj, Nat.bit] <;> omega

lemma addL_length : ∀ (n : ℕ) (c : Bool) (xs ys : List Bool),
    xs.length + ys.length + c.toNat = n →
    (addL c xs ys).length ≤ max xs.length ys.length + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c xs ys hn
    rw [addL_eq]
    by_cases h : xs = [] ∧ ys = [] ∧ c = false
    · rw [if_pos h]; simp
    · rw [if_neg h]
      by_cases h' : xs.tail = [] ∧ ys.tail = [] ∧ maj (xs.headD false) (ys.headD false) c = false
      · rw [addL_eq, if_pos h']
        simp
      · have key := ih (xs.tail.length + ys.tail.length +
          (maj (xs.headD false) (ys.headD false) c).toNat) (by rw [← hn]; exact addL_meas c xs ys h)
          (maj (xs.headD false) (ys.headD false) c) xs.tail ys.tail rfl
        simp only [List.length_cons]
        have hne : xs ≠ [] ∨ ys ≠ [] := by
          by_contra hc; push Not at hc
          obtain ⟨rfl, rfl⟩ := hc
          apply h'; refine ⟨rfl, rfl, ?_⟩; cases c <;> simp_all [maj]
        have : max xs.tail.length ys.tail.length + 1 ≤ max xs.length ys.length := by
          rcases xs with _ | ⟨x, xs⟩ <;> rcases ys with _ | ⟨y, ys⟩ <;> simp_all <;> omega
        omega

lemma bits_headD (a : ℕ) : (Nat.bits a).headD false = a.bodd := by
  by_cases h : a = 0
  · subst h; simp
  · conv_lhs => rw [← Nat.bit_bodd_div2 a]
    rw [Nat.bits_append_bit _ _ (by
      intro h0; by_contra hb
      have : a = 0 := by
        rw [← Nat.bit_bodd_div2 a, h0]; simp at hb; simp [hb]
      exact h this)]
    rfl

lemma bits_tail (a : ℕ) : (Nat.bits a).tail = Nat.bits (a / 2) := by
  by_cases h : a = 0
  · subst h; simp
  · conv_lhs => rw [← Nat.bit_bodd_div2 a]
    rw [Nat.bits_append_bit _ _ (by
      intro h0; by_contra hb
      have : a = 0 := by
        rw [← Nat.bit_bodd_div2 a, h0]; simp at hb; simp [hb]
      exact h this)]
    simp [Nat.div2_val]

lemma addL_bits_gen : ∀ (n : ℕ) (c : Bool) (a b : ℕ),
    (Nat.bits a).length + (Nat.bits b).length + c.toNat = n →
    addL c (Nat.bits a) (Nat.bits b) = Nat.bits (a + b + c.toNat) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c a b hn
    rw [addL_eq]
    by_cases h : Nat.bits a = [] ∧ Nat.bits b = [] ∧ c = false
    · rw [if_pos h]
      obtain ⟨h1, h2, rfl⟩ := h
      rw [bits_eq_nil_iff'] at h1 h2; subst h1; subst h2; simp
    · rw [if_neg h]
      rw [bits_headD, bits_headD, bits_tail, bits_tail]
      have key := ih _ (by
          have := addL_meas c (Nat.bits a) (Nat.bits b) h
          rw [bits_headD, bits_headD, bits_tail, bits_tail] at this; omega)
        (maj a.bodd b.bodd c) (a / 2) (b / 2) rfl
      rw [key]
      have harith : a + b + c.toNat =
          Nat.bit (a.bodd ^^ b.bodd ^^ c) (a / 2 + b / 2 + (maj a.bodd b.bodd c).toNat) := by
        have ha := Nat.bit_bodd_div2 a
        have hb := Nat.bit_bodd_div2 b
        rw [Nat.div2_val] at ha hb
        conv_lhs => rw [← ha, ← hb]
        cases a.bodd <;> cases b.bodd <;> cases c <;> simp [Nat.bit, maj] <;> omega
      rw [harith, Nat.bits_append_bit]
      intro h0
      have h1 : a / 2 = 0 := by omega
      have h2 : b / 2 = 0 := by omega
      have h3 : maj a.bodd b.bodd c = false := by
        cases hm : maj a.bodd b.bodd c
        · rfl
        · rw [hm] at h0; simp at h0
      have ha1 : a ≤ 1 := by omega
      have hb1 : b ≤ 1 := by omega
      rw [bits_eq_nil_iff', bits_eq_nil_iff'] at h
      clear ih hn key harith h0
      interval_cases a <;> interval_cases b <;> cases c <;> simp_all [maj]

lemma addL_bits (a b : ℕ) : addL false (Nat.bits a) (Nat.bits b) = Nat.bits (a + b) := by
  simpa using addL_bits_gen _ false a b rfl

def addAct (a b z cy : Key) (h : Key → Option Bool) (k : Key) : StackAct Bool :=
  let x := (h a).getD false
  let y := (h b).getD false
  let c := (h cy).isSome
  if k = a then .pop else if k = b then .pop else if k = z then .push (x ^^ y ^^ c)
  else if k = cy then
    (if maj x y c then (if c then .keep else .push true) else (if c then .pop else .keep))
  else .keep

/-- `z := reverse (a + b + carry) ++ z`, consuming `a`, `b` and the carry `cy` -/
def addProg (a b z cy : Key) : Prog :=
  .loop (fun h => (h a).isSome || (h b).isSome || (h cy).isSome) (.act (addAct a b z cy))

def carryL (c : Bool) : List Bool := if c then [true] else []

lemma runs_add (a b z cy : Key) (hab : a ≠ b) (haz : a ≠ z) (hac : a ≠ cy) (hbz : b ≠ z)
    (hbc : b ≠ cy) (hzc : z ≠ cy) : ∀ (n : ℕ) (c : Bool) (xs ys : List Bool) (σ : Regs),
    xs.length + ys.length + c.toNat = n →
    σ.get a = xs → σ.get b = ys → σ.get cy = carryL c →
    Runs (addProg a b z cy) σ
      ((((σ.set a []).set b []).set cy []).set z ((addL c xs ys).reverse ++ σ.get z))
      (3 * (addL c xs ys).length + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c xs ys σ hn ha hb hc
    by_cases h : xs = [] ∧ ys = [] ∧ c = false
    · obtain ⟨rfl, rfl, rfl⟩ := h
      have hL : addL false [] [] = [] := by rw [addL_eq]; simp
      rw [hL]
      have : ((((σ.set a []).set b []).set cy []).set z ([].reverse ++ σ.get z)) = σ := by
        have hc' : σ.get cy = [] := by rw [hc]; rfl
        apply Regs.ext_get; funext i
        simp only [Regs.get_set, List.reverse_nil, List.nil_append]
        split_ifs <;> simp_all
      rw [this]
      unfold addProg
      exact Runs.loopF (by simp [hd, ha, hb, hc, carryL])
    · set x := xs.headD false
      set y := ys.headD false
      set c' := maj x y c
      have hL : addL c xs ys = (x ^^ y ^^ c) :: addL c' xs.tail ys.tail := by
        rw [addL_eq, if_neg h]
      -- one step
      set σ1 := (((σ.set a xs.tail).set b ys.tail).set cy (carryL c')).set z
        ((x ^^ y ^^ c) :: σ.get z) with hσ1
      have e1 : Runs (.act (addAct a b z cy)) σ σ1 1 := by
        refine runs_act _ _ _ (fun k => ?_)
        have hha : hd σ a = xs.head? := by simp [hd, ha]
        have hhb : hd σ b = ys.head? := by simp [hd, hb]
        have hhc : (hd σ cy).isSome = c := by cases c <;> simp [hd, hc, carryL]
        simp only [addAct, hha, hhb, hhc]
        have hx : xs.head?.getD false = x := by cases xs <;> rfl
        have hy : ys.head?.getD false = y := by cases ys <;> rfl
        rw [hx, hy]
        simp only [hσ1, Regs.get_set]
        by_cases k1 : k = a
        · subst k1; simp [hab, haz, hac, StackAct.apply, ha]
        · by_cases k2 : k = b
          · subst k2; simp [k1, hbz, hbc, StackAct.apply, hb]
          · by_cases k3 : k = z
            · subst k3; simp [k1, k2, hzc, StackAct.apply]
            · by_cases k4 : k = cy
              · subst k4
                simp only [k1, k2, k3, if_true, if_false, hc]
                cases c <;> cases hm : maj x y _ <;> simp [hm, c', carryL, StackAct.apply]
              · simp [k1, k2, k3, k4, StackAct.apply]
      have hn' : xs.tail.length + ys.tail.length + c'.toNat < n := by
        rw [← hn]; exact addL_meas c xs ys h
      have e2 := ih _ hn' c' xs.tail ys.tail σ1 rfl
        (by rw [hσ1]; simp [Regs.get_set, hab, hac, haz])
        (by rw [hσ1]; simp [Regs.get_set, hbc, hbz])
        (by rw [hσ1]; simp [Regs.get_set, Ne.symm hzc])
      have hres : ((((σ1.set a []).set b []).set cy []).set z
          ((addL c' xs.tail ys.tail).reverse ++ σ1.get z)) =
          ((((σ.set a []).set b []).set cy []).set z ((addL c xs ys).reverse ++ σ.get z)) := by
        rw [hL]
        apply Regs.ext_get; funext i
        simp only [hσ1, Regs.get_set]
        split_ifs <;> simp_all
      rw [← hres]
      unfold addProg
      refine (Runs.loopT ?_ e1 e2).mono ?_
      · have : ¬ (xs = [] ∧ ys = [] ∧ c = false) := h
        rcases xs with _ | ⟨x0, xs⟩ <;> rcases ys with _ | ⟨y0, ys⟩ <;> cases c <;>
          simp_all [hd, carryL]
      · rw [hL]; simp; omega

lemma addL_len_le (c : Bool) (xs ys : List Bool) :
    (addL c xs ys).length ≤ xs.length + ys.length + 1 := by
  have := addL_length _ c xs ys rfl
  omega

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## multiplication by a constant, powers -/

def mulBody : Prog :=
  .seq (copyProg .X .X2 .sc) (.seq (addProg .X2 .Y .Z .Cy) (mvProg .Z .Y))

lemma runs_mulBody (σ : Regs) (x y L : ℕ) (hX : σ.X = Nat.bits x) (hY : σ.Y = Nat.bits y)
    (hX2 : σ.X2 = []) (hZ : σ.Z = []) (hCy : σ.Cy = []) (hsc : σ.sc = [])
    (hLx : (Nat.bits x).length ≤ L) (hLy : (Nat.bits y).length ≤ L)
    (hLxy : (Nat.bits (x + y)).length ≤ L) :
    Runs mulBody σ { σ with Y := Nat.bits (x + y) } (15 * L + 12) := by
  have e1 := runs_copy .X .X2 .sc (by decide) (by decide) (by decide) σ hsc
  set σ1 := σ.set .X2 (σ.get .X ++ σ.get .X2) with hσ1
  have e2 := runs_add .X2 .Y .Z .Cy (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) _ false (Nat.bits x) (Nat.bits y) σ1 rfl
    (by rw [hσ1]; simp [Regs.get, Regs.set, hX, hX2])
    (by rw [hσ1]; simp [Regs.get, Regs.set, hY])
    (by rw [hσ1]; simp [Regs.get, Regs.set, hCy, carryL])
  rw [addL_bits] at e2
  set σ2 := (((σ1.set .X2 []).set .Y []).set .Cy []).set .Z ((Nat.bits (x + y)).reverse ++ σ1.get .Z)
    with hσ2
  have e3 := runs_mv .Z .Y (by decide) σ2
  have hfin : (σ2.set .Z []).set .Y ((σ2.get .Z).reverse ++ σ2.get .Y) =
      { σ with Y := Nat.bits (x + y) } := by
    rw [hσ2, hσ1]
    cases σ
    simp_all [Regs.get, Regs.set]
  rw [hfin] at e3
  refine (e1.seq (e2.seq e3)).mono ?_
  have hz : (σ2.get .Z).length = (Nat.bits (x + y)).length := by
    rw [hσ2, hσ1]; simp [Regs.get, Regs.set, hZ]
  rw [hz]
  simp only [Regs.get, hX]
  omega

def repeatP : ℕ → Prog → Prog
  | 0, _ => skipP
  | n + 1, p => .seq p (repeatP n p)

lemma runs_repeat_mul (x L : ℕ) : ∀ (j y : ℕ) (σ : Regs),
    σ.X = Nat.bits x → σ.Y = Nat.bits y → σ.X2 = [] → σ.Z = [] → σ.Cy = [] → σ.sc = [] →
    (Nat.bits x).length ≤ L → (Nat.bits (j * x + y)).length ≤ L →
    Runs (repeatP j mulBody) σ { σ with Y := Nat.bits (j * x + y) } (j * (15 * L + 13) + 1)
  | 0, y, σ, hX, hY, _, _, _, _, _, _ => by
      have : { σ with Y := Nat.bits (0 * x + y) } = σ := by cases σ; simp_all
      rw [this]; exact (runs_skip σ).mono (by omega)
  | j + 1, y, σ, hX, hY, hX2, hZ, hCy, hsc, hLx, hL => by
      have hLy : (Nat.bits y).length ≤ L :=
        le_trans (len_bits_mono (by nlinarith)) hL
      have hLxy : (Nat.bits (x + y)).length ≤ L :=
        le_trans (len_bits_mono (by nlinarith)) hL
      have e1 := runs_mulBody σ x y L hX hY hX2 hZ hCy hsc hLx hLy hLxy
      have e2 := runs_repeat_mul x L j (x + y) { σ with Y := Nat.bits (x + y) } hX rfl hX2 hZ hCy
        hsc hLx (by rw [show j * x + (x + y) = (j + 1) * x + y by ring]; exact hL)
      have : { { σ with Y := Nat.bits (x + y) } with Y := Nat.bits (j * x + (x + y)) } =
          { σ with Y := Nat.bits ((j + 1) * x + y) } := by
        rw [show j * x + (x + y) = (j + 1) * x + y by ring]
      rw [this] at e2
      exact (e1.seq e2).mono (by nlinarith)

/-- `X := c * X` (scratch `X2`, `Y`, `Z`, `Cy`, `sc`) -/
def mulc (c : ℕ) : Prog :=
  .seq (repeatP c mulBody) (.seq (clearProg .X) (.seq (copyProg .Y .X .sc) (clearProg .Y)))

lemma runs_mulc (c x L : ℕ) (hc : 1 ≤ c) (σ : Regs) (hX : σ.X = Nat.bits x) (hY : σ.Y = [])
    (hX2 : σ.X2 = []) (hZ : σ.Z = []) (hCy : σ.Cy = []) (hsc : σ.sc = [])
    (hL : (Nat.bits (c * x)).length ≤ L) :
    Runs (mulc c) σ { σ with X := Nat.bits (c * x) } ((c + 1) * (15 * L + 30)) := by
  have hLx : (Nat.bits x).length ≤ L := le_trans (len_bits_mono (by nlinarith)) hL
  have e1 := runs_repeat_mul x L c 0 σ hX (by rw [hY]; simp) hX2 hZ hCy hsc hLx (by simpa using hL)
  simp only [add_zero] at e1
  set σ1 := { σ with Y := Nat.bits (c * x) } with hσ1
  have e2 := runs_clear .X σ1
  have e3 := runs_copy .Y .X .sc (by decide) (by decide) (by decide) (σ1.set .X []) (by
    rw [hσ1]; simp [Regs.get, Regs.set, hsc])
  set σ3 := (σ1.set .X []).set .X ((σ1.set .X []).get .Y ++ (σ1.set .X []).get .X) with hσ3
  have e4 := runs_clear .Y σ3
  have hfin : σ3.set .Y [] = { σ with X := Nat.bits (c * x) } := by
    rw [hσ3, hσ1]; cases σ; simp_all [Regs.get, Regs.set]
  rw [hfin] at e4
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  have h1 : (σ1.get .X).length = (Nat.bits x).length := by rw [hσ1]; simp [Regs.get, hX]
  have h2 : ((σ1.set .X []).get .Y).length = (Nat.bits (c * x)).length := by
    rw [hσ1]; simp [Regs.get, Regs.set]
  have h3 : (σ3.get .Y).length = (Nat.bits (c * x)).length := by
    rw [hσ3, hσ1]; simp [Regs.get, Regs.set]
  rw [h1, h2, h3]
  nlinarith

/-- `X := c ^ |E| * X`, consuming the counter `E` -/
def powLoop (E : Key) (c : ℕ) : Prog :=
  .loop (fun h => (h E).isSome) (.seq (popProg E) (mulc c))

lemma runs_powLoop (E : Key) (hE1 : E ≠ .X) (hE2 : E ≠ .Y) (hE3 : E ≠ .X2) (hE4 : E ≠ .Z)
    (hE5 : E ≠ .Cy) (hE6 : E ≠ .sc) (c L : ℕ) (hc : 1 ≤ c) :
    ∀ (e x : ℕ) (σ : Regs), (σ.get E).length = e →
    σ.X = Nat.bits x → σ.Y = [] → σ.X2 = [] → σ.Z = [] → σ.Cy = [] → σ.sc = [] →
    (Nat.bits (c ^ e * x)).length ≤ L →
    Runs (powLoop E c) σ ((σ.set E []).set .X (Nat.bits (c ^ e * x)))
      (e * ((c + 1) * (15 * L + 30) + 4) + 1)
  | 0, x, σ, hlen, hX, _, _, _, _, _, _ => by
      have h0 : σ.get E = [] := List.length_eq_zero_iff.mp hlen
      have : (σ.set E []).set .X (Nat.bits (c ^ 0 * x)) = σ := by
        simp only [pow_zero, one_mul]
        rw [← h0, Regs.set_get, ← hX]
        cases σ; rfl
      rw [this]; unfold powLoop
      exact (Runs.loopF (by simp [hd, h0])).mono (by omega)
  | e + 1, x, σ, hlen, hX, hY, hX2, hZ, hCy, hsc, hL => by
      obtain ⟨t, r, htr⟩ : ∃ t r, σ.get E = t :: r := by
        cases h : σ.get E with
        | nil => rw [h] at hlen; simp at hlen
        | cons t r => exact ⟨t, r, rfl⟩
      have e1 := runs_pop E σ
      set σ1 := σ.set E (σ.get E).tail with hσ1
      have g : ∀ k : Key, k ≠ E → σ1.get k = σ.get k := fun k hk => by
        rw [hσ1, Regs.get_set_ne _ hk]
      have hLc : (Nat.bits (c * x)).length ≤ L :=
        le_trans (len_bits_mono (by
          have : c * x ≤ c ^ (e + 1) * x := by
            apply Nat.mul_le_mul_right
            calc c = c ^ 1 := (pow_one c).symm
              _ ≤ c ^ (e + 1) := Nat.pow_le_pow_right hc (by omega)
          exact this)) hL
      have e2 := runs_mulc c x L hc σ1
        (by have := g .X (Ne.symm hE1); simp only [Regs.get] at this; rw [this, hX])
        (by have := g .Y (Ne.symm hE2); simp only [Regs.get] at this; rw [this, hY])
        (by have := g .X2 (Ne.symm hE3); simp only [Regs.get] at this; rw [this, hX2])
        (by have := g .Z (Ne.symm hE4); simp only [Regs.get] at this; rw [this, hZ])
        (by have := g .Cy (Ne.symm hE5); simp only [Regs.get] at this; rw [this, hCy])
        (by have := g .sc (Ne.symm hE6); simp only [Regs.get] at this; rw [this, hsc]) hLc
      set σ2 := { σ1 with X := Nat.bits (c * x) } with hσ2
      have g2 : ∀ k : Key, k ≠ .X → σ2.get k = σ1.get k := fun k hk => by
        rw [hσ2]; cases k <;> first | rfl | exact absurd rfl hk
      have e3 := runs_powLoop E hE1 hE2 hE3 hE4 hE5 hE6 c L hc e (c * x) σ2
        (by rw [g2 _ hE1, hσ1, Regs.get_set_self, htr]; rw [htr] at hlen; simpa using hlen)
        rfl
        (by have := g2 .Y (by decide); simp only [Regs.get] at this; rw [this]
            have := g .Y (Ne.symm hE2); simp only [Regs.get] at this; rw [this, hY])
        (by have := g2 .X2 (by decide); simp only [Regs.get] at this; rw [this]
            have := g .X2 (Ne.symm hE3); simp only [Regs.get] at this; rw [this, hX2])
        (by have := g2 .Z (by decide); simp only [Regs.get] at this; rw [this]
            have := g .Z (Ne.symm hE4); simp only [Regs.get] at this; rw [this, hZ])
        (by have := g2 .Cy (by decide); simp only [Regs.get] at this; rw [this]
            have := g .Cy (Ne.symm hE5); simp only [Regs.get] at this; rw [this, hCy])
        (by have := g2 .sc (by decide); simp only [Regs.get] at this; rw [this]
            have := g .sc (Ne.symm hE6); simp only [Regs.get] at this; rw [this, hsc])
        (by rw [show c ^ e * (c * x) = c ^ (e + 1) * x by ring]; exact hL)
      have hfin : (σ2.set E []).set .X (Nat.bits (c ^ e * (c * x))) =
          (σ.set E []).set .X (Nat.bits (c ^ (e + 1) * x)) := by
        rw [show c ^ e * (c * x) = c ^ (e + 1) * x by ring]
        apply Regs.ext_get; funext k
        simp only [Regs.get_set]
        split_ifs with h1 h2
        · rfl
        · rfl
        · rw [g2 _ h1, g _ h2]
      rw [hfin] at e3
      unfold powLoop
      refine (Runs.loopT (by simp [hd, htr]) (e1.seq e2) e3).mono ?_
      unfold powLoop at e3
      nlinarith

/-! ## emitting `natBits` of a binary register -/

def nbList (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

lemma natBits_eq (k : ℕ) : NSWApxHard.Reduction.natBits k = nbList (Nat.bits k) := rfl

def emitBits (k : Key) : Prog :=
  .loop (fun h => (h k).isSome)
    (.seq (.branch (fun h => decide (h k = some true)) (emitC [true, true]) (emitC [true, false]))
      (popProg k))

def emitNat (k : Key) : Prog := .seq (emitBits k) (pushProg .O false)

lemma runs_emitBits (k : Key) (hk : k ≠ .O) : ∀ (l : List Bool) (σ : Regs), σ.get k = l →
    Runs (emitBits k) σ ((σ.set k []).set .O ((l.flatMap (fun b => [true, b])).reverse ++ σ.O))
      (10 * l.length + 1)
  | [], σ, hl => by
      have : (σ.set k []).set .O ((([] : List Bool).flatMap (fun b => [true, b])).reverse ++ σ.O) = σ := by
        simp only [List.flatMap_nil, List.reverse_nil, List.nil_append]
        rw [← hl, Regs.set_get]; cases σ; rfl
      rw [this]; unfold emitBits
      exact Runs.loopF (by simp [hd, hl])
  | b :: l, σ, hl => by
      have e1 : Runs (.branch (fun h => decide (h k = some true)) (emitC [true, true])
          (emitC [true, false])) σ (σ.set .O ([b, true] ++ σ.O)) 6 := by
        cases b
        · have := runs_emitC [true, false] σ
          exact (Runs.brF (by simp [hd, hl]) this).mono (by simp)
        · have := runs_emitC [true, true] σ
          exact (Runs.brT (by simp [hd, hl]) this).mono (by simp)
      set σ1 := σ.set .O ([b, true] ++ σ.O) with hσ1
      have e2 := runs_pop k σ1
      set σ2 := σ1.set k (σ1.get k).tail with hσ2
      have h2 : σ2.get k = l := by
        rw [hσ2, Regs.get_set_self, hσ1, Regs.get_set_ne _ hk, hl]; rfl
      have e3 := runs_emitBits k hk l σ2 h2
      have hfin : (σ2.set k []).set .O ((l.flatMap (fun b => [true, b])).reverse ++ σ2.O) =
          (σ.set k []).set .O (((b :: l).flatMap (fun b => [true, b])).reverse ++ σ.O) := by
        have : σ2.O = [b, true] ++ σ.O := by
          have := Regs.get_set_ne σ1 (Ne.symm hk) (σ1.get k).tail
          rw [← hσ2] at this
          simp only [Regs.get] at this
          rw [this, hσ1]; cases σ; rfl
        rw [this]
        apply Regs.ext_get; funext i
        simp only [hσ2, hσ1, Regs.get_set]
        split_ifs <;> simp_all
      rw [hfin] at e3
      unfold emitBits
      refine (Runs.loopT (by simp [hd, hl]) (e1.seq e2) e3).mono ?_
      simp; omega

lemma runs_emitNat (k : Key) (hk : k ≠ .O) (n : ℕ) (σ : Regs) (hl : σ.get k = Nat.bits n) :
    Runs (emitNat k) σ ((σ.set k []).set .O ((NSWApxHard.Reduction.natBits n).reverse ++ σ.O))
      (10 * (Nat.bits n).length + 3) := by
  have e1 := runs_emitBits k hk _ σ hl
  have e2 := runs_push .O false ((σ.set k []).set .O
    (((Nat.bits n).flatMap (fun b => [true, b])).reverse ++ σ.O))
  have hfin : ((σ.set k []).set .O
      (((Nat.bits n).flatMap (fun b => [true, b])).reverse ++ σ.O)).set .O
      (false :: ((σ.set k []).set .O
      (((Nat.bits n).flatMap (fun b => [true, b])).reverse ++ σ.O)).get .O) =
      (σ.set k []).set .O ((NSWApxHard.Reduction.natBits n).reverse ++ σ.O) := by
    rw [natBits_eq]
    apply Regs.ext_get; funext i
    simp only [Regs.get_set, nbList]
    split_ifs <;> simp_all
  rw [hfin] at e2
  exact (e1.seq e2).mono (by omega)

/-! ## unary to binary -/

def toBin (C B : Key) : Prog := .loop (fun h => (h C).isSome) (.seq (popProg C) (incProg B .T))

lemma runs_toBin (C B : Key) (hCB : C ≠ B) (hCT : C ≠ .T) (hBT : B ≠ .T) (L : ℕ) :
    ∀ (n j : ℕ) (σ : Regs), (σ.get C).length = n → σ.get B = Nat.bits j → σ.T = [] →
    (Nat.bits (j + n)).length ≤ L →
    Runs (toBin C B) σ ((σ.set C []).set B (Nat.bits (j + n))) (n * (6 * L + 14) + 1)
  | 0, j, σ, hlen, hB, _, _ => by
      have h0 : σ.get C = [] := List.length_eq_zero_iff.mp hlen
      have : (σ.set C []).set B (Nat.bits (j + 0)) = σ := by
        rw [add_zero, ← hB, ← h0, Regs.set_get, Regs.set_get]
      rw [this]; unfold toBin
      exact (Runs.loopF (by simp [hd, h0])).mono (by omega)
  | n + 1, j, σ, hlen, hB, hT, hL => by
      obtain ⟨t, r, htr⟩ : ∃ t r, σ.get C = t :: r := by
        cases h : σ.get C with
        | nil => rw [h] at hlen; simp at hlen
        | cons t r => exact ⟨t, r, rfl⟩
      have e1 := runs_pop C σ
      set σ1 := σ.set C (σ.get C).tail with hσ1
      have e2 := runs_inc_bits B .T hBT σ1 j (by rw [hσ1, Regs.get_set_ne _ (Ne.symm hCB), hB])
        (by rw [hσ1, Regs.get_set_ne _ (Ne.symm hCT)]; exact hT)
      set σ2 := σ1.set B (Nat.bits (j + 1)) with hσ2
      have e3 := runs_toBin C B hCB hCT hBT L n (j + 1) σ2
        (by rw [hσ2, Regs.get_set_ne _ hCB, hσ1, Regs.get_set_self, htr]; rw [htr] at hlen;
            simpa using hlen)
        (by rw [hσ2, Regs.get_set_self])
        (by have := Regs.get_set_ne σ1 (Ne.symm hBT) (Nat.bits (j + 1)); rw [← hσ2] at this
            simp only [Regs.get] at this; rw [this]
            have := Regs.get_set_ne σ (Ne.symm hCT) (σ.get C).tail; rw [← hσ1] at this
            simp only [Regs.get] at this; rw [this, hT])
        (by rw [show j + 1 + n = j + (n + 1) by ring]; exact hL)
      have hfin : (σ2.set C []).set B (Nat.bits (j + 1 + n)) =
          (σ.set C []).set B (Nat.bits (j + (n + 1))) := by
        rw [show j + 1 + n = j + (n + 1) by ring]
        apply Regs.ext_get; funext k
        simp only [hσ2, hσ1, Regs.get_set]
        split_ifs <;> rfl
      rw [hfin] at e3
      unfold toBin
      refine (Runs.loopT (by simp [hd, htr]) (e1.seq e2) e3).mono ?_
      unfold toBin at e3
      have : (Nat.bits j).length ≤ L := le_trans (len_bits_mono (by omega)) hL
      nlinarith

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## Phase 0: parse the self-delimiting numeral -/

def pn : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: r => ([], false :: r)
  | [true] => ([], [])
  | true :: b :: r => (b :: (pn r).1, (pn r).2)

def p0a : Prog := .loop (fun h => decide (h .inp = some true)) (.seq (popProg .inp) (mv1 .inp .D))

lemma pn_len : ∀ w : List Bool, (pn w).1.length + (pn w).2.length ≤ w.length
  | [] => by simp [pn]
  | false :: r => by simp [pn]
  | [true] => by simp [pn]
  | true :: b :: r => by have := pn_len r; simp [pn]; omega

lemma runs_p0a : ∀ (w : List Bool) (σ : Regs), σ.inp = w →
    Runs p0a σ { σ with inp := (pn w).2, D := (pn w).1.reverse ++ σ.D } (5 * w.length + 1)
  | [], σ, hw => by
      have : { σ with inp := (pn []).2, D := (pn []).1.reverse ++ σ.D } = σ := by
        cases σ; simp_all [pn]
      rw [this]; unfold p0a
      exact Runs.loopF (by simp [hd, Regs.get, hw])
  | false :: r, σ, hw => by
      have : { σ with inp := (pn (false :: r)).2, D := (pn (false :: r)).1.reverse ++ σ.D } = σ := by
        cases σ; simp_all [pn]
      rw [this]; unfold p0a
      exact (Runs.loopF (by simp [hd, Regs.get, hw])).mono (by omega)
  | [true], σ, hw => by
      have e1 := runs_pop .inp σ
      have e2 := runs_mv1_nil .inp .D (σ.set .inp (σ.get .inp).tail) (by simp [Regs.get, Regs.set, hw])
      have e3 : Runs p0a (σ.set .inp (σ.get .inp).tail) (σ.set .inp (σ.get .inp).tail) 1 := by
        unfold p0a; exact Runs.loopF (by simp [hd, Regs.get, Regs.set, hw])
      have key : Runs p0a σ (σ.set .inp (σ.get .inp).tail) (3 + 1 + 2) := by
        unfold p0a; unfold p0a at e3
        exact Runs.loopT (by simp [hd, Regs.get, hw]) (e1.seq e2) e3
      have : σ.set .inp (σ.get .inp).tail = { σ with inp := (pn [true]).2, D := (pn [true]).1.reverse ++ σ.D } := by
        cases σ; simp_all [pn, Regs.get, Regs.set]
      rw [this] at key
      exact key.mono (by simp)
  | true :: b :: r, σ, hw => by
      have e1 := runs_pop .inp σ
      set σ1 := σ.set .inp (σ.get .inp).tail with hσ1
      have e2 := runs_mv1 .inp .D (by decide) σ1 b r (by rw [hσ1]; simp [Regs.get, Regs.set, hw])
      set σ2 := (σ1.set .inp r).set .D (b :: σ1.get .D) with hσ2
      have e3 := runs_p0a r σ2 (by rw [hσ2]; simp [Regs.get, Regs.set])
      have hfin : { σ2 with inp := (pn r).2, D := (pn r).1.reverse ++ σ2.D } =
          { σ with inp := (pn (true :: b :: r)).2, D := (pn (true :: b :: r)).1.reverse ++ σ.D } := by
        rw [hσ2, hσ1]; cases σ; simp [pn, Regs.get, Regs.set]
      rw [hfin] at e3
      unfold p0a
      refine (Runs.loopT (by simp [hd, Regs.get, hw]) (e1.seq e2) e3).mono ?_
      simp; omega

/-- pop `K` while its top is `x` -/
def whilePop (K : Key) (x : Bool) : Prog :=
  .loop (fun h => decide (h K = some x)) (popProg K)

lemma runs_whilePop (K : Key) (x : Bool) : ∀ (c : ℕ) (r : List Bool) (σ : Regs),
    σ.get K = List.replicate c x ++ r → r.head? ≠ some x →
    Runs (whilePop K x) σ (σ.set K r) (3 * c + 1)
  | 0, r, σ, hK, hr => by
      simp only [List.replicate_zero, List.nil_append] at hK
      rw [← hK, Regs.set_get]; unfold whilePop
      exact Runs.loopF (by simp [hd, hK, hr])
  | c + 1, r, σ, hK, hr => by
      have e1 := runs_pop K σ
      have e2 := runs_whilePop K x c r (σ.set K (σ.get K).tail) (by
        rw [Regs.get_set_self, hK]; simp [List.replicate_succ]) hr
      have : (σ.set K (σ.get K).tail).set K r = σ.set K r := by
        apply Regs.ext_get; funext i; simp only [Regs.get_set]; split_ifs <;> rfl
      rw [this] at e2
      unfold whilePop
      exact (Runs.loopT (by simp [hd, hK, List.replicate_succ]) e1 e2).mono (by omega)

lemma split_false (l : List Bool) :
    ∃ c rest, l = List.replicate c false ++ rest ∧ rest.head? ≠ some false := by
  induction l with
  | nil => exact ⟨0, [], by simp⟩
  | cons b l ih =>
    cases b
    · obtain ⟨c, rest, h1, h2⟩ := ih
      exact ⟨c + 1, rest, by rw [h1]; simp [List.replicate_succ], h2⟩
    · exact ⟨0, true :: l, by simp⟩

/-- the canonical form of the digit list: trailing zeros removed -/
def canonD (l : List Bool) : List Bool := (l.reverse.dropWhile (fun b => b = false)).reverse

lemma dropWhile_rep (c : ℕ) (r : List Bool) (hr : r.head? ≠ some false) :
    (List.replicate c false ++ r).dropWhile (fun b => b = false) = r := by
  induction c with
  | zero =>
    cases r with
    | nil => rfl
    | cons b r => cases b <;> simp_all
  | succ c ih => simpa [List.replicate_succ] using ih

lemma canonD_getLast (l : List Bool) : (canonD l).getLast? ≠ some false := by
  obtain ⟨c, r, h1, h2⟩ := split_false l.reverse
  unfold canonD; rw [h1, dropWhile_rep c r h2, List.getLast?_reverse]; exact h2

lemma canonD_bits (n : ℕ) : canonD (Nat.bits n) = Nat.bits n := by
  unfold canonD
  have h := bits_getLast n
  rw [← List.head?_reverse] at h
  have := dropWhile_rep 0 (Nat.bits n).reverse h
  simp only [List.replicate_zero, List.nil_append] at this
  rw [this, List.reverse_reverse]

lemma canonD_len (l : List Bool) : (canonD l).length ≤ l.length := by
  unfold canonD; simp only [List.length_reverse]
  exact (List.dropWhile_sublist _).length_le.trans (by simp)

def p0 : Prog := .seq p0a (.seq (popProg .inp) (.seq (whilePop .D false) (mvProg .D .Bn)))

lemma runs_p0 (w : List Bool) (σ : Regs) (hw : σ.inp = w) (hD : σ.D = []) (hBn : σ.Bn = []) :
    Runs p0 σ { σ with inp := (pn w).2.tail, Bn := canonD (pn w).1 } (9 * w.length + 10) := by
  have e1 := runs_p0a w σ hw
  have e2 := runs_pop .inp { σ with inp := (pn w).2, D := (pn w).1.reverse ++ σ.D }
  simp only [Regs.get, Regs.set] at e2
  obtain ⟨c, r, h1, h2⟩ := split_false (pn w).1.reverse
  have e3 := runs_whilePop .D false c r
    { σ with inp := (pn w).2.tail, D := (pn w).1.reverse ++ σ.D } (by simp [Regs.get, hD, h1]) h2
  simp only [Regs.get, Regs.set] at e3
  have e4 := runs_mv .D .Bn (by decide)
    { σ with inp := (pn w).2.tail, D := r }
  simp only [Regs.get, Regs.set] at e4
  have hc : canonD (pn w).1 = r.reverse := by
    unfold canonD; rw [h1, dropWhile_rep c r h2]
  have hfin : { { σ with inp := (pn w).2.tail, D := r } with D := [], Bn := r.reverse ++ σ.Bn } =
      { σ with inp := (pn w).2.tail, Bn := canonD (pn w).1 } := by
    rw [hc, hBn]; cases σ; simp_all
  rw [hfin] at e4
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  have hl : c + r.length ≤ w.length := by
    have := congrArg List.length h1
    simp at this
    have := pn_len w
    omega
  omega

/-! ## Phase 1: fuel-bounded conversion of the numeral to unary -/

def fuelBody : Prog := .seq (popProg .F) (.seq (pushProg .Nu false) (decProg .Bn .T))

def fuelLoop : Prog := .loop (fun h => (h .Bn).isSome && (h .F).isSome) fuelBody

def p1 : Prog := .seq (copyProg .inp .F .sc) fuelLoop

lemma runs_fuelLoop (x : ℕ) (rest : List Bool) (L : ℕ) (hL : (Nat.bits x).length ≤ L) :
    ∀ (j : ℕ) (σ : Regs), j ≤ min x rest.length →
    σ.Bn = Nat.bits (x - j) → σ.F = rest.drop j → σ.Nu = List.replicate j false → σ.T = [] →
    Runs fuelLoop σ { σ with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false }
      ((min x rest.length - j) * (6 * L + 18) + 1) := by
  intro j
  induction h : min x rest.length - j generalizing j with
  | zero =>
    intro σ hj hBn hF hNu hT
    have hj' : j = min x rest.length := by omega
    subst hj'
    have : { σ with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false } = σ := by
      cases σ; simp_all
    rw [this]
    unfold fuelLoop
    refine (Runs.loopF ?_).mono (by omega)
    simp only [hd, Regs.get, hBn, hF]
    rcases Nat.le_total x rest.length with hx | hx
    · rw [min_eq_left hx, Nat.sub_self]; simp
    · rw [min_eq_right hx, List.drop_length]; simp
  | succ m ih =>
    intro σ hj hBn hF hNu hT
    have hjx : j < x := by omega
    have hjr : j < rest.length := by omega
    obtain ⟨t, r', htr⟩ : ∃ t r', rest.drop j = t :: r' := by
      cases hh : rest.drop j with
      | nil => simp at hh; omega
      | cons t r' => exact ⟨t, r', rfl⟩
    have e1 := runs_pop .F σ
    simp only [Regs.get, Regs.set] at e1
    have e2 := runs_push .Nu false { σ with F := σ.F.tail }
    simp only [Regs.get, Regs.set] at e2
    have e3 := runs_dec_bits .Bn .T (by decide) { σ with F := σ.F.tail, Nu := false :: σ.Nu }
      (x - j) (by omega) (by simp [Regs.get, hBn]) (by simp [Regs.get, hT])
    simp only [Regs.get, Regs.set] at e3
    have e4 := ih (j + 1) (by omega)
      { σ with F := σ.F.tail, Nu := false :: σ.Nu, Bn := Nat.bits (x - j - 1) } (by omega)
      (by simp; congr 1)
      (by simp [hF, htr]; rw [← List.drop_drop, htr]; rfl)
      (by simp [hNu, List.replicate_succ])
      (by simp [hT])
    have hfin : { { σ with F := σ.F.tail, Nu := false :: σ.Nu, Bn := Nat.bits (x - j - 1) } with
        Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false } =
        { σ with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false } := by
      cases σ; rfl
    rw [hfin] at e4
    unfold fuelLoop
    unfold fuelLoop at e4
    refine (Runs.loopT ?_ (e1.seq (e2.seq e3)) e4).mono ?_
    · simp only [hd, Regs.get, hBn, hF, htr]
      have : Nat.bits (x - j) ≠ [] := by rw [Ne, bits_eq_nil_iff']; omega
      cases hb : Nat.bits (x - j) with
      | nil => exact absurd hb this
      | cons _ _ => simp
    · have : (Nat.bits (x - j)).length ≤ L := le_trans (len_bits_mono (by omega)) hL
      nlinarith

lemma runs_p1 (x : ℕ) (rest : List Bool) (σ : Regs) (hinp : σ.inp = rest) (hBn : σ.Bn = Nat.bits x)
    (hF : σ.F = []) (hNu : σ.Nu = []) (hT : σ.T = []) (hsc : σ.sc = []) :
    Runs p1 σ { σ with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false }
      ((rest.length + 1) * (6 * (Nat.bits x).length + 30)) := by
  have e1 := runs_copy .inp .F .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  simp only [Regs.get, Regs.set, hF, List.append_nil] at e1
  have e2 := runs_fuelLoop x rest (Nat.bits x).length le_rfl 0 { σ with F := σ.inp } (by omega)
    (by simp [hBn]) (by simp [hinp]) (by simp [hNu]) (by simp [hT])
  have hfin : { { σ with F := σ.inp } with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false } =
      { σ with Bn := Nat.bits (x - min x rest.length), F := rest.drop (min x rest.length), Nu := List.replicate (min x rest.length) false } := by
    cases σ; rfl
  rw [hfin] at e2
  refine (e1.seq e2).mono ?_
  rw [hinp]
  have : min x rest.length - 0 ≤ rest.length := by omega
  nlinarith

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## Phase 2: read `N'^2` adjacency bits (padding with `false`) -/

def padTake : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, l => l.headD false :: padTake n l.tail

lemma padTake_length : ∀ (n : ℕ) (l : List Bool), (padTake n l).length = n
  | 0, _ => rfl
  | n + 1, l => by simp [padTake, padTake_length n]

def readAct (h : Key → Option Bool) (k : Key) : StackAct Bool :=
  if k = .Q then .pop else if k = .inp then .pop else if k = .A then .push ((h .inp).getD false)
  else .keep

def readLoop : Prog := .loop (fun h => (h .Q).isSome) (.act readAct)

lemma runs_readLoop : ∀ (n : ℕ) (σ : Regs), σ.Q.length = n →
    Runs readLoop σ { σ with Q := [], inp := σ.inp.drop n, A := (padTake n σ.inp).reverse ++ σ.A }
      (3 * n + 1)
  | 0, σ, hn => by
      have h0 : σ.Q = [] := List.length_eq_zero_iff.mp hn
      have : { σ with Q := [], inp := σ.inp.drop 0, A := (padTake 0 σ.inp).reverse ++ σ.A } = σ := by
        cases σ; simp_all [padTake]
      rw [this]; unfold readLoop
      exact Runs.loopF (by simp [hd, Regs.get, h0])
  | n + 1, σ, hn => by
      obtain ⟨t, r, htr⟩ : ∃ t r, σ.Q = t :: r := by
        cases h : σ.Q with
        | nil => rw [h] at hn; simp at hn
        | cons t r => exact ⟨t, r, rfl⟩
      set σ1 := { σ with Q := r, inp := σ.inp.tail, A := σ.inp.headD false :: σ.A } with hσ1
      have e1 : Runs (.act readAct) σ σ1 1 := by
        refine runs_act _ _ _ (fun k => ?_)
        have hh : (hd σ .inp).getD false = σ.inp.headD false := by
          simp only [hd, Regs.get]; cases σ.inp <;> rfl
        cases k <;> simp [readAct, hh, StackAct.apply, Regs.get, hσ1, htr]
      have e2 := runs_readLoop n σ1 (by rw [hσ1]; rw [htr] at hn; simpa using hn)
      have h1 : σ.inp.tail.drop n = σ.inp.drop (n + 1) := by
        cases σ.inp <;> simp
      have h2 : (padTake n σ.inp.tail).reverse ++ σ.inp.headD false :: σ.A =
          (padTake (n + 1) σ.inp).reverse ++ σ.A := by simp [padTake]
      have hfin : { σ1 with Q := [], inp := σ1.inp.drop n, A := (padTake n σ1.inp).reverse ++ σ1.A } =
          { σ with Q := [], inp := σ.inp.drop (n + 1), A := (padTake (n + 1) σ.inp).reverse ++ σ.A } := by
        rw [hσ1]; dsimp only; rw [h1, h2]
      rw [hfin] at e2
      unfold readLoop
      exact (Runs.loopT (by simp [hd, Regs.get, htr]) e1 e2).mono (by omega)

def p2 : Prog :=
  .seq (copyProg .Nu .C1 .sc)
    (.seq (repProg .Nu .Q .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) readLoop)

lemma flatten_rep_rep (n m : ℕ) (x : Bool) :
    (List.replicate n (List.replicate m x)).flatten = List.replicate (n * m) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_append_replicate]
    congr 1; ring

lemma runs_p2 (n : ℕ) (σ : Regs) (hNu : σ.Nu = List.replicate n false) (hC1 : σ.C1 = [])
    (hQ : σ.Q = []) (hsc : σ.sc = []) (hA : σ.A = []) :
    Runs p2 σ { σ with inp := σ.inp.drop (n * n), A := (padTake (n * n) σ.inp).reverse }
      ((6 * n + 7) * n + 3 * (n * n) + 6 * n + 10) := by
  have e1 := runs_copy .Nu .C1 .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
  simp only [Regs.get, Regs.set, hC1, List.append_nil] at e1
  have e2 := runs_rep .Nu .Q .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) { σ with C1 := σ.Nu } (by simp [Regs.get, hsc])
  have e3 := runs_readLoop (n * n) (({ σ with C1 := σ.Nu }.set .C1 []).set .Q
    ((List.replicate ({ σ with C1 := σ.Nu }.get .C1).length ({ σ with C1 := σ.Nu }.get .Nu)).flatten ++
      ({ σ with C1 := σ.Nu }.get .Q))) (by simp [Regs.get, Regs.set, hNu, hQ, flatten_rep_rep])
  refine (e1.seq (e2.seq (e3.congr ?_))).mono ?_
  · cases σ; simp_all [Regs.get, Regs.set, flatten_rep_rep]
  · simp [Regs.get, Regs.set, hNu]; nlinarith

/-! ## Phase 3: the strict-upper-triangle mask, and the masked adjacency stream -/

def maskRow (N i : ℕ) : List Bool := List.replicate (i + 1) false ++ List.replicate (N - i - 1) true

def Ulist (N : ℕ) : List Bool := (List.range N).flatMap (maskRow N)

def urev (N : ℕ) : ℕ → List Bool
  | 0 => []
  | j + 1 => (List.replicate (N - 1 - j) true ++ List.replicate (j + 1) false) ++ urev N j

lemma urev_eq (N : ℕ) : ∀ j, urev N j = ((List.range j).flatMap (maskRow N)).reverse
  | 0 => rfl
  | j + 1 => by
      rw [urev, urev_eq N j, List.range_succ, List.flatMap_append, List.reverse_append]
      have : N - 1 - j = N - j - 1 := by omega
      simp [maskRow, List.reverse_replicate, this]

def maskBody : Prog :=
  .seq (copyProg .Wa .U .sc) (.seq (copyProg .Wb .U .sc)
    (.seq (pushProg .Wa false) (.seq (popProg .Wb) (popProg .C1))))

def maskLoop : Prog := .loop (fun h => (h .C1).isSome) maskBody

lemma runs_maskLoop (N : ℕ) : ∀ (m j : ℕ) (σ : Regs), m + j = N →
    σ.Wa = List.replicate (j + 1) false → σ.Wb = List.replicate (N - 1 - j) true →
    σ.C1 = List.replicate m false → σ.U = urev N j → σ.sc = [] →
    Runs maskLoop σ { σ with Wa := List.replicate (N + 1) false, Wb := List.replicate (N - 1 - N) true, C1 := [], U := urev N N } (m * (12 * N + 30) + 1)
  | 0, j, σ, hm, hWa, hWb, hC1, hU, _ => by
      have hj : j = N := by omega
      subst hj
      have : { σ with Wa := List.replicate (j + 1) false, Wb := List.replicate (j - 1 - j) true, C1 := [], U := urev j j } = σ := by
        cases σ; simp_all
      rw [this]; unfold maskLoop
      exact (Runs.loopF (by simp [hd, Regs.get, hC1])).mono (by omega)
  | m + 1, j, σ, hm, hWa, hWb, hC1, hU, hsc => by
      have e1 := runs_copy .Wa .U .sc (by decide) (by decide) (by decide) σ (by simp [Regs.get, hsc])
      simp only [Regs.get, Regs.set] at e1
      have e2 := runs_copy .Wb .U .sc (by decide) (by decide) (by decide) { σ with U := σ.Wa ++ σ.U }
        (by simp [Regs.get, hsc])
      simp only [Regs.get, Regs.set] at e2
      have e3 := runs_push .Wa false { σ with U := σ.Wb ++ (σ.Wa ++ σ.U) }
      simp only [Regs.get, Regs.set] at e3
      have e4 := runs_pop .Wb { { σ with U := σ.Wb ++ (σ.Wa ++ σ.U) } with Wa := false :: σ.Wa }
      simp only [Regs.get, Regs.set] at e4
      have e5 := runs_pop .C1 { { { σ with U := σ.Wb ++ (σ.Wa ++ σ.U) } with Wa := false :: σ.Wa } with
        Wb := σ.Wb.tail }
      simp only [Regs.get, Regs.set] at e5
      have e6 := runs_maskLoop N m (j + 1)
        { { { { σ with U := σ.Wb ++ (σ.Wa ++ σ.U) } with Wa := false :: σ.Wa } with
          Wb := σ.Wb.tail } with C1 := σ.C1.tail } (by omega)
        (by simp [hWa, List.replicate_succ])
        (by simp only [hWb, List.tail_replicate]; congr 1)
        (by simp [hC1])
        (by simp [urev, hWa, hWb, hU])
        (by simp [hsc])
      have hfin : _ := e6.congr (τ' := { σ with Wa := List.replicate (N + 1) false, Wb := List.replicate (N - 1 - N) true, C1 := [], U := urev N N }) (by cases σ; rfl)
      replace e6 := hfin
      unfold maskLoop
      unfold maskLoop at e6
      refine (Runs.loopT (by simp [hd, Regs.get, hC1, List.replicate_succ])
        (e1.seq (e2.seq (e3.seq (e4.seq e5)))) e6).mono ?_
      simp [hWa, hWb]
      have : N - 1 - j ≤ N := by omega
      nlinarith

def andAct (h : Key → Option Bool) (k : Key) : StackAct Bool :=
  if k = .A then .pop else if k = .U then .pop
  else if k = .UA then .push ((h .A).getD false && (h .U).getD false) else .keep

def andLoop : Prog := .loop (fun h => (h .A).isSome) (.act andAct)

lemma runs_andLoop : ∀ (la lu : List Bool) (σ : Regs), la.length = lu.length →
    σ.A = la → σ.U = lu →
    Runs andLoop σ { σ with A := [], U := [], UA := (List.zipWith (· && ·) la lu).reverse ++ σ.UA }
      (3 * la.length + 1)
  | [], lu, σ, hl, hA, hU => by
      have hlu : lu = [] := by cases lu <;> simp_all
      subst hlu
      have : { σ with A := [], U := [], UA := (List.zipWith (· && ·) [] ([] : List Bool)).reverse ++ σ.UA } = σ := by
        cases σ; simp_all
      rw [this]; unfold andLoop
      exact Runs.loopF (by simp [hd, Regs.get, hA])
  | a :: la, [], σ, hl, _, _ => by simp at hl
  | a :: la, u :: lu, σ, hl, hA, hU => by
      set σ1 := { σ with A := la, U := lu, UA := (a && u) :: σ.UA } with hσ1
      have e1 : Runs (.act andAct) σ σ1 1 := by
        refine runs_act _ _ _ (fun k => ?_)
        cases k <;> simp [andAct, StackAct.apply, Regs.get, hσ1, hd, hA, hU]
      have e2 := runs_andLoop la lu σ1 (by simpa using hl) rfl rfl
      have hfin : { σ1 with A := [], U := [], UA := (List.zipWith (· && ·) la lu).reverse ++ σ1.UA } =
          { σ with A := [], U := [], UA := (List.zipWith (· && ·) (a :: la) (u :: lu)).reverse ++ σ.UA } := by
        rw [hσ1]; cases σ; simp
      rw [hfin] at e2
      unfold andLoop
      exact (Runs.loopT (by simp [hd, Regs.get, hA]) e1 e2).mono (by simp; omega)

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

lemma Ulist_length (N : ℕ) : (Ulist N).length = N * N := by
  unfold Ulist
  rw [List.length_flatMap]
  have : ∀ i ∈ List.range N, (maskRow N i).length = N := by
    intro i hi
    simp [maskRow] at hi ⊢; omega
  rw [List.map_congr_left this]
  simp

def p3 : Prog :=
  .seq (copyProg .Nu .C1 .sc) (.seq (drainProg .C1 .Ts true) (.seq (copyProg .Ts .Wb .sc)
    (.seq (popProg .Wb) (.seq (pushProg .Wa false) (.seq (copyProg .Nu .C1 .sc)
      (.seq maskLoop andLoop))))))

lemma runs_p3 (n : ℕ) (la : List Bool) (σ : Regs) (hNu : σ.Nu = List.replicate n false)
    (hC1 : σ.C1 = []) (hTs : σ.Ts = []) (hWb : σ.Wb = []) (hWa : σ.Wa = []) (hU : σ.U = [])
    (hsc : σ.sc = []) (hUA : σ.UA = []) (hA : σ.A = la.reverse) (hla : la.length = n * n) :
    Runs p3 σ { σ with Ts := List.replicate n true, Wa := List.replicate (n + 1) false, Wb := List.replicate (n - 1 - n) true, C1 := [], U := [], A := [], UA := List.zipWith (· && ·) la (Ulist n) }
      (n * (12 * n + 30) + 3 * (n * n) + 30 * n + 30) := by
  have hz : (List.zipWith (· && ·) la.reverse (Ulist n).reverse).reverse =
      List.zipWith (· && ·) la (Ulist n) := by
    rw [List.reverse_zipWith (by simp [hla, Ulist_length])]; simp
  refine (((runs_copy .Nu .C1 .sc (by decide) (by decide) (by decide) σ ?_).seq
    ((runs_drain .C1 .Ts (by decide) true n _ ?_).seq
    ((runs_copy .Ts .Wb .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_pop .Wb _).seq
    ((runs_push .Wa false _).seq
    ((runs_copy .Nu .C1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_maskLoop n n 0 _ (by omega) ?_ ?_ ?_ ?_ ?_).seq
    (runs_andLoop la.reverse (Ulist n).reverse _ ?_ ?_ ?_)))))))).congr ?_).mono ?_
  all_goals (try simp [Regs.get, Regs.set, hNu, hC1, hTs, hWb, hWa, hU, hsc, hUA, hA, hla, Ulist_length,
    urev, urev_eq])
  · simp [Ulist]
  · cases σ; simp_all
  · nlinarith

/-! ## Phase 4: counts -/

def cntAct (h : Key → Option Bool) (k : Key) : StackAct Bool :=
  if k = .S1 then .pop else if k = .Ec then (if h .S1 = some true then .push false else .keep)
  else .keep

def cntLoop : Prog := .loop (fun h => (h .S1).isSome) (.act cntAct)

lemma runs_cntLoop : ∀ (l : List Bool) (σ : Regs), σ.S1 = l →
    Runs cntLoop σ { σ with S1 := [], Ec := List.replicate (l.count true) false ++ σ.Ec }
      (3 * l.length + 1)
  | [], σ, hl => by
      have : { σ with S1 := [], Ec := List.replicate (([] : List Bool).count true) false ++ σ.Ec } = σ := by
        cases σ; simp_all
      rw [this]; unfold cntLoop
      exact Runs.loopF (by simp [hd, Regs.get, hl])
  | b :: l, σ, hl => by
      set σ1 := { σ with S1 := l, Ec := (if b then [false] else []) ++ σ.Ec } with hσ1
      have e1 : Runs (.act cntAct) σ σ1 1 := by
        refine runs_act _ _ _ (fun k => ?_)
        cases b <;> cases k <;> simp [cntAct, StackAct.apply, Regs.get, hσ1, hd, hl]
      have e2 := runs_cntLoop l σ1 rfl
      have hfin : { σ1 with S1 := [], Ec := List.replicate (l.count true) false ++ σ1.Ec } =
          { σ with S1 := [], Ec := List.replicate ((b :: l).count true) false ++ σ.Ec } := by
        rw [hσ1]; cases σ; cases b <;> simp [List.replicate_succ']
      rw [hfin] at e2
      unfold cntLoop
      exact (Runs.loopT (by simp [hd, Regs.get, hl]) e1 e2).mono (by simp; omega)

lemma runs_repeatCopy (a d : Key) (had : a ≠ d) (ha : a ≠ .sc) (hd' : d ≠ .sc) :
    ∀ (j : ℕ) (σ : Regs), σ.sc = [] →
    Runs (repeatP j (copyProg a d .sc)) σ (σ.set d ((List.replicate j (σ.get a)).flatten ++ σ.get d))
      (j * (6 * (σ.get a).length + 4) + 1)
  | 0, σ, _ => by
      have : σ.set d ((List.replicate 0 (σ.get a)).flatten ++ σ.get d) = σ := by
        simp [Regs.set_get]
      rw [this]; exact (runs_skip σ).mono (by omega)
  | j + 1, σ, hsc => by
      have e1 := runs_copy a d .sc had ha hd' σ (by simp [Regs.get, hsc])
      have e2 := runs_repeatCopy a d had ha hd' j (σ.set d (σ.get a ++ σ.get d)) (by
        cases d <;> first | exact hsc | exact absurd rfl hd')
      have hga : (σ.set d (σ.get a ++ σ.get d)).get a = σ.get a := Regs.get_set_ne _ had _
      rw [hga] at e2
      refine (e1.seq (e2.congr ?_)).mono (by nlinarith)
      rw [Regs.get_set_self]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs
      · simp [List.replicate_succ']
      · rfl

lemma runs_repeatPush (d : Key) (x : Bool) : ∀ (j : ℕ) (σ : Regs),
    Runs (repeatP j (pushProg d x)) σ (σ.set d (List.replicate j x ++ σ.get d)) (2 * j + 1)
  | 0, σ => by
      have : σ.set d (List.replicate 0 x ++ σ.get d) = σ := by simp [Regs.set_get]
      rw [this]; exact runs_skip σ
  | j + 1, σ => by
      have e1 := runs_push d x σ
      have e2 := runs_repeatPush d x j (σ.set d (x :: σ.get d))
      have hfin : (σ.set d (x :: σ.get d)).set d (List.replicate j x ++ (σ.set d (x :: σ.get d)).get d) =
          σ.set d (List.replicate (j + 1) x ++ σ.get d) := by
        rw [Regs.get_set_self]
        apply Regs.ext_get; funext i; simp only [Regs.get_set]
        split_ifs
        · simp [List.replicate_succ']
        · rfl
      rw [hfin] at e2
      exact (e1.seq e2).mono (by omega)

/-! ### floor division by a constant -/

def divBody (b : ℕ) : Prog :=
  .seq (popProg .AN) (.branch (fun h => (h .R).isSome) (popProg .R)
    (.seq (pushProg .Kk false) (repeatP (b - 1) (pushProg .R false))))

def divLoop (b : ℕ) : Prog := .loop (fun h => (h .AN).isSome) (divBody b)

lemma div_step (b t : ℕ) (hb : 0 < b) :
    (t % b < b - 1 → (t + 1) % b = t % b + 1 ∧ (t + 1) / b = t / b) ∧
    (t % b = b - 1 → (t + 1) % b = 0 ∧ (t + 1) / b = t / b + 1) := by
  have hdm := Nat.div_add_mod t b
  have hlt := Nat.mod_lt t hb
  constructor
  · intro h
    have e : t + 1 = (t % b + 1) + b * (t / b) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hb,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    simp
  · intro h
    have e : t + 1 = b * (t / b + 1) := by
      have : b * (t / b + 1) = b * (t / b) + b := by ring
      omega
    rw [e, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hb]
    simp

lemma runs_divLoop (b : ℕ) (hb : 0 < b) : ∀ (m t : ℕ) (σ : Regs),
    σ.AN.length = m → σ.Kk = List.replicate (t / b) false →
    σ.R = List.replicate (b - 1 - t % b) false →
    Runs (divLoop b) σ { σ with AN := [], Kk := List.replicate ((t + m) / b) false, R := List.replicate (b - 1 - (t + m) % b) false } (m * (2 * b + 8) + 1)
  | 0, t, σ, hm, hK, hR => by
      have h0 : σ.AN = [] := List.length_eq_zero_iff.mp hm
      have : { σ with AN := [], Kk := List.replicate ((t + 0) / b) false, R := List.replicate (b - 1 - (t + 0) % b) false } = σ := by
        cases σ; simp_all
      rw [this]; unfold divLoop
      exact (Runs.loopF (by simp [hd, Regs.get, h0])).mono (by omega)
  | m + 1, t, σ, hm, hK, hR => by
      obtain ⟨x, r, hxr⟩ : ∃ x r, σ.AN = x :: r := by
        cases h : σ.AN with
        | nil => rw [h] at hm; simp at hm
        | cons x r => exact ⟨x, r, rfl⟩
      have e1 := runs_pop .AN σ
      simp only [Regs.get, Regs.set, hxr, List.tail_cons] at e1
      have hlt := Nat.mod_lt t hb
      obtain ⟨σ2, e2, h2K, h2R, h2AN⟩ : ∃ σ2, Runs (.branch (fun h => (h .R).isSome) (popProg .R)
          (.seq (pushProg .Kk false) (repeatP (b - 1) (pushProg .R false)))) { σ with AN := r } σ2
          (2 * b + 4) ∧ σ2.Kk = List.replicate ((t + 1) / b) false ∧
          σ2.R = List.replicate (b - 1 - (t + 1) % b) false ∧ σ2 = { σ with AN := r, Kk := σ2.Kk, R := σ2.R } := by
        by_cases hc : t % b < b - 1
        · obtain ⟨hm1, hd1⟩ := (div_step b t hb).1 hc
          have e := runs_pop .R { σ with AN := r }
          simp only [Regs.get, Regs.set] at e
          refine ⟨_, (Runs.brT (by simp [hd, Regs.get, hR]; omega) e).mono (by omega), ?_, ?_, ?_⟩
          · simp [hK, hd1]
          · simp [hR, hm1]; omega
          · cases σ; rfl
        · have hc' : t % b = b - 1 := by omega
          obtain ⟨hm1, hd1⟩ := (div_step b t hb).2 hc'
          have ea := runs_push .Kk false { σ with AN := r }
          simp only [Regs.get, Regs.set] at ea
          have eb := runs_repeatPush .R false (b - 1) { { σ with AN := r } with Kk := false :: σ.Kk }
          simp only [Regs.get, Regs.set] at eb
          refine ⟨_, (Runs.brF (by simp [hd, Regs.get, hR, hc']) (ea.seq eb)).mono (by omega), ?_, ?_, ?_⟩
          · simp [hK, hd1, List.replicate_succ]
          · simp [hR, hm1, hc']
          · cases σ; rfl
      have e3 := runs_divLoop b hb m (t + 1) σ2 (by rw [h2AN]; rw [hxr] at hm; simpa using hm) h2K h2R
      have hfin : { σ2 with AN := [], Kk := List.replicate ((t + 1 + m) / b) false, R := List.replicate (b - 1 - (t + 1 + m) % b) false } =
          { σ with AN := [], Kk := List.replicate ((t + (m + 1)) / b) false, R := List.replicate (b - 1 - (t + (m + 1)) % b) false } := by
        rw [h2AN, show t + 1 + m = t + (m + 1) by ring]
      rw [hfin] at e3
      unfold divLoop
      unfold divLoop at e3
      exact (Runs.loopT (by simp [hd, Regs.get, hxr]) (e1.seq e2) e3).mono (by nlinarith)

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

abbrev nb := NSWApxHard.Reduction.natBits

/-! ## selection loops -/

def selLoop (K : Key) (l1 l0 : List Bool) : Prog :=
  .loop (fun h => (h K).isSome)
    (.seq (.branch (fun h => decide (h K = some true)) (emitC l1) (emitC l0)) (popProg K))

lemma runs_selLoop (K : Key) (hK : K ≠ .O) (l1 l0 : List Bool) : ∀ (bs : List Bool) (σ : Regs),
    σ.get K = bs →
    Runs (selLoop K l1 l0) σ ((σ.set K []).set .O
      ((bs.flatMap (fun b => if b then l1 else l0)).reverse ++ σ.O))
      (bs.length * (2 * (l1.length + l0.length) + 6) + 1)
  | [], σ, hl => by
      have : (σ.set K []).set .O ((([] : List Bool).flatMap (fun b => if b then l1 else l0)).reverse ++ σ.O) = σ := by
        simp only [List.flatMap_nil, List.reverse_nil, List.nil_append]
        rw [← hl, Regs.set_get]; cases σ; rfl
      rw [this]; unfold selLoop
      exact (Runs.loopF (by simp [hd, hl])).mono (by omega)
  | b :: l, σ, hl => by
      have e1 : Runs (.branch (fun h => decide (h K = some true)) (emitC l1) (emitC l0)) σ
          (σ.set .O ((if b then l1 else l0).reverse ++ σ.O)) (2 * (l1.length + l0.length) + 2) := by
        cases b
        · have := runs_emitC l0 σ
          exact (Runs.brF (by simp [hd, hl]) this).mono (by simp <;> omega)
        · have := runs_emitC l1 σ
          exact (Runs.brT (by simp [hd, hl]) this).mono (by simp <;> omega)
      set σ1 := σ.set .O ((if b then l1 else l0).reverse ++ σ.O) with hσ1
      have e2 := runs_pop K σ1
      set σ2 := σ1.set K (σ1.get K).tail with hσ2
      have h2 : σ2.get K = l := by
        rw [hσ2, Regs.get_set_self, hσ1, Regs.get_set_ne _ hK, hl]; rfl
      have e3 := runs_selLoop K hK l1 l0 l σ2 h2
      have hfin : (σ2.set K []).set .O ((l.flatMap (fun b => if b then l1 else l0)).reverse ++ σ2.O) =
          (σ.set K []).set .O (((b :: l).flatMap (fun b => if b then l1 else l0)).reverse ++ σ.O) := by
        have : σ2.O = (if b then l1 else l0).reverse ++ σ.O := by
          have := Regs.get_set_ne σ1 (Ne.symm hK) (σ1.get K).tail
          rw [← hσ2] at this
          simp only [Regs.get] at this
          rw [this, hσ1]; cases σ; rfl
        rw [this]
        apply Regs.ext_get; funext i
        simp only [hσ2, hσ1, Regs.get_set]
        split_ifs <;> simp_all
      rw [hfin] at e3
      unfold selLoop
      refine (Runs.loopT (by simp [hd, hl]) (e1.seq e2) e3).mono ?_
      simp; nlinarith

/-! ## the incidence scan of a vertex row -/

def scanV (uV : ℕ) : List Bool → List Bool → List Bool → List Bool
  | a :: as, r :: rs, c :: cs =>
      (if a then nb (if r then uV else 0) ++ nb (if c then uV else 0) else []) ++ scanV uV as rs cs
  | _, _, _ => []

def pop3Act (h : Key → Option Bool) (k : Key) : StackAct Bool :=
  if k = .S1 then .pop else if k = .RF then .pop else if k = .CF then .pop else .keep

def scanBody (uV : ℕ) : Prog :=
  .seq (.branch (fun h => decide (h .S1 = some true))
      (.seq (.branch (fun h => decide (h .RF = some true)) (emitC (nb uV)) (emitC (nb 0)))
        (.branch (fun h => decide (h .CF = some true)) (emitC (nb uV)) (emitC (nb 0))))
      skipP)
    (.act pop3Act)

def scanLoop (uV : ℕ) : Prog := .loop (fun h => (h .S1).isSome) (scanBody uV)

lemma runs_scanLoop (uV cb : ℕ) (hcb : (nb uV).length + (nb 0).length ≤ cb) :
    ∀ (as rs cs : List Bool) (σ : Regs), as.length = rs.length → as.length = cs.length →
    σ.S1 = as → σ.RF = rs → σ.CF = cs →
    Runs (scanLoop uV) σ { σ with S1 := [], RF := [], CF := [], O := (scanV uV as rs cs).reverse ++ σ.O }
      (as.length * (4 * cb + 12) + 1)
  | [], rs, cs, σ, h1, h2, hS, hR, hC => by
      have hr : rs = [] := List.length_eq_zero_iff.mp h1.symm
      have hc : cs = [] := List.length_eq_zero_iff.mp h2.symm
      subst hr; subst hc
      have : { σ with S1 := [], RF := [], CF := [], O := (scanV uV [] [] []).reverse ++ σ.O } = σ := by
        cases σ; simp_all [scanV]
      rw [this]; unfold scanLoop
      exact (Runs.loopF (by simp [hd, Regs.get, hS])).mono (by omega)
  | a :: as, [], cs, σ, h1, _, _, _, _ => by simp at h1
  | a :: as, r :: rs, [], σ, _, h2, _, _, _ => by simp at h2
  | a :: as, r :: rs, c :: cs, σ, h1, h2, hS, hR, hC => by
      set blk := (if a then nb (if r then uV else 0) ++ nb (if c then uV else 0) else []) with hblk
      have e1 : Runs (.branch (fun h => decide (h .S1 = some true))
          (.seq (.branch (fun h => decide (h .RF = some true)) (emitC (nb uV)) (emitC (nb 0)))
            (.branch (fun h => decide (h .CF = some true)) (emitC (nb uV)) (emitC (nb 0))))
          skipP) σ { σ with O := blk.reverse ++ σ.O } (4 * cb + 8) := by
        cases a
        · have : { σ with O := blk.reverse ++ σ.O } = σ := by cases σ; simp [hblk]
          rw [this]
          exact (Runs.brF (by simp [hd, Regs.get, hS]) (runs_skip σ)).mono (by omega)
        · have eR : Runs (.branch (fun h => decide (h .RF = some true)) (emitC (nb uV)) (emitC (nb 0)))
              σ { σ with O := (nb (if r then uV else 0)).reverse ++ σ.O } (2 * cb + 2) := by
            cases r
            · have := runs_emitC (nb 0) σ
              simp only [Regs.set] at this
              exact (Runs.brF (by simp [hd, Regs.get, hR]) this).mono (by simp; omega)
            · have := runs_emitC (nb uV) σ
              simp only [Regs.set] at this
              exact (Runs.brT (by simp [hd, Regs.get, hR]) this).mono (by simp; omega)
          have eC : Runs (.branch (fun h => decide (h .CF = some true)) (emitC (nb uV)) (emitC (nb 0)))
              { σ with O := (nb (if r then uV else 0)).reverse ++ σ.O }
              { σ with O := (nb (if c then uV else 0)).reverse ++ ((nb (if r then uV else 0)).reverse ++ σ.O) }
              (2 * cb + 2) := by
            cases c
            · have := runs_emitC (nb 0) { σ with O := (nb (if r then uV else 0)).reverse ++ σ.O }
              simp only [Regs.set] at this
              exact (Runs.brF (by simp [hd, Regs.get, hC]) this).mono (by simp; omega)
            · have := runs_emitC (nb uV) { σ with O := (nb (if r then uV else 0)).reverse ++ σ.O }
              simp only [Regs.set] at this
              exact (Runs.brT (by simp [hd, Regs.get, hC]) this).mono (by simp; omega)
          have := (eR.seq eC)
          refine (Runs.brT (by simp [hd, Regs.get, hS]) (this.congr ?_)).mono (by omega)
          cases σ; simp [hblk]
      set σ1 := { σ with O := blk.reverse ++ σ.O } with hσ1
      set σ2 := { σ1 with S1 := as, RF := rs, CF := cs } with hσ2
      have e2 : Runs (.act pop3Act) σ1 σ2 1 := by
        refine runs_act _ _ _ (fun k => ?_)
        cases k <;> simp [pop3Act, StackAct.apply, Regs.get, hσ1, hσ2, hS, hR, hC]
      have e3 := runs_scanLoop uV cb hcb as rs cs σ2 (by simpa using h1) (by simpa using h2) rfl rfl rfl
      have hfin : { σ2 with S1 := [], RF := [], CF := [], O := (scanV uV as rs cs).reverse ++ σ2.O } =
          { σ with S1 := [], RF := [], CF := [], O := (scanV uV (a :: as) (r :: rs) (c :: cs)).reverse ++ σ.O } := by
        rw [hσ2, hσ1]; cases σ; simp [scanV, hblk]
      rw [hfin] at e3
      unfold scanLoop
      unfold scanLoop at e3
      refine (Runs.loopT (by simp [hd, Regs.get, hS]) (e1.seq e2) e3).mono ?_
      simp; nlinarith

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## vertex rows -/

def ohL (n v : ℕ) : List Bool := List.replicate v false ++ true :: List.replicate (n - v - 1) false
def rfL (n v : ℕ) : List Bool :=
  List.replicate (v * n) false ++ List.replicate n true ++ List.replicate ((n - v - 1) * n) false
def cfL (n v : ℕ) : List Bool := (List.replicate n (ohL n v)).flatten

def vrow (k E uS uV n : ℕ) (ua : List Bool) (v : ℕ) : List Bool :=
  (List.replicate k (nb uS)).flatten ++ (List.replicate E (nb 0)).flatten ++ scanV uV ua (rfL n v) (cfL n v)

def vBody (uS uV : ℕ) : Prog :=
  .seq (copyProg .Kk .C1 .sc) (.seq (repEmit .C1 (nb uS)) (.seq (copyProg .Ec .C1 .sc)
  (.seq (repEmit .C1 (nb 0)) (.seq (copyProg .Vr .OH .sc) (.seq (popProg .OH)
  (.seq (pushProg .OH true) (.seq (copyProg .Vd .OH .sc) (.seq (copyProg .Nu .C1 .sc)
  (.seq (repProg .OH .CF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  (.seq (clearProg .OH) (.seq (copyProg .Vr .C1 .sc) (.seq (popProg .C1)
  (.seq (repProg .Nu .RF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  (.seq (copyProg .Ts .RF .sc) (.seq (copyProg .Vd .C1 .sc)
  (.seq (repProg .Nu .RF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  (.seq (copyProg .UA .S1 .sc) (.seq (scanLoop uV) (.seq (popProg .Vr) (pushProg .Vd false))))))))))))))))))))

lemma ohL_length (n v : ℕ) (hv : v < n) : (ohL n v).length = n := by
  simp [ohL]; omega

lemma rfL_length (n v : ℕ) (hv : v < n) : (rfL n v).length = n * n := by
  simp only [rfL, List.length_append, List.length_replicate]
  have : (n - v - 1) * n + v * n + n = n * n := by
    have h : n - v - 1 + v + 1 = n := by omega
    calc (n - v - 1) * n + v * n + n = (n - v - 1 + v + 1) * n := by ring
      _ = n * n := by rw [h]
  omega

lemma cfL_length (n v : ℕ) (hv : v < n) : (cfL n v).length = n * n := by
  simp [cfL, ohL_length n v hv]

lemma runs_vBody (n k E v uS uV cb : ℕ) (ua : List Bool) (hv : v < n)
    (hcb1 : (nb uS).length ≤ cb) (hcb2 : (nb uV).length + (nb 0).length ≤ cb) (σ : Regs)
    (hNu : σ.Nu = List.replicate n false) (hTs : σ.Ts = List.replicate n true) (hUA : σ.UA = ua)
    (hua : ua.length = n * n) (hKk : σ.Kk = List.replicate k false)
    (hEc : σ.Ec = List.replicate E false) (hC1 : σ.C1 = []) (hOH : σ.OH = []) (hCF : σ.CF = [])
    (hRF : σ.RF = []) (hS1 : σ.S1 = []) (hsc : σ.sc = []) (hVd : σ.Vd = List.replicate v false)
    (hVr : σ.Vr = List.replicate (n - v) false) :
    Runs (vBody uS uV) σ { σ with Vd := List.replicate (v + 1) false, Vr := List.replicate (n - v - 1) false, O := (vrow k E uS uV n ua v).reverse ++ σ.O }
      (k * (2 * cb + 11) + E * (2 * cb + 11) + n * n * (4 * cb + 30) + 60 * n + 100) := by
  refine (((runs_copy .Kk .C1 .sc (by decide) (by decide) (by decide) σ ?_).seq
    ((runs_repEmit .C1 (by decide) (nb uS) k _ ?_).seq
    ((runs_copy .Ec .C1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_repEmit .C1 (by decide) (nb 0) E _ ?_).seq
    ((runs_copy .Vr .OH .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_pop .OH _).seq
    ((runs_push .OH true _).seq
    ((runs_copy .Vd .OH .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .Nu .C1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_rep .OH .CF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_clear .OH _).seq
    ((runs_copy .Vr .C1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_pop .C1 _).seq
    ((runs_rep .Nu .RF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .Ts .RF .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .Vd .C1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_rep .Nu .RF .C1 .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .UA .S1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_scanLoop uV cb hcb2 ua (rfL n v) (cfL n v) _ ?_ ?_ ?_ ?_ ?_).seq
    ((runs_pop .Vr _).seq
    (runs_push .Vd false _))))))))))))))))))))).congr ?_).mono ?_
  all_goals (try simp [Regs.get, Regs.set, hNu, hTs, hUA, hua, hKk, hEc, hC1, hOH, hCF, hRF, hS1, hsc,
    hVd, hVr, rfL_length n v hv, cfL_length n v hv])
  · simp [rfL]
  · rfl
  · exact ⟨by simp [vrow], by simp [List.replicate_succ]⟩
  · have h1 : v + (n - v - 1 + 1) = n := by omega
    rw [h1]
    have hk1 : k * (nb uS).length ≤ k * cb := Nat.mul_le_mul_left _ hcb1
    have hE1 : E * (nb 0).length ≤ E * cb := Nat.mul_le_mul_left _ (by omega)
    have hnv : (6 * n + 7) * (n - v - 1) + (6 * n + 7) * v ≤ (6 * n + 7) * n := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    have h2 : n - v + v = n := by omega
    nlinarith [Nat.sub_le n v, hk1, hE1, hnv, h2]

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

def vLoop (uS uV : ℕ) : Prog := .loop (fun h => (h .Vr).isSome) (vBody uS uV)

lemma runs_vLoop (n k E uS uV cb : ℕ) (ua : List Bool)
    (hcb1 : (nb uS).length ≤ cb) (hcb2 : (nb uV).length + (nb 0).length ≤ cb) :
    ∀ (m v : ℕ) (σ : Regs), m + v = n →
    σ.Nu = List.replicate n false → σ.Ts = List.replicate n true → σ.UA = ua →
    ua.length = n * n → σ.Kk = List.replicate k false →
    σ.Ec = List.replicate E false → σ.C1 = [] → σ.OH = [] → σ.CF = [] →
    σ.RF = [] → σ.S1 = [] → σ.sc = [] → σ.Vd = List.replicate v false →
    σ.Vr = List.replicate m false →
    Runs (vLoop uS uV) σ { σ with Vd := List.replicate n false, Vr := [], O := ((List.range m).flatMap (fun i => vrow k E uS uV n ua (v + i))).reverse ++ σ.O }
      (m * (k * (2 * cb + 11) + E * (2 * cb + 11) + n * n * (4 * cb + 30) + 60 * n + 102) + 1)
  | 0, v, σ, hm, _, _, _, _, _, _, _, _, _, _, _, _, hVd, hVr => by
      have : { σ with Vd := List.replicate n false, Vr := [], O := ((List.range 0).flatMap (fun i => vrow k E uS uV n ua (v + i))).reverse ++ σ.O } = σ := by
        have : v = n := by omega
        subst this
        cases σ; simp_all
      rw [this]; unfold vLoop
      exact (Runs.loopF (by simp [hd, Regs.get, hVr])).mono (by omega)
  | m + 1, v, σ, hm, hNu, hTs, hUA, hua, hKk, hEc, hC1, hOH, hCF, hRF, hS1, hsc, hVd, hVr => by
      have e1 := runs_vBody n k E v uS uV cb ua (by omega) hcb1 hcb2 σ hNu hTs hUA hua hKk hEc hC1
        hOH hCF hRF hS1 hsc hVd (by rw [hVr]; congr 1; omega)
      have e2 := runs_vLoop n k E uS uV cb ua hcb1 hcb2 m (v + 1) { σ with Vd := List.replicate (v + 1) false, Vr := List.replicate (n - v - 1) false, O := (vrow k E uS uV n ua v).reverse ++ σ.O } (by omega)
        (by simp [hNu]) (by simp [hTs]) (by simp [hUA]) hua (by simp [hKk]) (by simp [hEc])
        (by simp [hC1]) (by simp [hOH]) (by simp [hCF]) (by simp [hRF]) (by simp [hS1])
        (by simp [hsc]) (by simp) (by simp; congr 1; omega)
      unfold vLoop
      unfold vLoop at e2
      refine ((Runs.loopT (by simp [hd, Regs.get, hVr]) e1 e2).congr ?_).mono ?_
      · cases σ
        simp only [Regs.mk.injEq, true_and, and_true]
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.reverse_append,
          List.append_assoc]
        simp only [add_zero]
        congr 3
        funext i; congr 1; omega
      · nlinarith

/-! ## edge rows -/

def erow (k E uA uB e : ℕ) : List Bool :=
  (List.replicate k (nb 0)).flatten ++ (ohL E e).flatMap (fun b => if b then nb uA else nb 0) ++
    (ohL E e).flatMap (fun b => if b then nb uB ++ nb uB else nb 0 ++ nb 0)

def eBody (uA uB : ℕ) : Prog :=
  .seq (copyProg .Kk .C1 .sc) (.seq (repEmit .C1 (nb 0)) (.seq (copyProg .Er .OH .sc)
  (.seq (popProg .OH) (.seq (pushProg .OH true) (.seq (copyProg .Ed .OH .sc)
  (.seq (copyProg .OH .S1 .sc) (.seq (selLoop .S1 (nb uA) (nb 0))
  (.seq (selLoop .OH (nb uB ++ nb uB) (nb 0 ++ nb 0)) (.seq (popProg .Er) (pushProg .Ed false))))))))))

lemma runs_eBody (k E e uA uB cb : ℕ) (he : e < E)
    (hcb : (nb uA).length + (nb uB).length + (nb 0).length ≤ cb) (σ : Regs)
    (hKk : σ.Kk = List.replicate k false) (hC1 : σ.C1 = []) (hOH : σ.OH = [])
    (hS1 : σ.S1 = []) (hsc : σ.sc = []) (hEd : σ.Ed = List.replicate e false)
    (hEr : σ.Er = List.replicate (E - e) false) :
    Runs (eBody uA uB) σ { σ with Ed := List.replicate (e + 1) false, Er := List.replicate (E - e - 1) false, O := (erow k E uA uB e).reverse ++ σ.O }
      (k * (2 * cb + 11) + E * (8 * cb + 40) + 60) := by
  refine (((runs_copy .Kk .C1 .sc (by decide) (by decide) (by decide) σ ?_).seq
    ((runs_repEmit .C1 (by decide) (nb 0) k _ ?_).seq
    ((runs_copy .Er .OH .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_pop .OH _).seq
    ((runs_push .OH true _).seq
    ((runs_copy .Ed .OH .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .OH .S1 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_selLoop .S1 (by decide) (nb uA) (nb 0) (ohL E e) _ ?_).seq
    ((runs_selLoop .OH (by decide) (nb uB ++ nb uB) (nb 0 ++ nb 0) (ohL E e) _ ?_).seq
    ((runs_pop .Er _).seq
    (runs_push .Ed false _))))))))))).congr ?_).mono ?_
  all_goals (try simp [Regs.get, Regs.set, hKk, hC1, hOH, hS1, hsc, hEd, hEr, ohL_length E e he])
  · rfl
  · rfl
  · exact ⟨by simp [erow], by simp [List.replicate_succ]⟩
  · have hk1 : k * (nb 0).length ≤ k * cb := Nat.mul_le_mul_left _ (by omega)
    have hE1 : E * ((nb uA).length + (nb 0).length) ≤ E * cb := Nat.mul_le_mul_left _ (by omega)
    have hE2 : E * ((nb uB).length + (nb 0).length) ≤ E * cb := Nat.mul_le_mul_left _ (by omega)
    have h2 : E - e + e = E := by omega
    have h3 : e + (E - e - 1 + 1) = E := by omega
    rw [h3]
    nlinarith [Nat.sub_le E e, hk1, hE1, hE2, h2]

def eLoop (uA uB : ℕ) : Prog := .loop (fun h => (h .Er).isSome) (eBody uA uB)

lemma runs_eLoop (k E uA uB cb : ℕ) (hcb : (nb uA).length + (nb uB).length + (nb 0).length ≤ cb) :
    ∀ (m e : ℕ) (σ : Regs), m + e = E →
    σ.Kk = List.replicate k false → σ.C1 = [] → σ.OH = [] → σ.S1 = [] → σ.sc = [] →
    σ.Ed = List.replicate e false → σ.Er = List.replicate m false →
    Runs (eLoop uA uB) σ { σ with Ed := List.replicate E false, Er := [], O := ((List.range m).flatMap (fun i => erow k E uA uB (e + i))).reverse ++ σ.O }
      (m * (k * (2 * cb + 11) + E * (8 * cb + 40) + 62) + 1)
  | 0, e, σ, hm, _, _, _, _, _, hEd, hEr => by
      have : { σ with Ed := List.replicate E false, Er := [], O := ((List.range 0).flatMap (fun i => erow k E uA uB (e + i))).reverse ++ σ.O } = σ := by
        have : e = E := by omega
        subst this
        cases σ; simp_all
      rw [this]; unfold eLoop
      exact (Runs.loopF (by simp [hd, Regs.get, hEr])).mono (by omega)
  | m + 1, e, σ, hm, hKk, hC1, hOH, hS1, hsc, hEd, hEr => by
      have e1 := runs_eBody k E e uA uB cb (by omega) hcb σ hKk hC1 hOH hS1 hsc hEd
        (by rw [hEr]; congr 1; omega)
      have e2 := runs_eLoop k E uA uB cb hcb m (e + 1) { σ with Ed := List.replicate (e + 1) false, Er := List.replicate (E - e - 1) false, O := (erow k E uA uB e).reverse ++ σ.O } (by omega)
        (by simp [hKk]) (by simp [hC1]) (by simp [hOH]) (by simp [hS1]) (by simp [hsc])
        (by simp) (by simp; omega)
      unfold eLoop
      unfold eLoop at e2
      refine ((Runs.loopT (by simp [hd, Regs.get, hEr]) e1 e2).congr ?_).mono ?_
      · cases σ
        simp only [Regs.mk.injEq, true_and, and_true]
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.reverse_append,
          List.append_assoc]
        simp only [add_zero]
        congr 3
        funext i; congr 1; omega
      · nlinarith

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## Global quantities computed from the input -/

def restOf (w : List Bool) : List Bool := (pn w).2.tail
def xOf (w : List Bool) : ℕ := bval (canonD (pn w).1)
def nOf (w : List Bool) : ℕ := min (xOf w) (restOf w).length
def uaOf (w : List Bool) : List Bool :=
  List.zipWith (· && ·) (padTake (nOf w * nOf w) (restOf w)) (Ulist (nOf w))
def EOf (w : List Bool) : ℕ := (uaOf w).count true

def σ0 (w : List Bool) : Regs := { Regs.empty with inp := w }

def SA (w : List Bool) : Regs := { Regs.empty with inp := (restOf w).drop (nOf w * nOf w), Bn := Nat.bits (xOf w - nOf w), F := (restOf w).drop (nOf w), Nu := List.replicate (nOf w) false, Ts := List.replicate (nOf w) true, Wa := List.replicate (nOf w + 1) false, UA := uaOf w }

def pA : Prog := .seq p0 (.seq p1 (.seq p2 p3))

lemma canonD_eq_bits (w : List Bool) : canonD (pn w).1 = Nat.bits (xOf w) := by
  unfold xOf; rw [bits_bval _ (canonD_getLast _)]

lemma restOf_len (w : List Bool) : (restOf w).length ≤ w.length := by
  unfold restOf; have := pn_len w; simp; omega

lemma xbits_len (w : List Bool) : (Nat.bits (xOf w)).length ≤ w.length := by
  rw [← canonD_eq_bits]; have := pn_len w; have := canonD_len (pn w).1; omega

lemma nOf_le (w : List Bool) : nOf w ≤ w.length := by
  unfold nOf; have := restOf_len w; omega

lemma uaOf_length (w : List Bool) : (uaOf w).length = nOf w * nOf w := by
  simp [uaOf, padTake_length, Ulist_length]

lemma EOf_le (w : List Bool) : EOf w ≤ nOf w * nOf w := by
  unfold EOf; rw [← uaOf_length]; exact List.count_le_length

lemma runs_pA (w : List Bool) : Runs pA (σ0 w) (SA w) (100 * ((w.length + 1) * (w.length + 1))) := by
  have hn := nOf_le w
  have hr := restOf_len w
  have hx := xbits_len w
  refine (((runs_p0 w (σ0 w) rfl rfl rfl).seq
    ((runs_p1 (xOf w) (restOf w) _ ?_ ?_ ?_ ?_ ?_ ?_).seq
    ((runs_p2 (nOf w) _ ?_ ?_ ?_ ?_ ?_).seq
    (runs_p3 (nOf w) (padTake (nOf w * nOf w) (restOf w)) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)))).congr ?_).mono ?_
  all_goals (try simp [σ0, Regs.empty, canonD_eq_bits, padTake_length])
  all_goals (try rfl)
  · simp [SA, restOf, nOf, uaOf, Regs.empty]
  · set L := w.length
    have h1 : ((restOf w).length + 1) * (6 * (Nat.bits (xOf w)).length + 30) ≤ (L + 1) * (6 * L + 30) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (6 * nOf w + 7) * nOf w ≤ (6 * L + 7) * L := Nat.mul_le_mul (by omega) hn
    have h3 : nOf w * nOf w ≤ L * L := Nat.mul_le_mul hn hn
    have h4 : nOf w * (12 * nOf w + 30) ≤ L * (12 * L + 30) := Nat.mul_le_mul hn (by omega)
    nlinarith

end NSWEnc

namespace NSWEnc

open CookPvsNP

def kOf (a b : ℕ) (w : List Bool) : ℕ := (a * nOf w) / b
def TOf (a b c1 c2 : ℕ) (w : List Bool) : ℕ :=
  c2 ^ (3 * kOf a b w + nOf w) * (c1 ^ (4 * nOf w - 3 * kOf a b w) * 1)

def SB (a b c1 c2 : ℕ) (w : List Bool) : Regs := { SA w with Ec := List.replicate (EOf w) false, Kk := List.replicate (kOf a b w) false, R := List.replicate (b - 1 - (a * nOf w) % b) false, Bnn := Nat.bits (EOf w + nOf w), Bnm := Nat.bits (3 * EOf w + kOf a b w), X := Nat.bits (TOf a b c1 c2 w) }

def pB (a b c1 c2 : ℕ) : Prog :=
  .seq (copyProg .UA .S1 .sc) (.seq cntLoop (.seq (repeatP a (copyProg .Nu .AN .sc))
  (.seq (repeatP (b - 1) (pushProg .R false)) (.seq (divLoop b)
  (.seq (repeatP 4 (copyProg .Nu .E1 .sc)) (.seq (repeatP 3 (copyProg .Kk .C2 .sc))
  (.seq (syncPopProg .E1 .C2) (.seq (copyProg .Nu .E2 .sc) (.seq (repeatP 3 (copyProg .Kk .E2 .sc))
  (.seq (copyProg .Nu .Nn .sc) (.seq (copyProg .Ec .Nn .sc) (.seq (toBin .Nn .Bnn)
  (.seq (copyProg .Kk .Mm .sc) (.seq (repeatP 3 (copyProg .Ec .Mm .sc)) (.seq (toBin .Mm .Bnm)
  (.seq (pushProg .X true) (.seq (powLoop .E1 c1) (powLoop .E2 c2))))))))))))))))))

lemma len_bits_pow_mul (c e x : ℕ) : (Nat.bits (c ^ e * x)).length ≤ c * e + (Nat.bits x).length := by
  apply len_bits_le_of_lt
  have h1 : c ^ e ≤ 2 ^ (c * e) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le e
  have h2 : x < 2 ^ (Nat.bits x).length := by
    rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self x
  rw [pow_add]
  calc c ^ e * x ≤ 2 ^ (c * e) * x := Nat.mul_le_mul_right _ h1
    _ < 2 ^ (c * e) * 2 ^ (Nat.bits x).length := Nat.mul_lt_mul_of_pos_left h2 (by positivity)


lemma costB_bound (a b c1 c2 n E k kd mn e1 e2 l1 lT ln lm Z : ℕ) (hZ1 : 1 ≤ Z) (ha : a ≤ Z) (hb : b ≤ Z)
    (hc1 : c1 ≤ Z) (hc2 : c2 ≤ Z) (hn : n ≤ Z) (hE : E ≤ Z * Z) (hk : k ≤ Z) (hkd : kd ≤ Z)
    (hmn : mn ≤ 4 * Z) (he1 : e1 ≤ 4 * Z) (he2 : e2 ≤ 4 * Z) (hl1 : l1 ≤ 4 * (Z * Z) + 1)
    (hlT : lT ≤ 8 * (Z * Z) + 1) (hln : ln ≤ 2 * (Z * Z)) (hlm : lm ≤ 4 * (Z * Z)) :
    6 * (n * n) + 3 + 1 + (3 * (n * n) + 1 + 1 + (a * (6 * n + 4) + 1 + 1 + (2 * (b - 1) + 1 + 1 + (a * n * (2 * b + 8) + 1 + 1 + (4 * (6 * n + 4) + 1 + 1 + (3 * (6 * kd + 4) + 1 + 1 + (3 * mn + 1 + 1 + (6 * n + 3 + 1 + (3 * (6 * kd + 4) + 1 + 1 + (6 * n + 3 + 1 + (6 * E + 3 + 1 + ((E + n) * (6 * ln + 14) + 1 + 1 + (6 * kd + 3 + 1 + (3 * (6 * E + 4) + 1 + 1 + ((3 * E + k) * (6 * lm + 14) + 1 + 1 + (2 + (e1 * ((c1 + 1) * (15 * l1 + 30) + 4) + 1 + 1 + (e2 * ((c2 + 1) * (15 * lT + 30) + 4) + 1)))))))))))))))))) ≤ 4000 * Z ^ 4 := by
  have z2 : Z ≤ Z * Z := Nat.le_mul_self Z
  have z3 : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have z4 : Z * Z * Z ≤ Z * Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have hz4 : Z ^ 4 = Z * Z * Z * Z := by ring
  rw [hz4]
  have t1 : n * n ≤ Z * Z := Nat.mul_le_mul hn hn
  have t2 : a * (6 * n + 4) ≤ 10 * (Z * Z) :=
    calc a * (6 * n + 4) ≤ Z * (10 * Z) := Nat.mul_le_mul ha (by omega)
      _ = 10 * (Z * Z) := by ring
  have t3 : a * n * (2 * b + 8) ≤ 10 * (Z * Z * Z) :=
    calc a * n * (2 * b + 8) ≤ Z * Z * (10 * Z) := Nat.mul_le_mul (Nat.mul_le_mul ha hn) (by omega)
      _ = 10 * (Z * Z * Z) := by ring
  have t4 : (E + n) * (6 * ln + 14) ≤ 52 * (Z * Z * Z * Z) :=
    calc (E + n) * (6 * ln + 14) ≤ (2 * (Z * Z)) * (26 * (Z * Z)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 52 * (Z * Z * Z * Z) := by ring
  have t5 : (3 * E + k) * (6 * lm + 14) ≤ 152 * (Z * Z * Z * Z) :=
    calc (3 * E + k) * (6 * lm + 14) ≤ (4 * (Z * Z)) * (38 * (Z * Z)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 152 * (Z * Z * Z * Z) := by ring
  have t6 : (c1 + 1) * (15 * l1 + 30) ≤ 210 * (Z * Z * Z) :=
    calc (c1 + 1) * (15 * l1 + 30) ≤ (2 * Z) * (105 * (Z * Z)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 210 * (Z * Z * Z) := by ring
  have t6' : e1 * ((c1 + 1) * (15 * l1 + 30) + 4) ≤ 856 * (Z * Z * Z * Z) :=
    calc e1 * ((c1 + 1) * (15 * l1 + 30) + 4) ≤ (4 * Z) * (214 * (Z * Z * Z)) :=
          Nat.mul_le_mul he1 (by omega)
      _ = 856 * (Z * Z * Z * Z) := by ring
  have t7 : (c2 + 1) * (15 * lT + 30) ≤ 330 * (Z * Z * Z) :=
    calc (c2 + 1) * (15 * lT + 30) ≤ (2 * Z) * (165 * (Z * Z)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 330 * (Z * Z * Z) := by ring
  have t7' : e2 * ((c2 + 1) * (15 * lT + 30) + 4) ≤ 1336 * (Z * Z * Z * Z) :=
    calc e2 * ((c2 + 1) * (15 * lT + 30) + 4) ≤ (4 * Z) * (334 * (Z * Z * Z)) :=
          Nat.mul_le_mul he2 (by omega)
      _ = 1336 * (Z * Z * Z * Z) := by ring
  have tb : b - 1 ≤ Z := by omega
  linarith

lemma runs_pB (a b c1 c2 : ℕ) (hb : 0 < b) (hab : a < b) (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (w : List Bool) :
    Runs (pB a b c1 c2) (SA w) (SB a b c1 c2 w) (4000 * ((a + b + c1 + c2 + 1) * (w.length + 1)) ^ 4) := by
  have hn := nOf_le w
  have hE := EOf_le w
  have hk : kOf a b w ≤ nOf w := Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ hab.le)
  refine (((runs_copy .UA .S1 .sc (by decide) (by decide) (by decide) (SA w) ?_).seq
    ((runs_cntLoop (uaOf w) _ ?_).seq
    ((runs_repeatCopy .Nu .AN (by decide) (by decide) (by decide) a _ ?_).seq
    ((runs_repeatPush .R false (b - 1) _).seq
    ((runs_divLoop b hb (a * nOf w) 0 _ ?_ ?_ ?_).seq
    ((runs_repeatCopy .Nu .E1 (by decide) (by decide) (by decide) 4 _ ?_).seq
    ((runs_repeatCopy .Kk .C2 (by decide) (by decide) (by decide) 3 _ ?_).seq
    ((runs_syncpop .E1 .C2 (by decide) _).seq
    ((runs_copy .Nu .E2 .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_repeatCopy .Kk .E2 (by decide) (by decide) (by decide) 3 _ ?_).seq
    ((runs_copy .Nu .Nn .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_copy .Ec .Nn .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_toBin .Nn .Bnn (by decide) (by decide) (by decide) (Nat.bits (EOf w + nOf w)).length (EOf w + nOf w) 0 _ ?_ ?_ ?_ ?_).seq
    ((runs_copy .Kk .Mm .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_repeatCopy .Ec .Mm (by decide) (by decide) (by decide) 3 _ ?_).seq
    ((runs_toBin .Mm .Bnm (by decide) (by decide) (by decide) (Nat.bits (3 * EOf w + kOf a b w)).length (3 * EOf w + kOf a b w) 0 _ ?_ ?_ ?_ ?_).seq
    ((runs_push .X true _).seq
    ((runs_powLoop .E1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) c1 (Nat.bits (c1 ^ (4 * nOf w - 3 * kOf a b w) * 1)).length hc1 (4 * nOf w - 3 * kOf a b w) 1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).seq
    (runs_powLoop .E2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) c2 (Nat.bits (TOf a b c1 c2 w)).length hc2 (3 * kOf a b w + nOf w) (c1 ^ (4 * nOf w - 3 * kOf a b w) * 1) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))))))))))))))))))).congr ?_).mono ?_
  all_goals (try simp [SA, Regs.empty, Regs.get, Regs.set, uaOf_length, EOf])
  · simp only [kOf]; ring
  · simp only [kOf] at hk ⊢; omega
  · simp only [kOf]; ring
  · simp [TOf]
  · have hmin : min (nOf w + (nOf w + (nOf w + nOf w))) (a * nOf w / b + (a * nOf w / b + a * nOf w / b)) =
        a * nOf w / b + (a * nOf w / b + a * nOf w / b) := by simp only [kOf] at hk; omega
    rw [hmin]
    simp [SB, SA, EOf, TOf, Regs.empty, kOf]
  · set Z := (a + b + c1 + c2 + 1) * (w.length + 1) with hZ
    have hL : w.length + 1 ≤ Z := Nat.le_mul_of_pos_left _ (by omega)
    have hK : a + b + c1 + c2 + 1 ≤ Z := Nat.le_mul_of_pos_right _ (by omega)
    have hEZ : List.count true (uaOf w) ≤ Z * Z := le_trans hE (Nat.mul_le_mul (by omega) (by omega))
    have he1 : 4 * nOf w - 3 * kOf a b w ≤ 4 * Z := by omega
    have he2 : 3 * kOf a b w + nOf w ≤ 4 * Z := by omega
    have z2 : Z ≤ Z * Z := Nat.le_mul_self Z
    have h' : c1 * (4 * nOf w - 3 * kOf a b w) ≤ 4 * (Z * Z) :=
      calc c1 * (4 * nOf w - 3 * kOf a b w) ≤ Z * (4 * Z) := Nat.mul_le_mul (by omega) he1
        _ = 4 * (Z * Z) := by ring
    have h'' : c2 * (3 * kOf a b w + nOf w) ≤ 4 * (Z * Z) :=
      calc c2 * (3 * kOf a b w + nOf w) ≤ Z * (4 * Z) := Nat.mul_le_mul (by omega) he2
        _ = 4 * (Z * Z) := by ring
    have hb1 : (Nat.bits 1).length = 1 := by simp
    have hl1 : (Nat.bits (c1 ^ (4 * nOf w - 3 * kOf a b w))).length ≤ 4 * (Z * Z) + 1 := by
      have := len_bits_pow_mul c1 (4 * nOf w - 3 * kOf a b w) 1
      rw [mul_one] at this; omega
    have hlT : (Nat.bits (TOf a b c1 c2 w)).length ≤ 8 * (Z * Z) + 1 := by
      have h1 := len_bits_pow_mul c2 (3 * kOf a b w + nOf w) (c1 ^ (4 * nOf w - 3 * kOf a b w) * 1)
      have h2 := len_bits_pow_mul c1 (4 * nOf w - 3 * kOf a b w) 1
      unfold TOf; omega
    have hln : (Nat.bits (List.count true (uaOf w) + nOf w)).length ≤ 2 * (Z * Z) := by
      have := len_bits_le (List.count true (uaOf w) + nOf w); omega
    have hlm : (Nat.bits (3 * List.count true (uaOf w) + kOf a b w)).length ≤ 4 * (Z * Z) := by
      have := len_bits_le (3 * List.count true (uaOf w) + kOf a b w); omega
    have hkd : a * nOf w / b ≤ Z := by simp only [kOf] at hk; omega
    exact costB_bound a b c1 c2 (nOf w) _ (kOf a b w) _ _ _ _ _ _ _ _ Z (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hEZ (by omega) hkd (min_le_left _ _ |>.trans (by omega)) he1 he2 hl1 hlT hln hlm

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

def VR (a b uS uV : ℕ) (w : List Bool) : List Bool :=
  (List.range (nOf w)).flatMap (fun i => vrow (kOf a b w) (EOf w) uS uV (nOf w) (uaOf w) (0 + i))

def ER (a b uA uB : ℕ) (w : List Bool) : List Bool :=
  (List.range (EOf w)).flatMap (fun i => erow (kOf a b w) (EOf w) uA uB (0 + i))

def OUT (a b c1 c2 uS uV uA uB : ℕ) (w : List Bool) : List Bool :=
  nb (EOf w + nOf w) ++ nb (3 * EOf w + kOf a b w) ++ nb (TOf a b c1 c2 w) ++ VR a b uS uV w ++ ER a b uA uB w

def SC (a b c1 c2 uS uV uA uB : ℕ) (w : List Bool) : Regs := { SB a b c1 c2 w with Bnn := [], Bnm := [], X := [], Vd := List.replicate (nOf w) false, Vr := [], Ed := List.replicate (EOf w) false, Er := [], O := [], out := OUT a b c1 c2 uS uV uA uB w }

def pC (uS uV uA uB : ℕ) : Prog :=
  .seq (emitNat .Bnn) (.seq (emitNat .Bnm) (.seq (emitNat .X) (.seq (copyProg .Nu .Vr .sc)
  (.seq (vLoop uS uV) (.seq (copyProg .Ec .Er .sc) (.seq (eLoop uA uB) (mvProg .O .out)))))))


lemma nb_length (x : ℕ) : (nb x).length = 2 * (Nat.bits x).length + 1 := by
  simp [nb, natBits_eq, nbList]; ring

lemma scanV_length (uV : ℕ) : ∀ (as rs cs : List Bool),
    (scanV uV as rs cs).length ≤ as.length * (2 * ((nb uV).length + (nb 0).length))
  | a :: as, r :: rs, c :: cs => by
      have ih := scanV_length uV as rs cs
      simp only [scanV, List.length_append, List.length_cons]
      have : (if a then nb (if r then uV else 0) ++ nb (if c then uV else 0) else []).length ≤
          2 * ((nb uV).length + (nb 0).length) := by
        cases a <;> cases r <;> cases c <;> simp <;> omega
      nlinarith
  | [], _, _ => by simp [scanV]
  | _ :: _, [], _ => by simp [scanV]
  | _ :: _, _ :: _, [] => by simp [scanV]

lemma flatMap_sel_len (l1 l0 : List Bool) : ∀ bs : List Bool,
    (bs.flatMap (fun b => if b then l1 else l0)).length ≤ bs.length * (l1.length + l0.length)
  | [] => by simp
  | b :: bs => by
      have ih := flatMap_sel_len l1 l0 bs
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : (if b then l1 else l0).length ≤ l1.length + l0.length := by cases b <;> simp
      nlinarith

lemma vrow_length (k E uS uV n : ℕ) (ua : List Bool) (v : ℕ) :
    (vrow k E uS uV n ua v).length ≤ k * (nb uS).length + E * (nb 0).length +
      ua.length * (2 * ((nb uV).length + (nb 0).length)) := by
  unfold vrow
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  have := scanV_length uV ua (rfL n v) (cfL n v)
  omega

lemma erow_length (k E uA uB e : ℕ) (he : e < E) :
    (erow k E uA uB e).length ≤ k * (nb 0).length + E * ((nb uA).length + (nb 0).length) +
      E * (2 * (nb uB).length + 2 * (nb 0).length) := by
  unfold erow
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  have h1 := flatMap_sel_len (nb uA) (nb 0) (ohL E e)
  have h2 := flatMap_sel_len (nb uB ++ nb uB) (nb 0 ++ nb 0) (ohL E e)
  rw [ohL_length E e he] at h1 h2
  simp only [List.length_append] at h2
  nlinarith


lemma natBits_length (x : ℕ) : (NSWApxHard.Reduction.natBits x).length = 2 * (Nat.bits x).length + 1 :=
  nb_length x

lemma costC_bound (n k E cb bn bm bT SV SE Z : ℕ) (hZ1 : 1 ≤ Z) (hn : n ≤ Z) (hk : k ≤ Z)
    (hE : E ≤ Z * Z) (hcb : cb ≤ Z) (hbn : bn ≤ 2 * (Z * Z)) (hbm : bm ≤ 4 * (Z * Z))
    (hbT : bT ≤ 8 * (Z * Z) + 1) (hSV : SV ≤ n * (k * cb + E * cb + n * n * (2 * cb)))
    (hSE : SE ≤ E * (k * cb + E * cb + E * (2 * cb))) :
    10 * bn + 3 + 1 + (10 * bm + 3 + 1 + (10 * bT + 3 + 1 + (6 * n + 3 + 1 +
      (n * (k * (2 * cb + 11) + E * (2 * cb + 11) + n * n * (4 * cb + 30) + 60 * n + 102) + 1 + 1 +
      (6 * E + 3 + 1 + (E * (k * (2 * cb + 11) + E * (8 * cb + 40) + 62) + 1 + 1 +
      (3 * (SE + (SV + ((2 * bT + 1) + ((2 * bm + 1) + (2 * bn + 1))))) + 1))))))) ≤
      3000 * Z ^ 5 := by
  have z2 : Z ≤ Z * Z := Nat.le_mul_self Z
  have z3 : Z * Z ≤ Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have z4 : Z * Z * Z ≤ Z * Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have z5 : Z * Z * Z * Z ≤ Z * Z * Z * Z * Z := Nat.le_mul_of_pos_right _ (by omega)
  have hz5 : Z ^ 5 = Z * Z * Z * Z * Z := by ring
  rw [hz5]
  have i1 : k * (2 * cb + 11) ≤ 13 * (Z * Z) :=
    calc k * (2 * cb + 11) ≤ Z * (13 * Z) := Nat.mul_le_mul hk (by omega)
      _ = 13 * (Z * Z) := by ring
  have i2 : E * (2 * cb + 11) ≤ 13 * (Z * Z * Z) :=
    calc E * (2 * cb + 11) ≤ (Z * Z) * (13 * Z) := Nat.mul_le_mul hE (by omega)
      _ = 13 * (Z * Z * Z) := by ring
  have i3 : n * n * (4 * cb + 30) ≤ 34 * (Z * Z * Z) :=
    calc n * n * (4 * cb + 30) ≤ (Z * Z) * (34 * Z) := Nat.mul_le_mul (Nat.mul_le_mul hn hn) (by omega)
      _ = 34 * (Z * Z * Z) := by ring
  have i4 : n * (k * (2 * cb + 11) + E * (2 * cb + 11) + n * n * (4 * cb + 30) + 60 * n + 102) ≤
      222 * (Z * Z * Z * Z) :=
    calc _ ≤ Z * (222 * (Z * Z * Z)) := Nat.mul_le_mul hn (by omega)
      _ = 222 * (Z * Z * Z * Z) := by ring
  have i5 : E * (8 * cb + 40) ≤ 48 * (Z * Z * Z) :=
    calc E * (8 * cb + 40) ≤ (Z * Z) * (48 * Z) := Nat.mul_le_mul hE (by omega)
      _ = 48 * (Z * Z * Z) := by ring
  have i6 : E * (k * (2 * cb + 11) + E * (8 * cb + 40) + 62) ≤ 123 * (Z * Z * Z * Z * Z) :=
    calc _ ≤ (Z * Z) * (123 * (Z * Z * Z)) := Nat.mul_le_mul hE (by omega)
      _ = 123 * (Z * Z * Z * Z * Z) := by ring
  have j1 : k * cb ≤ Z * Z := Nat.mul_le_mul hk hcb
  have j2 : E * cb ≤ Z * Z * Z := Nat.mul_le_mul hE hcb
  have j3 : n * n * (2 * cb) ≤ 2 * (Z * Z * Z) :=
    calc n * n * (2 * cb) ≤ (Z * Z) * (2 * Z) := Nat.mul_le_mul (Nat.mul_le_mul hn hn) (by omega)
      _ = 2 * (Z * Z * Z) := by ring
  have j4 : n * (k * cb + E * cb + n * n * (2 * cb)) ≤ 4 * (Z * Z * Z * Z) :=
    calc _ ≤ Z * (4 * (Z * Z * Z)) := Nat.mul_le_mul hn (by omega)
      _ = 4 * (Z * Z * Z * Z) := by ring
  have j5 : E * (2 * cb) ≤ 2 * (Z * Z * Z) :=
    calc E * (2 * cb) ≤ (Z * Z) * (2 * Z) := Nat.mul_le_mul hE (by omega)
      _ = 2 * (Z * Z * Z) := by ring
  have j6 : E * (k * cb + E * cb + E * (2 * cb)) ≤ 4 * (Z * Z * Z * Z * Z) :=
    calc _ ≤ (Z * Z) * (4 * (Z * Z * Z)) := Nat.mul_le_mul hE (by omega)
      _ = 4 * (Z * Z * Z * Z * Z) := by ring
  linarith

lemma runs_pC (a b c1 c2 uS uV uA uB cb : ℕ) (hcb1 : (nb uS).length ≤ cb)
    (hcb2 : (nb uV).length + (nb 0).length ≤ cb)
    (hcb3 : (nb uA).length + (nb uB).length + (nb 0).length ≤ cb) (hab : a < b) (w : List Bool) :
    Runs (pC uS uV uA uB) (SB a b c1 c2 w) (SC a b c1 c2 uS uV uA uB w)
      (3000 * ((a + b + c1 + c2 + cb + 1) * (w.length + 1)) ^ 5) := by
  refine (((runs_emitNat .Bnn (by decide) (EOf w + nOf w) (SB a b c1 c2 w) ?_).seq
    ((runs_emitNat .Bnm (by decide) (3 * EOf w + kOf a b w) _ ?_).seq
    ((runs_emitNat .X (by decide) (TOf a b c1 c2 w) _ ?_).seq
    ((runs_copy .Nu .Vr .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_vLoop (nOf w) (kOf a b w) (EOf w) uS uV cb (uaOf w) hcb1 hcb2 (nOf w) 0 _ (by omega)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).seq
    ((runs_copy .Ec .Er .sc (by decide) (by decide) (by decide) _ ?_).seq
    ((runs_eLoop (kOf a b w) (EOf w) uA uB cb hcb3 (EOf w) 0 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_).seq
    (runs_mv .O .out (by decide) _)))))))).congr ?_).mono ?_
  all_goals (try simp [SB, SA, Regs.empty, Regs.get, Regs.set, uaOf_length])
  · simp [SC, SB, SA, OUT, VR, ER, Regs.empty]
  · have hn := nOf_le w
    have hE := EOf_le w
    have hk : kOf a b w ≤ nOf w := Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ hab.le)
    set Z := (a + b + c1 + c2 + cb + 1) * (w.length + 1) with hZ
    have hL : w.length + 1 ≤ Z := Nat.le_mul_of_pos_left _ (by omega)
    have hK : a + b + c1 + c2 + cb + 1 ≤ Z := Nat.le_mul_of_pos_right _ (by omega)
    have z2 : Z ≤ Z * Z := Nat.le_mul_self Z
    have hEZ : EOf w ≤ Z * Z := le_trans hE (Nat.mul_le_mul (by omega) (by omega))
    have he1 : 4 * nOf w - 3 * kOf a b w ≤ 4 * Z := by omega
    have he2 : 3 * kOf a b w + nOf w ≤ 4 * Z := by omega
    have h' : c1 * (4 * nOf w - 3 * kOf a b w) ≤ 4 * (Z * Z) :=
      calc c1 * (4 * nOf w - 3 * kOf a b w) ≤ Z * (4 * Z) := Nat.mul_le_mul (by omega) he1
        _ = 4 * (Z * Z) := by ring
    have h'' : c2 * (3 * kOf a b w + nOf w) ≤ 4 * (Z * Z) :=
      calc c2 * (3 * kOf a b w + nOf w) ≤ Z * (4 * Z) := Nat.mul_le_mul (by omega) he2
        _ = 4 * (Z * Z) := by ring
    have hb1 : (Nat.bits 1).length = 1 := by simp
    have hlT : (Nat.bits (TOf a b c1 c2 w)).length ≤ 8 * (Z * Z) + 1 := by
      have h1 := len_bits_pow_mul c2 (3 * kOf a b w + nOf w) (c1 ^ (4 * nOf w - 3 * kOf a b w) * 1)
      have h2 := len_bits_pow_mul c1 (4 * nOf w - 3 * kOf a b w) 1
      unfold TOf; omega
    have hln : (Nat.bits (EOf w + nOf w)).length ≤ 2 * (Z * Z) := by
      have := len_bits_le (EOf w + nOf w); omega
    have hlm : (Nat.bits (3 * EOf w + kOf a b w)).length ≤ 4 * (Z * Z) := by
      have := len_bits_le (3 * EOf w + kOf a b w); omega
    have hSV : (List.map (fun i => (vrow (kOf a b w) (EOf w) uS uV (nOf w) (uaOf w) i).length)
        (List.range (nOf w))).sum ≤ nOf w * (kOf a b w * cb + EOf w * cb + nOf w * nOf w * (2 * cb)) := by
      have := List.sum_le_card_nsmul (List.map (fun i => (vrow (kOf a b w) (EOf w) uS uV (nOf w) (uaOf w) i).length)
        (List.range (nOf w))) (kOf a b w * cb + EOf w * cb + nOf w * nOf w * (2 * cb)) (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨i, _, rfl⟩ := hx
          have := vrow_length (kOf a b w) (EOf w) uS uV (nOf w) (uaOf w) i
          rw [uaOf_length] at this
          have q1 : kOf a b w * (nb uS).length ≤ kOf a b w * cb := Nat.mul_le_mul_left _ hcb1
          have q2 : EOf w * (nb 0).length ≤ EOf w * cb := Nat.mul_le_mul_left _ (by omega)
          have q3 : nOf w * nOf w * (2 * ((nb uV).length + (nb 0).length)) ≤ nOf w * nOf w * (2 * cb) :=
            Nat.mul_le_mul_left _ (by omega)
          omega)
      simpa using this
    have hSE : (List.map (fun i => (erow (kOf a b w) (EOf w) uA uB i).length)
        (List.range (EOf w))).sum ≤ EOf w * (kOf a b w * cb + EOf w * cb + EOf w * (2 * cb)) := by
      have := List.sum_le_card_nsmul (List.map (fun i => (erow (kOf a b w) (EOf w) uA uB i).length)
        (List.range (EOf w))) (kOf a b w * cb + EOf w * cb + EOf w * (2 * cb)) (by
          intro x hx
          simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          have := erow_length (kOf a b w) (EOf w) uA uB i hi
          have q1 : kOf a b w * (nb 0).length ≤ kOf a b w * cb := Nat.mul_le_mul_left _ (by omega)
          have q2 : EOf w * ((nb uA).length + (nb 0).length) ≤ EOf w * cb := Nat.mul_le_mul_left _ (by omega)
          have q3 : EOf w * (2 * (nb uB).length + 2 * (nb 0).length) ≤ EOf w * (2 * cb) :=
            Nat.mul_le_mul_left _ (by omega)
          omega)
      simpa using this
    simp only [natBits_length]
    exact costC_bound (nOf w) (kOf a b w) (EOf w) cb _ _ _ _ _ Z (by omega) (by omega) (by omega) hEZ
      (by omega) hln hlm hlT hSV hSE

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

def mainProg (a b c1 c2 uS uV uA uB : ℕ) : Prog := .seq pA (.seq (pB a b c1 c2) (pC uS uV uA uB))

lemma total_cost_bound (K1 K2 L : ℕ) :
    100 * ((L + 1) * (L + 1)) + 1 + (4000 * (K1 * (L + 1)) ^ 4 + 1 + 3000 * (K2 * (L + 1)) ^ 5) ≤
      (100 + 4000 * K1 ^ 4 + 3000 * K2 ^ 5) * (L + 1) ^ 5 + 2 := by
  generalize hP : L + 1 = P
  have hP1 : 1 ≤ P := by omega
  have p2 : P * P ≤ P ^ 5 := by
    calc P * P = P ^ 2 := by ring
      _ ≤ P ^ 5 := Nat.pow_le_pow_right hP1 (by omega)
  have p4 : (K1 * P) ^ 4 ≤ K1 ^ 4 * P ^ 5 := by
    rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hP1 (by omega))
  have p5 : (K2 * P) ^ 5 = K2 ^ 5 * P ^ 5 := by rw [mul_pow]
  have q : (100 + 4000 * K1 ^ 4 + 3000 * K2 ^ 5) * P ^ 5 =
      100 * P ^ 5 + 4000 * (K1 ^ 4 * P ^ 5) + 3000 * (K2 ^ 5 * P ^ 5) := by ring
  rw [q, p5]
  omega

theorem out_polyTime (a b c1 c2 uS uV uA uB : ℕ) (hb : 0 < b) (hab : a < b) (hc1 : 1 ≤ c1)
    (hc2 : 1 ≤ c2) : PolyTimeComputable (OUT a b c1 c2 uS uV uA uB) := by
  obtain ⟨cb, hcb⟩ : ∃ cb, cb = (nb uS).length + (nb uV).length + (nb uA).length + (nb uB).length +
      (nb 0).length := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := polynomial_absorb (100 + 4000 * (a + b + c1 + c2 + 1) ^ 4 +
    3000 * (a + b + c1 + c2 + cb + 1) ^ 5) 5 2
  refine stack_program_polytime (mainProg a b c1 c2 uS uV uA uB) .inp .out
    (OUT a b c1 c2 uS uV uA uB) k (fun w => ?_)
  have e := (runs_pA w).seq ((runs_pB a b c1 c2 hb hab hc1 hc2 w).seq
    (runs_pC a b c1 c2 uS uV uA uB cb (by omega) (by omega) (by omega) hab w))
  obtain ⟨n, hn, hex⟩ := e
  have hout : (SC a b c1 c2 uS uV uA uB w).get Key.out = OUT a b c1 c2 uS uV uA uB w := by
    simp only [Regs.get, SC]
  refine ⟨(SC a b c1 c2 uS uV uA uB w).get, n, ?_, ?_, hout⟩
  · exact le_trans hn (le_trans (total_cost_bound _ _ w.length) (hk w.length))
  · have : (σ0 w).get = (fun j => if j = Key.inp then w else []) := by
      funext j; cases j <;> rfl
    rw [← this]
    exact hex

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP

/-! ## Row-major index lemmas -/

lemma range_flatMap_map {α : Type} (M : ℕ) (f : ℕ → ℕ → α) : ∀ N : ℕ,
    (List.range N).flatMap (fun i => (List.range M).map (fun j => f i j)) =
      (List.range (N * M)).map (fun p => f (p / M) (p % M))
  | 0 => by simp
  | N + 1 => by
      rw [List.range_succ, List.flatMap_append, range_flatMap_map M f N, Nat.succ_mul, List.range_add,
        List.map_append, List.map_map]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      simp only [Function.comp]
      have h1 : (N * M + j) / M = N := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]; simp
      have h2 : (N * M + j) % M = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      rw [h1, h2]

lemma ofFn_eq_range_map {α : Type} (n : ℕ) (g : Fin n → α) (g' : ℕ → α)
    (h : ∀ i (hi : i < n), g ⟨i, hi⟩ = g' i) : List.ofFn g = (List.range n).map g' := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h i (by simpa using h1)

lemma matrix_eq {α : Type} (N : ℕ) (g : Fin N → Fin N → α) (g' : ℕ → ℕ → α)
    (h : ∀ i j (hi : i < N) (hj : j < N), g ⟨i, hi⟩ ⟨j, hj⟩ = g' i j) :
    (List.ofFn fun i : Fin N => List.ofFn fun j : Fin N => g i j).flatten =
      (List.range (N * N)).map (fun p => g' (p / N) (p % N)) := by
  rw [← range_flatMap_map N g' N]
  rw [ofFn_eq_range_map N (fun i => List.ofFn fun j : Fin N => g i j)
    (fun i => (List.range N).map (fun j => g' i j))]
  · simp [List.flatMap]
  · intro i hi
    exact ofFn_eq_range_map N _ _ (fun j hj => h i j hi hj)

lemma maskRow_eq (N i : ℕ) (hi : i < N) : maskRow N i = (List.range N).map (fun j => decide (i < j)) := by
  apply List.ext_getElem
  · simp [maskRow]; omega
  · intro j h1 h2
    simp only [maskRow, List.getElem_map, List.getElem_range]
    rw [List.getElem_append]
    split_ifs with h
    · simp at h; simp; omega
    · simp at h ⊢; omega

lemma Ulist_eq (N : ℕ) : Ulist N = (List.range (N * N)).map (fun p => decide (p / N < p % N)) := by
  rw [← range_flatMap_map N (fun i j => decide (i < j)) N]
  unfold Ulist
  apply List.flatMap_congr
  intro i hi
  exact maskRow_eq N i (by simpa using hi)

lemma replicate_eq_map (n : ℕ) (b : Bool) : List.replicate n b = (List.range n).map (fun _ => b) := by
  simp

lemma ohL_eq (n v : ℕ) (hv : v < n) : ohL n v = (List.range n).map (fun j => decide (j = v)) := by
  apply List.ext_getElem
  · simp [ohL]; omega
  · intro j h1 h2
    simp only [ohL, List.getElem_map, List.getElem_range]
    by_cases h : j < v
    · rw [List.getElem_append_left (by simpa using h)]
      simp; omega
    · rw [List.getElem_append_right (by simpa using h)]
      have hj : j - (List.replicate v false).length = j - v := by simp
      simp only [hj]
      by_cases h' : j = v
      · subst h'; simp
      · obtain ⟨t, ht⟩ : ∃ t, j - v = t + 1 := ⟨j - v - 1, by omega⟩
        simp only [ht, List.getElem_cons_succ, List.getElem_replicate]
        simp; omega

lemma cfL_eq (n v : ℕ) (hv : v < n) :
    cfL n v = (List.range (n * n)).map (fun p => decide (p % n = v)) := by
  rw [← range_flatMap_map n (fun _ j => decide (j = v)) n]
  unfold cfL
  rw [ohL_eq n v hv]
  generalize (List.range n).map (fun j => decide (j = v)) = X
  clear hv
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, ← ih, List.replicate_succ']; simp

lemma rfL_eq (n v : ℕ) (hv : v < n) :
    rfL n v = (List.range (n * n)).map (fun p => decide (p / n = v)) := by
  apply List.ext_getElem
  · simp [rfL_length n v hv]
  · intro p h1 h2
    simp only [rfL, List.getElem_map, List.getElem_range]
    have hn : 0 < n := by omega
    have hp : p < n * n := by simpa using h2
    by_cases ha : p < v * n
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_replicate]
      have : p / n < v := (Nat.div_lt_iff_lt_mul hn).mpr ha
      simp; omega
    · by_cases hb : p < v * n + n
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_replicate]
        have : p / n = v := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
        simp [this]
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_replicate]
        have : v + 1 ≤ p / n := (Nat.le_div_iff_mul_le hn).mpr (by rw [Nat.succ_mul]; omega)
        simp; omega

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP NSWApxHard.Reduction

/-! ## Parsing a valid graph encoding -/

lemma pn_natBits : ∀ (l R : List Bool),
    pn (l.flatMap (fun b => [true, b]) ++ false :: R) = (l, false :: R)
  | [], R => by simp [pn]
  | b :: l, R => by
      have := pn_natBits l R
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      rw [pn, this]

lemma padTake_self : ∀ l : List Bool, padTake l.length l = l
  | [] => rfl
  | b :: l => by simp [padTake, padTake_self l]

lemma padTake_eq (n : ℕ) (l : List Bool) (h : l.length = n) : padTake n l = l := by
  subst h; exact padTake_self l

open Classical in
/-- the adjacency relation as a Boolean function on indices -/
noncomputable def Adjb (I : GraphInput) (i j : ℕ) : Bool :=
  if h : i < I.N ∧ j < I.N then decide (I.G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩) else false

lemma encGraph_eq (I : GraphInput) : encGraph I =
    (Nat.bits I.N).flatMap (fun b => [true, b]) ++ false ::
      (List.range (I.N * I.N)).map (fun p => Adjb I (p / I.N) (p % I.N)) := by
  unfold encGraph
  rw [natBits_eq]
  unfold nbList
  rw [matrix_eq I.N _ (fun i j => Adjb I i j)]
  · simp
  · intro i j hi hj
    simp [Adjb, hi, hj]

noncomputable def uaP (I : GraphInput) (p : ℕ) : Bool := Adjb I (p / I.N) (p % I.N) && decide (p / I.N < p % I.N)

lemma zipWith_map_range {α β γ : Type} (f : α → β → γ) (g : ℕ → α) (h : ℕ → β) : ∀ L : List ℕ,
    List.zipWith f (L.map g) (L.map h) = L.map (fun p => f (g p) (h p))
  | [] => rfl
  | p :: L => by simp [zipWith_map_range f g h L]

lemma restOf_enc (I : GraphInput) : restOf (encGraph I) =
    (List.range (I.N * I.N)).map (fun p => Adjb I (p / I.N) (p % I.N)) := by
  unfold restOf; rw [encGraph_eq, pn_natBits]; rfl

lemma xOf_enc (I : GraphInput) : xOf (encGraph I) = I.N := by
  unfold xOf; rw [encGraph_eq, pn_natBits]; simp only; rw [canonD_bits, bval_bits]

lemma nOf_enc (I : GraphInput) : nOf (encGraph I) = I.N := by
  unfold nOf; rw [xOf_enc, restOf_enc]; simp
  exact Nat.le_mul_self _

lemma uaOf_enc (I : GraphInput) : uaOf (encGraph I) = (List.range (I.N * I.N)).map (uaP I) := by
  unfold uaOf
  rw [nOf_enc, restOf_enc, padTake_eq _ _ (by simp), Ulist_eq, zipWith_map_range]
  rfl

/-- the strict-upper-triangle positions of the edges -/
noncomputable def EP (I : GraphInput) : List ℕ := (List.range (I.N * I.N)).filter (uaP I)

lemma count_map_true {α : Type} (f : α → Bool) : ∀ L : List α, (L.map f).count true = (L.filter f).length
  | [] => rfl
  | x :: L => by
      have := count_map_true f L
      cases h : f x <;> simp [List.filter_cons, h, this, List.count_cons]

lemma EOf_enc (I : GraphInput) : EOf (encGraph I) = (EP I).length := by
  unfold EOf EP; rw [uaOf_enc, count_map_true]

lemma scanV_map (uV : ℕ) (fa fr fc : ℕ → Bool) : ∀ L : List ℕ,
    scanV uV (L.map fa) (L.map fr) (L.map fc) =
      L.flatMap (fun p => if fa p then nb (if fr p then uV else 0) ++ nb (if fc p then uV else 0) else [])
  | [] => by simp [scanV]
  | p :: L => by simp [scanV, scanV_map uV fa fr fc L]

lemma flatMap_ite_filter {α β : Type} (q : α → Bool) (F : α → List β) : ∀ L : List α,
    L.flatMap (fun p => if q p then F p else []) = (L.filter q).flatMap F
  | [] => rfl
  | x :: L => by
      have := flatMap_ite_filter q F L
      cases h : q x <;> simp [List.filter_cons, h, this]

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP NSWApxHard.Reduction

def c1C (m₀ : ℕ) : ℕ := 3 * m₀ + 3
def c2C (m₀ : ℕ) : ℕ := 4 * m₀ + 5
def uSC (m₀ : ℕ) : ℕ := c1C m₀ * c2C m₀
def uVC (m₀ : ℕ) : ℕ := (m₀ + 1) * c2C m₀
def uAC (m₀ : ℕ) : ℕ := c2C m₀ * (2 * m₀ + 1)
def uBC (m₀ : ℕ) : ℕ := c2C m₀ * (m₀ + 2)

def vrowN (k E N uS uV : ℕ) (EPl : List ℕ) (v : ℕ) : List ℕ :=
  List.replicate k uS ++ List.replicate E 0 ++
    EPl.flatMap (fun p => [if p / N = v then uV else 0, if p % N = v then uV else 0])

def erowN (k E uA uB : ℕ) (e : ℕ) : List ℕ :=
  List.replicate k 0 ++ (List.range E).map (fun j => if j = e then uA else 0) ++
    (List.range E).flatMap (fun j => if j = e then [uB, uB] else [0, 0])

noncomputable def rowsN (m₀ a b : ℕ) (I : GraphInput) : List (List ℕ) :=
  (List.range I.N).map (vrowN (a * I.N / b) (EP I).length I.N (uSC m₀) (uVC m₀) (EP I)) ++
    (List.range (EP I).length).map (erowN (a * I.N / b) (EP I).length (uAC m₀) (uBC m₀))

noncomputable def PI (m₀ a b : ℕ) (I : GraphInput) : NSWInput where
  n := I.N + (EP I).length
  m := a * I.N / b + ((EP I).length + 2 * (EP I).length)
  u := fun ag it => (((rowsN m₀ a b I).getD ag []).getD it 0)
  T := c1C m₀ ^ (4 * I.N - 3 * (a * I.N / b)) * c2C m₀ ^ (I.N + 3 * (a * I.N / b))

lemma ofFn_getD_eq {α β : Type} (l : List α) (d : α) (n : ℕ) (h : l.length = n) (F : α → β) :
    List.ofFn (fun i : Fin n => F (l.getD i d)) = l.map F := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getD_eq_getElem]

lemma vrowN_length (k E N uS uV : ℕ) (EPl : List ℕ) (v : ℕ) :
    (vrowN k E N uS uV EPl v).length = k + E + 2 * EPl.length := by
  unfold vrowN
  simp only [List.length_append, List.length_replicate, List.length_flatMap]
  simp [List.sum_const_nat]; ring

lemma erowN_length (k E uA uB e : ℕ) : (erowN k E uA uB e).length = k + E + 2 * E := by
  unfold erowN
  simp only [List.length_append, List.length_replicate, List.length_map, List.length_range,
    List.length_flatMap]
  have : ∀ j ∈ List.range E, (if j = e then [uB, uB] else [0, 0]).length = 2 := by
    intro j _; split_ifs <;> rfl
  rw [List.map_congr_left this]
  simp; ring

lemma flatMap_pair_nb (x y : ℕ → ℕ) : ∀ L : List ℕ,
    ((L.flatMap (fun p => [x p, y p])).map nb).flatten = L.flatMap (fun p => nb (x p) ++ nb (y p))
  | [] => rfl
  | p :: L => by simp [flatMap_pair_nb x y L]

lemma flatMap_map_nb (F : ℕ → List ℕ) : ∀ L : List ℕ,
    ((L.flatMap F).map nb).flatten = L.flatMap (fun j => ((F j).map nb).flatten)
  | [] => rfl
  | p :: L => by simp [flatMap_map_nb F L]

lemma vrowN_nb (m₀ a b : ℕ) (I : GraphInput) (v : ℕ) (hv : v < I.N) :
    ((vrowN (a * I.N / b) (EP I).length I.N (uSC m₀) (uVC m₀) (EP I) v).map nb).flatten =
      vrow (a * I.N / b) (EP I).length (uSC m₀) (uVC m₀) I.N (uaOf (encGraph I)) v := by
  unfold vrowN vrow
  rw [uaOf_enc, rfL_eq _ _ hv, cfL_eq _ _ hv, scanV_map, flatMap_ite_filter]
  simp only [List.map_append, List.flatten_append, List.map_replicate]
  rw [flatMap_pair_nb]
  simp [EP]

lemma erowN_nb (m₀ k E : ℕ) (e : ℕ) (he : e < E) :
    ((erowN k E (uAC m₀) (uBC m₀) e).map nb).flatten = erow k E (uAC m₀) (uBC m₀) e := by
  unfold erowN erow
  rw [ohL_eq _ _ he]
  have h2 : (((List.range E).map (fun j => if j = e then uAC m₀ else 0)).map nb).flatten =
      ((List.range E).map (fun j => decide (j = e))).flatMap
        (fun b => if b then nb (uAC m₀) else nb 0) := by
    rw [List.flatMap_map, List.map_map]
    simp only [List.flatMap]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    split_ifs <;> simp_all
  have h3 : (((List.range E).flatMap (fun j => if j = e then [uBC m₀, uBC m₀] else [0, 0])).map nb).flatten =
      ((List.range E).map (fun j => decide (j = e))).flatMap
        (fun b => if b then nb (uBC m₀) ++ nb (uBC m₀) else nb 0 ++ nb 0) := by
    rw [flatMap_map_nb, List.flatMap_map]
    apply List.flatMap_congr
    intro j _
    split_ifs <;> simp_all
  simp only [List.map_append, List.flatten_append, List.map_replicate]
  rw [h2, h3]

lemma rowsN_length (m₀ a b : ℕ) (I : GraphInput) :
    (rowsN m₀ a b I).length = I.N + (EP I).length := by
  simp [rowsN]

lemma rowsN_row_length (m₀ a b : ℕ) (I : GraphInput) :
    ∀ r ∈ rowsN m₀ a b I, r.length = a * I.N / b + ((EP I).length + 2 * (EP I).length) := by
  intro r hr
  simp only [rowsN, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨v, _, rfl⟩ | ⟨e, _, rfl⟩
  · rw [vrowN_length]; ring
  · rw [erowN_length]; ring

lemma matrix_enc (m₀ a b : ℕ) (I : GraphInput) :
    (List.ofFn fun ag : Fin (PI m₀ a b I).n =>
      (List.ofFn fun it : Fin (PI m₀ a b I).m => natBits ((PI m₀ a b I).u ag it)).flatten).flatten =
    ((rowsN m₀ a b I).map (fun r => (r.map nb).flatten)).flatten := by
  congr 1
  have := ofFn_getD_eq (rowsN m₀ a b I) [] (PI m₀ a b I).n (rowsN_length m₀ a b I)
    (fun r => (List.ofFn fun it : Fin (PI m₀ a b I).m => natBits (r.getD it 0)).flatten)
  refine this.trans ?_
  apply List.map_congr_left
  intro r hr
  have h2 := ofFn_getD_eq r 0 (PI m₀ a b I).m (rowsN_row_length m₀ a b I r hr) natBits
  rw [h2]

lemma encNSW_PI (m₀ a b : ℕ) (I : GraphInput) :
    encNSW (PI m₀ a b I) = OUT a b (c1C m₀) (c2C m₀) (uSC m₀) (uVC m₀) (uAC m₀) (uBC m₀) (encGraph I) := by
  have hk : kOf a b (encGraph I) = a * I.N / b := by unfold kOf; rw [nOf_enc]
  unfold encNSW NSWInput.enc
  rw [matrix_enc]
  unfold OUT VR ER TOf
  rw [hk, nOf_enc, EOf_enc]
  have hN : (PI m₀ a b I).n = I.N + (EP I).length := rfl
  have hM : (PI m₀ a b I).m = a * I.N / b + ((EP I).length + 2 * (EP I).length) := rfl
  have hT : (PI m₀ a b I).T = c2C m₀ ^ (3 * (a * I.N / b) + I.N) * (c1C m₀ ^ (4 * I.N - 3 * (a * I.N / b)) * 1) := by
    simp only [PI]; rw [mul_one, mul_comm]; congr 2; ring
  rw [hN, hM, hT]
  have h1 : I.N + (EP I).length = (EP I).length + I.N := by ring
  have h2 : a * I.N / b + ((EP I).length + 2 * (EP I).length) = 3 * (EP I).length + a * I.N / b := by ring
  rw [h1, h2]
  simp only [List.append_assoc]
  congr 3
  unfold rowsN
  rw [List.map_append, List.flatten_append, List.map_map, List.map_map]
  congr 1
  · simp only [List.flatMap, zero_add]
    congr 1
    apply List.map_congr_left
    intro v hv
    simp only [Function.comp]
    exact vrowN_nb m₀ a b I v (by simpa using hv)
  · simp only [List.flatMap, zero_add]
    congr 1
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    exact erowN_nb m₀ _ _ e (by simpa using he)

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP NSWApxHard.Reduction

section Edges

variable (I : GraphInput) [DecidableRel I.G.Adj]

lemma EP_mem (p : ℕ) : p ∈ EP I ↔ p < I.N * I.N ∧ uaP I p = true := by
  simp [EP]

lemma EP_div_lt {p : ℕ} (hp : p ∈ EP I) : p / I.N < I.N := by
  rw [EP_mem] at hp
  have hN : 0 < I.N := by
    rcases Nat.eq_zero_or_pos I.N with h | h
    · rw [h] at hp; simp at hp
    · exact h
  exact (Nat.div_lt_iff_lt_mul hN).mpr hp.1

lemma EP_mod_lt {p : ℕ} (hp : p ∈ EP I) : p % I.N < I.N := by
  rw [EP_mem] at hp
  have hN : 0 < I.N := by
    rcases Nat.eq_zero_or_pos I.N with h | h
    · rw [h] at hp; simp at hp
    · exact h
  exact Nat.mod_lt _ hN

lemma EP_lt {p : ℕ} (hp : p ∈ EP I) : p / I.N < p % I.N := by
  rw [EP_mem] at hp
  have := hp.2
  simp [uaP] at this
  exact this.2

lemma EP_adj {p : ℕ} (hp : p ∈ EP I) :
    I.G.Adj ⟨p / I.N, EP_div_lt I hp⟩ ⟨p % I.N, EP_mod_lt I hp⟩ := by
  have h := (EP_mem I p).mp hp
  have h2 := h.2
  simp only [uaP, Bool.and_eq_true, decide_eq_true_eq] at h2
  have h3 := h2.1
  unfold Adjb at h3
  rw [dif_pos ⟨EP_div_lt I hp, EP_mod_lt I hp⟩] at h3
  simpa using h3

lemma EP_nodup : (EP I).Nodup := (List.nodup_range).filter _

/-- the edge of the graph at an upper-triangle position -/
def edgeOf (p : ℕ) (hp : p ∈ EP I) : Edge I.G :=
  ⟨s(⟨p / I.N, EP_div_lt I hp⟩, ⟨p % I.N, EP_mod_lt I hp⟩), by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact EP_adj I hp⟩

noncomputable def edgeL : List (Edge I.G) := (EP I).attach.map (fun x => edgeOf I x.1 x.2)

lemma edgeL_length : (edgeL I).length = (EP I).length := by simp [edgeL]

lemma pos_eq_of_divmod {N p q : ℕ} (h1 : p / N = q / N) (h2 : p % N = q % N) : p = q := by
  rw [← Nat.div_add_mod p N, ← Nat.div_add_mod q N, h1, h2]

lemma edgeOf_inj {p q : ℕ} (hp : p ∈ EP I) (hq : q ∈ EP I) (h : edgeOf I p hp = edgeOf I q hq) :
    p = q := by
  have h' := congrArg Subtype.val h
  simp only [edgeOf, Sym2.eq_iff, Fin.mk.injEq] at h'
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact pos_eq_of_divmod h1 h2
  · have := EP_lt I hp; have := EP_lt I hq; omega

lemma edgeL_nodup : (edgeL I).Nodup := by
  unfold edgeL
  apply List.Nodup.map_on
  · intro x _ y _ h
    exact Subtype.ext (edgeOf_inj I x.2 y.2 h)
  · exact (EP_nodup I).attach

lemma mem_edgeL_aux (x y : Fin I.N) (he : I.G.Adj x y) (hlt : x < y) :
    ∃ p, ∃ hp : p ∈ EP I, (edgeOf I p hp).1 = s(x, y) := by
  have hN : 0 < I.N := Fin.pos x
  set p := x.val * I.N + y.val with hpdef
  have hpd : p / I.N = x.val := by
    rw [hpdef, Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt y.isLt]; simp
  have hpm : p % I.N = y.val := by
    rw [hpdef, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.isLt]
  have hp : p ∈ EP I := by
    rw [EP_mem]
    refine ⟨?_, ?_⟩
    · have := x.isLt; have := y.isLt
      calc p = x.val * I.N + y.val := rfl
        _ < x.val * I.N + I.N := by omega
        _ = (x.val + 1) * I.N := by ring
        _ ≤ I.N * I.N := Nat.mul_le_mul_right _ (by omega)
    · simp only [uaP, hpd, hpm, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, hlt⟩
      unfold Adjb
      rw [dif_pos ⟨x.isLt, y.isLt⟩]
      simpa using he
  refine ⟨p, hp, ?_⟩
  simp only [edgeOf]
  congr 1
  · exact Fin.ext hpd
  · exact Fin.ext hpm

lemma mem_edgeL (e : Edge I.G) : e ∈ edgeL I := by
  obtain ⟨e, he⟩ := e
  have key : ∃ p, ∃ hp : p ∈ EP I, (edgeOf I p hp).1 = e := by
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hxy : x ≠ y := I.G.ne_of_adj he
      rcases lt_or_gt_of_ne hxy with hlt | hlt
      · exact mem_edgeL_aux I x y he hlt
      · obtain ⟨p, hp, h⟩ := mem_edgeL_aux I y x (I.G.adj_symm he) hlt
        exact ⟨p, hp, by rw [h, Sym2.eq_swap]⟩
  obtain ⟨p, hp, h⟩ := key
  unfold edgeL
  rw [List.mem_map]
  exact ⟨⟨p, hp⟩, List.mem_attach _ _, Subtype.ext h⟩

noncomputable def eEdge : Fin (edgeL I).length ≃ Edge I.G :=
  List.Nodup.getEquivOfForallMemList (edgeL I) (edgeL_nodup I) (mem_edgeL I)

lemma getElem?_flatMap_two {α β : Type} (F : α → List β) (hF : ∀ x, (F x).length = 2) :
    ∀ (L : List α) (t : ℕ), (L.flatMap F)[t]? = (L[t / 2]?).bind (fun x => (F x)[t % 2]?)
  | [], t => by simp
  | x :: L, t => by
      rw [List.flatMap_cons]
      rcases Nat.lt_or_ge t 2 with h | h
      · rw [List.getElem?_append_left (by rw [hF]; exact h)]
        have h1 : t / 2 = 0 := by omega
        have h2 : t % 2 = t := Nat.mod_eq_of_lt h
        rw [h1, h2]; simp
      · rw [List.getElem?_append_right (by rw [hF]; exact h), hF, getElem?_flatMap_two F hF L (t - 2)]
        have h1 : t / 2 = (t - 2) / 2 + 1 := by omega
        have h2 : t % 2 = (t - 2) % 2 := by omega
        rw [h1, h2]; simp

/-- the two incidences of the edge at position `p` -/
def incPair (p : ℕ) (hp : p ∈ EP I) : List (Inc I.G) :=
  [⟨(⟨p / I.N, EP_div_lt I hp⟩, (edgeOf I p hp).1), (edgeOf I p hp).2, Sym2.mem_mk_left _ _⟩,
   ⟨(⟨p % I.N, EP_mod_lt I hp⟩, (edgeOf I p hp).1), (edgeOf I p hp).2, Sym2.mem_mk_right _ _⟩]

noncomputable def incidL : List (Inc I.G) := (EP I).attach.flatMap (fun x => incPair I x.1 x.2)

lemma incL_length : (incidL I).length = 2 * (EP I).length := by
  simp [incidL, incPair, List.length_flatMap]; ring

lemma incL_nodup : (incidL I).Nodup := by
  unfold incidL
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro x _
    simp only [incPair, List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, and_true]
    intro h
    have := congrArg (fun s : Inc I.G => s.1.1.val) h
    simp at this
    have := EP_lt I x.2
    omega
  · refine List.Pairwise.imp_of_mem (fun {x y} _ _ hxy => ?_) ((EP_nodup I).attach)
    simp only [Function.onFun, incPair]
    rw [List.disjoint_cons_left, List.disjoint_cons_left]
    have hne : (edgeOf I x.1 x.2).1 ≠ (edgeOf I y.1 y.2).1 := by
      intro h
      exact hxy (Subtype.ext (edgeOf_inj I x.2 y.2 (Subtype.ext h)))
    refine ⟨?_, ?_, List.disjoint_nil_left _⟩ <;>
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_⟩ <;>
      · intro h
        exact hne (congrArg (fun s : Inc I.G => s.1.2) h)

lemma mem_incL (s : Inc I.G) : s ∈ incidL I := by
  obtain ⟨⟨v, e⟩, he, hv⟩ := s
  have hmem := mem_edgeL I ⟨e, he⟩
  unfold edgeL at hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨p, hp⟩, _, hpe⟩ := hmem
  have hpe' : (edgeOf I p hp).1 = e := congrArg Subtype.val hpe
  unfold incidL
  rw [List.mem_flatMap]
  refine ⟨⟨p, hp⟩, List.mem_attach _ _, ?_⟩
  simp only at hv
  rw [← hpe'] at hv
  simp only [edgeOf, Sym2.mem_iff] at hv
  simp only [incPair, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  rcases hv with h | h
  · left; apply Subtype.ext; simp only [Prod.mk.injEq]; exact ⟨h, hpe'.symm⟩
  · right; apply Subtype.ext; simp only [Prod.mk.injEq]; exact ⟨h, hpe'.symm⟩

noncomputable def eInc : Fin (incidL I).length ≃ Inc I.G :=
  List.Nodup.getEquivOfForallMemList (incidL I) (incL_nodup I) (mem_incL I)

end Edges

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP NSWApxHard.Reduction

section Index

lemma getD_flatMap_pair (f g : ℕ → ℕ) (L : List ℕ) (t : ℕ) (ht : t < 2 * L.length) :
    (L.flatMap (fun p => [f p, g p])).getD t 0 =
      if t % 2 = 0 then f (L[t / 2]'(by omega)) else g (L[t / 2]'(by omega)) := by
  rw [List.getD_eq_getElem?_getD, getElem?_flatMap_two _ (fun _ => rfl)]
  rw [List.getElem?_eq_getElem (show t / 2 < L.length by omega)]
  have : t % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]

lemma vrowN_getD1 (k E N uS uV : ℕ) (EPl : List ℕ) (v j : ℕ) (hj : j < k) :
    (vrowN k E N uS uV EPl v).getD j 0 = uS := by
  unfold vrowN
  rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append _ _ _ _ (by simp <;> omega)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma vrowN_getD2 (k E N uS uV : ℕ) (EPl : List ℕ) (v q : ℕ) (hq : q < E) :
    (vrowN k E N uS uV EPl v).getD (k + q) 0 = 0 := by
  unfold vrowN
  rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hq]

lemma vrowN_getD3 (k E N uS uV : ℕ) (EPl : List ℕ) (v t : ℕ) (hE : E = EPl.length)
    (ht : t < 2 * EPl.length) :
    (vrowN k E N uS uV EPl v).getD (k + (E + t)) 0 =
      if t % 2 = 0 then (if EPl[t / 2]'(by omega) / N = v then uV else 0)
      else (if EPl[t / 2]'(by omega) % N = v then uV else 0) := by
  unfold vrowN
  rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
  have : k + (E + t) - (List.replicate k uS ++ List.replicate E 0).length = t := by simp; omega
  rw [this, getD_flatMap_pair _ _ _ _ ht]

lemma erowN_getD1 (k E uA uB e j : ℕ) (hj : j < k) : (erowN k E uA uB e).getD j 0 = 0 := by
  unfold erowN
  rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append _ _ _ _ (by simp <;> omega)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma erowN_getD2 (k E uA uB e q : ℕ) (hq : q < E) :
    (erowN k E uA uB e).getD (k + q) 0 = if q = e then uA else 0 := by
  unfold erowN
  rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp <;> omega)]
  simp

lemma erowN_getD3 (k E uA uB e t : ℕ) (ht : t < 2 * E) :
    (erowN k E uA uB e).getD (k + (E + t)) 0 = if t / 2 = e then uB else 0 := by
  unfold erowN
  rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
  have : k + (E + t) - (List.replicate k 0 ++ List.map (fun j => if j = e then uA else 0) (List.range E)).length = t := by
    simp; omega
  rw [this, List.getD_eq_getElem?_getD, getElem?_flatMap_two _ (fun j => by split_ifs <;> rfl)]
  rw [List.getElem?_eq_getElem (show t / 2 < (List.range E).length by simp; omega)]
  have : t % 2 < 2 := Nat.mod_lt _ (by omega)
  simp only [List.getElem_range, Option.bind_some]
  split_ifs <;> rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]

lemma rowsN_getD_v (m₀ a b : ℕ) (I : GraphInput) (v : ℕ) (hv : v < I.N) :
    (rowsN m₀ a b I).getD v [] = vrowN (a * I.N / b) (EP I).length I.N (uSC m₀) (uVC m₀) (EP I) v := by
  unfold rowsN
  rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_eq_getElem _ _ (by simp <;> omega)]
  simp

lemma rowsN_getD_e (m₀ a b : ℕ) (I : GraphInput) (e : ℕ) (he : e < (EP I).length) :
    (rowsN m₀ a b I).getD (I.N + e) [] = erowN (a * I.N / b) (EP I).length (uAC m₀) (uBC m₀) e := by
  unfold rowsN
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp <;> omega)]
  simp

end Index

end NSWEnc


set_option autoImplicit false

namespace NSWEnc

open CookPvsNP NSWApxHard.Reduction

section Final

variable (I : GraphInput) [DecidableRel I.G.Adj]

lemma edgeL_getElem (q : ℕ) (hq : q < (edgeL I).length) :
    (edgeL I)[q] = edgeOf I ((EP I)[q]'(by rw [← edgeL_length I]; exact hq)) (List.getElem_mem _) := by
  simp [edgeL]

lemma incidL_getElem? (t : ℕ) : (incidL I)[t]? =
    ((EP I).attach[t / 2]?).bind (fun x => (incPair I x.1 x.2)[t % 2]?) := by
  unfold incidL
  exact getElem?_flatMap_two _ (fun _ => rfl) _ t

lemma incidL_fst (t : ℕ) (ht : t < (incidL I).length) :
    ((incidL I)[t]).1.1.val = if t % 2 = 0 then (EP I)[t / 2]'(by rw [incL_length] at ht; omega) / I.N
      else (EP I)[t / 2]'(by rw [incL_length] at ht; omega) % I.N := by
  have h := incidL_getElem? I t
  rw [List.getElem?_eq_getElem ht] at h
  have h2 : t / 2 < (EP I).attach.length := by rw [List.length_attach]; rw [incL_length] at ht; omega
  rw [List.getElem?_eq_getElem h2] at h
  have hm : t % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases Nat.mod_two_eq_zero_or_one t with h0 | h0
  · simp only [h0, Option.bind_some] at h
    simp [incPair] at h
    rw [h]; simp [h0]
  · simp only [h0, Option.bind_some] at h
    simp [incPair] at h
    rw [h]; simp [h0]

lemma incidL_snd (t : ℕ) (ht : t < (incidL I).length) :
    ((incidL I)[t]).1.2 = ((edgeL I)[t / 2]'(by rw [edgeL_length]; rw [incL_length] at ht; omega)).1 := by
  have h := incidL_getElem? I t
  rw [List.getElem?_eq_getElem ht] at h
  have h2 : t / 2 < (EP I).attach.length := by rw [List.length_attach]; rw [incL_length] at ht; omega
  rw [List.getElem?_eq_getElem h2] at h
  rw [edgeL_getElem]
  rcases Nat.mod_two_eq_zero_or_one t with h0 | h0
  · simp only [h0, Option.bind_some] at h
    simp [incPair] at h
    rw [h]
  · simp only [h0, Option.bind_some] at h
    simp [incPair] at h
    rw [h]

end Final

end NSWEnc


set_option autoImplicit false

open NSWApxHard.Reduction NSWEnc

theorem solution (m₀ a b : ℕ) (hm₀ : 1 ≤ m₀) (hb : 0 < b) (hab : a < b) :
    ∃ (P : GraphInput → NSWInput) (g : List Bool → List Bool),
      CookPvsNP.PolyTimeComputable g ∧
      ∀ (I : GraphInput) [DecidableRel I.G.Adj], 0 < I.N → IsCubic I.G →
        let k := (a * I.N) / b
        encNSW (P I) = g (encGraph I) ∧
        (P I).T = (3 * m₀ + 3) ^ (4 * I.N - 3 * k) * (4 * m₀ + 5) ^ (I.N + 3 * k) ∧
        ∃ (eA : Fin (P I).n ≃ Agent I.G) (eB : Fin (P I).m ≃ Item I.G k),
          ∀ (ag : Fin (P I).n) (it : Fin (P I).m),
            ((P I).u ag it : ℝ) =
              ((3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5)) *
                redUtil I.G k (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) (eA ag) (eB it) := by
  refine ⟨PI m₀ a b, OUT a b (c1C m₀) (c2C m₀) (uSC m₀) (uVC m₀) (uAC m₀) (uBC m₀),
    NSWEnc.out_polyTime _ _ _ _ _ _ _ _ hb hab (by simp [c1C]) (by simp [c2C]), ?_⟩
  intro I _ hN _
  intro k
  refine ⟨encNSW_PI m₀ a b I, rfl, ?_⟩
  let eE : Fin (EP I).length ≃ Edge I.G := (finCongr (edgeL_length I).symm).trans (eEdge I)
  let eI : Fin (2 * (EP I).length) ≃ Inc I.G := (finCongr (incL_length I).symm).trans (eInc I)
  let eA : Fin (PI m₀ a b I).n ≃ Agent I.G :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) eE)
  let eB : Fin (PI m₀ a b I).m ≃ Item I.G k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _)
      (finSumFinEquiv.symm.trans (Equiv.sumCongr eE eI)))
  have eA_l : ∀ v : Fin I.N, eA (Fin.castAdd _ v) = Sum.inl v := by
    intro v
    show (Equiv.sumCongr (Equiv.refl _) eE) (finSumFinEquiv.symm (Fin.castAdd (EP I).length v)) = _
    rw [finSumFinEquiv_symm_apply_castAdd]; rfl
  have eA_r : ∀ e : Fin (EP I).length, eA (Fin.natAdd _ e) = Sum.inr (eE e) := by
    intro e
    show (Equiv.sumCongr (Equiv.refl _) eE) (finSumFinEquiv.symm (Fin.natAdd I.N e)) = _
    rw [finSumFinEquiv_symm_apply_natAdd]; rfl
  have eB_l : ∀ j : Fin k, eB (Fin.castAdd _ j) = Sum.inl j := by
    intro j
    show (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm.trans (Equiv.sumCongr eE eI)))
      (finSumFinEquiv.symm (Fin.castAdd ((EP I).length + 2 * (EP I).length) j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd]; rfl
  have eB_q : ∀ q : Fin (EP I).length, eB (Fin.natAdd k (Fin.castAdd _ q)) = Sum.inr (Sum.inl (eE q)) := by
    intro q
    show (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm.trans (Equiv.sumCongr eE eI)))
      (finSumFinEquiv.symm (Fin.natAdd k (Fin.castAdd (2 * (EP I).length) q))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    show Sum.inr ((Equiv.sumCongr eE eI) (finSumFinEquiv.symm (Fin.castAdd (2 * (EP I).length) q))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]; rfl
  have eB_t : ∀ t : Fin (2 * (EP I).length), eB (Fin.natAdd k (Fin.natAdd _ t)) = Sum.inr (Sum.inr (eI t)) := by
    intro t
    show (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm.trans (Equiv.sumCongr eE eI)))
      (finSumFinEquiv.symm (Fin.natAdd k (Fin.natAdd (EP I).length t))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    show Sum.inr ((Equiv.sumCongr eE eI) (finSumFinEquiv.symm (Fin.natAdd (EP I).length t))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]; rfl
  refine ⟨eA, eB, ?_⟩
  intro ag it
  have hV : ((uVC m₀ : ℕ) : ℝ) = (3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5) * 3⁻¹ := by
    simp only [uVC, c2C]; push_cast; ring
  have hA : ((uAC m₀ : ℕ) : ℝ) = (3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5) *
      (1 - ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) := by
    have : (3 * (m₀ : ℝ) + 3) ≠ 0 := by positivity
    simp only [uAC, c2C]; push_cast; field_simp; ring
  have hB : ((uBC m₀ : ℕ) : ℝ) = (3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5) *
      (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) := by
    have : (3 * (m₀ : ℝ) + 3) ≠ 0 := by positivity
    simp only [uBC, c2C]; push_cast; field_simp
  have hS : ((3 * (m₀ : ℝ) + 3) ≠ 0) := by positivity
  have heE : ∀ q : Fin (EP I).length, eE q = (edgeL I)[q.val]'(by rw [edgeL_length]; exact q.isLt) := by
    intro q; rfl
  have heI : ∀ t : Fin (2 * (EP I).length), eI t = (incidL I)[t.val]'(by rw [incL_length]; exact t.isLt) := by
    intro t; rfl
  induction ag using Fin.addCases with
  | left v =>
    induction it using Fin.addCases with
    | left j =>
      have hu : (PI m₀ a b I).u (Fin.castAdd _ v) (Fin.castAdd _ j) = uSC m₀ := by
        show ((rowsN m₀ a b I).getD v.val []).getD j.val 0 = uSC m₀
        rw [rowsN_getD_v _ _ _ _ _ v.isLt, vrowN_getD1 _ _ _ _ _ _ _ _ j.isLt]
      rw [hu, eA_l, eB_l]
      simp [redUtil, uSC, c1C, c2C]
    | right it' =>
      induction it' using Fin.addCases with
      | left q =>
        have hu : (PI m₀ a b I).u (Fin.castAdd _ v) (Fin.natAdd _ (Fin.castAdd _ q)) = 0 := by
          show ((rowsN m₀ a b I).getD v.val []).getD (k + q.val) 0 = 0
          rw [rowsN_getD_v _ _ _ _ _ v.isLt, vrowN_getD2 _ _ _ _ _ _ _ _ q.isLt]
        rw [hu, eA_l, eB_q]
        simp [redUtil]
      | right t =>
        have hu : (PI m₀ a b I).u (Fin.castAdd _ v) (Fin.natAdd _ (Fin.natAdd _ t)) =
            if t.val % 2 = 0 then (if (EP I)[t.val / 2]'(by have := t.isLt; omega) / I.N = v.val then uVC m₀ else 0)
            else (if (EP I)[t.val / 2]'(by have := t.isLt; omega) % I.N = v.val then uVC m₀ else 0) := by
          show ((rowsN m₀ a b I).getD v.val []).getD (k + ((EP I).length + t.val)) 0 = _
          rw [rowsN_getD_v _ _ _ _ _ v.isLt, vrowN_getD3 _ _ _ _ _ _ _ _ rfl t.isLt]
        have hf := incidL_fst I t.val (by rw [incL_length]; exact t.isLt)
        rw [hu, eA_l, eB_t, heI]
        simp only [redUtil]
        by_cases hc : ((incidL I)[t.val]'(by rw [incL_length]; exact t.isLt)).1.1 = v
        · have hc' := congrArg Fin.val hc
          rw [hf] at hc'
          rw [if_pos hc]
          rcases Nat.mod_two_eq_zero_or_one t.val with h0 | h0
          · simp only [h0, if_true] at hc' ⊢; rw [if_pos hc', hV]; norm_num
          · simp only [h0, if_false, one_ne_zero] at hc' ⊢; rw [if_pos hc', hV]; norm_num
        · rw [if_neg hc]
          have hc' : ¬ (((incidL I)[t.val]'(by rw [incL_length]; exact t.isLt)).1.1.val = v.val) :=
            fun h => hc (Fin.ext h)
          rw [hf] at hc'
          rcases Nat.mod_two_eq_zero_or_one t.val with h0 | h0
          · simp only [h0, if_true] at hc' ⊢; rw [if_neg hc']; simp
          · simp only [h0, if_false, one_ne_zero] at hc' ⊢; rw [if_neg hc']; simp
  | right e =>
    induction it using Fin.addCases with
    | left j =>
      have hu : (PI m₀ a b I).u (Fin.natAdd _ e) (Fin.castAdd _ j) = 0 := by
        show ((rowsN m₀ a b I).getD (I.N + e.val) []).getD j.val 0 = 0
        rw [rowsN_getD_e _ _ _ _ _ e.isLt, erowN_getD1 _ _ _ _ _ _ j.isLt]
      rw [hu, eA_r, eB_l]
      simp [redUtil]
    | right it' =>
      induction it' using Fin.addCases with
      | left q =>
        have hu : (PI m₀ a b I).u (Fin.natAdd _ e) (Fin.natAdd _ (Fin.castAdd _ q)) =
            if q.val = e.val then uAC m₀ else 0 := by
          show ((rowsN m₀ a b I).getD (I.N + e.val) []).getD (k + q.val) 0 = _
          rw [rowsN_getD_e _ _ _ _ _ e.isLt, erowN_getD2 _ _ _ _ _ _ q.isLt]
        rw [hu, eA_r, eB_q, heE, heE]
        simp only [redUtil]
        by_cases hc : q.val = e.val
        · have : (edgeL I)[e.val]'(by rw [edgeL_length]; exact e.isLt) =
              (edgeL I)[q.val]'(by rw [edgeL_length]; exact q.isLt) := by simp [hc]
          rw [if_pos hc, if_pos this, hA]
        · have : ¬ ((edgeL I)[e.val]'(by rw [edgeL_length]; exact e.isLt) =
              (edgeL I)[q.val]'(by rw [edgeL_length]; exact q.isLt)) := by
            rw [(edgeL_nodup I).getElem_inj_iff]; omega
          rw [if_neg hc, if_neg this]; simp
      | right t =>
        have hu : (PI m₀ a b I).u (Fin.natAdd _ e) (Fin.natAdd _ (Fin.natAdd _ t)) =
            if t.val / 2 = e.val then uBC m₀ else 0 := by
          show ((rowsN m₀ a b I).getD (I.N + e.val) []).getD (k + ((EP I).length + t.val)) 0 = _
          rw [rowsN_getD_e _ _ _ _ _ e.isLt, erowN_getD3 _ _ _ _ _ _ t.isLt]
        have hs := incidL_snd I t.val (by rw [incL_length]; exact t.isLt)
        rw [hu, eA_r, eB_t, heE, heI]
        simp only [redUtil]
        rw [hs]
        by_cases hc : t.val / 2 = e.val
        · have : ((edgeL I)[e.val]'(by rw [edgeL_length]; exact e.isLt)).1 =
              ((edgeL I)[t.val / 2]'(by rw [edgeL_length]; have := t.isLt; omega)).1 := by simp [hc]
          rw [if_pos hc, if_pos this, hB]
        · have : ¬ (((edgeL I)[e.val]'(by rw [edgeL_length]; exact e.isLt)).1 =
              ((edgeL I)[t.val / 2]'(by rw [edgeL_length]; have := t.isLt; omega)).1) := by
            rw [← Subtype.ext_iff, (edgeL_nodup I).getElem_inj_iff]; omega
          rw [if_neg hc, if_neg this]; simp
