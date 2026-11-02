-- Prove2me | solution 1 for MultiPurchase.Hardness.maxCut_polyReducible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:56:25.687393+00:00
-- url     : https://prove2.me/submissions/2349553f-b0f9-457f-b258-1ec0cbdba0f1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_MultiPurchase_Hardness_compare_step
import Theorems.Thm_MultiPurchase_Hardness_eq_7_maxcut


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## Registers of the stack machine -/

inductive Key
  | inp | out | bad | A | Pd | Bn | Bt | F | N | M | R | C | X | Y | Z | T | T2 | W | Cs | Cns | Ct | E | B2 | Us | D | P | Q | sc | Mv | G | Dg
  deriving DecidableEq

instance : Fintype Key :=
  ⟨⟨([.inp, .out, .bad, .A, .Pd, .Bn, .Bt, .F, .N, .M, .R, .C, .X, .Y, .Z, .T, .T2, .W, .Cs, .Cns, .Ct, .E, .B2, .Us, .D, .P, .Q, .sc, .Mv, .G, .Dg] : List Key), by decide⟩, by intro x; cases x <;> decide⟩

structure Regs where
  inp : List BSym
  out : List BSym
  bad : List BSym
  A : List BSym
  Pd : List BSym
  Bn : List BSym
  Bt : List BSym
  F : List BSym
  N : List BSym
  M : List BSym
  R : List BSym
  C : List BSym
  X : List BSym
  Y : List BSym
  Z : List BSym
  T : List BSym
  T2 : List BSym
  W : List BSym
  Cs : List BSym
  Cns : List BSym
  Ct : List BSym
  E : List BSym
  B2 : List BSym
  Us : List BSym
  D : List BSym
  P : List BSym
  Q : List BSym
  sc : List BSym
  Mv : List BSym
  G : List BSym
  Dg : List BSym

namespace Regs

def get (σ : Regs) : Key → List BSym
  | .inp => σ.inp
  | .out => σ.out
  | .bad => σ.bad
  | .A => σ.A
  | .Pd => σ.Pd
  | .Bn => σ.Bn
  | .Bt => σ.Bt
  | .F => σ.F
  | .N => σ.N
  | .M => σ.M
  | .R => σ.R
  | .C => σ.C
  | .X => σ.X
  | .Y => σ.Y
  | .Z => σ.Z
  | .T => σ.T
  | .T2 => σ.T2
  | .W => σ.W
  | .Cs => σ.Cs
  | .Cns => σ.Cns
  | .Ct => σ.Ct
  | .E => σ.E
  | .B2 => σ.B2
  | .Us => σ.Us
  | .D => σ.D
  | .P => σ.P
  | .Q => σ.Q
  | .sc => σ.sc
  | .Mv => σ.Mv
  | .G => σ.G
  | .Dg => σ.Dg

def set (σ : Regs) : Key → List BSym → Regs
  | .inp, l => { σ with inp := l }
  | .out, l => { σ with out := l }
  | .bad, l => { σ with bad := l }
  | .A, l => { σ with A := l }
  | .Pd, l => { σ with Pd := l }
  | .Bn, l => { σ with Bn := l }
  | .Bt, l => { σ with Bt := l }
  | .F, l => { σ with F := l }
  | .N, l => { σ with N := l }
  | .M, l => { σ with M := l }
  | .R, l => { σ with R := l }
  | .C, l => { σ with C := l }
  | .X, l => { σ with X := l }
  | .Y, l => { σ with Y := l }
  | .Z, l => { σ with Z := l }
  | .T, l => { σ with T := l }
  | .T2, l => { σ with T2 := l }
  | .W, l => { σ with W := l }
  | .Cs, l => { σ with Cs := l }
  | .Cns, l => { σ with Cns := l }
  | .Ct, l => { σ with Ct := l }
  | .E, l => { σ with E := l }
  | .B2, l => { σ with B2 := l }
  | .Us, l => { σ with Us := l }
  | .D, l => { σ with D := l }
  | .P, l => { σ with P := l }
  | .Q, l => { σ with Q := l }
  | .sc, l => { σ with sc := l }
  | .Mv, l => { σ with Mv := l }
  | .G, l => { σ with G := l }
  | .Dg, l => { σ with Dg := l }

lemma update_get (σ : Regs) (k : Key) (l : List BSym) :
    Function.update σ.get k l = (σ.set k l).get := by
  funext j
  cases k <;> cases j <;> rfl

lemma get_set (σ : Regs) (k j : Key) (l : List BSym) :
    (σ.set k l).get j = if j = k then l else σ.get j := by
  rw [← update_get]; simp [Function.update_apply]

@[simp] lemma get_set_self (σ : Regs) (k : Key) (l : List BSym) : (σ.set k l).get k = l := by
  simp [get_set]

lemma ext_get {σ τ : Regs} (h : σ.get = τ.get) : σ = τ := by
  cases σ; cases τ
  simp only [Regs.mk.injEq]
  exact ⟨congrFun h .inp, congrFun h .out, congrFun h .bad, congrFun h .A, congrFun h .Pd, congrFun h .Bn, congrFun h .Bt, congrFun h .F, congrFun h .N, congrFun h .M, congrFun h .R, congrFun h .C, congrFun h .X, congrFun h .Y, congrFun h .Z, congrFun h .T, congrFun h .T2, congrFun h .W, congrFun h .Cs, congrFun h .Cns, congrFun h .Ct, congrFun h .E, congrFun h .B2, congrFun h .Us, congrFun h .D, congrFun h .P, congrFun h .Q, congrFun h .sc, congrFun h .Mv, congrFun h .G, congrFun h .Dg⟩

lemma set_set (σ : Regs) (k : Key) (u v : List BSym) : (σ.set k u).set k v = σ.set k v := by
  apply ext_get; funext j; simp only [get_set]; split_ifs <;> rfl

lemma set_comm (σ : Regs) {k j : Key} (h : k ≠ j) (u v : List BSym) :
    (σ.set k u).set j v = (σ.set j v).set k u := by
  apply ext_get; funext i; simp only [get_set]
  split_ifs with h1 h2 <;> first | rfl | (subst h1; subst h2; exact absurd rfl h)

lemma set_get (σ : Regs) (k : Key) : σ.set k (σ.get k) = σ := by
  apply ext_get; funext j; simp only [get_set]; split_ifs with h <;> first | rfl | (subst h; rfl)

end Regs

/-- the empty register file, except for the register `Mv` -/
def Regs.empty (m : List BSym) : Regs :=
  ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], m, [], []⟩

abbrev Prog := StackProg Key BSym

/-- the tops of a register file -/
def hd (σ : Regs) : Key → Option BSym := fun k => (σ.get k).head?

/-- `p` runs from `σ` to `τ` within `B` steps. -/
def Runs (p : Prog) (σ τ : Regs) (B : ℕ) : Prop := ∃ n ≤ B, p.Exec σ.get τ.get n

/-! ## Combinators -/

lemma Runs.mono {p : Prog} {σ τ : Regs} {B B' : ℕ} (h : Runs p σ τ B) (hB : B ≤ B') :
    Runs p σ τ B' := by
  obtain ⟨n, hn, e⟩ := h; exact ⟨n, le_trans hn hB, e⟩

lemma Runs.seq {p q : Prog} {σ τ υ : Regs} {B1 B2 : ℕ} (h1 : Runs p σ τ B1)
    (h2 : Runs q τ υ B2) : Runs (.seq p q) σ υ (B1 + 1 + B2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨n + 1 + m, by omega, StackProg.Exec.seq e e'⟩

lemma Runs.seq' {p q : Prog} {σ τ υ : Regs} {B1 B2 B : ℕ} (h1 : Runs p σ τ B1)
    (h2 : Runs q τ υ B2) (hB : B1 + 1 + B2 ≤ B) : Runs (.seq p q) σ υ B :=
  (h1.seq h2).mono hB

lemma Runs.brT {t : (Key → Option BSym) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = true) (h : Runs p σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchTrue ht e⟩

lemma Runs.brF {t : (Key → Option BSym) → Bool} {p q : Prog} {σ τ : Regs} {B : ℕ}
    (ht : t (hd σ) = false) (h : Runs q σ τ B) : Runs (.branch t p q) σ τ (B + 1) := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨1 + n, by omega, StackProg.Exec.branchFalse ht e⟩

/-- a loop driven by an explicit sequence of register files -/
lemma Runs.loopU (t : (Key → Option BSym) → Bool) (body : Prog) (h : ℕ → Regs) (B m : ℕ)
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

/-! ## Primitive programs -/

def mvProg (a b : Key) : Prog := transferProg a (fun k => decide (k = b))

lemma runs_push (k : Key) (a : BSym) (σ : Regs) :
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

/-- `b := (src repeated |c| times) ++ b`, consuming `c` -/
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
  have e := StackProg.Exec.act (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) σ.get
  have : StackProg.applyAct (fun (_ : Key → Option BSym) (_ : Key) => (StackAct.keep : StackAct BSym)) σ.get = σ.get := by
    funext k; rfl
  rw [this] at e; exact e

/-- move the top of `a` onto `b` (one step) -/
def mv1 (a b : Key) : Prog := .act (transferAct a (fun k => decide (k = b)))

lemma runs_mv1 (a b : Key) (hab : a ≠ b) (σ : Regs) (x : BSym) (l : List BSym)
    (h : σ.get a = x :: l) : Runs (mv1 a b) σ ((σ.set a l).set b (x :: σ.get b)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (transferAct a (fun k => decide (k = b))) σ.get
  unfold mv1
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [StackProg.applyAct, transferAct]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, h, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [h, StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

/-- move the maximal prefix of `a` satisfying `pred` onto `b` (reversed) -/
def mvwProg (a b : Key) (pred : BSym → Bool) : Prog :=
  .loop (fun h => match h a with | some x => pred x | none => false) (mv1 a b)

lemma runs_mvw (a b : Key) (hab : a ≠ b) (pred : BSym → Bool) :
    ∀ (l : List BSym) (σ : Regs), σ.get a = l →
      Runs (mvwProg a b pred) σ
        ((σ.set a (l.dropWhile pred)).set b ((l.takeWhile pred).reverse ++ σ.get b))
        (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ hσ
    refine ⟨1, le_rfl, ?_⟩
    simp only [List.dropWhile_nil, List.takeWhile_nil, List.reverse_nil, List.nil_append]
    rw [← hσ, Regs.set_get, Regs.set_get]
    exact StackProg.Exec.loopFalse (by simp [hd, hσ])
  | cons x l ih =>
    intro σ hσ
    by_cases hp : pred x = true
    · have h1 := runs_mv1 a b hab σ x l hσ
      set σ1 := (σ.set a l).set b (x :: σ.get b) with hσ1
      have hσ1a : σ1.get a = l := by
        rw [hσ1, Regs.get_set, if_neg hab, Regs.get_set_self]
      obtain ⟨m, hm, e2⟩ := ih σ1 hσ1a
      obtain ⟨n, hn, e1⟩ := h1
      refine ⟨1 + n + 1 + m, by simp; omega, ?_⟩
      have hres : ((σ1.set a (l.dropWhile pred)).set b ((l.takeWhile pred).reverse ++ σ1.get b)) =
          ((σ.set a ((x :: l).dropWhile pred)).set b (((x :: l).takeWhile pred).reverse ++ σ.get b)) := by
        have hb : σ1.get b = x :: σ.get b := by rw [hσ1, Regs.get_set_self]
        rw [hb]
        simp only [List.dropWhile_cons, List.takeWhile_cons, hp, if_true, List.reverse_cons,
          List.append_assoc, List.singleton_append]
        rw [hσ1]
        apply Regs.ext_get; funext i; simp only [Regs.get_set]
        split_ifs <;> simp_all
      rw [← hres]
      exact StackProg.Exec.loopTrue (by simp [hσ, hp]) e1 e2
    · refine ⟨1, by omega, ?_⟩
      have hpf : pred x = false := by simpa using hp
      simp only [List.dropWhile_cons, List.takeWhile_cons, hpf, Bool.false_eq_true, if_false,
        List.reverse_nil, List.nil_append]
      rw [← hσ, Regs.set_get, Regs.set_get]
      exact StackProg.Exec.loopFalse (by simp [hσ, hpf])

/-! ## size bounds -/

lemma pw_mono {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

/-! ## Binary counters (least significant bit first) -/

def toB (b : Bool) : BSym := if b then .one else .zero
def enc (x : List Bool) : List BSym := x.map toB

@[simp] lemma enc_nil : enc [] = [] := rfl
@[simp] lemma enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = toB b :: enc l := rfl
@[simp] lemma enc_append (l l' : List Bool) : enc (l ++ l') = enc l ++ enc l' := by
  simp [enc]
@[simp] lemma enc_replicate (c : ℕ) (b : Bool) : enc (List.replicate c b) = List.replicate c (toB b) := by
  simp [enc]
@[simp] lemma length_enc (l : List Bool) : (enc l).length = l.length := by simp [enc]
@[simp] lemma toB_true : toB true = .one := rfl
@[simp] lemma toB_false : toB false = .zero := rfl

def incL : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incL r

def decL : List Bool → List Bool
  | [] => []
  | true :: r => if r = [] then [] else false :: r
  | false :: r => true :: decL r

lemma bit_ne_zero_aux (b : Bool) (n : ℕ) (h : n = 0 → b = true) : Nat.bit b n ≠ 0 := by
  cases b
  · have : n ≠ 0 := fun h0 => by simpa using h h0
    simp [Nat.bit]; omega
  · simp [Nat.bit]

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

lemma bits_eq_nil_iff' (k : ℕ) : Nat.bits k = [] ↔ k = 0 := by
  induction k using Nat.binaryRec' with
  | zero => simp
  | bit b n hn _ =>
    rw [Nat.bits_append_bit _ _ hn]
    simp only [reduceCtorEq, false_iff]
    exact bit_ne_zero_aux b n hn

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

lemma len_bits_le (x : ℕ) : (Nat.bits x).length ≤ x := by
  induction x using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    have : n ≠ 0 ∨ b = true := by
      by_cases h : n = 0
      · exact Or.inr (hn h)
      · exact Or.inl h
    cases b <;> simp [Nat.bit] at this ⊢ <;> omega

lemma bits_double (n : ℕ) (hn : n ≠ 0) : Nat.bits (2 * n) = false :: Nat.bits n := by
  have := Nat.bits_append_bit n false (fun h => absurd h hn)
  simpa [Nat.bit] using this

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

/-- split off the maximal block of leading `true`s -/
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

def ppAct (a b : Key) (y : BSym) : (Key → Option BSym) → Key → StackAct BSym :=
  fun _ k => if k = a then .pop else if k = b then .push y else .keep

lemma runs_pp (a b : Key) (hab : a ≠ b) (y : BSym) (σ : Regs) :
    Runs (.act (ppAct a b y)) σ ((σ.set a (σ.get a).tail).set b (y :: σ.get b)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have e := StackProg.Exec.act (ppAct a b y) σ.get
  convert e using 1
  funext k
  rw [Regs.get_set, Regs.get_set]
  simp only [StackProg.applyAct, ppAct]
  by_cases h1 : k = b
  · subst h1; simp [Ne.symm hab, StackAct.apply]
  · by_cases h2 : k = a
    · subst h2; simp [StackAct.apply, hab]
    · simp [h1, h2, StackAct.apply]

/-- while the top of `a` is `x`: pop `a`, push `y` onto `b` -/
def whilePP (a b : Key) (x y : BSym) : Prog :=
  .loop (fun h => decide (h a = some x)) (.act (ppAct a b y))

lemma runs_whilePP (a b : Key) (hab : a ≠ b) (x y : BSym) :
    ∀ (c : ℕ) (r : List BSym) (σ : Regs), σ.get a = List.replicate c x ++ r → r.head? ≠ some x →
      Runs (whilePP a b x y) σ ((σ.set a r).set b (List.replicate c y ++ σ.get b)) (3 * c + 1) := by
  intro c
  induction c with
  | zero =>
    intro r σ ha hr
    simp only [List.replicate_zero, List.nil_append] at ha ⊢
    rw [← ha, Regs.set_get, Regs.set_get]
    exact ⟨1, le_rfl, StackProg.Exec.loopFalse (by simp [hd, ha, hr])⟩
  | succ c ih =>
    intro r σ ha hr
    obtain ⟨n, hn, e1⟩ := runs_pp a b hab y σ
    set σ1 := (σ.set a (σ.get a).tail).set b (y :: σ.get b) with hσ1
    have h1 : σ1.get a = List.replicate c x ++ r := by
      rw [hσ1, Regs.get_set, if_neg hab, Regs.get_set_self, ha]; simp [List.replicate_succ]
    obtain ⟨m, hm, e2⟩ := ih r σ1 h1 hr
    refine ⟨1 + n + 1 + m, by omega, ?_⟩
    have hres : (σ1.set a r).set b (List.replicate c y ++ σ1.get b) =
        (σ.set a r).set b (List.replicate (c + 1) y ++ σ.get b) := by
      have hb : σ1.get b = y :: σ.get b := by rw [hσ1, Regs.get_set_self]
      rw [hb, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs <;> simp_all [List.replicate_succ']
    rw [← hres]
    exact StackProg.Exec.loopTrue (by simp [hd, ha, List.replicate_succ]) e1 e2

/-! ## increment, decrement, emission -/

/-- increment the counter `X` (scratch `T`, empty before and after) -/
def incProg (X T : Key) : Prog :=
  .seq (whilePP X T .one .zero)
    (.seq (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP)
      (.seq (pushProg X .one) (mvProg T X)))

lemma runs_inc (X T : Key) (hXT : X ≠ T) (σ : Regs) (l : List Bool)
    (hX : σ.get X = enc l) (hT : σ.get T = []) :
    Runs (incProg X T) σ (σ.set X (enc (incL l))) (6 * l.length + 10) := by
  obtain ⟨c, rest, hl, hrest⟩ := split_true l
  subst hl
  have hX' : σ.get X = List.replicate c BSym.one ++ enc rest := by rw [hX]; simp
  have hr : (enc rest).head? ≠ some BSym.one := by
    cases rest with
    | nil => simp
    | cons b r => cases b <;> simp_all
  have e1 := runs_whilePP X T hXT .one .zero c (enc rest) σ hX' hr
  set σ1 := (σ.set X (enc rest)).set T (List.replicate c BSym.zero ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = enc rest := by rw [hσ1, Regs.get_set, if_neg hXT, Regs.get_set_self]
  have hσ1T : σ1.get T = List.replicate c BSym.zero := by rw [hσ1, Regs.get_set_self, hT]; simp
  -- the branch: pop a leading zero
  obtain ⟨σ2, rest', e2, hσ2, hrest'⟩ : ∃ σ2 rest', Runs (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP) σ1 σ2 2 ∧
      σ2 = σ1.set X (enc rest') ∧ incL rest = true :: rest' := by
    cases rest with
    | nil =>
      refine ⟨σ1, [], (runs_skip σ1).brF (by simp [hd, hσ1X]), ?_, by simp [incL]⟩
      rw [← hσ1X, Regs.set_get]
    | cons b r =>
      cases b
      · have hb : Runs (.branch (fun h => decide (h X = some .zero)) (popProg X) skipP) σ1
            (σ1.set X (σ1.get X).tail) 2 := (runs_pop X σ1).brT (by simp [hd, hσ1X])
        have ht : (σ1.get X).tail = enc r := by rw [hσ1X]; rfl
        rw [ht] at hb
        exact ⟨σ1.set X (enc r), r, hb, rfl, by simp [incL]⟩
      · simp at hrest
  have e3 := runs_push X .one σ2
  set σ3 := σ2.set X (BSym.one :: σ2.get X) with hσ3
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (enc (incL (List.replicate c true ++ rest))) := by
    rw [incL_rep, hrest']
    have h3T : σ3.get T = List.replicate c BSym.zero := by
      rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1T]
    have h3X : σ3.get X = BSym.one :: enc rest' := by
      rw [hσ3, Regs.get_set_self, hσ2, Regs.get_set_self]
    rw [h3T, h3X, hσ3, hσ2, hσ1]
    apply Regs.ext_get; funext i; simp only [Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  have : (σ3.get T).length = c := by
    rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1T]
    simp
  rw [this]; simp; omega

/-- decrement the counter `X` holding a nonzero canonical value (scratch `T`) -/
def decProg (X T : Key) : Prog :=
  .seq (whilePP X T .zero .one)
    (.seq (popProg X)
      (.seq (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) (mvProg T X)))

lemma runs_dec (X T : Key) (hXT : X ≠ T) (σ : Regs) (c : ℕ) (r : List Bool)
    (hX : σ.get X = enc (List.replicate c false ++ true :: r)) (hT : σ.get T = []) :
    Runs (decProg X T) σ (σ.set X (enc (decL (List.replicate c false ++ true :: r))))
      (6 * c + 10) := by
  have hX' : σ.get X = List.replicate c BSym.zero ++ enc (true :: r) := by rw [hX]; simp
  have e1 := runs_whilePP X T hXT .zero .one c (enc (true :: r)) σ hX' (by simp)
  set σ1 := (σ.set X (enc (true :: r))).set T (List.replicate c BSym.one ++ σ.get T) with hσ1
  have hσ1X : σ1.get X = BSym.one :: enc r := by
    rw [hσ1, Regs.get_set, if_neg hXT, Regs.get_set_self]; simp
  have e2 := runs_pop X σ1
  set σ2 := σ1.set X (σ1.get X).tail with hσ2
  have hσ2X : σ2.get X = enc r := by rw [hσ2, Regs.get_set_self, hσ1X]; rfl
  obtain ⟨σ3, e3, hσ3⟩ : ∃ σ3, Runs (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) σ2 σ3 2 ∧
      σ3 = σ2.set X (enc (if r = [] then [] else false :: r)) := by
    by_cases hr : r = []
    · subst hr
      refine ⟨σ2, (runs_skip σ2).brF (by simp [hd, hσ2X]), ?_⟩
      simp only [if_true]; rw [← hσ2X, Regs.set_get]
    · have hb : Runs (.branch (fun h => (h X).isSome) (pushProg X .zero) skipP) σ2
          (σ2.set X (BSym.zero :: σ2.get X)) 2 := (runs_push X .zero σ2).brT (by
          cases r with
          | nil => exact absurd rfl hr
          | cons b r => simp [hd, hσ2X])
      refine ⟨_, hb, ?_⟩
      rw [if_neg hr, hσ2X]; rfl
  have e4 := runs_mv T X (Ne.symm hXT) σ3
  have h3T : σ3.get T = List.replicate c BSym.one := by
    rw [hσ3, Regs.get_set, if_neg (Ne.symm hXT), hσ2, Regs.get_set, if_neg (Ne.symm hXT), hσ1,
      Regs.get_set_self, hT]; simp
  have hfin : (σ3.set T []).set X ((σ3.get T).reverse ++ σ3.get X) =
      σ.set X (enc (decL (List.replicate c false ++ true :: r))) := by
    rw [decL_rep, h3T]
    have h3X : σ3.get X = enc (if r = [] then [] else false :: r) := by
      rw [hσ3, Regs.get_set_self]
    rw [h3X, hσ3, hσ2, hσ1]
    apply Regs.ext_get; funext i; simp only [Regs.get_set]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  rw [← hfin]
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_
  rw [h3T]; simp; omega

/-- append `encNat` of the counter `X` to the reversed output `W` (scratch `T`, `sc`) -/
def emitProg (X : Key) : Prog :=
  .seq (copyProg X .T .sc) (.seq (mvProg .T .W) (pushProg .W .sep))

lemma runs_emit (X : Key) (h1 : X ≠ .T) (h2 : X ≠ .sc) (h3 : X ≠ .W) (σ : Regs)
    (hT : σ.T = []) (hsc : σ.sc = []) :
    Runs (emitProg X) σ { σ with W := BSym.sep :: (σ.get X).reverse ++ σ.W }
      (9 * (σ.get X).length + 7) := by
  have e1 := runs_copy X .T .sc h1 h2 (by decide) σ hsc
  set σ1 := σ.set .T (σ.get X ++ σ.get .T) with hσ1
  have e2 := runs_mv .T .W (by decide) σ1
  set σ2 := (σ1.set .T []).set .W ((σ1.get .T).reverse ++ σ1.get .W) with hσ2
  have e3 := runs_push .W .sep σ2
  have hfin : σ2.set .W (BSym.sep :: σ2.get .W) = { σ with W := BSym.sep :: (σ.get X).reverse ++ σ.W } := by
    rw [hσ2, hσ1]
    apply Regs.ext_get; funext i
    simp only [Regs.get_set]
    have hXW : σ.get X = σ.get X := rfl
    cases i <;> simp_all [Regs.get] <;> rfl
  rw [← hfin]
  refine (e1.seq (e2.seq e3)).mono ?_
  have hl : (σ1.get .T).length = (σ.get X).length := by
    rw [hσ1, Regs.get_set_self, show σ.get .T = [] from hT]; simp
  rw [hl]; omega

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

/-! ## more combinators -/

lemma Runs.congr {p : Prog} {σ τ τ' : Regs} {B : ℕ} (h : Runs p σ τ B) (e : τ = τ') :
    Runs p σ τ' B := e ▸ h

lemma Runs.loopT {t : (Key → Option BSym) → Bool} {body : Prog} {σ σ' τ : Regs} {B1 B2 : ℕ}
    (ht : t (hd σ) = true) (h1 : Runs body σ σ' B1) (h2 : Runs (.loop t body) σ' τ B2) :
    Runs (.loop t body) σ τ (B1 + B2 + 2) := by
  obtain ⟨n, hn, e⟩ := h1; obtain ⟨m, hm, e'⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, StackProg.Exec.loopTrue ht e e'⟩

lemma Runs.loopF {t : (Key → Option BSym) → Bool} {body : Prog} {σ : Regs}
    (ht : t (hd σ) = false) : Runs (.loop t body) σ σ 1 :=
  ⟨1, le_rfl, StackProg.Exec.loopFalse ht⟩


def initM (m w : List BSym) : Regs := { Regs.empty m with inp := w }

def gate (p : Prog) : Prog := .branch (fun h => (h .bad).isNone) p skipP

lemma runs_gate_ok {p : Prog} {σ τ : Regs} {B : ℕ} (hb : σ.bad = []) (h : Runs p σ τ B) :
    Runs (gate p) σ τ (B + 1) :=
  Runs.brT (by simp [hd, Regs.get, hb]) h

lemma runs_gate_skip {p : Prog} {σ : Regs} (hb : σ.bad ≠ []) : Runs (gate p) σ σ 2 :=
  Runs.brF (by
    cases h : σ.bad with
    | nil => exact absurd h hb
    | cons a l => simp [hd, Regs.get, h]) (runs_skip σ)

/-! ## Phase 1-3: the number `n` -/

def isDigB : BSym → Bool
  | .one => true
  | .zero => true
  | _ => false

def pP1 : Prog := mvwProg .inp .A isDigB

def pP2 : Prog :=
  .branch (fun h => decide (h .inp = some .sep) && decide (h .A ≠ some .zero)) (popProg .inp)
    (pushProg .bad .one)

def pP3 : Prog := mvProg .A .Bn

/-- the digits read and the rest -/
def digs (w : List BSym) : List BSym := w.takeWhile isDigB
def rest (w : List BSym) : List BSym := w.dropWhile isDigB

/-- the check of phase 2 -/
def numOK (w : List BSym) : Prop :=
  (rest w).head? = some .sep ∧ (digs w).getLast? ≠ some .zero

instance (w : List BSym) : Decidable (numOK w) := by unfold numOK; infer_instance

def st3 (m w : List BSym) : Regs := { Regs.empty m with inp := (rest w).tail, Bn := digs w }

lemma runs_P123 (w : List BSym) :
    ∃ τ, Runs (.seq pP1 (.seq pP2 pP3)) (initM m w) τ (6 * w.length + 10) ∧
      (numOK w → τ = st3 m w) ∧ (¬ numOK w → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_mvw .inp .A (by decide) isDigB w (initM m w) rfl
  set σ1 := ((initM m w).set .inp (w.dropWhile isDigB)).set .A
    ((w.takeWhile isDigB).reverse ++ (initM m w).get .A) with hσ1
  have h1i : σ1.inp = rest w := rfl
  have h1A : σ1.A = (digs w).reverse := by simp [hσ1, Regs.set, Regs.get, initM, Regs.empty, digs]
  by_cases hok : numOK w
  · obtain ⟨hs, hl⟩ := hok
    have e2 : Runs pP2 σ1 (σ1.set .inp (σ1.get .inp).tail) 2 := by
      refine (runs_pop .inp σ1).brT ?_
      simp only [hd, Regs.get, h1i, hs, h1A, List.head?_reverse, decide_true, Bool.true_and,
        decide_eq_true_eq]
      exact hl
    set σ2 := σ1.set .inp (σ1.get .inp).tail with hσ2
    have e3 := runs_mv .A .Bn (by decide) σ2
    refine ⟨_, (e1.seq (e2.seq e3)).mono ?_, fun _ => ?_, fun h => absurd ⟨hs, hl⟩ h⟩
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.set, Regs.get, h1A, List.length_reverse, digs]
        exact (List.takeWhile_sublist _).length_le
      omega
    · simp only [hσ2, Regs.set, Regs.get, h1A, h1i, st3, List.reverse_reverse]
      simp [hσ1, Regs.set, Regs.get, initM, Regs.empty, rest]
  · have e2 : Runs pP2 σ1 (σ1.set .bad (.one :: σ1.get .bad)) 2 := by
      refine (runs_push .bad .one σ1).brF ?_
      simp only [hd, Regs.get, h1i, h1A, List.head?_reverse]
      unfold numOK at hok
      by_cases hs : (rest w).head? = some .sep
      · have hl : (digs w).getLast? = some .zero := by
          by_contra h; exact hok ⟨hs, h⟩
        simp [hs, hl]
      · simp [hs]
    set σ2 := σ1.set .bad (.one :: σ1.get .bad) with hσ2
    have e3 := runs_mv .A .Bn (by decide) σ2
    refine ⟨_, (e1.seq (e2.seq e3)).mono ?_, fun h => absurd h hok, ?_⟩
    · have : (σ2.get .A).length ≤ w.length := by
        simp only [hσ2, Regs.set, Regs.get, h1A, List.length_reverse, digs]
        exact (List.takeWhile_sublist _).length_le
      omega
    · intro _
      simp [hσ2, Regs.set, Regs.get]
      simp [hσ1, Regs.set, Regs.get, initM, Regs.empty]

/-! ## Phase 4: the entries -/

def tokB : Bool → List BSym
  | false => [.sep]
  | true => [.one, .sep]

def tokP : Bool → List BSym → Option (List Bool)
  | false, [] => some []
  | true, [] => none
  | false, .sep :: r => (tokP false r).map (false :: ·)
  | false, .one :: r => tokP true r
  | false, _ :: _ => none
  | true, .sep :: r => (tokP false r).map (true :: ·)
  | true, _ :: _ => none

def pdS : Bool → List BSym
  | false => []
  | true => [.one]

def tokBody : Prog :=
  .branch (fun h => (h .Pd).isNone)
    (.branch (fun h => decide (h .inp = some .sep)) (.seq (popProg .inp) (pushProg .A .zero))
      (.branch (fun h => decide (h .inp = some .one)) (.seq (popProg .inp) (pushProg .Pd .one))
        (pushProg .bad .one)))
    (.branch (fun h => decide (h .inp = some .sep))
      (.seq (popProg .inp) (.seq (popProg .Pd) (pushProg .A .one)))
      (pushProg .bad .one))

def tokLoop : Prog := .loop (fun h => (h .inp).isSome && (h .bad).isNone) tokBody

lemma tb_sep0 (σ : Regs) (r : List BSym) (hi : σ.inp = .sep :: r) (hp : σ.Pd = []) :
    Runs tokBody σ { σ with inp := r, A := .zero :: σ.A } 7 := by
  have e : Runs (.seq (popProg .inp) (pushProg .A .zero)) σ { σ with inp := r, A := .zero :: σ.A } 3 :=
    ((runs_pop .inp σ).seq (runs_push .A .zero _)).congr (by simp [Regs.set, Regs.get, hi])
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brT ?_ e)).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]

lemma tb_one0 (σ : Regs) (r : List BSym) (hi : σ.inp = .one :: r) (hp : σ.Pd = []) :
    Runs tokBody σ { σ with inp := r, Pd := [.one] } 7 := by
  have e : Runs (.seq (popProg .inp) (pushProg .Pd .one)) σ { σ with inp := r, Pd := [.one] } 3 :=
    ((runs_pop .inp σ).seq (runs_push .Pd .one _)).congr (by simp [Regs.set, Regs.get, hi, hp])
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brF ?_ (Runs.brT ?_ e))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]
  · simp [hd, Regs.get, hi]

lemma tb_bad0 (σ : Regs) (x : BSym) (r : List BSym) (hi : σ.inp = x :: r) (hp : σ.Pd = [])
    (hx : x ≠ .sep) (hx' : x ≠ .one) :
    Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7 := by
  unfold tokBody
  refine (Runs.brT ?_ (Runs.brF ?_ (Runs.brF ?_ (runs_push .bad .one σ)))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi, hx]
  · simp [hd, Regs.get, hi, hx']

lemma tb_sep1 (σ : Regs) (r : List BSym) (hi : σ.inp = .sep :: r) (hp : σ.Pd = [.one]) :
    Runs tokBody σ { σ with inp := r, Pd := [], A := .one :: σ.A } 7 := by
  have e : Runs (.seq (popProg .inp) (.seq (popProg .Pd) (pushProg .A .one))) σ
      { σ with inp := r, Pd := [], A := .one :: σ.A } 5 :=
    ((runs_pop .inp σ).seq ((runs_pop .Pd _).seq (runs_push .A .one _))).congr
      (by simp [Regs.set, Regs.get, hi, hp])
  unfold tokBody
  refine (Runs.brF ?_ (Runs.brT ?_ e)).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi]

lemma tb_bad1 (σ : Regs) (x : BSym) (r : List BSym) (hi : σ.inp = x :: r) (hp : σ.Pd = [.one])
    (hx : x ≠ .sep) :
    Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7 := by
  unfold tokBody
  refine (Runs.brF ?_ (Runs.brF ?_ (runs_push .bad .one σ))).mono (by omega)
  · simp [hd, Regs.get, hp]
  · simp [hd, Regs.get, hi, hx]

lemma tok_loop : ∀ (l : List BSym) (pd : Bool) (σ : Regs), σ.inp = l → σ.bad = [] →
    σ.Pd = pdS pd →
    ∃ τ, Runs tokLoop σ τ (10 * l.length + 1) ∧ τ.out = σ.out ∧
      (∀ bs, tokP pd l = some bs →
        τ = { σ with inp := [], Pd := [], A := (enc bs).reverse ++ σ.A }) ∧
      (tokP pd l = none → τ.bad ≠ [] ∨ τ.Pd ≠ []) := by
  intro l
  induction l with
  | nil =>
    intro pd σ hi hb hp
    refine ⟨σ, (Runs.loopF (by simp [hd, Regs.get, hi])), rfl, ?_, ?_⟩
    · intro bs h
      cases pd
      · simp [tokP] at h; subst h; cases σ; simp_all [pdS]
      · simp [tokP] at h
    · intro h; cases pd
      · simp [tokP] at h
      · right; simp [hp, pdS]
  | cons x r ih =>
    intro pd σ hi hb hp
    have ht : (fun h : Key → Option BSym => (h .inp).isSome && (h .bad).isNone) (hd σ) = true := by
      simp [hd, Regs.get, hi, hb]
    -- the bad case
    have badCase : ∀ (hbody : Runs tokBody σ (σ.set .bad (.one :: σ.get .bad)) 7),
        ∃ τ, Runs tokLoop σ τ (10 * (x :: r).length + 1) ∧ τ.out = σ.out ∧
          (tokP pd (x :: r) = none → τ.bad ≠ [] ∨ τ.Pd ≠ []) := by
      intro hbody
      have hstop : (fun h : Key → Option BSym => (h .inp).isSome && (h .bad).isNone)
          (hd (σ.set .bad (.one :: σ.get .bad))) = false := by
        simp [hd, Regs.get, Regs.set]
      refine ⟨_, (Runs.loopT ht hbody (Runs.loopF hstop)).mono (by simp; omega), rfl, ?_⟩
      intro _; left; simp [Regs.set, Regs.get]
    cases pd
    · -- no pending digit
      have hp0 : σ.Pd = [] := hp
      cases x with
      | sep =>
        have hbody := tb_sep0 σ r hi hp0
        obtain ⟨τ, e, ho, hs, hn⟩ := ih false { σ with inp := r, A := .zero :: σ.A } rfl hb hp
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          simp only [tokP, Option.map_eq_some_iff] at h
          obtain ⟨bs', h1, rfl⟩ := h
          rw [hs bs' h1]; cases σ; simp_all
        · intro h; simp only [tokP, Option.map_eq_none_iff] at h; exact hn h
      | one =>
        have hbody := tb_one0 σ r hi hp0
        obtain ⟨τ, e, ho, hs, hn⟩ := ih true { σ with inp := r, Pd := [.one] } rfl hb rfl
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          rw [hs bs h]
        · intro h; exact hn h
      | zero =>
        obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad0 σ _ r hi hp0 (by decide) (by decide))
        exact ⟨τ, e, ho, fun bs h => by simp [tokP] at h, hn⟩
      | minus =>
        obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad0 σ _ r hi hp0 (by decide) (by decide))
        exact ⟨τ, e, ho, fun bs h => by simp [tokP] at h, hn⟩
    · -- a pending digit `1`
      have hp1 : σ.Pd = [.one] := hp
      by_cases hx : x = .sep
      · subst hx
        have hbody := tb_sep1 σ r hi hp1
        obtain ⟨τ, e, ho, hs, hn⟩ :=
          ih false { σ with inp := r, Pd := [], A := .one :: σ.A } rfl hb rfl
        refine ⟨τ, (Runs.loopT ht hbody e).mono (by simp; omega), ho, ?_, ?_⟩
        · intro bs h
          simp only [tokP, Option.map_eq_some_iff] at h
          obtain ⟨bs', h1, rfl⟩ := h
          rw [hs bs' h1]; cases σ; simp_all
        · intro h; simp only [tokP, Option.map_eq_none_iff] at h; exact hn h
      · obtain ⟨τ, e, ho, hn⟩ := badCase (tb_bad1 σ x r hi hp1 hx)
        refine ⟨τ, e, ho, fun bs h => ?_, hn⟩
        cases x <;> simp_all [tokP]

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

/-! ## tokens: pure facts -/

lemma tokP_some : ∀ (l : List BSym) (pd : Bool) (bs : List Bool), tokP pd l = some bs →
    (if pd then BSym.one :: l else l) = bs.flatMap tokB := by
  intro l
  induction l with
  | nil => intro pd bs h; cases pd <;> simp_all [tokP]
  | cons x r ih =>
    intro pd bs h
    cases pd with
    | false =>
      cases x with
      | sep =>
        simp only [tokP, Option.map_eq_some_iff] at h
        obtain ⟨bs', h1, rfl⟩ := h
        have := ih false bs' h1
        simp only [Bool.false_eq_true, if_false] at this ⊢
        simp [this, tokB]
      | one =>
        simp only [tokP] at h
        have := ih true bs h
        simpa using this
      | zero => simp [tokP] at h
      | minus => simp [tokP] at h
    | true =>
      cases x with
      | sep =>
        simp only [tokP, Option.map_eq_some_iff] at h
        obtain ⟨bs', h1, rfl⟩ := h
        have := ih false bs' h1
        simp only [Bool.false_eq_true, if_false] at this ⊢
        simp [this, tokB]
      | one => simp [tokP] at h
      | zero => simp [tokP] at h
      | minus => simp [tokP] at h

lemma tokP_flat (bs : List Bool) : tokP false (bs.flatMap tokB) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [tokB, tokP, ih]

lemma length_flat_tokB (bs : List Bool) : bs.length ≤ (bs.flatMap tokB).length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    cases b <;> simp only [tokB, List.length_cons, List.length_nil] <;> omega

lemma tokP_len (l : List BSym) (bs : List Bool) (h : tokP false l = some bs) :
    bs.length ≤ l.length := by
  have := tokP_some l false bs h
  simp at this; rw [this]; exact length_flat_tokB bs

/-! ## Phase 4 -/

def pdCheck : Prog := .branch (fun h => (h .Pd).isSome) (pushProg .bad .one) skipP

def pP4 : Prog := .seq tokLoop (.seq pdCheck (gate (mvProg .A .M)))

lemma runs_P4 (σ : Regs) (hb : σ.bad = []) (hp : σ.Pd = []) (hA : σ.A = []) (hM : σ.M = []) :
    ∃ τ, Runs pP4 σ τ (13 * σ.inp.length + 8) ∧
      (∀ bs, tokP false σ.inp = some bs → τ = { σ with inp := [], M := enc bs }) ∧
      (tokP false σ.inp = none → τ.bad ≠ [] ∧ τ.out = σ.out) := by
  obtain ⟨τ, e, ho, hs, hn⟩ := tok_loop σ.inp false σ rfl hb hp
  by_cases hsome : ∃ bs, tokP false σ.inp = some bs
  · obtain ⟨bs, hbs⟩ := hsome
    have hτ := hs bs hbs
    have e2 : Runs pdCheck τ τ 2 := (runs_skip τ).brF (by simp [hd, Regs.get, hτ])
    have e3 := runs_gate_ok (p := mvProg .A .M) (by rw [hτ]; exact hb) (runs_mv .A .M (by decide) τ)
    refine ⟨_, (e.seq (e2.seq e3)).mono ?_, ?_, ?_⟩
    · have : (τ.get .A).length ≤ σ.inp.length := by
        rw [hτ]; simp only [Regs.get, hA, List.append_nil, List.length_reverse, length_enc]
        exact tokP_len _ _ hbs
      omega
    · intro bs' h'
      rw [hbs] at h'; cases h'
      rw [hτ]; simp [Regs.set, Regs.get, hA, hM, hp]
    · intro h; rw [hbs] at h; cases h
  · have hnone : tokP false σ.inp = none := by
      cases h : tokP false σ.inp with
      | none => rfl
      | some bs => exact absurd ⟨bs, h⟩ hsome
    rcases hn hnone with hbad | hpd
    · have e2 : ∃ τ2, Runs pdCheck τ τ2 2 ∧ τ2.bad ≠ [] ∧ τ2.out = τ.out := by
        by_cases hP : τ.Pd = []
        · exact ⟨τ, (runs_skip τ).brF (by simp [hd, Regs.get, hP]), hbad, rfl⟩
        · refine ⟨_, (runs_push .bad .one τ).brT (by
            cases h : τ.Pd with
            | nil => exact absurd h hP
            | cons a l => simp [hd, Regs.get, h]), by simp [Regs.set], rfl⟩
      obtain ⟨τ2, e2, hb2, ho2⟩ := e2
      refine ⟨τ2, (e.seq (e2.seq (runs_gate_skip hb2))).mono (by omega), ?_, ?_⟩
      · intro bs h; rw [hnone] at h; cases h
      · intro _; exact ⟨hb2, by rw [ho2, ho]⟩
    · have e2 : Runs pdCheck τ (τ.set .bad (.one :: τ.get .bad)) 2 :=
        (runs_push .bad .one τ).brT (by
          cases h : τ.Pd with
          | nil => exact absurd h hpd
          | cons a l => simp [hd, Regs.get, h])
      have hb2 : (τ.set .bad (.one :: τ.get .bad)).bad ≠ [] := by simp [Regs.set]
      refine ⟨_, (e.seq (e2.seq (runs_gate_skip hb2))).mono (by omega), ?_, ?_⟩
      · intro bs h; rw [hnone] at h; cases h
      · intro _; exact ⟨hb2, by simp [Regs.set, ho]⟩

/-! ## Phase 6: the unary form of `n`, with fuel -/

def fuelBody : Prog := .seq (popProg .F) (.seq (pushProg .N .one) (decProg .Bt .T))

def fuelLoop : Prog := .loop (fun h => (h .Bt).isSome && (h .F).isSome) fuelBody

def btCheck : Prog := .branch (fun h => (h .Bt).isSome) (pushProg .bad .one) skipP

def pP6 : Prog :=
  .seq (.seq (copyProg .M .F .sc) (copyProg .Bn .Bt .sc)) (.seq fuelLoop (.seq btCheck (clearProg .F)))

/-- the register file once `n` and the entries are known -/
def st4 (m : List BSym) (n : ℕ) (bs : List Bool) : Regs := { Regs.empty m with Bn := enc (Nat.bits n), M := enc bs }

def st6 (m : List BSym) (n : ℕ) (bs : List Bool) : Regs :=
  { Regs.empty m with Bn := enc (Nat.bits n), M := enc bs, N := List.replicate n .one }

def fuelSt (m : List BSym) (n : ℕ) (bs : List Bool) (j : ℕ) : Regs :=
  { Regs.empty m with
    Bn := enc (Nat.bits n)
    M := enc bs
    F := (enc bs).drop j
    Bt := enc (Nat.bits (n - j))
    N := List.replicate j .one }

lemma len_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

lemma fuel_step (n : ℕ) (bs : List Bool) (j : ℕ) (hj : j < n) (hj' : j < bs.length) :
    Runs fuelBody (fuelSt m n bs j) (fuelSt m n bs (j + 1)) (6 * (Nat.bits n).length + 20) := by
  obtain ⟨c, r, hcr⟩ := bits_split_false (n - j) (by omega)
  have e1 := runs_pop .F (fuelSt m n bs j)
  have e2 := runs_push .N .one ((fuelSt m n bs j).set .F ((fuelSt m n bs j).get .F).tail)
  set σ2 := ((fuelSt m n bs j).set .F ((fuelSt m n bs j).get .F).tail).set .N
    (.one :: (((fuelSt m n bs j).set .F ((fuelSt m n bs j).get .F).tail).get .N)) with hσ2
  have e3 := runs_dec .Bt .T (by decide) σ2 c r (by simp [hσ2, Regs.set, Regs.get, fuelSt, hcr])
    (by simp [hσ2, Regs.set, Regs.get, fuelSt, Regs.empty])
  have hres : σ2.set .Bt (enc (decL (List.replicate c false ++ true :: r))) = fuelSt m n bs (j + 1) := by
    rw [← hcr, decL_bits]
    have h1 : n - j - 1 = n - (j + 1) := by omega
    simp only [hσ2, Regs.set, Regs.get, fuelSt, List.tail_drop, List.replicate_succ, h1]
  refine ((e1.seq (e2.seq e3)).congr hres).mono ?_
  have : c ≤ (Nat.bits n).length := by
    have h1 : c ≤ (Nat.bits (n - j)).length := by rw [hcr]; simp
    exact le_trans h1 (len_bits_mono (by omega))
  omega

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

lemma enc_bits_ne_nil {k : ℕ} (hk : k ≠ 0) : enc (Nat.bits k) ≠ [] := by
  intro h
  have : Nat.bits k = [] := by simpa [enc] using h
  exact hk ((bits_eq_nil_iff' k).1 this)

lemma isSome_head_of_ne_nil {l : List BSym} (h : l ≠ []) : l.head?.isSome = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

lemma runs_fuelLoop (n : ℕ) (bs : List Bool) :
    Runs fuelLoop (fuelSt m n bs 0) (fuelSt m n bs (min n bs.length))
      (min n bs.length * (6 * (Nat.bits n).length + 22) + 1) := by
  refine Runs.loopU _ fuelBody (fuelSt m n bs) _ _ (fun j hj => ⟨?_, fuel_step m n bs j ?_ ?_⟩) ?_
  · have h1 : (fuelSt m n bs j).Bt ≠ [] := enc_bits_ne_nil (by omega)
    have h2 : (fuelSt m n bs j).F ≠ [] := by
      simp only [fuelSt]; intro h; rw [List.drop_eq_nil_iff] at h; simp at h; omega
    simp only [hd, Regs.get, isSome_head_of_ne_nil h1, isSome_head_of_ne_nil h2, Bool.and_true]
  · omega
  · omega
  · by_cases h : n ≤ bs.length
    · rw [min_eq_left h]; simp [hd, Regs.get, fuelSt, enc]
    · rw [min_eq_right (by omega)]; simp [hd, Regs.get, fuelSt]

lemma runs_P6 (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hL2 : (Nat.bits n).length ≤ L) :
    ∃ τ, Runs pP6 (st4 m n bs) τ (60 * (L + 1) ^ 2) ∧
      (n ≤ bs.length → τ = st6 m n bs) ∧ (bs.length < n → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_copy .M .F .sc (by decide) (by decide) (by decide) (st4 m n bs) rfl
  have e2 := runs_copy .Bn .Bt .sc (by decide) (by decide) (by decide)
    ((st4 m n bs).set .F ((st4 m n bs).get .M ++ (st4 m n bs).get .F)) rfl
  have h0 : ((st4 m n bs).set .F ((st4 m n bs).get .M ++ (st4 m n bs).get .F)).set .Bt
      (((st4 m n bs).set .F ((st4 m n bs).get .M ++ (st4 m n bs).get .F)).get .Bn ++
        ((st4 m n bs).set .F ((st4 m n bs).get .M ++ (st4 m n bs).get .F)).get .Bt) = fuelSt m n bs 0 := by
    simp [st4, fuelSt, Regs.set, Regs.get, Regs.empty]
  have e12 := (e1.seq e2).congr h0
  have e3 := runs_fuelLoop m n bs
  have hb1 : (6 * ((st4 m n bs).get .M).length + 3) = 6 * bs.length + 3 := by simp [st4, Regs.get]
  have hb2 : (6 * (((st4 m n bs).set .F ((st4 m n bs).get .M ++ (st4 m n bs).get .F)).get .Bn).length + 3) =
      6 * (Nat.bits n).length + 3 := by simp [st4, Regs.get, Regs.set]
  rw [hb1, hb2] at e12
  have hm : min n bs.length * (6 * (Nat.bits n).length + 22) ≤ L * (6 * L + 22) :=
    Nat.mul_le_mul (le_trans (min_le_right _ _) hL1) (by omega)
  by_cases h : n ≤ bs.length
  · have hmin : min n bs.length = n := min_eq_left h
    have hBt : (fuelSt m n bs (min n bs.length)).Bt = [] := by rw [hmin]; simp [fuelSt, enc]
    have e4 : Runs btCheck (fuelSt m n bs (min n bs.length)) (fuelSt m n bs (min n bs.length)) 2 :=
      (runs_skip _).brF (by simp [hd, Regs.get, hBt])
    have e5 := runs_clear .F (fuelSt m n bs (min n bs.length))
    have hfin : (fuelSt m n bs (min n bs.length)).set .F [] = st6 m n bs := by
      simp [fuelSt, st6, Regs.set, hmin, enc, Regs.empty]
    refine ⟨_, ((e12.seq (e3.seq (e4.seq e5))).congr hfin).mono ?_, fun _ => rfl, fun h' => by omega⟩
    have hF : ((fuelSt m n bs (min n bs.length)).get .F).length ≤ L := by
      simp [fuelSt, Regs.get]; omega
    nlinarith
  · have hmin : min n bs.length = bs.length := min_eq_right (by omega)
    have hne : (fuelSt m n bs (min n bs.length)).Bt ≠ [] := enc_bits_ne_nil (by omega)
    have e4 : Runs btCheck (fuelSt m n bs (min n bs.length))
        ((fuelSt m n bs (min n bs.length)).set .bad (.one :: (fuelSt m n bs (min n bs.length)).get .bad)) 2 :=
      (runs_push .bad .one _).brT (by simp only [hd, Regs.get]; exact isSome_head_of_ne_nil hne)
    have e5 := runs_clear .F
      ((fuelSt m n bs (min n bs.length)).set .bad (.one :: (fuelSt m n bs (min n bs.length)).get .bad))
    refine ⟨_, (e12.seq (e3.seq (e4.seq e5))).mono ?_, fun h' => absurd h' h, fun _ => ?_⟩
    · have hF : (((fuelSt m n bs (min n bs.length)).set .bad
          (.one :: (fuelSt m n bs (min n bs.length)).get .bad)).get .F).length ≤ L := by
        simp [fuelSt, Regs.get, Regs.set]; omega
      nlinarith
    · simp [Regs.set, Regs.get, fuelSt, Regs.empty]

/-! ## Phase 7: the number of entries is `n * n` -/

def zxCheck : Prog := .branch (fun h => (h .Z).isSome || (h .X).isSome) (pushProg .bad .one) skipP

def pP7a : Prog :=
  .seq (copyProg .N .R .sc)
    (.seq (repProg .N .Z .R .sc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (.seq (copyProg .M .X .sc) (syncPopProg .Z .X)))

def pP7 : Prog := .seq pP7a (.seq zxCheck (.seq (clearProg .Z) (clearProg .X)))

def st7a (m : List BSym) (n : ℕ) (bs : List Bool) : Regs :=
  { st6 m n bs with
    Z := (List.replicate (n * n) BSym.one).drop (min (n * n) bs.length)
    X := (enc bs).drop (min (n * n) bs.length) }

lemma flatten_rep_rep (n : ℕ) (x : BSym) :
    (List.replicate n (List.replicate n x)).flatten = List.replicate (n * n) x := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [List.length_flatten, List.sum_replicate, Nat.mul_comm], ?_⟩
  intro b hb
  rw [List.mem_flatten] at hb
  obtain ⟨l, hl, hb⟩ := hb
  rw [List.mem_replicate] at hl
  rw [hl.2] at hb
  exact (List.mem_replicate.1 hb).2

lemma runs_P7a (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hn : n ≤ bs.length) :
    Runs pP7a (st6 m n bs) (st7a m n bs) (30 * (L + 1) ^ 2) := by
  have e1 := runs_copy .N .R .sc (by decide) (by decide) (by decide) (st6 m n bs) rfl
  set σ1 := (st6 m n bs).set .R ((st6 m n bs).get .N ++ (st6 m n bs).get .R) with hσ1
  have e2 := runs_rep .N .Z .R .sc (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ1 rfl
  set σ2 := (σ1.set .R []).set .Z ((List.replicate (σ1.get .R).length (σ1.get .N)).flatten ++ σ1.get .Z)
    with hσ2
  have e3 := runs_copy .M .X .sc (by decide) (by decide) (by decide) σ2 rfl
  set σ3 := σ2.set .X (σ2.get .M ++ σ2.get .X) with hσ3
  have e4 := runs_syncpop .Z .X (by decide) σ3
  have h3Z : σ3.get .Z = List.replicate (n * n) BSym.one := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, Regs.empty, flatten_rep_rep]
  have h3X : σ3.get .X = enc bs := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, Regs.empty]
  rw [h3Z, h3X] at e4
  have hfin : (σ3.set .Z ((List.replicate (n * n) BSym.one).drop
      (min (List.replicate (n * n) BSym.one).length (enc bs).length))).set .X
      ((enc bs).drop (min (List.replicate (n * n) BSym.one).length (enc bs).length)) = st7a m n bs := by
    simp [hσ3, hσ2, hσ1, Regs.set, Regs.get, st6, st7a, Regs.empty]
  refine ((e1.seq (e2.seq (e3.seq e4))).congr hfin).mono ?_
  have l1 : ((st6 m n bs).get .N).length = n := by simp [st6, Regs.get]
  have l2 : (σ1.get .N).length = n := by simp [hσ1, st6, Regs.get, Regs.set]
  have l3 : (σ1.get .R).length = n := by simp [hσ1, st6, Regs.get, Regs.set, Regs.empty]
  have l4 : (σ2.get .M).length = bs.length := by simp [hσ2, hσ1, st6, Regs.get, Regs.set]
  rw [l1, l2, l3, l4]
  simp only [List.length_replicate, length_enc]
  have : min (n * n) bs.length ≤ L := le_trans (min_le_right _ _) hL1
  nlinarith

lemma runs_P7 (n : ℕ) (bs : List Bool) (L : ℕ) (hL1 : bs.length ≤ L) (hn : n ≤ bs.length) :
    ∃ τ, Runs pP7 (st6 m n bs) τ (60 * (L + 1) ^ 2) ∧
      (n * n = bs.length → τ = st6 m n bs) ∧ (n * n ≠ bs.length → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_P7a m n bs L hL1 hn
  by_cases h : n * n = bs.length
  · have hZ : (st7a m n bs).Z = [] := by simp [st7a, h]
    have hX : (st7a m n bs).X = [] := by simp [st7a, h]
    have e2 : Runs zxCheck (st7a m n bs) (st7a m n bs) 2 :=
      (runs_skip _).brF (by simp [hd, Regs.get, hZ, hX])
    have e3 := runs_clear .Z (st7a m n bs)
    have e4 := runs_clear .X ((st7a m n bs).set .Z [])
    have hfin : ((st7a m n bs).set .Z []).set .X [] = st6 m n bs := by
      simp [st7a, st6, Regs.set, Regs.empty, h]
    refine ⟨_, ((e1.seq (e2.seq (e3.seq e4))).congr hfin).mono ?_, fun _ => rfl, fun h' => absurd h h'⟩
    simp [Regs.get, Regs.set, hZ, hX]; nlinarith
  · have hne : (st7a m n bs).Z ≠ [] ∨ (st7a m n bs).X ≠ [] := by
      by_cases hle : n * n ≤ bs.length
      · right; simp [st7a, min_eq_left hle]; omega
      · left; simp [st7a, min_eq_right (show bs.length ≤ n * n by omega)]; omega
    have e2 : Runs zxCheck (st7a m n bs) ((st7a m n bs).set .bad (.one :: (st7a m n bs).get .bad)) 2 := by
      refine (runs_push .bad .one _).brT ?_
      rcases hne with h1 | h1
      · simp only [hd, Regs.get, isSome_head_of_ne_nil h1, Bool.true_or]
      · simp only [hd, Regs.get, isSome_head_of_ne_nil h1, Bool.or_true]
    set σ2 := (st7a m n bs).set .bad (.one :: (st7a m n bs).get .bad) with hσ2
    have e3 := runs_clear .Z σ2
    have e4 := runs_clear .X (σ2.set .Z [])
    refine ⟨_, (e1.seq (e2.seq (e3.seq e4))).mono ?_, fun h' => absurd h' h, fun _ => ?_⟩
    · have hZl : (σ2.get .Z).length ≤ n * n := by simp [hσ2, Regs.get, Regs.set, st7a]
      have hXl : ((σ2.set .Z []).get .X).length ≤ bs.length := by
        simp [hσ2, Regs.get, Regs.set, st7a]
      have : n * n ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · simp [hσ2, Regs.set, Regs.get, st7a, st6, Regs.empty]

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

/-! ## the input format: `n` in binary, then the `n * n` entries -/

def code (n : ℕ) (bs : List Bool) : List BSym := enc (Nat.bits n) ++ BSym.sep :: bs.flatMap tokB

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval l)

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

def fromB (x : BSym) : Bool := decide (x = .one)

lemma enc_fromB (l : List BSym) (h : ∀ x ∈ l, isDigB x = true) : enc (l.map fromB) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, enc_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have := h x (List.mem_cons_self)
    cases x <;> simp_all [isDigB, fromB, toB]

lemma map_fromB_enc (l : List Bool) : (enc l).map fromB = l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp_all [fromB, toB]

lemma isDigB_enc (l : List Bool) : ∀ x ∈ enc l, isDigB x = true := by
  intro x hx
  simp only [enc, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  cases b <;> rfl

lemma digs_code (l : List Bool) (r : List BSym) : digs (enc l ++ BSym.sep :: r) = enc l := by
  unfold digs
  rw [List.takeWhile_append_of_pos (isDigB_enc l)]
  simp [List.takeWhile, isDigB]

lemma rest_code (l : List Bool) (r : List BSym) : rest (enc l ++ BSym.sep :: r) = BSym.sep :: r := by
  unfold rest
  rw [List.dropWhile_append_of_pos (isDigB_enc l)]
  simp [List.dropWhile, isDigB]

lemma numOK_code (n : ℕ) (bs : List Bool) : numOK (code n bs) := by
  unfold numOK code
  rw [rest_code, digs_code]
  refine ⟨rfl, ?_⟩
  have := bits_getLast n
  rw [enc, List.getLast?_map]
  intro h
  cases hh : (Nat.bits n).getLast? with
  | none => rw [hh] at h; cases h
  | some b =>
    rw [hh] at h; simp at h
    cases b
    · exact this hh
    · simp [toB] at h

/-- the value read from the digits -/
def nval (w : List BSym) : ℕ := bval ((digs w).map fromB)

lemma digs_eq (w : List BSym) (h : numOK w) : digs w = enc (Nat.bits (nval w)) := by
  have hdig : ∀ x ∈ digs w, isDigB x = true := fun x hx => List.mem_takeWhile_imp hx
  have hl : ((digs w).map fromB).getLast? ≠ some false := by
    rw [List.getLast?_map]
    intro hc
    apply h.2
    cases hh : (digs w).getLast? with
    | none => rw [hh] at hc; cases hc
    | some x =>
      rw [hh] at hc
      have hx := hdig x (List.mem_of_getLast? hh)
      cases x <;> simp_all [fromB, isDigB]
  unfold nval
  rw [bits_bval _ hl, enc_fromB _ hdig]

lemma w_eq (w : List BSym) (h : numOK w) (bs : List Bool) (hb : tokP false (rest w).tail = some bs) :
    w = code (nval w) bs := by
  have h1 := List.takeWhile_append_dropWhile (p := isDigB) (l := w)
  have h2 := tokP_some _ false bs hb
  simp only [Bool.false_eq_true, if_false] at h2
  have h3 : rest w = BSym.sep :: (rest w).tail := by
    have := h.1
    cases hr : rest w with
    | nil => rw [hr] at this; cases this
    | cons a l => rw [hr] at this; simp at this; subst this; rfl
  unfold code
  rw [← digs_eq w h, ← h2, ← h3]
  exact h1.symm

lemma code_unique (w : List BSym) (bs : List Bool) (hb : tokP false (rest w).tail = some bs)
    (n' : ℕ) (bs' : List Bool) (hw : w = code n' bs') : n' = nval w ∧ bs' = bs := by
  subst hw
  constructor
  · unfold nval code; rw [digs_code, map_fromB_enc, bval_bits]
  · unfold code at hb; rw [rest_code] at hb; simp only [List.tail_cons] at hb
    rw [tokP_flat] at hb; exact Option.some.inj hb

/-! ## the parsing program -/

def parseProg : Prog :=
  .seq (.seq pP1 (.seq pP2 pP3)) (.seq (gate pP4) (.seq (gate pP6) (gate pP7)))

lemma digs_len (w : List BSym) : (digs w).length ≤ w.length :=
  (List.takeWhile_sublist _).length_le

lemma rest_len (w : List BSym) : (rest w).length ≤ w.length :=
  (List.dropWhile_sublist _).length_le

theorem parse_spec (w : List BSym) :
    ∃ τ, Runs parseProg (initM m w) τ (300 * (w.length + 1) ^ 2) ∧
      ((∃ n bs, bs.length = n * n ∧ w = code n bs ∧ τ = st6 m n bs) ∨
        (τ.bad ≠ [] ∧ τ.out = [] ∧ ∀ n bs, bs.length = n * n → w ≠ code n bs)) := by
  obtain ⟨τ1, e1, hok, hnok⟩ := runs_P123 m w
  set L := w.length with hL
  have hsq : 0 ≤ (L + 1) ^ 2 := Nat.zero_le _
  have hLsq : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  by_cases hw : numOK w
  · have hτ1 := hok hw
    subst hτ1
    obtain ⟨τ4, e4, hs4, hn4⟩ := runs_P4 (st3 m w) rfl rfl rfl rfl
    have e4' := runs_gate_ok (p := pP4) rfl e4
    have hinpL : (st3 m w).inp.length ≤ L := by
      simp only [st3]; have := rest_len w; simp; omega
    cases htok : tokP false (st3 m w).inp with
    | none =>
      obtain ⟨hb4, ho4⟩ := hn4 htok
      refine ⟨τ4, (e1.seq (e4'.seq ((runs_gate_skip hb4).seq (runs_gate_skip hb4)))).mono ?_,
        Or.inr ⟨hb4, by rw [ho4]; rfl, ?_⟩⟩
      · nlinarith
      · intro n bs _ hcode
        have : tokP false (rest w).tail = some bs := by
          rw [hcode]; unfold code; rw [rest_code]; exact tokP_flat bs
        simp only [st3] at htok
        rw [this] at htok; cases htok
    | some bs =>
      have hτ4 := hs4 bs htok
      have hst4 : τ4 = st4 m (nval w) bs := by
        rw [hτ4]; unfold st4; rw [← digs_eq w hw]; rfl
      have hbsL : bs.length ≤ L := le_trans (tokP_len _ _ htok) hinpL
      have hnL : (Nat.bits (nval w)).length ≤ L := by
        have := digs_len w; rw [digs_eq w hw] at this; simpa using this
      obtain ⟨τ6, e6, h6a, h6b⟩ := runs_P6 m (nval w) bs L hbsL hnL
      rw [← hst4] at e6
      have e6' := runs_gate_ok (p := pP6) (by rw [hτ4]; rfl) e6
      have htok' : tokP false (rest w).tail = some bs := htok
      by_cases hle : nval w ≤ bs.length
      · have hτ6 := h6a hle
        subst hτ6
        obtain ⟨τ7, e7, h7a, h7b⟩ := runs_P7 m (nval w) bs L hbsL hle
        have e7' := runs_gate_ok (p := pP7) rfl e7
        by_cases hsq' : nval w * nval w = bs.length
        · have hτ7 := h7a hsq'
          subst hτ7
          refine ⟨st6 m (nval w) bs, (e1.seq (e4'.seq (e6'.seq e7'))).mono ?_,
            Or.inl ⟨nval w, bs, hsq'.symm, w_eq w hw bs htok', rfl⟩⟩
          nlinarith
        · obtain ⟨hb7, ho7⟩ := h7b hsq'
          refine ⟨τ7, (e1.seq (e4'.seq (e6'.seq e7'))).mono ?_, Or.inr ⟨hb7, ho7, ?_⟩⟩
          · nlinarith
          · intro n' bs' hl hcode
            obtain ⟨h1, h2⟩ := code_unique w bs htok' n' bs' hcode
            rw [h1, h2] at hl; exact hsq' hl.symm
      · obtain ⟨hb6, ho6⟩ := h6b (by omega)
        refine ⟨τ6, (e1.seq (e4'.seq (e6'.seq (runs_gate_skip hb6)))).mono ?_,
          Or.inr ⟨hb6, ho6, ?_⟩⟩
        · nlinarith
        · intro n' bs' hl hcode
          obtain ⟨h1, h2⟩ := code_unique w bs htok' n' bs' hcode
          rw [h1, h2] at hl
          have : nval w ≤ nval w * nval w := Nat.le_mul_self _
          omega
  · obtain ⟨hb, ho⟩ := hnok hw
    refine ⟨τ1, (e1.seq ((runs_gate_skip hb).seq ((runs_gate_skip hb).seq (runs_gate_skip hb)))).mono ?_,
      Or.inr ⟨hb, ho, ?_⟩⟩
    · nlinarith
    · intro n bs _ hcode
      exact hw (hcode ▸ numOK_code n bs)

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

variable (m : List BSym)

/-! ## emitting a list of numbers -/

/-- an emitted item: the counter held by a register, or a constant `0`/`1` -/
abbrev Item := Key ⊕ Bool

def emitItem : Item → Prog
  | .inl k => emitProg k
  | .inr false => pushProg .W .sep
  | .inr true => .seq (pushProg .W .one) (pushProg .W .sep)

def emitSeq : List Item → Prog
  | [] => skipP
  | x :: xs => .seq (emitItem x) (emitSeq xs)

def itemVal (ν : Key → ℕ) : Item → ℕ
  | .inl k => ν k
  | .inr b => if b then 1 else 0

def itemOK (σ : Regs) (ν : Key → ℕ) : Item → Prop
  | .inl k => k ≠ .T ∧ k ≠ .sc ∧ k ≠ .W ∧ σ.get k = enc (Nat.bits (ν k))
  | .inr _ => True

lemma encNats_cons' (k : ℕ) (l : List ℕ) : encNats (k :: l) = encNat k ++ encNats l := by
  simp [encNats]

lemma encNats_append' (l l' : List ℕ) : encNats (l ++ l') = encNats l ++ encNats l' := by
  simp [encNats]

lemma encNat_eq' (k : ℕ) : encNat k = enc (Nat.bits k) ++ [BSym.sep] := by
  simp [encNat, enc, toB]

lemma runs_emitSeq (ν : Key → ℕ) (K : ℕ) (hK : ∀ k, (Nat.bits (ν k)).length ≤ K) :
    ∀ (items : List Item) (σ : Regs), σ.T = [] → σ.sc = [] → (∀ x ∈ items, itemOK σ ν x) →
      Runs (emitSeq items) σ { σ with W := (encNats (items.map (itemVal ν))).reverse ++ σ.W }
        (items.length * (9 * K + 10) + 1) := by
  intro items
  induction items with
  | nil =>
    intro σ _ _ _
    simp only [emitSeq, List.map_nil, List.length_nil, zero_mul, zero_add]
    exact (runs_skip σ).congr rfl
  | cons x xs ih =>
    intro σ hT hsc hok
    have hx := hok x List.mem_cons_self
    obtain ⟨σ1, e1, hσ1, hb⟩ : ∃ σ1, Runs (emitItem x) σ σ1 (9 * K + 8) ∧
        σ1 = { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } ∧ True := by
      rcases x with k | b
      · obtain ⟨h1, h2, h3, h4⟩ := hx
        refine ⟨_, (runs_emit k h1 h2 h3 σ hT hsc).mono ?_, ?_, trivial⟩
        · rw [h4]; simp only [length_enc]; have := hK k; omega
        · simp [itemVal, encNat_eq', h4]
      · cases b
        · exact ⟨_, (runs_push .W .sep σ).mono (by omega), by simp [Regs.set, Regs.get, itemVal, encNat], trivial⟩
        · refine ⟨_, ((runs_push .W .one σ).seq (runs_push .W .sep _)).mono (by omega), ?_, trivial⟩
          simp [Regs.set, Regs.get, itemVal, encNat]
    subst hσ1
    have hok' : ∀ y ∈ xs, itemOK { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } ν y := by
      intro y hy
      have := hok y (List.mem_cons_of_mem _ hy)
      rcases y with k | b
      · obtain ⟨h1, h2, h3, h4⟩ := this
        refine ⟨h1, h2, h3, ?_⟩
        rw [← h4]; cases k <;> first | exact absurd rfl h3 | rfl
      · trivial
    have e2 := ih { σ with W := (encNat (itemVal ν x)).reverse ++ σ.W } hT hsc hok'
    simp only [emitSeq]
    refine ((e1.seq e2).congr ?_).mono ?_
    · simp [encNats_cons']
    · simp; nlinarith


lemma len_bits_le_of_le {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ b :=
  le_trans (len_bits_mono h) (len_bits_le b)


def adjB (bs : List Bool) (n s t : ℕ) : Bool := bs.getD (s * n + t) false

lemma enc_bits_double (n : ℕ) :
    enc (Nat.bits (2 * n)) = if n = 0 then [] else BSym.zero :: enc (Nat.bits n) := by
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h, bits_double n h]; rfl


lemma drop_eq_cons_getD (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    bs.drop k = bs.getD k false :: bs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]


lemma code_inj {n n' : ℕ} {bs bs' : List Bool} (h : code n bs = code n' bs') : n = n' ∧ bs = bs' := by
  have hb : tokP false (rest (code n bs)).tail = some bs := by
    unfold code; rw [rest_code]; exact tokP_flat bs
  obtain ⟨h1, h2⟩ := code_unique (code n bs) bs hb n' bs' h
  obtain ⟨h3, _⟩ := code_unique (code n bs) bs hb n bs rfl
  exact ⟨h3.trans h1.symm, h2.symm⟩

lemma length_code (n : ℕ) (bs : List Bool) : bs.length ≤ (code n bs).length := by
  unfold code
  have := length_flat_tokB bs
  simp only [List.length_append, List.length_cons]; omega


lemma n_le_of_sq {n m : ℕ} (h : m = n * n) : n ≤ m := by
  subst h; rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Nat.le_mul_of_pos_left n h


/-! ## the symmetry check -/

/-- some entry before position `k` (row-major) differs from its transpose -/
def symBad (bs : List Bool) (n k : ℕ) : Prop :=
  ∃ i < k, adjB bs n (i / n) (i % n) ≠ adjB bs n (i % n) (i / n)

instance (bs : List Bool) (n k : ℕ) : Decidable (symBad bs n k) := by
  unfold symBad; infer_instance

def flagL (bs : List Bool) (n k : ℕ) : List BSym := if symBad bs n k then [.one] else []

lemma symBad_succ (bs : List Bool) (n k : ℕ) :
    symBad bs n (k + 1) ↔ symBad bs n k ∨ adjB bs n (k / n) (k % n) ≠ adjB bs n (k % n) (k / n) := by
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hik : i < k
    · exact Or.inl ⟨i, hik, h⟩
    · have : i = k := by omega
      subst this; exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, by omega, h⟩
    · exact ⟨k, by omega, h⟩

def lookT : Prog := .seq (copyProg .M .T .sc) (.seq (copyProg .P .X .sc) (syncPopProg .T .X))
def lookT2 : Prog := .seq (copyProg .M .T2 .sc) (.seq (copyProg .Q .Y .sc) (syncPopProg .T2 .Y))
def cmpP : Prog :=
  .branch (fun h => decide (h .T ≠ h .T2) && (h .bad).isNone) (pushProg .bad .one) skipP

def symColBody : Prog :=
  .seq (popProg .C) (.seq lookT (.seq lookT2 (.seq cmpP (.seq (clearProg .T)
    (.seq (clearProg .T2) (.seq (pushProg .P .one) (copyProg .N .Q .sc)))))))

def symColLoop : Prog := .loop (fun h => (h .C).isSome) symColBody

def symRowBody : Prog :=
  .seq (popProg .R) (.seq (copyProg .Us .Q .sc) (.seq (copyProg .N .C .sc)
    (.seq symColLoop (.seq (clearProg .Q) (pushProg .Us .one)))))

def symRowLoop : Prog := .loop (fun h => (h .R).isSome) symRowBody

def symAll : Prog := .seq (copyProg .N .R .sc) (.seq symRowLoop (.seq (clearProg .Us) (clearProg .P)))

def symSt (m : List BSym) (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 m n bs with
    R := List.replicate (n - (s + 1)) .one
    Us := List.replicate s .one
    P := List.replicate (s * n + t) .one
    Q := List.replicate (t * n + s) .one
    C := List.replicate (n - t) .one
    bad := flagL bs n (s * n + t) }

def symRow (m : List BSym) (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 m n bs with
    R := List.replicate (n - s) .one
    Us := List.replicate s .one
    P := List.replicate (s * n) .one
    bad := flagL bs n (s * n) }

lemma head_drop_enc (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    ((enc bs).drop k).head? = some (toB (bs.getD k false)) := by
  rw [show (enc bs).drop k = enc (bs.drop k) by simp [enc, List.map_drop], drop_eq_cons_getD bs k hk]
  rfl

lemma runs_lookT (σ : Regs) (hT : σ.T = []) (hX : σ.X = []) (hsc : σ.sc = [])
    (hk : σ.P.length ≤ σ.M.length) :
    Runs lookT σ { σ with T := σ.M.drop σ.P.length } (6 * σ.M.length + 9 * σ.P.length + 10) := by
  have e1 := runs_copy .M .T .sc (by decide) (by decide) (by decide) σ hsc
  have e2 := runs_copy .P .X .sc (by decide) (by decide) (by decide) (σ.set .T (σ.get .M ++ σ.get .T)) hsc
  have e3 := runs_syncpop .T .X (by decide)
    ((σ.set .T (σ.get .M ++ σ.get .T)).set .X ((σ.set .T (σ.get .M ++ σ.get .T)).get .P ++
      (σ.set .T (σ.get .M ++ σ.get .T)).get .X))
  have hm : min σ.M.length σ.P.length = σ.P.length := min_eq_right hk
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [Regs.set, Regs.get, hT, hX, hm]
  · simp only [Regs.set, Regs.get, hT, hX, List.append_nil]; omega

lemma runs_lookT2 (σ : Regs) (hT : σ.T2 = []) (hY : σ.Y = []) (hsc : σ.sc = [])
    (hk : σ.Q.length ≤ σ.M.length) :
    Runs lookT2 σ { σ with T2 := σ.M.drop σ.Q.length } (6 * σ.M.length + 9 * σ.Q.length + 10) := by
  have e1 := runs_copy .M .T2 .sc (by decide) (by decide) (by decide) σ hsc
  have e2 := runs_copy .Q .Y .sc (by decide) (by decide) (by decide) (σ.set .T2 (σ.get .M ++ σ.get .T2)) hsc
  have e3 := runs_syncpop .T2 .Y (by decide)
    ((σ.set .T2 (σ.get .M ++ σ.get .T2)).set .Y ((σ.set .T2 (σ.get .M ++ σ.get .T2)).get .Q ++
      (σ.set .T2 (σ.get .M ++ σ.get .T2)).get .Y))
  have hm : min σ.M.length σ.Q.length = σ.Q.length := min_eq_right hk
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [Regs.set, Regs.get, hT, hY, hm]
  · simp only [Regs.set, Regs.get, hT, hY, List.append_nil]; omega

lemma runs_cmpP (σ : Regs) (bs : List Bool) (n k : ℕ) (hb : σ.bad = flagL bs n k)
    (h1 : σ.T.head? = some (toB (adjB bs n (k / n) (k % n))))
    (h2 : σ.T2.head? = some (toB (adjB bs n (k % n) (k / n)))) :
    Runs cmpP σ { σ with bad := flagL bs n (k + 1) } 2 := by
  by_cases hk : symBad bs n k
  · have hk' : symBad bs n (k + 1) := (symBad_succ bs n k).2 (Or.inl hk)
    have hb' : σ.bad = [.one] := by rw [hb, flagL, if_pos hk]
    refine ((runs_skip σ).brF ?_).congr ?_
    · simp [hd, Regs.get, hb']
    · rw [flagL, if_pos hk', ← hb']
  · have hb' : σ.bad = [] := by rw [hb, flagL, if_neg hk]
    by_cases hm : adjB bs n (k / n) (k % n) ≠ adjB bs n (k % n) (k / n)
    · have hk' : symBad bs n (k + 1) := (symBad_succ bs n k).2 (Or.inr hm)
      refine ((runs_push .bad .one σ).brT ?_).congr ?_
      · simp only [hd, Regs.get, h1, h2, hb']
        have : toB (adjB bs n (k / n) (k % n)) ≠ toB (adjB bs n (k % n) (k / n)) := by
          revert hm; cases adjB bs n (k / n) (k % n) <;> cases adjB bs n (k % n) (k / n) <;> simp [toB]
        simp [this]
      · rw [flagL, if_pos hk']; simp [Regs.set, Regs.get, hb']
    · have hk' : ¬ symBad bs n (k + 1) := by
        rw [symBad_succ]; push Not; exact ⟨hk, by simpa using hm⟩
      refine ((runs_skip σ).brF ?_).congr ?_
      · simp only [hd, Regs.get, h1, h2, hb']
        have : adjB bs n (k / n) (k % n) = adjB bs n (k % n) (k / n) := by simpa using hm
        simp [this]
      · rw [flagL, if_neg hk', ← hb']









lemma div_mod_aux (n s t : ℕ) (ht : t < n) : (s * n + t) / n = s ∧ (s * n + t) % n = t := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma stepSym (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs symColBody (symSt m n bs s t) (symSt m n bs s (t + 1)) (100 * (n * n + n + 1)) := by
  have hk : s * n + t < n * n := by nlinarith
  have hk' : t * n + s < n * n := by nlinarith
  obtain ⟨hd1, hm1⟩ := div_mod_aux n s t ht
  have e1 := runs_pop .C (symSt m n bs s t)
  set σ1 := (symSt m n bs s t).set .C ((symSt m n bs s t).get .C).tail with hσ1
  have e2 := runs_lookT σ1 (by simp [hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ1, symSt, st6, Regs.set, Regs.empty]) (by simp [hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ1, symSt, st6, Regs.set, hbs]; omega)
  set σ2 := { σ1 with T := σ1.M.drop σ1.P.length } with hσ2
  have e3 := runs_lookT2 σ2 (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, Regs.empty])
    (by simp [hσ2, hσ1, symSt, st6, Regs.set, hbs]; omega)
  set σ3 := { σ2 with T2 := σ2.M.drop σ2.Q.length } with hσ3
  have e4 := runs_cmpP σ3 bs n (s * n + t) (by simp [hσ3, hσ2, hσ1, symSt, Regs.set])
    (by
      simp only [hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, List.length_replicate, hd1, hm1]
      rw [head_drop_enc bs _ (by omega)]; rfl)
    (by
      simp only [hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, List.length_replicate, hd1, hm1]
      rw [head_drop_enc bs _ (by omega)]; rfl)
  set σ4 := { σ3 with bad := flagL bs n (s * n + t + 1) } with hσ4
  have e5 := runs_clear .T σ4
  have e6 := runs_clear .T2 (σ4.set .T [])
  have e7 := runs_push .P .one ((σ4.set .T []).set .T2 [])
  set σ7 := ((σ4.set .T []).set .T2 []).set .P (.one :: ((σ4.set .T []).set .T2 []).get .P) with hσ7
  have e8 := runs_copy .N .Q .sc (by decide) (by decide) (by decide) σ7
    (by simp [hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty])
  refine ((e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).congr ?_).mono ?_
  · have hC : n - t - 1 = n - (t + 1) := by omega
    have hQ : n + (t * n + s) = (t + 1) * n + s := by ring
    have hP : List.replicate (s * n + (t + 1)) BSym.one = BSym.one :: List.replicate (s * n + t) BSym.one := by
      rw [← Nat.add_assoc, List.replicate_succ]
    simp [hP, hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate,
      hC, List.replicate_append_replicate, hQ, List.replicate_succ, Nat.add_assoc]
  · simp only [hσ7, hσ4, hσ3, hσ2, hσ1, symSt, st6, Regs.set, Regs.get, Regs.empty,
      List.length_replicate, List.length_drop, length_enc, hbs, List.length_tail]
    have h1 := hk; have h2 := hk'
    generalize s * n = a at *; generalize t * n = b at *; generalize n * n = c at *
    omega

lemma runs_symColLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs symColLoop (symSt m n bs s 0) (symSt m n bs s n) (n * (100 * (n * n + n + 1) + 2) + 1) := by
  refine Runs.loopU _ symColBody (symSt m n bs s) _ _ (fun j hj => ⟨?_, stepSym m n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, symSt, hk, List.replicate_succ]
  · simp [hd, Regs.get, symSt]

lemma stepSymRow (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs symRowBody (symRow m n bs s) (symRow m n bs (s + 1))
      (n * (100 * (n * n + n + 1) + 2) + 3 * n * n + 20 * n + 20) := by
  have e1 := runs_pop .R (symRow m n bs s)
  set σ1 := (symRow m n bs s).set .R ((symRow m n bs s).get .R).tail with hσ1
  have e2 := runs_copy .Us .Q .sc (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, symRow, st6, Regs.set, Regs.get, Regs.empty])
  set σ2 := σ1.set .Q (σ1.get .Us ++ σ1.get .Q) with hσ2
  have e3 := runs_copy .N .C .sc (by decide) (by decide) (by decide) σ2
    (by simp [hσ2, hσ1, symRow, st6, Regs.set, Regs.get, Regs.empty])
  have h0 : σ2.set .C (σ2.get .N ++ σ2.get .C) = symSt m n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [hσ2, hσ1, symRow, symSt, st6, Regs.set, Regs.get, Regs.empty, List.tail_replicate, hR]
  have e4 := runs_symColLoop m n bs hbs s hs
  have e5 := runs_clear .Q (symSt m n bs s n)
  have e6 := runs_push .Us .one ((symSt m n bs s n).set .Q [])
  refine ((e1.seq (e2.seq ((e3.congr h0).seq (e4.seq (e5.seq e6))))).congr ?_).mono ?_
  · have hP : s * n + n = (s + 1) * n := by ring
    simp [symRow, symSt, st6, Regs.set, Regs.get, Regs.empty, hP, List.replicate_succ]
  · simp only [hσ2, hσ1, symRow, symSt, st6, Regs.set, Regs.get, Regs.empty,
      List.length_replicate, List.length_tail, List.length_append, List.length_nil]
    have : s ≤ n := by omega
    nlinarith

lemma runs_symAll (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs symAll (st6 m n bs) { st6 m n bs with bad := flagL bs n (n * n) } (400 * (n + 1) ^ 4) := by
  have e1 := runs_copy .N .R .sc (by decide) (by decide) (by decide) (st6 m n bs) rfl
  have h0 : (st6 m n bs).set .R ((st6 m n bs).get .N ++ (st6 m n bs).get .R) = symRow m n bs 0 := by
    have : ¬ symBad bs n 0 := by rintro ⟨i, hi, _⟩; omega
    simp [symRow, st6, Regs.set, Regs.get, Regs.empty, flagL, this]
  have e2 : Runs symRowLoop (symRow m n bs 0) (symRow m n bs n)
      (n * (n * (100 * (n * n + n + 1) + 2) + 3 * n * n + 20 * n + 22) + 1) :=
    Runs.loopU _ symRowBody (symRow m n bs) _ _ (fun j hj => ⟨by
      obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
      simp [hd, Regs.get, symRow, hk, List.replicate_succ], stepSymRow m n bs hbs j hj⟩)
      (by simp [hd, Regs.get, symRow])
  have e3 := runs_clear .Us (symRow m n bs n)
  have e4 := runs_clear .P ((symRow m n bs n).set .Us [])
  refine (((e1.congr h0).seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · simp [symRow, st6, Regs.set, Regs.empty]
  · simp only [symRow, st6, Regs.set, Regs.get, Regs.empty, List.length_replicate]
    nlinarith [sq_nonneg (n + 1), pow_le_pow_left₀ (Nat.zero_le n) (Nat.le_succ n) 4]



end MCRed


set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## pushing constant blocks -/

def pushL (k : Key) : List BSym → Prog
  | [] => skipP
  | a :: l => .seq (pushProg k a) (pushL k l)

lemma runs_pushL (k : Key) : ∀ (l : List BSym) (σ : Regs),
    Runs (pushL k l) σ (σ.set k (l.reverse ++ σ.get k)) (2 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro σ
    simp only [pushL, List.reverse_nil, List.nil_append, Regs.set_get, List.length_nil]
    exact runs_skip σ
  | cons a l ih =>
    intro σ
    have e1 := runs_push k a σ
    have e2 := ih (σ.set k (a :: σ.get k))
    refine ((e1.seq e2).congr ?_).mono ?_
    · simp [Regs.set_set]
    · simp; omega

def constLoop (R W : Key) (l : List BSym) : Prog :=
  .loop (fun h => (h R).isSome) (.seq (popProg R) (pushL W l))

lemma runs_constLoop (R W : Key) (hRW : R ≠ W) (l : List BSym) : ∀ (c : ℕ) (σ : Regs),
    σ.get R = List.replicate c .one →
    Runs (constLoop R W l) σ ((σ.set R []).set W ((List.replicate c l).flatten.reverse ++ σ.get W))
      (c * (2 * l.length + 6) + 1) := by
  intro c
  induction c with
  | zero =>
    intro σ hR
    simp only [List.replicate_zero, List.flatten_nil, List.reverse_nil, List.nil_append, zero_mul,
      zero_add]
    have : (σ.set R []).set W (σ.get W) = σ := by
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [this]
    exact Runs.loopF (by simp [hd, hR])
  | succ c ih =>
    intro σ hR
    have e1 := runs_pop R σ
    set σ1 := σ.set R (σ.get R).tail with hσ1
    have e2 := runs_pushL W l σ1
    set σ2 := σ1.set W (l.reverse ++ σ1.get W) with hσ2
    have h2R : σ2.get R = List.replicate c .one := by
      rw [hσ2, Regs.get_set, if_neg hRW, hσ1, Regs.get_set_self, hR]; simp [List.replicate_succ]
    have e3 := ih σ2 h2R
    refine ((Runs.loopT (by simp [hd, hR, List.replicate_succ]) (e1.seq e2) e3).congr ?_).mono ?_
    · rw [hσ2, hσ1]
      apply Regs.ext_get; funext i; simp only [Regs.get_set]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all [List.replicate_succ]
    · simp only [Nat.succ_mul]; omega

/-! ## constant blocks of the output -/

/-- `encRat (11/4)` -/
def l114 : List BSym := [.one, .one, .zero, .one, .sep, .zero, .zero, .one, .sep]
/-- `encRat (1/4)` -/
def l14 : List BSym := [.one, .sep, .zero, .zero, .one, .sep]
/-- `encRat (4/7)` -/
def l47 : List BSym := [.zero, .zero, .one, .sep, .one, .one, .one, .sep]
/-- `encRat 0` -/
def l0 : List BSym := [.sep, .one, .sep]
/-- `encRat 8` -/
def l8 : List BSym := [.zero, .zero, .zero, .one, .sep, .one, .sep]
/-- `encRat 1` -/
def lk : List BSym := [.one, .sep, .one, .sep]

/-! ## the output, piece by piece -/

def rowCnt (bs : List Bool) (n s t : ℕ) : ℕ := ((List.range t).filter (fun t' => adjB bs n s t')).length

def P1 (n : ℕ) : List BSym := encNat (n + 1)
def P2 (n : ℕ) : List BSym := P1 n ++ l114 ++ (List.replicate n l14).flatten
def P3 (n : ℕ) : List BSym := P2 n ++ l47 ++ (List.replicate n l0).flatten
def degBlock (bs : List Bool) (n s : ℕ) : List BSym :=
  (List.range s).flatMap (fun s' => encNat (rowCnt bs n s' n) ++ [.one, .sep])
def P4 (n : ℕ) (bs : List Bool) (s : ℕ) : List BSym := P3 n ++ degBlock bs n s

def triEnt (bs : List Bool) (n s t : ℕ) : List BSym :=
  if s < t then (if adjB bs n s t then l8 else l0) else []
def triRow (bs : List Bool) (n s t : ℕ) : List BSym := (List.range t).flatMap (fun t' => triEnt bs n s t')
def triBlock (bs : List Bool) (n s : ℕ) : List BSym := (List.range s).flatMap (fun s' => triRow bs n s' n)
def P5 (n : ℕ) (bs : List Bool) (s t : ℕ) : List BSym := P4 n bs n ++ triBlock bs n s ++ triRow bs n s t

def P6 (n : ℕ) (bs : List Bool) (m : List BSym) : List BSym :=
  P5 n bs n 0 ++ (BSym.one :: m ++ [.sep, .one, .sep]) ++ lk

/-! ## phases 1–3 -/

variable (m : List BSym)

def gen1 : Prog :=
  .seq (copyProg .Bn .X .sc) (.seq (incProg .X .T) (.seq (emitProg .X) (clearProg .X)))

def gen2 : Prog :=
  .seq (pushL .W l114) (.seq (copyProg .N .R .sc) (constLoop .R .W l14))

def gen3 : Prog :=
  .seq (pushL .W l47) (.seq (copyProg .N .R .sc) (constLoop .R .W l0))

def gW (n : ℕ) (bs : List Bool) (l : List BSym) : Regs := { st6 m n bs with W := l.reverse }

lemma runs_gen1 (n : ℕ) (bs : List Bool) :
    Runs gen1 (st6 m n bs) (gW m n bs (P1 n)) (50 * n + 50) := by
  have e1 := runs_copy .Bn .X .sc (by decide) (by decide) (by decide) (st6 m n bs) rfl
  set σ1 := (st6 m n bs).set .X ((st6 m n bs).get .Bn ++ (st6 m n bs).get .X) with hσ1
  have e2 := runs_inc .X .T (by decide) σ1 (Nat.bits n) (by simp [hσ1, st6, Regs.set, Regs.get, Regs.empty])
    (by simp [hσ1, st6, Regs.set, Regs.get, Regs.empty])
  set σ2 := σ1.set .X (enc (incL (Nat.bits n))) with hσ2
  have e3 := runs_emit .X (by decide) (by decide) (by decide) σ2 (by simp [hσ2, hσ1, st6, Regs.set, Regs.get, Regs.empty])
    (by simp [hσ2, hσ1, st6, Regs.set, Regs.get, Regs.empty])
  have e4 := runs_clear .X { σ2 with W := BSym.sep :: (σ2.get .X).reverse ++ σ2.W }
  refine ((e1.seq (e2.seq (e3.seq e4))).congr ?_).mono ?_
  · rw [incL_bits] at hσ2
    simp [hσ2, hσ1, gW, st6, Regs.set, Regs.get, Regs.empty, P1, encNat_eq']
  · rw [incL_bits] at hσ2
    have h1 : (Nat.bits n).length ≤ n := len_bits_le n
    have h2 : (Nat.bits (n + 1)).length ≤ n + 1 := len_bits_le (n + 1)
    simp [hσ2, hσ1, st6, Regs.set, Regs.get, Regs.empty]
    omega

lemma runs_gen2 (n : ℕ) (bs : List Bool) :
    Runs gen2 (gW m n bs (P1 n)) (gW m n bs (P2 n)) (30 * n + 50) := by
  have e1 := runs_pushL .W l114 (gW m n bs (P1 n))
  set σ1 := (gW m n bs (P1 n)).set .W (l114.reverse ++ (gW m n bs (P1 n)).get .W) with hσ1
  have e2 := runs_copy .N .R .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .R (σ1.get .N ++ σ1.get .R) with hσ2
  have e3 := runs_constLoop .R .W (by decide) l14 n σ2 (by simp [hσ2, hσ1, gW, st6, Regs.set, Regs.get, Regs.empty])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [hσ2, hσ1, gW, st6, Regs.set, Regs.get, Regs.empty, P2]
  · simp [hσ1, gW, st6, Regs.set, Regs.get, l114, l14]; omega

lemma runs_gen3 (n : ℕ) (bs : List Bool) :
    Runs gen3 (gW m n bs (P2 n)) (gW m n bs (P3 n)) (30 * n + 50) := by
  have e1 := runs_pushL .W l47 (gW m n bs (P2 n))
  set σ1 := (gW m n bs (P2 n)).set .W (l47.reverse ++ (gW m n bs (P2 n)).get .W) with hσ1
  have e2 := runs_copy .N .R .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .R (σ1.get .N ++ σ1.get .R) with hσ2
  have e3 := runs_constLoop .R .W (by decide) l0 n σ2 (by simp [hσ2, hσ1, gW, st6, Regs.set, Regs.get, Regs.empty])
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · simp [hσ2, hσ1, gW, st6, Regs.set, Regs.get, Regs.empty, P3]
  · simp [hσ1, gW, st6, Regs.set, Regs.get, l47, l0]; omega

/-! ## phase 4: the degrees -/

def degColBody : Prog :=
  .seq (popProg .C) (.seq (.branch (fun h => decide (h .G = some .one)) (incProg .Dg .T) skipP) (popProg .G))

def degColLoop : Prog := .loop (fun h => (h .C).isSome) degColBody

def degRowBody : Prog :=
  .seq (popProg .R) (.seq (copyProg .N .C .sc) (.seq degColLoop (.seq (emitProg .Dg)
    (.seq (pushL .W [.one, .sep]) (clearProg .Dg)))))

def degRowLoop : Prog := .loop (fun h => (h .R).isSome) degRowBody

def gen4 : Prog := .seq (copyProg .M .G .sc) (.seq (copyProg .N .R .sc) degRowLoop)

def degR (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 m n bs with W := (P4 n bs s).reverse, G := enc (bs.drop (s * n)), R := List.replicate (n - s) .one }

def degC (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 m n bs with
    W := (P4 n bs s).reverse
    G := enc (bs.drop (s * n + t))
    R := List.replicate (n - (s + 1)) .one
    C := List.replicate (n - t) .one
    Dg := enc (Nat.bits (rowCnt bs n s t)) }

lemma rowCnt_succ (bs : List Bool) (n s t : ℕ) :
    rowCnt bs n s (t + 1) = rowCnt bs n s t + (if adjB bs n s t then 1 else 0) := by
  simp only [rowCnt, List.range_succ, List.filter_append, List.length_append]
  congr 1
  by_cases h : adjB bs n s t <;> simp [h]

lemma rowCnt_le (bs : List Bool) (n s t : ℕ) : rowCnt bs n s t ≤ t := by
  unfold rowCnt
  exact le_trans (List.length_filter_le _ _) (by simp)

lemma stepDC (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs degColBody (degC m n bs s t) (degC m n bs s (t + 1)) (10 * n + 30) := by
  have hk : s * n + t < bs.length := by rw [hbs]; nlinarith
  have hG : (degC m n bs s t).G = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := by
    simp only [degC]; rw [drop_eq_cons_getD bs _ hk]; rfl
  have e1 := runs_pop .C (degC m n bs s t)
  set σ1 := (degC m n bs s t).set .C ((degC m n bs s t).get .C).tail with hσ1
  have hσ1G : σ1.G = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := hG
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Runs (.branch (fun h => decide (h .G = some .one)) (incProg .Dg .T) skipP)
      σ1 σ2 (6 * n + 12) ∧ σ2 = σ1.set .Dg (enc (Nat.bits (rowCnt bs n s (t + 1)))) := by
    cases hadj : adjB bs n s t
    · refine ⟨σ1, ((runs_skip σ1).brF ?_).mono (by omega), ?_⟩
      · simp [hd, Regs.get, hσ1G, hadj, toB]
      · rw [rowCnt_succ, hadj]; simp only [Bool.false_eq_true, if_false, add_zero]
        apply Regs.ext_get; funext i; simp only [Regs.get_set]
        split_ifs with h1 <;> subst_vars <;> simp [hσ1, degC, Regs.set, Regs.get]
    · have e21 := runs_inc .Dg .T (by decide) σ1 (Nat.bits (rowCnt bs n s t))
        (by simp [hσ1, degC, Regs.set, Regs.get]) (by simp [hσ1, degC, st6, Regs.set, Regs.get, Regs.empty])
      refine ⟨_, (e21.brT ?_).mono ?_, ?_⟩
      · simp [hd, Regs.get, hσ1G, hadj, toB]
      · have : (Nat.bits (rowCnt bs n s t)).length ≤ n := len_bits_le_of_le (le_trans (rowCnt_le bs n s t) ht.le)
        omega
      · rw [incL_bits, rowCnt_succ, hadj]; rfl
  have e3 := runs_pop .G σ2
  refine ((e1.seq (e2.seq e3)).congr ?_).mono ?_
  · have hC : n - t - 1 = n - (t + 1) := by omega
    rw [hσ2]
    simp only [Regs.set, Regs.get, hσ1G]
    simp [hσ1, degC, Regs.set, Regs.get, hC, Nat.add_assoc]
  · omega

lemma runs_degColLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs degColLoop (degC m n bs s 0) (degC m n bs s n) (n * (10 * n + 32) + 1) := by
  refine Runs.loopU _ degColBody (degC m n bs s) _ _ (fun j hj => ⟨?_, stepDC m n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, degC, hk, List.replicate_succ]
  · simp [hd, Regs.get, degC]

lemma degBlock_succ (bs : List Bool) (n s : ℕ) :
    degBlock bs n (s + 1) = degBlock bs n s ++ (encNat (rowCnt bs n s n) ++ [.one, .sep]) := by
  simp [degBlock, List.range_succ, List.flatMap_append]

lemma stepDR (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs degRowBody (degR m n bs s) (degR m n bs (s + 1)) (n * (10 * n + 32) + 40 * n + 40) := by
  have e1 := runs_pop .R (degR m n bs s)
  set σ1 := (degR m n bs s).set .R ((degR m n bs s).get .R).tail with hσ1
  have e2 := runs_copy .N .C .sc (by decide) (by decide) (by decide) σ1 rfl
  have h0 : σ1.set .C (σ1.get .N ++ σ1.get .C) = degC m n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [hσ1, degR, degC, st6, Regs.set, Regs.get, Regs.empty, hR, List.tail_replicate, rowCnt]
  have e3 := runs_degColLoop m n bs hbs s hs
  have e4 := runs_emit .Dg (by decide) (by decide) (by decide) (degC m n bs s n) rfl rfl
  set σ4 := { degC m n bs s n with W := BSym.sep :: ((degC m n bs s n).get .Dg).reverse ++ (degC m n bs s n).W }
    with hσ4
  have e5 := runs_pushL .W [.one, .sep] σ4
  have e6 := runs_clear .Dg (σ4.set .W ([BSym.one, BSym.sep].reverse ++ σ4.get .W))
  refine ((e1.seq ((e2.congr h0).seq (e3.seq (e4.seq (e5.seq e6))))).congr ?_).mono ?_
  · have hG : s * n + n = (s + 1) * n := by ring
    simp [hσ4, degR, degC, st6, Regs.set, Regs.get, Regs.empty, P4, degBlock_succ, hG, encNat_eq']
  · have l1 : (σ1.get .N).length = n := by simp [hσ1, degR, st6, Regs.get, Regs.set]
    have l2 : ((degC m n bs s n).get .Dg).length ≤ n := by
      simp [degC, Regs.get]; exact len_bits_le_of_le (rowCnt_le bs n s n)
    have l3 : ((σ4.set .W ([BSym.one, BSym.sep].reverse ++ σ4.get .W)).get .Dg).length ≤ n := by
      simp [hσ4, degC, Regs.get, Regs.set]; exact len_bits_le_of_le (rowCnt_le bs n s n)
    rw [l1]; simp only [List.length_cons, List.length_nil]
    omega

lemma runs_degRowLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs degRowLoop (degR m n bs 0) (degR m n bs n)
      (n * (n * (10 * n + 32) + 40 * n + 42) + 1) := by
  refine Runs.loopU _ degRowBody (degR m n bs) _ _ (fun j hj => ⟨?_, stepDR m n bs hbs j hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, degR, hk, List.replicate_succ]
  · simp [hd, Regs.get, degR]

lemma runs_gen4 (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs gen4 (gW m n bs (P3 n)) (gW m n bs (P4 n bs n))
      (n * (n * (10 * n + 32) + 40 * n + 42) + 12 * n * n + 6 * n + 10) := by
  have e1 := runs_copy .M .G .sc (by decide) (by decide) (by decide) (gW m n bs (P3 n)) rfl
  set σ1 := (gW m n bs (P3 n)).set .G ((gW m n bs (P3 n)).get .M ++ (gW m n bs (P3 n)).get .G) with hσ1
  have e2 := runs_copy .N .R .sc (by decide) (by decide) (by decide) σ1 rfl
  have h0 : σ1.set .R (σ1.get .N ++ σ1.get .R) = degR m n bs 0 := by
    simp [hσ1, gW, degR, st6, Regs.set, Regs.get, Regs.empty, P4, degBlock]
  have e3 := runs_degRowLoop m n bs hbs
  have hfin : degR m n bs n = gW m n bs (P4 n bs n) := by
    simp [degR, gW, st6, Regs.empty, ← hbs]
  refine (((e1.seq ((e2.congr h0).seq e3))).congr hfin).mono ?_
  have l1 : ((gW m n bs (P3 n)).get .M).length = n * n := by simp [gW, st6, Regs.get, hbs]
  have l2 : (σ1.get .N).length = n := by simp [hσ1, gW, st6, Regs.get, Regs.set]
  rw [l1, l2]; nlinarith

/-! ## phase 5: the pair weights of the nodes, with the check of the diagonal -/

def diagBad (bs : List Bool) (n k : ℕ) : Prop := ∃ s' < k, adjB bs n s' s' = true

instance (bs : List Bool) (n k : ℕ) : Decidable (diagBad bs n k) := by unfold diagBad; infer_instance

def flagD (bs : List Bool) (n k : ℕ) : List BSym := if diagBad bs n k then [.one] else []

lemma diagBad_succ (bs : List Bool) (n k : ℕ) :
    diagBad bs n (k + 1) ↔ diagBad bs n k ∨ adjB bs n k k = true := by
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hik : i < k
    · exact Or.inl ⟨i, hik, h⟩
    · have : i = k := by omega
      subst this; exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, by omega, h⟩
    · exact ⟨k, by omega, h⟩

def dD (s t : ℕ) : List BSym := if t ≤ s then List.replicate (s - t) .one ++ [.zero] else []

def diagChk : Prog :=
  .branch (fun h => decide (h .M = some .one) && (h .bad).isNone) (pushProg .bad .one) skipP

def triColBody : Prog :=
  .seq (popProg .C)
    (.seq (.branch (fun h => decide (h .D = some .one)) (popProg .D)
        (.branch (fun h => decide (h .D = some .zero)) (.seq diagChk (popProg .D))
          (.branch (fun h => decide (h .M = some .one)) (pushL .W l8) (pushL .W l0))))
      (popProg .M))

def triColLoop : Prog := .loop (fun h => (h .C).isSome) triColBody

def triRowBody : Prog :=
  .seq (popProg .R) (.seq (copyProg .N .C .sc) (.seq (pushProg .D .zero)
    (.seq (copyProg .Us .D .sc) (.seq triColLoop (pushProg .Us .one)))))

def triRowLoop : Prog := .loop (fun h => (h .R).isSome) triRowBody

def gen5 : Prog := .seq (copyProg .N .R .sc) (.seq triRowLoop (clearProg .Us))

def triR (n : ℕ) (bs : List Bool) (s : ℕ) : Regs :=
  { st6 m n bs with
    W := (P5 n bs s 0).reverse
    M := enc (bs.drop (s * n))
    R := List.replicate (n - s) .one
    Us := List.replicate s .one
    bad := flagD bs n s }

def triC (n : ℕ) (bs : List Bool) (s t : ℕ) : Regs :=
  { st6 m n bs with
    W := (P5 n bs s t).reverse
    M := enc (bs.drop (s * n + t))
    R := List.replicate (n - (s + 1)) .one
    Us := List.replicate s .one
    C := List.replicate (n - t) .one
    D := dD s t
    bad := flagD bs n (if t ≤ s then s else s + 1) }

lemma triRow_succ (bs : List Bool) (n s t : ℕ) :
    triRow bs n s (t + 1) = triRow bs n s t ++ triEnt bs n s t := by
  simp [triRow, List.range_succ, List.flatMap_append]

lemma triBlock_succ (bs : List Bool) (n s : ℕ) :
    triBlock bs n (s + 1) = triBlock bs n s ++ triRow bs n s n := by
  simp [triBlock, List.range_succ, List.flatMap_append]

lemma stepTC (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    Runs triColBody (triC m n bs s t) (triC m n bs s (t + 1)) 40 := by
  have hk : s * n + t < bs.length := by rw [hbs]; nlinarith
  have hM : (triC m n bs s t).M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := by
    simp only [triC]; rw [drop_eq_cons_getD bs _ hk]; rfl
  have e1 := runs_pop .C (triC m n bs s t)
  set σ1 := (triC m n bs s t).set .C ((triC m n bs s t).get .C).tail with hσ1
  have hσ1M : σ1.M = toB (adjB bs n s t) :: enc (bs.drop (s * n + t + 1)) := hM
  have hσ1D : σ1.D = dD s t := rfl
  have hσ1b : σ1.bad = flagD bs n (if t ≤ s then s else s + 1) := rfl
  obtain ⟨σ2, e2, hσ2⟩ : ∃ σ2, Runs (.branch (fun h => decide (h .D = some .one)) (popProg .D)
        (.branch (fun h => decide (h .D = some .zero)) (.seq diagChk (popProg .D))
          (.branch (fun h => decide (h .M = some .one)) (pushL .W l8) (pushL .W l0)))) σ1 σ2 30 ∧
      σ2 = { σ1 with
        W := (triEnt bs n s t).reverse ++ σ1.W
        D := dD s (t + 1)
        bad := flagD bs n (if t + 1 ≤ s then s else s + 1) } := by
    rcases Nat.lt_trichotomy t s with hlt | heq | hgt
    · -- before the diagonal
      have hD : dD s t = BSym.one :: dD s (t + 1) := by
        simp only [dD, if_pos hlt.le, if_pos (show t + 1 ≤ s by omega)]
        rw [show s - t = (s - (t + 1)) + 1 by omega, List.replicate_succ]; rfl
      refine ⟨_, ((runs_pop .D σ1).brT ?_).mono (by omega), ?_⟩
      · simp [hd, Regs.get, hσ1D, hD]
      · have he : triEnt bs n s t = [] := by simp [triEnt]; omega
        have hb : σ1.bad = flagD bs n s := by rw [hσ1b, if_pos hlt.le]
        rw [he, if_pos (show t + 1 ≤ s by omega)]
        apply Regs.ext_get; funext i; cases i <;> simp [Regs.set, Regs.get, hσ1D, hD, hb]
    · -- the diagonal entry
      subst heq
      have hD : dD t t = [BSym.zero] := by simp [dD]
      have hD' : dD t (t + 1) = [] := by simp [dD]
      have he : triEnt bs n t t = [] := by simp [triEnt]
      obtain ⟨σ', e', hσ'⟩ : ∃ σ', Runs diagChk σ1 σ' 2 ∧ σ' = { σ1 with bad := flagD bs n (t + 1) } := by
        by_cases hb : diagBad bs n t
        · have hb' : diagBad bs n (t + 1) := (diagBad_succ bs n t).2 (Or.inl hb)
          refine ⟨σ1, (runs_skip σ1).brF ?_, ?_⟩
          · simp [hd, Regs.get, hσ1b, flagD, hb]
          · simp only [flagD, if_pos hb']
            simp only [if_pos (le_refl t), flagD, if_pos hb] at hσ1b
            rw [← hσ1b]
        · cases hadj : adjB bs n t t
          · have hb' : ¬ diagBad bs n (t + 1) := by
              rw [diagBad_succ]; push Not; exact ⟨hb, by simp [hadj]⟩
            refine ⟨σ1, (runs_skip σ1).brF ?_, ?_⟩
            · simp [hd, Regs.get, hσ1M, hadj, toB]
            · simp only [flagD, if_neg hb']
              simp only [if_pos (le_refl t), flagD, if_neg hb] at hσ1b
              rw [← hσ1b]
          · have hb' : diagBad bs n (t + 1) := (diagBad_succ bs n t).2 (Or.inr hadj)
            refine ⟨_, (runs_push .bad .one σ1).brT ?_, ?_⟩
            · simp [hd, Regs.get, hσ1M, hadj, toB, hσ1b, flagD, hb]
            · simp only [flagD, if_pos hb']
              simp [Regs.set, Regs.get, hσ1b, flagD, hb]
      have e'' := runs_pop .D σ'
      refine ⟨_, ((e'.seq e'').brT ?_ |>.brF ?_).mono (by omega), ?_⟩
      · simp [hd, Regs.get, hσ', hσ1D, hD]
      · simp [hd, Regs.get, hσ1D, hD]
      · rw [he, if_neg (by omega), hσ', hD']
        simp [Regs.set, Regs.get, hσ1D, hD]
    · -- after the diagonal
      have hD : dD s t = [] := by simp [dD]; omega
      have hD' : dD s (t + 1) = [] := by simp [dD]; omega
      have hb1 : (if t ≤ s then s else s + 1) = s + 1 := if_neg (by omega)
      have hb2 : (if t + 1 ≤ s then s else s + 1) = s + 1 := if_neg (by omega)
      cases hadj : adjB bs n s t
      · have e' := runs_pushL .W l0 σ1
        refine ⟨_, ((e'.brF ?_).brF ?_ |>.brF ?_).mono (by simp [l0]), ?_⟩
        · simp [hd, Regs.get, hσ1M, hadj, toB]
        · simp [hd, Regs.get, hσ1D, hD]
        · simp [hd, Regs.get, hσ1D, hD]
        · have he : triEnt bs n s t = l0 := by simp [triEnt, hadj]; omega
          rw [he, hb2, hD']
          simp [Regs.set, Regs.get, hσ1D, hD, hσ1b, hb1]
      · have e' := runs_pushL .W l8 σ1
        refine ⟨_, ((e'.brT ?_).brF ?_ |>.brF ?_).mono (by simp [l8]), ?_⟩
        · simp [hd, Regs.get, hσ1M, hadj, toB]
        · simp [hd, Regs.get, hσ1D, hD]
        · simp [hd, Regs.get, hσ1D, hD]
        · have he : triEnt bs n s t = l8 := by simp [triEnt, hadj]; omega
          rw [he, hb2, hD']
          simp [Regs.set, Regs.get, hσ1D, hD, hσ1b, hb1]
  have e3 := runs_pop .M σ2
  refine ((e1.seq (e2.seq e3)).congr ?_).mono (by omega)
  have hC : n - t - 1 = n - (t + 1) := by omega
  rw [hσ2]
  simp only [Regs.set, Regs.get, hσ1M]
  simp [hσ1, triC, Regs.set, Regs.get, hC, Nat.add_assoc, P5, triRow_succ]

lemma runs_triColLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs triColLoop (triC m n bs s 0) (triC m n bs s n) (n * 42 + 1) := by
  refine Runs.loopU _ triColBody (triC m n bs s) _ _ (fun j hj => ⟨?_, stepTC m n bs hbs s j hs hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, triC, hk, List.replicate_succ]
  · simp [hd, Regs.get, triC]

lemma stepTR (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) (s : ℕ) (hs : s < n) :
    Runs triRowBody (triR m n bs s) (triR m n bs (s + 1)) (60 * n + 30) := by
  have e1 := runs_pop .R (triR m n bs s)
  set σ1 := (triR m n bs s).set .R ((triR m n bs s).get .R).tail with hσ1
  have e2 := runs_copy .N .C .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .C (σ1.get .N ++ σ1.get .C) with hσ2
  have e3 := runs_push .D .zero σ2
  set σ3 := σ2.set .D (.zero :: σ2.get .D) with hσ3
  have e4 := runs_copy .Us .D .sc (by decide) (by decide) (by decide) σ3 rfl
  have h0 : σ3.set .D (σ3.get .Us ++ σ3.get .D) = triC m n bs s 0 := by
    have hR : n - s - 1 = n - (s + 1) := by omega
    simp [hσ3, hσ2, hσ1, triR, triC, st6, Regs.set, Regs.get, Regs.empty, hR, List.tail_replicate, dD,
      P5, triRow]
  have e5 := runs_triColLoop m n bs hbs s hs
  have e6 := runs_push .Us .one (triC m n bs s n)
  refine ((e1.seq (e2.seq (e3.seq ((e4.congr h0).seq (e5.seq e6))))).congr ?_).mono ?_
  · have hG : s * n + n = (s + 1) * n := by ring
    have h1 : ¬ n ≤ s := by omega
    simp [triR, triC, st6, Regs.set, Regs.get, Regs.empty, P5, triBlock_succ, hG, dD, h1, triRow,
      List.replicate_succ]
  · have l1 : (σ1.get .N).length = n := by simp [hσ1, triR, st6, Regs.get, Regs.set]
    have l2 : (σ3.get .Us).length = s := by simp [hσ3, hσ2, hσ1, triR, st6, Regs.get, Regs.set]
    rw [l1, l2]; omega

lemma runs_triRowLoop (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs triRowLoop (triR m n bs 0) (triR m n bs n) (n * (60 * n + 32) + 1) := by
  refine Runs.loopU _ triRowBody (triR m n bs) _ _ (fun j hj => ⟨?_, stepTR m n bs hbs j hj⟩) ?_
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    simp [hd, Regs.get, triR, hk, List.replicate_succ]
  · simp [hd, Regs.get, triR]

def gT (n : ℕ) (bs : List Bool) (l b : List BSym) : Regs :=
  { st6 m n bs with W := l.reverse, M := [], bad := b }

lemma runs_gen5 (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    Runs gen5 (gW m n bs (P4 n bs n)) (gT m n bs (P5 n bs n 0) (flagD bs n n))
      (n * (60 * n + 32) + 12 * n + 10) := by
  have e1 := runs_copy .N .R .sc (by decide) (by decide) (by decide) (gW m n bs (P4 n bs n)) rfl
  have h0 : (gW m n bs (P4 n bs n)).set .R ((gW m n bs (P4 n bs n)).get .N ++ (gW m n bs (P4 n bs n)).get .R)
      = triR m n bs 0 := by
    have : ¬ diagBad bs n 0 := by rintro ⟨i, hi, _⟩; omega
    simp [gW, triR, st6, Regs.set, Regs.get, Regs.empty, P5, triBlock, triRow, flagD, this]
  have e2 := runs_triRowLoop m n bs hbs
  have e3 := runs_clear .Us (triR m n bs n)
  refine (((e1.congr h0).seq (e2.seq e3)).congr ?_).mono ?_
  · simp [triR, gT, st6, Regs.set, Regs.empty, ← hbs]
  · simp [gW, triR, st6, Regs.get, Regs.set]; omega

/-! ## phases 6–7: `v0 = 2M + 1`, `κ = 1`, and the output -/

def gen6 : Prog :=
  .seq (pushL .W [.one]) (.seq (copyProg .Mv .T .sc) (.seq (mvProg .T .W)
    (.seq (pushL .W [.sep, .one, .sep]) (pushL .W lk))))

lemma runs_gen6 (n : ℕ) (bs : List Bool) (b : List BSym) :
    Runs gen6 (gT m n bs (P5 n bs n 0) b) (gT m n bs (P6 n bs m) b) (10 * m.length + 40) := by
  have e1 := runs_pushL .W [.one] (gT m n bs (P5 n bs n 0) b)
  set σ1 := (gT m n bs (P5 n bs n 0) b).set .W ([BSym.one].reverse ++ (gT m n bs (P5 n bs n 0) b).get .W)
    with hσ1
  have e2 := runs_copy .Mv .T .sc (by decide) (by decide) (by decide) σ1 rfl
  set σ2 := σ1.set .T (σ1.get .Mv ++ σ1.get .T) with hσ2
  have e3 := runs_mv .T .W (by decide) σ2
  set σ3 := (σ2.set .T []).set .W ((σ2.get .T).reverse ++ σ2.get .W) with hσ3
  have e4 := runs_pushL .W [.sep, .one, .sep] σ3
  set σ4 := σ3.set .W ([BSym.sep, .one, .sep].reverse ++ σ3.get .W) with hσ4
  have e5 := runs_pushL .W lk σ4
  refine ((e1.seq (e2.seq (e3.seq (e4.seq e5)))).congr ?_).mono ?_
  · simp [hσ4, hσ3, hσ2, hσ1, gT, st6, Regs.set, Regs.get, Regs.empty, P6, lk]
  · have l1 : (σ1.get .Mv).length = m.length := by simp [hσ1, gT, st6, Regs.get, Regs.set, Regs.empty]
    have l2 : (σ2.get .T).length = m.length := by simp [hσ2, hσ1, gT, st6, Regs.get, Regs.set, Regs.empty]
    rw [l1, l2]; simp [lk]; omega

def gen7 : Prog := gate (mvProg .W .out)

lemma runs_gen7_ok (n : ℕ) (bs : List Bool) (l : List BSym) :
    ∃ τ, Runs gen7 (gT m n bs l []) τ (3 * l.length + 2) ∧ τ.out = l := by
  have e := runs_mv .W .out (by decide) (gT m n bs l [])
  refine ⟨_, runs_gate_ok rfl e |>.mono ?_, ?_⟩
  · simp [gT, Regs.get]
  · simp [gT, st6, Regs.set, Regs.get, Regs.empty]

lemma runs_gen7_bad (n : ℕ) (bs : List Bool) (l b : List BSym) (hb : b ≠ []) :
    ∃ τ, Runs gen7 (gT m n bs l b) τ 2 ∧ τ.out = [] := by
  refine ⟨_, runs_gate_skip (by simpa [gT] using hb), ?_⟩
  simp [gT, st6, Regs.empty]

end MCRed


set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## splitting off the last number `M` -/

def sp2 : Prog := .branch (fun h => decide (h .A = some .sep)) (popProg .A) (pushProg .bad .one)
def sp3 : Prog := .branch (fun h => decide (h .A = some .zero)) (pushProg .bad .one) skipP

def splitProg : Prog :=
  .seq (mvProg .inp .A) (.seq sp2 (.seq sp3 (.seq (mvwProg .A .Mv isDigB) (mvProg .A .inp))))

def splitOK (w : List BSym) : Prop :=
  w.reverse.head? = some .sep ∧ w.reverse.tail.head? ≠ some .zero

instance (w : List BSym) : Decidable (splitOK w) := by unfold splitOK; infer_instance

def mdig (w : List BSym) : List BSym := (w.reverse.tail.takeWhile isDigB).reverse
def pre (w : List BSym) : List BSym := (w.reverse.tail.dropWhile isDigB).reverse

lemma runs_split (w : List BSym) :
    ∃ τ, Runs splitProg (initM [] w) τ (12 * w.length + 20) ∧
      (splitOK w → τ = initM (mdig w) (pre w)) ∧ (¬ splitOK w → τ.bad ≠ [] ∧ τ.out = []) := by
  have e1 := runs_mv .inp .A (by decide) (initM [] w)
  set σ1 := ((initM [] w).set .inp []).set .A (((initM [] w).get .inp).reverse ++ (initM [] w).get .A)
    with hσ1
  have h1A : σ1.A = w.reverse := by simp [hσ1, initM, Regs.set, Regs.get, Regs.empty]
  have hlen1 : 3 * ((initM [] w).get .inp).length + 1 = 3 * w.length + 1 := by
    simp [initM, Regs.get]
  rw [hlen1] at e1
  by_cases hs : w.reverse.head? = some .sep
  · obtain ⟨v, hv⟩ : ∃ v, w.reverse = .sep :: v := by
      cases h : w.reverse with
      | nil => rw [h] at hs; cases hs
      | cons a v => rw [h] at hs; simp at hs; subst hs; exact ⟨v, rfl⟩
    have e2 : Runs sp2 σ1 (σ1.set .A v) 2 := by
      have := (runs_pop .A σ1).brT (t := fun h => decide (h .A = some .sep)) (q := pushProg .bad .one)
        (by simp [hd, Regs.get, h1A, hv])
      exact this.congr (by simp [Regs.get, h1A, hv])
    set σ2 := σ1.set .A v with hσ2
    have hlenv : v.length ≤ w.length := by
      have := congrArg List.length hv; simp at this; omega
    by_cases hz : v.head? = some .zero
    · -- non-canonical `M`
      have e3 : Runs sp3 σ2 (σ2.set .bad (.one :: σ2.get .bad)) 2 :=
        (runs_push .bad .one σ2).brT (by simp [hd, Regs.get, Regs.set, hσ2, hz])
      set σ3 := σ2.set .bad (.one :: σ2.get .bad) with hσ3
      have e4 := runs_mvw .A .Mv (by decide) isDigB v σ3 (by simp [hσ3, hσ2, Regs.get, Regs.set])
      set σ4 := (σ3.set .A (v.dropWhile isDigB)).set .Mv ((v.takeWhile isDigB).reverse ++ σ3.get .Mv)
        with hσ4
      have e5 := runs_mv .A .inp (by decide) σ4
      refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, fun h => absurd ?_ h.2, fun _ => ?_⟩
      · have : (σ4.get .A).length ≤ w.length := by
          simp only [hσ4, Regs.get_set, Regs.get_set_self, if_neg (show Key.A ≠ Key.Mv by decide)]
          exact le_trans (List.dropWhile_sublist _).length_le hlenv
        omega
      · rw [hv]; exact hz
      · constructor
        · simp [Regs.set, Regs.get, hσ4, hσ3]
        · simp [Regs.set, Regs.get, hσ4, hσ3, hσ2, hσ1, initM, Regs.empty]
    · have e3 : Runs sp3 σ2 σ2 2 := (runs_skip σ2).brF (by simp [hd, Regs.get, Regs.set, hσ2, hz])
      have e4 := runs_mvw .A .Mv (by decide) isDigB v σ2 (by simp [hσ2, Regs.get, Regs.set])
      set σ4 := (σ2.set .A (v.dropWhile isDigB)).set .Mv ((v.takeWhile isDigB).reverse ++ σ2.get .Mv)
        with hσ4
      have e5 := runs_mv .A .inp (by decide) σ4
      have hok : splitOK w := ⟨hs, by rw [hv]; exact hz⟩
      refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, fun _ => ?_, fun h => absurd hok h⟩
      · have : (σ4.get .A).length ≤ w.length := by
          simp only [hσ4, Regs.get_set, Regs.get_set_self, if_neg (show Key.A ≠ Key.Mv by decide)]
          exact le_trans (List.dropWhile_sublist _).length_le hlenv
        omega
      · simp [hσ4, hσ2, hσ1, initM, Regs.set, Regs.get, Regs.empty, mdig, pre, hv]
  · have e2 : Runs sp2 σ1 (σ1.set .bad (.one :: σ1.get .bad)) 2 :=
      (runs_push .bad .one σ1).brF (by simp only [hd, Regs.get, h1A]; simpa using hs)
    set σ2 := σ1.set .bad (.one :: σ1.get .bad) with hσ2
    obtain ⟨σ3, e3, h3b, h3o, h3A⟩ : ∃ σ3, Runs sp3 σ2 σ3 2 ∧ σ3.bad ≠ [] ∧ σ3.out = [] ∧ σ3.A = w.reverse := by
      by_cases hz : (hd σ2) .A = some .zero
      · refine ⟨_, (runs_push .bad .one σ2).brT (by simp [hz]), ?_, ?_, ?_⟩ <;>
          simp [Regs.set, Regs.get, hσ2, hσ1, initM, Regs.empty]
      · refine ⟨_, (runs_skip σ2).brF (by simp [hz]), ?_, ?_, ?_⟩ <;>
          simp [Regs.set, Regs.get, hσ2, hσ1, initM, Regs.empty]
    have e4 := runs_mvw .A .Mv (by decide) isDigB w.reverse σ3 (by simpa [Regs.get] using h3A)
    set σ4 := (σ3.set .A (w.reverse.dropWhile isDigB)).set .Mv
      ((w.reverse.takeWhile isDigB).reverse ++ σ3.get .Mv) with hσ4
    have e5 := runs_mv .A .inp (by decide) σ4
    refine ⟨_, (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_, fun h => absurd h.1 hs, fun _ => ?_⟩
    · have : (σ4.get .A).length ≤ w.length := by
        simp only [hσ4, Regs.get_set, Regs.get_set_self, if_neg (show Key.A ≠ Key.Mv by decide)]
        exact le_trans (List.dropWhile_sublist _).length_le (by simp)
      have : w.reverse.length = w.length := List.length_reverse
      omega
    · constructor
      · simpa [Regs.set, Regs.get, hσ4] using h3b
      · simpa [Regs.set, Regs.get, hσ4] using h3o

/-! ## pure facts about the split -/

lemma flat_tokB_ends (bs : List Bool) : bs.flatMap tokB = [] ∨ ∃ c, bs.flatMap tokB = c ++ [BSym.sep] := by
  induction bs with
  | nil => left; rfl
  | cons b bs ih =>
    right
    rcases ih with h | ⟨c, hc⟩
    · cases b
      · exact ⟨[], by simp [h, tokB]⟩
      · exact ⟨[.one], by simp [h, tokB]⟩
    · exact ⟨tokB b ++ c, by simp [hc]⟩

lemma code_ends (n : ℕ) (bs : List Bool) : ∃ c, code n bs = c ++ [.sep] := by
  unfold code
  rcases flat_tokB_ends bs with h | ⟨c, hc⟩
  · exact ⟨enc (Nat.bits n), by simp [h]⟩
  · exact ⟨enc (Nat.bits n) ++ .sep :: c, by simp [hc]⟩

lemma enc_bits_rev_head (M : ℕ) (r : List BSym) (hr : r.head? = some .sep) :
    ((enc (Nat.bits M)).reverse ++ r).head? ≠ some .zero := by
  cases h : Nat.bits M with
  | nil => simp [hr]
  | cons b l =>
    have hne : Nat.bits M ≠ [] := by rw [h]; simp
    have hl := bits_getLast M
    have : (Nat.bits M).getLast hne = true := by
      have h2 := List.getLast?_eq_some_getLast hne
      cases hb : (Nat.bits M).getLast hne
      · rw [hb] at h2; exact absurd h2 hl
      · rfl
    rw [← h]
    have hh : ((enc (Nat.bits M)).reverse ++ r).head? = some (toB ((Nat.bits M).getLast hne)) := by
      simp only [enc, ← List.map_reverse]
      rw [List.head?_append]
      have : (Nat.bits M).reverse ≠ [] := by simpa using hne
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil this
      have hx' : (Nat.bits M).getLast hne = x := by
        have := congrArg List.head? hx
        rw [List.head?_reverse, List.getLast?_eq_some_getLast hne] at this
        simpa using this
      rw [hx, hx']; simp
    rw [hh, this]; simp [toB]

lemma split_of_valid (n : ℕ) (bs : List Bool) (M : ℕ) :
    splitOK (code n bs ++ enc (Nat.bits M) ++ [.sep]) ∧
      mdig (code n bs ++ enc (Nat.bits M) ++ [.sep]) = enc (Nat.bits M) ∧
      pre (code n bs ++ enc (Nat.bits M) ++ [.sep]) = code n bs := by
  obtain ⟨c, hc⟩ := code_ends n bs
  have hrev : (code n bs ++ enc (Nat.bits M) ++ [BSym.sep]).reverse =
      BSym.sep :: ((enc (Nat.bits M)).reverse ++ (BSym.sep :: c.reverse)) := by
    rw [hc]; simp
  have hdig : ∀ x ∈ (enc (Nat.bits M)).reverse, isDigB x = true := by
    intro x hx; exact isDigB_enc _ x (List.mem_reverse.1 hx)
  have htw : ((enc (Nat.bits M)).reverse ++ (.sep :: c.reverse)).takeWhile isDigB = (enc (Nat.bits M)).reverse := by
    rw [List.takeWhile_append_of_pos hdig]; simp [List.takeWhile, isDigB]
  have hdw : ((enc (Nat.bits M)).reverse ++ (.sep :: c.reverse)).dropWhile isDigB = .sep :: c.reverse := by
    rw [List.dropWhile_append_of_pos hdig]; simp [List.dropWhile, isDigB]
  refine ⟨⟨by rw [hrev]; rfl, ?_⟩, ?_, ?_⟩
  · rw [hrev]; exact enc_bits_rev_head M _ rfl
  · unfold mdig; rw [hrev]; simp only [List.tail_cons]; rw [htw]; simp
  · unfold pre; rw [hrev]; simp only [List.tail_cons]; rw [hdw, hc]; simp

lemma valid_of_split (w : List BSym) (h : splitOK w) :
    w = pre w ++ mdig w ++ [.sep] ∧ mdig w = enc (Nat.bits (bval ((mdig w).map fromB))) := by
  obtain ⟨hs, hz⟩ := h
  obtain ⟨v, hv⟩ : ∃ v, w.reverse = .sep :: v := by
    cases h : w.reverse with
    | nil => rw [h] at hs; cases hs
    | cons a v => rw [h] at hs; simp at hs; subst hs; exact ⟨v, rfl⟩
  rw [hv] at hz
  simp only [List.tail_cons] at hz
  constructor
  · unfold pre mdig
    rw [hv]; simp only [List.tail_cons]
    rw [← List.reverse_append, List.takeWhile_append_dropWhile]
    have : w = (w.reverse).reverse := by simp
    rw [this, hv]; simp
  · have hdig : ∀ x ∈ mdig w, isDigB x = true := by
      intro x hx
      simp only [mdig, hv, List.tail_cons, List.mem_reverse] at hx
      exact List.mem_takeWhile_imp hx
    have hl : ((mdig w).map fromB).getLast? ≠ some false := by
      rw [List.getLast?_map]
      intro hc
      simp only [mdig, hv, List.tail_cons, List.getLast?_reverse] at hc
      cases hh : (v.takeWhile isDigB).head? with
      | none => rw [hh] at hc; cases hc
      | some x =>
        rw [hh] at hc
        have hx : x ∈ v.takeWhile isDigB := List.mem_of_head? hh
        have hxd := List.mem_takeWhile_imp hx
        have hvx : v.head? = some x := by
          cases v with
          | nil => simp at hh
          | cons y v =>
            simp only [List.takeWhile_cons] at hh
            split_ifs at hh <;> simp_all
        cases x <;> simp_all [fromB, isDigB]
    rw [bits_bval _ hl, enc_fromB _ hdig]

/-! ## the reduction function, read off the input -/

def VS (w : List BSym) (p : ℕ × List Bool × ℕ) : Prop :=
  p.2.1.length = p.1 * p.1 ∧ w = code p.1 p.2.1 ++ enc (Nat.bits p.2.2) ++ [.sep]

lemma enc_inj {a b : List Bool} (h : enc a = enc b) : a = b := by
  rw [← map_fromB_enc a, ← map_fromB_enc b, h]

lemma VS_unique {w : List BSym} {p q : ℕ × List Bool × ℕ} (hp : VS w p) (hq : VS w q) : p = q := by
  obtain ⟨_, hpw⟩ := hp
  obtain ⟨_, hqw⟩ := hq
  obtain ⟨_, hp2, hp3⟩ := split_of_valid p.1 p.2.1 p.2.2
  obtain ⟨_, hq2, hq3⟩ := split_of_valid q.1 q.2.1 q.2.2
  rw [← hpw] at hp2 hp3
  rw [← hqw] at hq2 hq3
  have hM : p.2.2 = q.2.2 := by
    have := enc_inj (hp2.symm.trans hq2)
    rw [← bval_bits p.2.2, this, bval_bits]
  obtain ⟨h1, h2⟩ := code_inj (hp3.symm.trans hq3)
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := q
  simp only at h1 h2 hM
  rw [h1, h2, hM]

def gOut (n : ℕ) (bs : List Bool) (M : ℕ) : List BSym :=
  if symBad bs n (n * n) ∨ diagBad bs n n then [] else P6 n bs (enc (Nat.bits M))

noncomputable def fR (w : List BSym) : List BSym :=
  open Classical in
  if h : ∃ p, VS w p then gOut (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2
  else []

lemma fR_valid {w : List BSym} {n : ℕ} {bs : List Bool} {M : ℕ} (h : VS w (n, bs, M)) :
    fR w = gOut n bs M := by
  have he : ∃ p, VS w p := ⟨_, h⟩
  unfold fR
  rw [dif_pos he]
  have := VS_unique (Classical.choose_spec he) h
  rw [this]

lemma fR_invalid {w : List BSym} (h : ∀ p, ¬ VS w p) : fR w = [] := by
  unfold fR
  rw [dif_neg (by rintro ⟨p, hp⟩; exact h p hp)]

end MCRed


set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity

/-! ## lengths -/

lemma len_encNat (k : ℕ) : (encNat k).length ≤ k + 1 := by
  rw [encNat_eq']; simp only [List.length_append, length_enc, List.length_singleton]
  have := len_bits_le k; omega

lemma len_flatMap_range {α : Type} (f : ℕ → List α) (K : ℕ) (h : ∀ i, (f i).length ≤ K) :
    ∀ s, ((List.range s).flatMap f).length ≤ s * K := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, Nat.succ_mul]
    have := h s
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

lemma len_P6 (n : ℕ) (bs : List Bool) (m : List BSym) :
    (P6 n bs m).length ≤ 10 * (n + 1) ^ 2 + m.length + 40 := by
  have h1 : (P1 n).length ≤ n + 2 := le_trans (len_encNat _) (by omega)
  have hdeg : (degBlock bs n n).length ≤ n * (n + 3) := by
    apply len_flatMap_range
    intro i
    have := len_encNat (rowCnt bs n i n)
    have := rowCnt_le bs n i n
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hrow : ∀ s t, (triRow bs n s t).length ≤ t * 7 := by
    intro s t
    apply len_flatMap_range
    intro i
    unfold triEnt
    split_ifs <;> simp [l8, l0]
  have htri : (triBlock bs n n).length ≤ n * (n * 7) := by
    apply len_flatMap_range
    intro i; exact hrow i n
  have hr0 : (triRow bs n n 0).length = 0 := by simp [triRow]
  simp only [P6, P5, P4, P3, P2, List.length_append, List.length_cons, List.length_flatten,
    List.map_replicate, List.sum_replicate, l114, l14, l47, l0, lk, List.length_nil, hr0,
    smul_eq_mul]
  nlinarith

/-! ## the whole program -/

def genAll : Prog := .seq gen1 (.seq gen2 (.seq gen3 (.seq gen4 (.seq gen5 (.seq gen6 gen7)))))

def mainProg : Prog := .seq splitProg (gate (.seq parseProg (gate (.seq symAll (gate genAll)))))

lemma runs_genAll (m : List BSym) (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) :
    ∃ τ, Runs genAll (st6 m n bs) τ (200 * (n + 1) ^ 3 + 20 * m.length + 400) ∧
      τ.out = if diagBad bs n n then [] else P6 n bs m := by
  have e1 := runs_gen1 m n bs
  have e2 := runs_gen2 m n bs
  have e3 := runs_gen3 m n bs
  have e4 := runs_gen4 m n bs hbs
  have e5 := runs_gen5 m n bs hbs
  have e6 := runs_gen6 m n bs (flagD bs n n)
  have hP := len_P6 n bs m
  by_cases hd : diagBad bs n n
  · obtain ⟨τ, e7, h7⟩ := runs_gen7_bad m n bs (P6 n bs m) (flagD bs n n) (by simp [flagD, hd])
    refine ⟨τ, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono ?_, by rw [h7, if_pos hd]⟩
    nlinarith
  · have hf : flagD bs n n = [] := by simp [flagD, hd]
    rw [hf] at e5 e6
    obtain ⟨τ, e7, h7⟩ := runs_gen7_ok m n bs (P6 n bs m)
    refine ⟨τ, (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono ?_, by rw [h7, if_neg hd]⟩
    nlinarith

theorem main_spec (w : List BSym) :
    ∃ τ, Runs mainProg (initM [] w) τ (20000 * (w.length + 1) ^ 2) ∧ τ.out = fR w := by
  obtain ⟨τ0, e0, h0ok, h0bad⟩ := runs_split w
  set L := w.length with hL
  have hpos : (L + 1) ^ 2 ≥ L + 1 := by nlinarith
  by_cases hok : splitOK w
  · have hτ0 := h0ok hok
    subst hτ0
    obtain ⟨hw, hmd⟩ := valid_of_split w hok
    set md := mdig w with hmdd
    set pr := pre w with hprd
    have hlens : pr.length + md.length + 1 = L := by
      have := congrArg List.length hw; simp at this; omega
    obtain ⟨τ1, e1, h1⟩ := parse_spec md pr
    have hprL : (pr.length + 1) ^ 2 ≤ (L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rcases h1 with ⟨n, bs, hbs, hpr, hτ1⟩ | ⟨hb, ho, hinv⟩
    · subst hτ1
      set M := bval (md.map fromB) with hM
      have hVS : VS w (n, bs, M) := ⟨hbs, by rw [hw, hpr, ← hmd]⟩
      have hfR : fR w = gOut n bs M := fR_valid hVS
      have hbL : bs.length ≤ L := by
        have := length_code n bs; rw [← hpr] at this; omega
      have hnn : n * n ≤ L := hbs ▸ hbL
      have hn : n ≤ L := le_trans (n_le_of_sq hbs) hbL
      have hsq : (n + 1) ^ 4 ≤ 16 * (L + 1) ^ 2 := by
        have h1 : (n + 1) ^ 2 ≤ 4 * (L + 1) := by nlinarith
        have h2 : (n + 1) ^ 4 = ((n + 1) ^ 2) ^ 2 := by ring
        rw [h2]; nlinarith
      have hcube : (n + 1) ^ 3 ≤ 4 * (L + 1) ^ 2 := by
        have h1 : (n + 1) ^ 2 ≤ 4 * (L + 1) := by nlinarith
        have h2 : (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) := by ring
        rw [h2]; nlinarith
      have es := runs_symAll md n bs hbs
      by_cases hsb : symBad bs n (n * n)
      · have hb' : ({ st6 md n bs with bad := flagL bs n (n * n) } : Regs).bad ≠ [] := by
          simp [flagL, hsb]
        refine ⟨_, (e0.seq (runs_gate_ok rfl (e1.seq (runs_gate_ok rfl (es.seq
          (runs_gate_skip hb')))))).mono ?_, ?_⟩
        · nlinarith
        · rw [hfR, gOut, if_pos (Or.inl hsb)]; rfl
      · have hσ : ({ st6 md n bs with bad := flagL bs n (n * n) } : Regs) = st6 md n bs := by
          simp [flagL, hsb, st6, Regs.empty]
        rw [hσ] at es
        obtain ⟨τ2, e2, h2⟩ := runs_genAll md n bs hbs
        refine ⟨τ2, (e0.seq (runs_gate_ok rfl (e1.seq (runs_gate_ok rfl (es.seq
          (runs_gate_ok rfl e2)))))).mono ?_, ?_⟩
        · nlinarith
        · rw [h2, hfR, gOut]
          by_cases hdb : diagBad bs n n
          · rw [if_pos hdb, if_pos (Or.inr hdb)]
          · rw [if_neg hdb, if_neg (by tauto), ← hmd]
    · refine ⟨τ1, (e0.seq (runs_gate_ok rfl (e1.seq (runs_gate_skip hb)))).mono ?_, ?_⟩
      · nlinarith
      · rw [ho, fR_invalid]
        rintro ⟨n, bs, M⟩ ⟨hbs, hwv⟩
        obtain ⟨_, _, h3⟩ := split_of_valid n bs M
        rw [← hwv] at h3
        exact hinv n bs hbs h3
  · obtain ⟨hb, ho⟩ := h0bad hok
    refine ⟨τ0, (e0.seq (runs_gate_skip hb)).mono ?_, ?_⟩
    · nlinarith
    · rw [ho, fR_invalid]
      rintro ⟨n, bs, M⟩ ⟨_, hwv⟩
      obtain ⟨h1, _, _⟩ := split_of_valid n bs M
      rw [← hwv] at h1
      exact hok h1

lemma initM_get (w : List BSym) : (initM [] w).get = fun j => if j = .inp then w else [] := by
  funext j; cases j <;> rfl

theorem fR_poly : PolyTimeComputable fR := by
  obtain ⟨k, hk⟩ := polynomial_absorb 20000 2 0
  refine stack_program_polytime mainProg .inp .out fR k (fun w => ?_)
  obtain ⟨τ, ⟨m, hm, ex⟩, ho⟩ := main_spec w
  refine ⟨τ.get, m, le_trans hm (by have := hk w.length; omega), ?_, ho⟩
  rw [← initM_get]; exact ex

end MCRed


set_option autoImplicit false

namespace MCSem

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

open Classical in
/-- the pair weights of the instance built from `G`: `V{0, j+1} = d_j` (the hub), and
`V{i+1, j+1} = 8` if `i, j` are adjacent, else `0` -/
noncomputable def V2f {ν : ℕ} (G : SimpleGraph (Fin ν)) (i j : Fin (ν + 1)) : ℚ :=
  Fin.cases (Fin.cases 0 (fun j' => (nodeDeg G j' : ℚ)) j)
    (fun i' => Fin.cases (nodeDeg G i' : ℚ) (fun j' => if G.Adj i' j' then 8 else 0) j) i

/-- revenues `r₀ = 11/4`, `rᵢ = 1/4`; singleton weights `V{0} = 4/7`, `V{i} = 0`; `v0 = 2M + 1` -/
@[reducible] noncomputable def inst {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : Instance where
  n := ν + 1
  r := Fin.cases (11 / 4) (fun _ => 1 / 4)
  V1 := Fin.cases (4 / 7) (fun _ => 0)
  V2 := V2f G
  v0 := 2 * M + 1

lemma inst_wf {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : (inst G M).WellFormed := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j _ => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> simp [inst] <;> norm_num
  · refine Fin.cases ?_ (fun i => ?_) i <;> simp [inst] <;> norm_num
  · show 0 ≤ V2f G i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [V2f] <;> split_ifs <;> norm_num
  · simp [inst]; positivity

lemma V2f_symm {ν : ℕ} (G : SimpleGraph (Fin ν)) (i j : Fin (ν + 1)) : V2f G i j = V2f G j i := by
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · rfl
  · simp [V2f]
  · simp [V2f]
  · simp only [V2f, Fin.cases_succ]
    by_cases h : G.Adj a b
    · simp [h, h.symm]
    · have h' : ¬ G.Adj b a := fun h' => h h'.symm
      simp [h, h']

lemma V2f_minmax {ν : ℕ} (G : SimpleGraph (Fin ν)) (i j : Fin (ν + 1)) :
    V2f G (min i j) (max i j) = V2f G i j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, V2f_symm]

open Classical in
lemma key {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) (i j : Fin (ν + 1)) :
    (inst G M).theta i j * ((inst G M).rhat i j - 1) =
      2 * hubQ G i j + (if i = 0 ∧ j = 0 then 1 else 0) := by
  have hth : (inst G M).theta i j = if i = j then (inst G M).V1 i else V2f G i j / 2 := by
    simp only [Instance.theta]
    split_ifs
    · rfl
    · exact congrArg (· / 2) (V2f_minmax G i j)
  rw [hth]
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · simp [Instance.rhat, hubQ]; norm_num
  · simp [Instance.rhat, V2f, hubQ, (Fin.succ_ne_zero b).symm]; ring
  · simp [Instance.rhat, V2f, hubQ, Fin.succ_ne_zero a]; ring
  · by_cases hab : a = b
    · subst hab
      simp [Instance.rhat, hubQ]
    · have hne : a.succ ≠ b.succ := fun h => hab (Fin.succ_injective _ h)
      simp only [Instance.rhat, hne, if_false, V2f, Fin.cases_succ, hubQ, Fin.succ_ne_zero, false_and,
        add_zero]
      split_ifs <;> norm_num

lemma xC_sq {n : ℕ} (C : Finset (Fin n)) (i : Fin n) : xC C i * xC C i = xC C i := by
  unfold xC; split_ifs <;> norm_num

open Classical in
lemma objective {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) (C : Finset (Fin (ν + 1))) :
    ∑ i, ∑ j, (inst G M).theta i j * xC C i * xC C j * ((inst G M).rhat i j - 1) =
      2 * (∑ i, ∑ j, hubQ G i j * xC C i * xC C j) + xC C 0 := by
  have h : ∀ i j : Fin (ν + 1), (inst G M).theta i j * xC C i * xC C j * ((inst G M).rhat i j - 1) =
      2 * (hubQ G i j * xC C i * xC C j) + (if i = 0 ∧ j = 0 then 1 else 0) * xC C i * xC C j := by
    intro i j
    have := key G M i j
    calc (inst G M).theta i j * xC C i * xC C j * ((inst G M).rhat i j - 1)
        = ((inst G M).theta i j * ((inst G M).rhat i j - 1)) * xC C i * xC C j := by ring
      _ = _ := by rw [this]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  have h2 : ∀ i j : Fin (ν + 1), (if i = 0 ∧ j = 0 then (1 : ℚ) else 0) * xC C i * xC C j =
      if i = 0 then (if j = 0 then xC C 0 * xC C 0 else 0) else 0 := by
    intro i j; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
  simp only [h2]
  simp [xC_sq]

/-- the semantic heart of the reduction -/
theorem inst_yes_iff {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    Yes (inst G M) 1 ↔ MaxCutYes G M := by
  obtain ⟨h1, h2, h3⟩ := eq_7_maxcut G
  have hcs := compare_step (inst G M) (inst_wf G M) 1
  unfold Yes
  rw [and_iff_right (inst_wf G M), hcs]
  have hv : (inst G M).v0 = 2 * M + 1 := rfl
  constructor
  · rintro ⟨C, hC⟩
    change (1 : ℚ) * (inst G M).v0 ≤ ∑ i, ∑ j, (inst G M).theta i j * xC C i * xC C j *
      ((inst G M).rhat i j - 1) at hC
    rw [objective, hv, one_mul] at hC
    by_cases h0 : (0 : Fin (ν + 1)) ∈ C
    · rw [h2 C h0] at hC
      have hx : xC C 0 = 1 := by simp [xC, h0]
      rw [hx] at hC
      refine ⟨nodesOf C, ?_⟩
      have : (M : ℚ) ≤ cutSize G (nodesOf C) := by linarith
      exact_mod_cast this
    · have hx : xC C 0 = 0 := by simp [xC, h0]
      rw [hx] at hC
      have hle := h1 C
      rw [h2 (insert 0 C) (Finset.mem_insert_self _ _)] at hle
      refine ⟨nodesOf (insert 0 C), ?_⟩
      have : (2 * M + 1 : ℚ) ≤ 2 * cutSize G (nodesOf (insert 0 C)) := by linarith
      have : 2 * M + 1 ≤ 2 * cutSize G (nodesOf (insert 0 C)) := by exact_mod_cast this
      omega
  · intro hy
    obtain ⟨C, hC⟩ := (h3 M).2 hy
    refine ⟨insert 0 C, ?_⟩
    change (1 : ℚ) * (inst G M).v0 ≤ ∑ i, ∑ j, (inst G M).theta i j * xC (insert 0 C) i *
      xC (insert 0 C) j * ((inst G M).rhat i j - 1)
    rw [objective, hv, one_mul]
    have hx : xC (insert 0 C) 0 = 1 := by simp [xC]
    rw [hx]
    have := h1 C
    linarith

end MCSem


set_option autoImplicit false

namespace MCSem

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

/-! ## the instance codes are uniquely decodable -/

def tb (b : Bool) : BSym := if b then BSym.one else BSym.zero

lemma tb_ne_sep (b : Bool) : tb b ≠ BSym.sep := by cases b <;> simp [tb]

lemma bits_split : ∀ {a b : List Bool} {r r' : List BSym},
    a.map tb ++ BSym.sep :: r = b.map tb ++ BSym.sep :: r' → a = b ∧ r = r' := by
  intro a
  induction a with
  | nil =>
    intro b r r' h
    cases b with
    | nil => simpa using h
    | cons y b => simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
        List.cons.injEq] at h; exact absurd h.1.symm (tb_ne_sep y)
  | cons x a ih =>
    intro b r r' h
    cases b with
    | nil => simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append,
        List.cons.injEq] at h; exact absurd h.1 (tb_ne_sep x)
    | cons y b =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hxy : x = y := by cases x <;> cases y <;> simp_all [tb]
      obtain ⟨h3, h4⟩ := ih h2
      exact ⟨by rw [hxy, h3], h4⟩

def bv : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bv l)

lemma bv_bits (n : ℕ) : bv (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bv]
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bv, ih]

lemma bits_inj {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  rw [← bv_bits a, h, bv_bits]

lemma encNat_eq_tb (k : ℕ) : encNat k = (Nat.bits k).map tb ++ [BSym.sep] := by
  simp [encNat, tb]

lemma encNat_app {a b : ℕ} {r r' : List BSym} (h : encNat a ++ r = encNat b ++ r') : a = b ∧ r = r' := by
  rw [encNat_eq_tb, encNat_eq_tb] at h
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := bits_split h
  exact ⟨bits_inj h1, h2⟩

lemma encNat_head (k : ℕ) (r : List BSym) : (encNat k ++ r).head? ≠ some BSym.minus := by
  rw [encNat_eq_tb]
  cases h : Nat.bits k with
  | nil => simp
  | cons b l => cases b <;> simp [tb]

lemma encInt_app {a b : ℤ} {r r' : List BSym} (h : encInt a ++ r = encInt b ++ r') : a = b ∧ r = r' := by
  unfold encInt at h
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp only [ha, hb, if_true, List.singleton_append, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := encNat_app (by simpa [List.append_assoc] using h)
    exact ⟨by omega, h2⟩
  · simp only [ha, hb, if_true, if_false, List.singleton_append, List.nil_append, List.cons_append] at h
    have := encNat_head b.natAbs r'
    rw [← h] at this; simp at this
  · simp only [ha, hb, if_true, if_false, List.singleton_append, List.nil_append, List.cons_append] at h
    have := encNat_head a.natAbs r
    rw [h] at this; simp at this
  · simp only [ha, hb, if_false, List.nil_append] at h
    obtain ⟨h1, h2⟩ := encNat_app (by simpa [List.append_assoc] using h)
    exact ⟨by omega, h2⟩

lemma encRat_app {p q : ℚ} {r r' : List BSym} (h : encRat p ++ r = encRat q ++ r') : p = q ∧ r = r' := by
  unfold encRat at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := encInt_app h
  obtain ⟨h3, h4⟩ := encNat_app h2
  exact ⟨Rat.ext h1 h3, h4⟩

lemma encRats_app : ∀ (l l' : List ℚ) (r r' : List BSym), l.length = l'.length →
    encRats l ++ r = encRats l' ++ r' → l = l' ∧ r = r' := by
  intro l
  induction l with
  | nil =>
    intro l' r r' hl h
    cases l' with
    | nil => simpa [encRats] using h
    | cons _ _ => simp at hl
  | cons x l ih =>
    intro l' r r' hl h
    cases l' with
    | nil => simp at hl
    | cons y l' =>
      simp only [encRats, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := encRat_app h
      obtain ⟨h3, h4⟩ := ih l' r r' (by simpa using hl) h2
      exact ⟨by rw [h1, h3], h4⟩

lemma flatMap_blocks {α β : Type} (f g : α → List β) (hlen : ∀ x, (f x).length = (g x).length) :
    ∀ (l : List α), l.flatMap f = l.flatMap g → ∀ x ∈ l, f x = g x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    intro h x hx
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (hlen a)
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact ih h2 x hx

/-- the pair weights in the order of the code -/
def pairs {n : ℕ} (V2 : Fin n → Fin n → ℚ) : List ℚ :=
  (List.finRange n).flatMap fun i => ((List.finRange n).filter (fun j => i < j)).map fun j => V2 i j

lemma pairs_length {n : ℕ} (V2 V2' : Fin n → Fin n → ℚ) : (pairs V2).length = (pairs V2').length := by
  simp [pairs, List.length_flatMap]

lemma pairs_inj {n : ℕ} {V2 V2' : Fin n → Fin n → ℚ} (h : pairs V2 = pairs V2') :
    ∀ i j, i < j → V2 i j = V2' i j := by
  intro i j hij
  have := flatMap_blocks _ _ (by intro x; simp) _ h i (List.mem_finRange i)
  have h2 := List.map_inj_left.1 this j (by simp [hij])
  exact h2

lemma code_eq' (I : Instance) (κ : ℚ) :
    code I κ = encNat I.n ++ (encRats (List.ofFn I.r) ++ (encRats (List.ofFn I.V1) ++
      (encRats (pairs I.V2) ++ (encRat I.v0 ++ encRat κ)))) := by
  simp [code, pairs, List.append_assoc]

lemma yes_of_code {I I' : Instance} {κ κ' : ℚ} (h : code I κ = code I' κ') : Yes I κ ↔ Yes I' κ' := by
  rw [code_eq', code_eq'] at h
  obtain ⟨n, r, V1, V2, v0⟩ := I
  obtain ⟨n', r', V1', V2', v0'⟩ := I'
  simp only at h
  obtain ⟨hn, h⟩ := encNat_app h
  subst hn
  obtain ⟨hr, h⟩ := encRats_app _ _ _ _ (by simp) h
  obtain ⟨hV1, h⟩ := encRats_app _ _ _ _ (by simp) h
  obtain ⟨hV2, h⟩ := encRats_app _ _ _ _ (pairs_length V2 V2') h
  have h' : encRat v0 ++ (encRat κ ++ []) = encRat v0' ++ (encRat κ' ++ []) := by simpa using h
  obtain ⟨hv0, h⟩ := encRat_app h'
  obtain ⟨hκ, -⟩ := encRat_app h
  have hr' := List.ofFn_injective hr
  have hV1' := List.ofFn_injective hV1
  have hV2' := pairs_inj hV2
  subst hr' hV1' hv0 hκ
  have hR2 : ∀ C : Finset (Fin n), Instance.R2 ⟨n, r, V1, V2, v0⟩ C = Instance.R2 ⟨n, r, V1, V2', v0⟩ C := by
    intro C
    unfold Instance.R2
    have hs : ∀ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), (r i + r j) * V2 i j =
        ∑ j ∈ C.filter (fun j => i < j), (r i + r j) * V2' i j := by
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      rw [hV2' i j (Finset.mem_filter.1 hj).2]
    have hs' : ∀ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), V2 i j =
        ∑ j ∈ C.filter (fun j => i < j), V2' i j := by
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      rw [hV2' i j (Finset.mem_filter.1 hj).2]
    simp only
    rw [Finset.sum_congr rfl hs, Finset.sum_congr rfl hs']
  unfold Yes Instance.WellFormed
  simp only [hR2]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h1, h2, fun i j hij => hV2' i j hij ▸ h3 i j hij, h4⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨⟨h1, h2, fun i j hij => (hV2' i j hij).symm ▸ h3 i j hij, h4⟩, h5⟩

lemma code_ne_nil (I : Instance) (κ : ℚ) : code I κ ≠ [] := by
  rw [code_eq']; simp [encNat]

end MCSem


set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness MCSem

/-- A Bool adjacency matrix is symmetric. -/
def IsSymm {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop := ∀ u v, adj u v = adj v u

/-! ## lists over `Fin n` versus `range n` -/

lemma ofFn_val {α : Type} (n : ℕ) (h : ℕ → α) :
    List.ofFn (fun v : Fin n => h v.val) = (List.range n).map h := by
  apply List.ext_getElem <;> simp

lemma finRange_flatMap {α : Type} (n : ℕ) (G : ℕ → List α) :
    (List.finRange n).flatMap (fun s => G s.val) = (List.range n).flatMap G := by
  rw [List.flatMap, List.flatMap, ← List.ofFn_eq_map, ofFn_val]

lemma finRange_flatMap' {α : Type} (n : ℕ) (G : Fin n → List α) (G' : ℕ → List α)
    (hG : ∀ s : Fin n, G s = G' s.val) :
    (List.finRange n).flatMap G = (List.range n).flatMap G' := by
  rw [← finRange_flatMap]; congr 1; funext s; exact hG s

lemma flat_ofFn {α : Type} (m n : ℕ) (f : ℕ → α) :
    (List.ofFn fun u : Fin m => List.ofFn fun v : Fin n => f (u * n + v)).flatten =
      (List.range (m * n)).map f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.coe_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    congr 1
    rw [ofFn_val n (fun v => f (m * n + v))]
    rfl

/-! ## adjacency matrices versus entry lists -/

def matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : List Bool :=
  (List.ofFn fun u => List.ofFn fun v => adj u v).flatten

def adjOf (n : ℕ) (bs : List Bool) : Fin n → Fin n → Bool := fun u v => adjB bs n u.val v.val

def mf {n : ℕ} (adj : Fin n → Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n * n then
    adj ⟨i / n, Nat.div_lt_of_lt_mul h⟩ ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
      rintro rfl; simp at h))⟩
  else false

lemma mf_eq {n : ℕ} (adj : Fin n → Fin n → Bool) (u v : Fin n) : mf adj (u.val * n + v.val) = adj u v := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact u.elim0)
  have h1 : u.val * n + v.val < n * n := by
    have := u.isLt; have := v.isLt; nlinarith
  unfold mf
  rw [dif_pos h1]
  congr 1
  · ext; simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, zero_add]
  · ext; simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]

lemma matBits_eq {n : ℕ} (adj : Fin n → Fin n → Bool) : matBits adj = (List.range (n * n)).map (mf adj) := by
  rw [← flat_ofFn]; unfold matBits
  exact congrArg List.flatten (congrArg List.ofFn (funext fun u =>
    congrArg List.ofFn (funext fun v => (mf_eq adj u v).symm)))

lemma length_matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : (matBits adj).length = n * n := by
  rw [matBits_eq]; simp

lemma adjOf_matBits {n : ℕ} (adj : Fin n → Fin n → Bool) : adjOf n (matBits adj) = adj := by
  funext u v
  have h1 : u.val * n + v.val < n * n := by
    have := u.isLt; have := v.isLt; nlinarith
  simp only [adjOf, adjB]
  rw [matBits_eq, List.getD_eq_getElem _ _ (by simpa using h1)]
  simp [mf_eq]

lemma matBits_adjOf (n : ℕ) (bs : List Bool) (hbs : bs.length = n * n) : matBits (adjOf n bs) = bs := by
  unfold matBits adjOf adjB
  rw [flat_ofFn n n (fun i => bs.getD i false)]
  apply List.ext_getElem
  · simp [hbs]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

lemma encNats_bits (bs : List Bool) :
    encNats (bs.map fun b => if b then 1 else 0) = bs.flatMap tokB := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, encNats_cons', ih, List.flatMap_cons]
    cases b
    · simp [encNat, tokB]
    · simp [encNat, tokB]


lemma flatMap_filter_map {α β : Type} (l : List α) (p : α → Bool) (g : α → List β) :
    (l.filter p).flatMap g = l.flatMap (fun x => if p x then g x else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

lemma symBad_iff (n : ℕ) (bs : List Bool) :
    symBad bs n (n * n) ↔ ¬ IsSymm (adjOf n bs) := by
  constructor
  · rintro ⟨i, hi, h⟩ hs
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    have := hs ⟨i / n, Nat.div_lt_of_lt_mul hi⟩ ⟨i % n, Nat.mod_lt _ hn⟩
    exact h this
  · intro hs
    simp only [IsSymm, not_forall] at hs
    obtain ⟨u, v, huv⟩ := hs
    obtain ⟨h1, h2⟩ := div_mod_aux n u.val v.val v.isLt
    refine ⟨u.val * n + v.val, by have := u.isLt; have := v.isLt; nlinarith, ?_⟩
    rw [h1, h2]; exact huv

/-! ## graphs versus matrices -/

open Classical in
noncomputable def adjG {ν : ℕ} (G : SimpleGraph (Fin ν)) : Fin ν → Fin ν → Bool :=
  fun u v => decide (G.Adj u v)

open Classical in
lemma maxCutCode_eq {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    maxCutCode G M = code ν (matBits (adjG G)) ++ enc (Nat.bits M) ++ [.sep] := by
  have hX : (List.ofFn fun i : Fin ν => List.ofFn fun j : Fin ν => if G.Adj i j then 1 else 0).flatten =
      (matBits (adjG G)).map (fun b => if b then 1 else 0) := by
    unfold matBits
    rw [List.map_flatten, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext u
    simp only [Function.comp_apply, List.map_ofFn]
    apply congrArg List.ofFn
    funext v
    simp [adjG]
  unfold maxCutCode code
  rw [hX, encNats_append', encNats_append', encNats_bits]
  simp [encNats, encNat_eq', List.append_assoc]

lemma not_symBad_G {ν : ℕ} (G : SimpleGraph (Fin ν)) : ¬ symBad (matBits (adjG G)) ν (ν * ν) := by
  rw [symBad_iff, adjOf_matBits, not_not]
  intro u v
  simp [adjG, SimpleGraph.adj_comm]

lemma not_diagBad_G {ν : ℕ} (G : SimpleGraph (Fin ν)) : ¬ diagBad (matBits (adjG G)) ν ν := by
  rintro ⟨s, hs, h⟩
  have := congrFun (congrFun (adjOf_matBits (adjG G)) ⟨s, hs⟩) ⟨s, hs⟩
  simp only [adjOf] at this
  rw [this] at h
  simp [adjG] at h

def graphOf (n : ℕ) (bs : List Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => adjOf n bs u v = true)

lemma graphOf_adj (n : ℕ) (bs : List Bool) (hsym : ¬ symBad bs n (n * n)) (hdg : ¬ diagBad bs n n)
    (u v : Fin n) : (graphOf n bs).Adj u v ↔ adjOf n bs u v = true := by
  rw [symBad_iff, not_not] at hsym
  simp only [graphOf, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rw [hsym]; exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact hdg ⟨u.val, u.isLt, h⟩

lemma adjG_graphOf (n : ℕ) (bs : List Bool) (hsym : ¬ symBad bs n (n * n)) (hdg : ¬ diagBad bs n n) :
    adjG (graphOf n bs) = adjOf n bs := by
  funext u v
  have := graphOf_adj n bs hsym hdg u v
  simp only [adjG]
  by_cases h : adjOf n bs u v = true
  · simp [this.2 h, h]
  · have : ¬ (graphOf n bs).Adj u v := fun h' => h ((graphOf_adj n bs hsym hdg u v).1 h')
    simp [this]; simpa using h

/-! ## the instance code equals the machine output -/

lemma encRats_cons (q : ℚ) (l : List ℚ) : encRats (q :: l) = encRat q ++ encRats l := by
  simp [encRats]

lemma encRats_append (l l' : List ℚ) : encRats (l ++ l') = encRats l ++ encRats l' := by
  simp [encRats]

lemma encRats_replicate (k : ℕ) (q : ℚ) : encRats (List.replicate k q) = (List.replicate k (encRat q)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, encRats_cons, ih, List.replicate_succ, List.flatten_cons]

lemma encRat_natCast (k : ℕ) : encRat (k : ℚ) = encNat k ++ [.one, .sep] := by
  simp only [encRat, encInt, Rat.num_natCast, Rat.den_natCast]
  have : ¬ ((k : ℤ) < 0) := by omega
  simp [this, encNat]

lemma encRat_l114 : encRat (11 / 4 : ℚ) = l114 := by decide +kernel
lemma encRat_l14 : encRat (1 / 4 : ℚ) = l14 := by decide +kernel
lemma encRat_l47 : encRat (4 / 7 : ℚ) = l47 := by decide +kernel
lemma encRat_l0 : encRat (0 : ℚ) = l0 := by decide +kernel
lemma encRat_l8 : encRat (8 : ℚ) = l8 := by decide +kernel
lemma encRat_lk : encRat (1 : ℚ) = lk := by decide +kernel

lemma encRat_v0 (M : ℕ) : encRat (2 * (M : ℚ) + 1) = (BSym.one :: enc (Nat.bits M) ++ [.sep, .one, .sep]) := by
  have h : (2 * (M : ℚ) + 1) = ((2 * M + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [h, encRat_natCast, encNat_eq']
  have hb : Nat.bits (2 * M + 1) = true :: Nat.bits M := by
    have := Nat.bits_append_bit M true (fun _ => rfl)
    simpa [Nat.bit] using this
  rw [hb]; simp

lemma len_filter_range (q : ℕ → Bool) (t : ℕ) :
    ((List.range t).filter q).length = ∑ x ∈ Finset.range t, (if q x then 1 else 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : q t <;> simp [h]

lemma nodeDeg_eq {ν : ℕ} (G : SimpleGraph (Fin ν)) (j : Fin ν) :
    nodeDeg G j = rowCnt (matBits (adjG G)) ν j ν := by
  classical
  have hadj : ∀ k : Fin ν, adjB (matBits (adjG G)) ν j k.val = decide (G.Adj j k) := by
    intro k
    have := congrFun (congrFun (adjOf_matBits (adjG G)) j) k
    simp only [adjOf] at this
    rw [this]; simp [adjG]
  unfold nodeDeg rowCnt
  rw [len_filter_range, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun x => if adjB (matBits (adjG G)) ν j x then 1 else 0)]
  apply Finset.sum_congr rfl
  intro k _
  rw [hadj k]
  by_cases h : G.Adj j k <;> simp [h]

lemma finRange_succ_filter0 (ν : ℕ) :
    ((0 : Fin (ν + 1)) :: (List.finRange ν).map Fin.succ).filter (fun j => (0 : Fin (ν + 1)) < j) =
      (List.finRange ν).map Fin.succ := by
  rw [List.filter_cons]
  simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, if_false]
  rw [List.filter_map]
  have : ((fun j => decide ((0 : Fin (ν + 1)) < j)) ∘ Fin.succ) = fun _ => true := by
    funext j; simp [Fin.succ_pos]
  rw [this, List.filter_true]

lemma finRange_succ_filterS (ν : ℕ) (i : Fin ν) :
    ((0 : Fin (ν + 1)) :: (List.finRange ν).map Fin.succ).filter (fun j => i.succ < j) =
      ((List.finRange ν).filter (fun j => i < j)).map Fin.succ := by
  rw [List.filter_cons]
  have h0 : ¬ (i.succ < (0 : Fin (ν + 1))) := by simp
  simp only [h0, decide_false, Bool.false_eq_true, if_false]
  rw [List.filter_map]
  congr 2
  funext j; simp [Fin.succ_lt_succ_iff]

lemma pairs_eq {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    encRats (pairs (inst G M).V2) =
      degBlock (matBits (adjG G)) ν ν ++ triBlock (matBits (adjG G)) ν ν := by
  classical
  set bs := matBits (adjG G) with hbs
  have hadj : ∀ s t : Fin ν, adjB bs ν s.val t.val = decide (G.Adj s t) := by
    intro s t
    have := congrFun (congrFun (adjOf_matBits (adjG G)) s) t
    simp only [adjOf] at this
    rw [hbs, this]; simp [adjG]
  show encRats (pairs (V2f G)) = _
  unfold pairs
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, encRats_append]
  congr 1
  · rw [finRange_succ_filter0, List.map_map]
    unfold encRats degBlock
    rw [List.flatMap_map]
    apply finRange_flatMap'
    intro j
    simp only [Function.comp_apply, V2f, Fin.cases_zero, Fin.cases_succ]
    rw [encRat_natCast, nodeDeg_eq]
  · unfold encRats triBlock
    rw [List.flatMap_assoc]
    apply finRange_flatMap'
    intro s
    rw [finRange_succ_filterS, List.map_map, List.flatMap_map, triRow, flatMap_filter_map]
    apply finRange_flatMap'
    intro t
    simp only [Function.comp_apply, V2f, Fin.cases_succ, triEnt, Fin.lt_def]
    by_cases hst : s.val < t.val
    · simp only [hst, decide_true, if_true, hadj s t]
      by_cases h : G.Adj s t
      · simp [h, encRat_l8]
      · simp [h, encRat_l0]
    · simp [hst]

theorem P6_eq {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    P6 ν (matBits (adjG G)) (enc (Nat.bits M)) = MultiPurchase.Hardness.code (inst G M) 1 := by
  rw [code_eq', pairs_eq]
  have hr : List.ofFn (inst G M).r = (11 / 4 : ℚ) :: List.replicate ν (1 / 4) := by
    show List.ofFn (Fin.cases (11 / 4 : ℚ) (fun _ => 1 / 4) : Fin (ν + 1) → ℚ) = _
    rw [List.ofFn_succ]; simp
  have hV1 : List.ofFn (inst G M).V1 = (4 / 7 : ℚ) :: List.replicate ν 0 := by
    show List.ofFn (Fin.cases (4 / 7 : ℚ) (fun _ => 0) : Fin (ν + 1) → ℚ) = _
    rw [List.ofFn_succ]; simp
  rw [hr, hV1, encRats_cons, encRats_cons, encRats_replicate, encRats_replicate, encRat_l114,
    encRat_l14, encRat_l47, encRat_l0]
  have hv : (inst G M).v0 = 2 * (M : ℚ) + 1 := rfl
  have hn : (inst G M).n = ν + 1 := rfl
  rw [hv, hn, encRat_v0, encRat_lk]
  simp [P6, P5, P4, P3, P2, P1, triRow, List.append_assoc]

end MCRed


set_option autoImplicit false

namespace MCRed

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness MCSem

theorem maxCut_red : PolyReducible maxCutLang bundleLang := by
  refine ⟨fR, fR_poly, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨ν, G, M, hy, rfl⟩
    have hbs := length_matBits (adjG G)
    have hVS : VS (maxCutCode G M) (ν, matBits (adjG G), M) := ⟨hbs, maxCutCode_eq G M⟩
    have hnb : ¬ (symBad (matBits (adjG G)) ν (ν * ν) ∨ diagBad (matBits (adjG G)) ν ν) := by
      rintro (h | h)
      · exact not_symBad_G G h
      · exact not_diagBad_G G h
    rw [fR_valid hVS, gOut, if_neg hnb, P6_eq]
    exact ⟨inst G M, 1, (inst_yes_iff G M).2 hy, rfl⟩
  · rintro ⟨I, κ, hI, hw⟩
    by_cases hv : ∃ p, VS w p
    · obtain ⟨⟨n, bs, M⟩, hp⟩ := hv
      rw [fR_valid hp, gOut] at hw
      split_ifs at hw with hbad
      · exact absurd hw.symm (code_ne_nil I κ)
      · have hs : ¬ symBad bs n (n * n) := fun h => hbad (Or.inl h)
        have hd : ¬ diagBad bs n n := fun h => hbad (Or.inr h)
        have hm : matBits (adjG (graphOf n bs)) = bs := by
          rw [adjG_graphOf n bs hs hd, matBits_adjOf n bs hp.1]
        rw [← hm, P6_eq] at hw
        have hy := (yes_of_code hw).2 hI
        refine ⟨n, graphOf n bs, M, (inst_yes_iff _ M).1 hy, ?_⟩
        rw [maxCutCode_eq, hm]; exact hp.2
    · rw [fR_invalid (fun p hp => hv ⟨p, hp⟩)] at hw
      exact absurd hw.symm (code_ne_nil I κ)

end MCRed

theorem solution : CookPvsNP.PolyReducible ProjSchedTW.Complexity.maxCutLang
    MultiPurchase.Hardness.bundleLang :=
  MCRed.maxCut_red
