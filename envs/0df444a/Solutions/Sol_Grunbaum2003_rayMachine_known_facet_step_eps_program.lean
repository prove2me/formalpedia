-- Prove2me | solution 1 for Grunbaum2003.rayMachine_known_facet_step_eps_program
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:15:05.64402+00:00
-- url     : https://prove2.me/submissions/2d6bd33f-2f8f-4826-8b64-da8a28268be9

import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Grunbaum2003.RayFieldExpr

inductive BinOp where
  | add | sub | mul | div
  deriving DecidableEq

def BinOp.eval : BinOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

def BinOp.Valid : BinOp → ℝ → Prop
  | .div, y => y ≠ 0
  | _, _ => True

def BinOp.instruction (op : BinOp) (dst left right : ℤ) (next : ℕ) : RayInstruction :=
  match op with
  | .add => .add dst left right next
  | .sub => .sub dst left right next
  | .mul => .mul dst left right next
  | .div => .div dst left right next

/-- A finite field expression. The four arithmetic constructors are supplied
as named abbreviations below; compilation is independent of all real input data. -/
inductive Expr where
  | const (q : ℚ)
  | read (address : ℤ)
  | bin (op : BinOp) (left right : Expr)

def Expr.add (a b : Expr) : Expr := .bin .add a b
def Expr.sub (a b : Expr) : Expr := .bin .sub a b
def Expr.mul (a b : Expr) : Expr := .bin .mul a b
def Expr.div (a b : Expr) : Expr := .bin .div a b

def Expr.eval (tape : ℤ → ℝ) : Expr → ℝ
  | .const q => q
  | .read address => tape address
  | .bin op a b => op.eval (a.eval tape) (b.eval tape)

/-- Every guard is an actual denominator value in the original input tape. -/
def Expr.Valid (tape : ℤ → ℝ) : Expr → Prop
  | .const _ => True
  | .read _ => True
  | .bin op a b => a.Valid tape ∧ b.Valid tape ∧ op.Valid (b.eval tape)

def Expr.reads : Expr → Finset ℤ
  | .const _ => ∅
  | .read address => {address}
  | .bin _ a b => a.reads ∪ b.reads

/-- Leaves use one scratch cell; binary children use adjacent disjoint regions. -/
def Expr.slots : Expr → ℕ
  | .const _ => 1
  | .read _ => 1
  | .bin _ a b => a.slots + b.slots

def Expr.steps : Expr → ℕ
  | .const _ => 1
  | .read _ => 2
  | .bin _ a b => a.steps + b.steps + 1

def Expr.emit : (e : Expr) → (base : ℤ) → (pc : ℕ) → List RayInstruction
  | .const q, base, pc => [.constant base q (pc + 1)]
  | .read address, base, pc =>
      [.constant base 0 (pc + 1), .add base address base (pc + 2)]
  | .bin op a b, base, pc =>
      a.emit base pc ++
        (b.emit (base + (a.slots : ℤ)) (pc + a.steps) ++
          [op.instruction base base (base + (a.slots : ℤ)) (pc + (a.steps + b.steps + 1))])

theorem Expr.slots_pos (e : Expr) : 0 < e.slots := by
  induction e with
  | const _ => exact Nat.zero_lt_one
  | read _ => exact Nat.zero_lt_one
  | bin _ a b ha hb =>
    change 0 < a.slots + b.slots
    omega

theorem Expr.steps_pos (e : Expr) : 0 < e.steps := by
  cases e <;> simp only [Expr.steps] <;> omega

theorem Expr.length_emit (e : Expr) (base : ℤ) (pc : ℕ) :
    (e.emit base pc).length = e.steps := by
  induction e generalizing base pc with
  | const _ => rfl
  | read _ => rfl
  | bin op a b ha hb =>
    simp only [Expr.emit, List.length_append, ha, hb, List.length_cons,
      List.length_nil, Expr.steps]
    omega

theorem Expr.eval_eq_of_reads_eq (e : Expr) (source target : ℤ → ℝ)
    (h : ∀ address ∈ e.reads, source address = target address) :
    e.eval source = e.eval target := by
  induction e with
  | const _ => rfl
  | read address => exact h address (Finset.mem_singleton_self address)
  | bin op a b ha hb =>
    change op.eval (a.eval source) (b.eval source) = op.eval (a.eval target) (b.eval target)
    rw [ha (fun address hmem => h address (Finset.mem_union.mpr (Or.inl hmem))),
      hb (fun address hmem => h address (Finset.mem_union.mpr (Or.inr hmem)))]

theorem run_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

/-- A literal finite body occurs in an ambient program at this absolute label. -/
def CodeAt (program : List RayInstruction) (pc : ℕ) (body : List RayInstruction) : Prop :=
  ∀ i, i < body.length → program[pc + i]? = body[i]?

theorem CodeAt.left {program left right : List RayInstruction} {pc : ℕ}
    (h : CodeAt program pc (left ++ right)) : CodeAt program pc left := by
  intro i hi
  rw [h i (by simpa only [List.length_append] using Nat.lt_add_right right.length hi)]
  exact List.getElem?_append_left hi

theorem CodeAt.right {program left right : List RayInstruction} {pc : ℕ}
    (h : CodeAt program pc (left ++ right)) :
    CodeAt program (pc + left.length) right := by
  intro i hi
  have hi' : left.length + i < (left ++ right).length := by
    simpa only [List.length_append] using Nat.add_lt_add_left hi left.length
  have hfetch := h (left.length + i) hi'
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hfetch
  simpa only [Nat.add_assoc] using hfetch

theorem CodeAt.singleton {program : List RayInstruction} {inst : RayInstruction} {pc : ℕ}
    (h : CodeAt program pc [inst]) : program[pc]? = some inst := by
  simpa only [Nat.add_zero, List.getElem?_cons_zero] using h 0 Nat.zero_lt_one

theorem CodeAt.emit_append (e : Expr) (base : ℤ) (suffix : List RayInstruction) :
    CodeAt (e.emit base 0 ++ suffix) 0 (e.emit base 0) := by
  intro i hi
  simpa only [Nat.zero_add] using (List.getElem?_append_left (l₂ := suffix) hi)

/-- One actual scalar instruction, with exactly the original division guard. -/
theorem binOp_step {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (op : BinOp) (dst left right : ℤ) (next : ℕ) (x y : ℝ)
    (c : RayConfiguration) (hhead : c.head = 0)
    (hfetch : program[c.pc]? = some (op.instruction dst left right next))
    (hleft : c.tape left = x) (hright : c.tape right = y) (hvalid : op.Valid y) :
    rayMachineStep program oracle c =
      some {c with pc := next, tape := Function.update c.tape dst (op.eval x y)} := by
  cases op with
  | add => simp only [BinOp.instruction] at hfetch
           simp only [rayMachineStep, hfetch, hhead, zero_add, hleft, hright, BinOp.eval]
  | sub => simp only [BinOp.instruction] at hfetch
           simp only [rayMachineStep, hfetch, hhead, zero_add, hleft, hright, BinOp.eval]
  | mul => simp only [BinOp.instruction] at hfetch
           simp only [rayMachineStep, hfetch, hhead, zero_add, hleft, hright, BinOp.eval]
  | div =>
    have hy : y ≠ 0 := hvalid
    simp only [BinOp.instruction] at hfetch
    simp only [rayMachineStep, hfetch, hhead, zero_add, hleft, hright, if_neg hy, BinOp.eval]

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003.RayFieldExpr

/-- The scratch interval lies strictly above every cell read by this expression. -/
def Expr.ReadFresh (e : Expr) (base : ℤ) : Prop :=
  ∀ address ∈ e.reads, address < base

/-- A syntactic fresh address. Computing it never inspects the real input tape. -/
def Expr.readBound : Expr → ℤ
  | .const _ => 0
  | .read address => address + 1
  | .bin _ a b => max a.readBound b.readBound

theorem Expr.readFresh_readBound (e : Expr) : e.ReadFresh e.readBound := by
  induction e with
  | const _ =>
    intro address hmem
    simp only [Expr.reads, Finset.notMem_empty] at hmem
  | read a =>
    intro address hmem
    have heq : address = a := Finset.mem_singleton.mp hmem
    subst address
    change a < a + 1
    omega
  | bin op a b iha ihb =>
    intro address hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact lt_of_lt_of_le (iha address hmem) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihb address hmem) (le_max_right _ _)

/-- Explicit result of executing only the emitted arithmetic body, before its exit. -/
theorem Expr.emit_correct (e : Expr) {d : ℕ}
    (program : List RayInstruction) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (source : ℤ → ℝ) (base : ℤ) (pc : ℕ) (c : RayConfiguration)
    (hpc : c.pc = pc) (hhead : c.head = 0)
    (hcode : CodeAt program pc (e.emit base pc))
    (hfresh : e.ReadFresh base)
    (hagree : ∀ address ∈ e.reads, c.tape address = source address)
    (hvalid : e.Valid source) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle e.steps c = some c' ∧
      c'.pc = pc + e.steps ∧ c'.head = 0 ∧ c'.queries = c.queries ∧
      c'.tape base = e.eval source ∧
      ∀ z : ℤ, (z < base ∨ base + (e.slots : ℤ) ≤ z) → c'.tape z = c.tape z := by
  classical
  induction e generalizing base pc c with
  | const q =>
    let c' : RayConfiguration :=
      {c with pc := pc + 1, tape := Function.update c.tape base (q : ℝ)}
    have hfetch : program[c.pc]? = some (.constant base q (pc + 1)) := by
      rw [hpc]
      exact hcode.singleton
    have hstep : rayMachineStep program oracle c = some c' := by
      simp only [rayMachineStep, hfetch, hhead, zero_add, c']
    refine ⟨c', ?_, rfl, hhead, rfl, ?_, ?_⟩
    · simp only [Expr.steps, rayMachineRun, hstep, Option.bind_some]
    · exact Function.update_self _ _ _
    · intro z hz
      have hne : z ≠ base := by
        change z < base ∨ base + (1 : ℤ) ≤ z at hz
        omega
      exact Function.update_of_ne hne _ _
  | read address =>
    have hlt : address < base := hfresh address (Finset.mem_singleton_self _)
    have hne : address ≠ base := ne_of_lt hlt
    have hread : c.tape address = source address :=
      hagree address (Finset.mem_singleton_self _)
    let c₁ : RayConfiguration :=
      {c with pc := pc + 1, tape := Function.update c.tape base 0}
    let c₂ : RayConfiguration :=
      {c₁ with pc := pc + 2, tape := Function.update c₁.tape base (source address)}
    have hfetch₁ : program[c.pc]? = some (.constant base 0 (pc + 1)) := by
      have h := hcode 0 (by simp [Expr.emit])
      simpa only [hpc, Nat.add_zero, Expr.emit, List.getElem?_cons_zero] using h
    have hfetch₂ : program[c₁.pc]? = some (.add base address base (pc + 2)) := by
      have h := hcode 1 (by simp [Expr.emit])
      simpa only [c₁, Expr.emit, List.getElem?_cons_succ, List.getElem?_cons_zero] using h
    have hstep₁ : rayMachineStep program oracle c = some c₁ := by
      simp only [rayMachineStep, hfetch₁, hhead, zero_add, Rat.cast_zero, c₁]
    have hstep₂ : rayMachineStep program oracle c₁ = some c₂ := by
      simp only [rayMachineStep, hfetch₂, c₁, hhead, zero_add,
        Function.update_of_ne hne, Function.update_self, hread, add_zero, c₂]
    refine ⟨c₂, ?_, rfl, hhead, rfl, ?_, ?_⟩
    · simp only [Expr.steps, rayMachineRun, hstep₁, hstep₂, Option.bind_some]
    · exact Function.update_self _ _ _
    · intro z hz
      have hn : z ≠ base := by
        change z < base ∨ base + (1 : ℤ) ≤ z at hz
        omega
      simp only [c₂, c₁, Function.update_of_ne hn]
  | bin op a b iha ihb =>
    rcases hvalid with ⟨hvalidA, hvalidB, hvalidOp⟩
    have hfreshA : a.ReadFresh base :=
      fun address hmem => hfresh address (Finset.mem_union.mpr (Or.inl hmem))
    have hfreshB : b.ReadFresh (base + (a.slots : ℤ)) := by
      intro address hmem
      have h := hfresh address (Finset.mem_union.mpr (Or.inr hmem))
      have ha := a.slots_pos
      omega
    have hagreeA : ∀ address ∈ a.reads, c.tape address = source address :=
      fun address hmem => hagree address (Finset.mem_union.mpr (Or.inl hmem))
    have hcodeA : CodeAt program pc (a.emit base pc) := hcode.left
    obtain ⟨c₁, hrunA, hpcA, hheadA, hqA, hvalueA, hframeA⟩ :=
      iha base pc c hpc hhead hcodeA hfreshA hagreeA hvalidA
    have hcodeRest : CodeAt program (pc + a.steps)
        (b.emit (base + (a.slots : ℤ)) (pc + a.steps) ++
          [op.instruction base base (base + (a.slots : ℤ))
            (pc + (a.steps + b.steps + 1))]) := by
      simpa only [a.length_emit] using hcode.right
    have hcodeB : CodeAt program (pc + a.steps)
        (b.emit (base + (a.slots : ℤ)) (pc + a.steps)) := hcodeRest.left
    have hagreeB : ∀ address ∈ b.reads, c₁.tape address = source address := by
      intro address hmem
      have hlt : address < base :=
        hfresh address (Finset.mem_union.mpr (Or.inr hmem))
      exact (hframeA address (Or.inl hlt)).trans
        (hagree address (Finset.mem_union.mpr (Or.inr hmem)))
    obtain ⟨c₂, hrunB, hpcB, hheadB, hqB, hvalueB, hframeB⟩ :=
      ihb (base + (a.slots : ℤ)) (pc + a.steps) c₁
        hpcA hheadA hcodeB hfreshB hagreeB hvalidB
    have hvalueA' : c₂.tape base = a.eval source := by
      have hlt : base < base + (a.slots : ℤ) := by
        have ha := a.slots_pos
        omega
      exact (hframeB base (Or.inl hlt)).trans hvalueA
    have hfetch : program[c₂.pc]? = some
        (op.instruction base base (base + (a.slots : ℤ))
          (pc + (a.steps + b.steps + 1))) := by
      rw [hpcB]
      have hlast := hcodeRest.right.singleton
      simpa only [b.length_emit] using hlast
    let c₃ : RayConfiguration :=
      { c₂ with
        pc := pc + (a.steps + b.steps + 1)
        tape := Function.update c₂.tape base (op.eval (a.eval source) (b.eval source)) }
    have hstep : rayMachineStep program oracle c₂ = some c₃ := by
      exact binOp_step program oracle op base base (base + (a.slots : ℤ))
        (pc + (a.steps + b.steps + 1)) (a.eval source) (b.eval source)
        c₂ hheadB hfetch hvalueA' hvalueB hvalidOp
    refine ⟨c₃, ?_, rfl, hheadB, hqB.trans hqA, ?_, ?_⟩
    · change rayMachineRun program oracle (a.steps + b.steps + 1) c = some c₃
      rw [run_add program oracle (a.steps + b.steps) 1,
        run_add program oracle a.steps b.steps, hrunA, Option.bind_some,
        hrunB, Option.bind_some]
      simp only [rayMachineRun, hstep, Option.bind_some]
    · exact Function.update_self _ _ _
    · intro z hz
      have hne : z ≠ base := by
        have ha := a.slots_pos
        have hb := b.slots_pos
        simp only [Expr.slots, Nat.cast_add] at hz
        omega
      change Function.update c₂.tape base _ z = c.tape z
      rw [Function.update_of_ne hne]
      have hzA : z < base ∨ base + (a.slots : ℤ) ≤ z := by
        simp only [Expr.slots, Nat.cast_add] at hz
        omega
      have hzB : z < base + (a.slots : ℤ) ∨
          base + (a.slots : ℤ) + (b.slots : ℤ) ≤ z := by
        simp only [Expr.slots, Nat.cast_add] at hz
        omega
      exact (hframeB z hzB).trans (hframeA z hzA)

theorem Expr.standalone_correct (e : Expr) {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ) (base : ℤ)
    (hfresh : e.ReadFresh base) (hvalid : e.Valid source) (q : ℕ) :
    ∃ c' : RayConfiguration,
      rayMachineRun (e.emit base 0 ++ [.halt]) oracle e.steps
        ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = e.steps ∧ c'.head = 0 ∧ c'.queries = q ∧
      c'.tape base = e.eval source ∧
      (∀ z : ℤ, (z < base ∨ base + (e.slots : ℤ) ≤ z) → c'.tape z = source z) ∧
      (e.emit base 0 ++ [.halt])[c'.pc]? = some .halt := by
  obtain ⟨c', hrun, hpc, hhead, hq, hvalue, hframe⟩ :=
    e.emit_correct (e.emit base 0 ++ [.halt]) oracle source base 0
      ⟨0, 0, source, q⟩ rfl rfl (CodeAt.emit_append e base [.halt])
      hfresh (fun _ _ => rfl) hvalid
  refine ⟨c', hrun, ?_, hhead, hq, hvalue, hframe, ?_⟩
  · simpa only [Nat.zero_add] using hpc
  · rw [hpc, Nat.zero_add]
    have hlen := e.length_emit base 0
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003.RayFieldExpr

/-- Static finite sum of `n` field expressions. -/
def Expr.sumFin : {n : ℕ} → (Fin n → Expr) → Expr
  | 0, _ => .const 0
  | _ + 1, f => Expr.add (f 0) (Expr.sumFin (fun i => f i.succ))

theorem Expr.eval_sumFin (tape : ℤ → ℝ) {n : ℕ} (f : Fin n → Expr) :
    (Expr.sumFin f).eval tape = ∑ i : Fin n, (f i).eval tape := by
  induction n with
  | zero =>
    simp only [Expr.sumFin, Expr.eval, Rat.cast_zero, Fin.sum_univ_zero]
  | succ n ih =>
    simp only [Expr.sumFin, Expr.add, Expr.eval, BinOp.eval, ih, Fin.sum_univ_succ]

theorem Expr.valid_sumFin (tape : ℤ → ℝ) {n : ℕ} (f : Fin n → Expr)
    (h : ∀ i : Fin n, (f i).Valid tape) :
    (Expr.sumFin f).Valid tape := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨h 0, ih (fun i => f i.succ) (fun i => h i.succ), trivial⟩

/-- Static finite product of `n` field expressions. -/
def Expr.prodFin : {n : ℕ} → (Fin n → Expr) → Expr
  | 0, _ => .const 1
  | _ + 1, f => Expr.mul (f 0) (Expr.prodFin (fun i => f i.succ))

theorem Expr.eval_prodFin (tape : ℤ → ℝ) {n : ℕ} (f : Fin n → Expr) :
    (Expr.prodFin f).eval tape = ∏ i : Fin n, (f i).eval tape := by
  induction n with
  | zero =>
    simp only [Expr.prodFin, Expr.eval, Rat.cast_one, Fin.prod_univ_zero]
  | succ n ih =>
    simp only [Expr.prodFin, Expr.mul, Expr.eval, BinOp.eval, ih, Fin.prod_univ_succ]

theorem Expr.valid_prodFin (tape : ℤ → ℝ) {n : ℕ} (f : Fin n → Expr)
    (h : ∀ i : Fin n, (f i).Valid tape) :
    (Expr.prodFin f).Valid tape := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨h 0, ih (fun i => f i.succ) (fun i => h i.succ), trivial⟩

/-- Static dot-product expression for two `d`-vectors stored at `aBase` and `xBase`. -/
def Expr.dot (d : ℕ) (aBase xBase : ℤ) : Expr :=
  Expr.sumFin (fun i : Fin d =>
    Expr.mul (.read (aBase + (i.val : ℤ))) (.read (xBase + (i.val : ℤ))))

theorem Expr.eval_dot (tape : ℤ → ℝ) (d : ℕ) (aBase xBase : ℤ) :
    (Expr.dot d aBase xBase).eval tape =
      ∑ i : Fin d, tape (aBase + (i.val : ℤ)) * tape (xBase + (i.val : ℤ)) := by
  rw [Expr.dot, Expr.eval_sumFin]
  rfl

theorem Expr.valid_dot (tape : ℤ → ℝ) (d : ℕ) (aBase xBase : ℤ) :
    (Expr.dot d aBase xBase).Valid tape := by
  apply Expr.valid_sumFin
  intro _
  exact ⟨trivial, trivial, trivial⟩

/-- Row evaluation expression for the `j`-th stored `d`-vector row at `rowBase + j * d`
against a `d`-vector at `xBase`. -/
def Expr.rowDot (d : ℕ) (rowBase : ℤ) (j : ℕ) (xBase : ℤ) : Expr :=
  Expr.dot d (rowBase + (j : ℤ) * (d : ℤ)) xBase

theorem Expr.eval_rowDot (tape : ℤ → ℝ) (d : ℕ) (rowBase : ℤ) (j : ℕ) (xBase : ℤ) :
    (Expr.rowDot d rowBase j xBase).eval tape =
      ∑ i : Fin d, tape (rowBase + (j : ℤ) * (d : ℤ) + (i.val : ℤ)) * tape (xBase + (i.val : ℤ)) :=
  Expr.eval_dot tape d (rowBase + (j : ℤ) * (d : ℤ)) xBase

theorem Expr.valid_rowDot (tape : ℤ → ℝ) (d : ℕ) (rowBase : ℤ) (j : ℕ) (xBase : ℤ) :
    (Expr.rowDot d rowBase j xBase).Valid tape :=
  Expr.valid_dot tape d (rowBase + (j : ℤ) * (d : ℤ)) xBase

/-- Static expression for a single known-facet slack factor `(1 - L_j(p)) / (1 + (1 - L_j(p)))`. -/
def Expr.slackFactor (d : ℕ) (rowBase pBase : ℤ) (j : ℕ) : Expr :=
  let s := Expr.sub (.const 1) (Expr.rowDot d rowBase j pBase)
  Expr.div s (Expr.add (.const 1) s)

theorem Expr.eval_slackFactor (tape : ℤ → ℝ) (d : ℕ) (rowBase pBase : ℤ) (j : ℕ) :
    (Expr.slackFactor d rowBase pBase j).eval tape =
      (1 - (Expr.rowDot d rowBase j pBase).eval tape) /
        (1 + (1 - (Expr.rowDot d rowBase j pBase).eval tape)) := by
  simp only [Expr.slackFactor, Expr.div, Expr.add, Expr.sub, Expr.eval, BinOp.eval, Rat.cast_one]

theorem Expr.valid_slackFactor (tape : ℤ → ℝ) (d : ℕ) (rowBase pBase : ℤ) (j : ℕ)
    (hstrict : (Expr.rowDot d rowBase j pBase).eval tape < 1) :
    (Expr.slackFactor d rowBase pBase j).Valid tape := by
  have hvalidDot : (Expr.rowDot d rowBase j pBase).Valid tape :=
    Expr.valid_rowDot tape d rowBase j pBase
  have hsValid : (Expr.sub (.const 1) (Expr.rowDot d rowBase j pBase)).Valid tape :=
    ⟨trivial, hvalidDot, trivial⟩
  refine ⟨hsValid, ⟨trivial, hsValid, trivial⟩, ?_⟩
  simp only [BinOp.Valid, Expr.add, Expr.sub, Expr.eval, BinOp.eval, Rat.cast_one]
  linarith

/-- Static expression for the product of known-facet slack factors
`δ = ∏ j : Fin k, (1 - L_j(p)) / (1 + (1 - L_j(p)))`. -/
def Expr.slackProd (d k : ℕ) (rowBase pBase : ℤ) : Expr :=
  Expr.prodFin (fun j : Fin k => Expr.slackFactor d rowBase pBase j.val)

theorem Expr.eval_slackProd (tape : ℤ → ℝ) (d k : ℕ) (rowBase pBase : ℤ) :
    (Expr.slackProd d k rowBase pBase).eval tape =
      ∏ j : Fin k,
        (1 - (Expr.rowDot d rowBase j.val pBase).eval tape) /
          (1 + (1 - (Expr.rowDot d rowBase j.val pBase).eval tape)) := by
  rw [Expr.slackProd, Expr.eval_prodFin]
  apply Finset.prod_congr rfl
  intro j _
  exact Expr.eval_slackFactor tape d rowBase pBase j.val

theorem Expr.valid_slackProd (tape : ℤ → ℝ) (d k : ℕ) (rowBase pBase : ℤ)
    (hstrict : ∀ j : Fin k, (Expr.rowDot d rowBase j.val pBase).eval tape < 1) :
    (Expr.slackProd d k rowBase pBase).Valid tape :=
  Expr.valid_prodFin tape _ (fun j => Expr.valid_slackFactor tape d rowBase pBase j.val (hstrict j))

/-- Static expression for the direction square-sum bound `M = 1 + ∑ j : Fin k, (L_j(u))^2`. -/
def Expr.dirSqSum (d k : ℕ) (rowBase uBase : ℤ) : Expr :=
  Expr.add (.const 1)
    (Expr.sumFin (fun j : Fin k =>
      let v := Expr.rowDot d rowBase j.val uBase
      Expr.mul v v))

theorem Expr.eval_dirSqSum (tape : ℤ → ℝ) (d k : ℕ) (rowBase uBase : ℤ) :
    (Expr.dirSqSum d k rowBase uBase).eval tape =
      1 + ∑ j : Fin k, ((Expr.rowDot d rowBase j.val uBase).eval tape) ^ 2 := by
  simp only [Expr.dirSqSum, Expr.add, Expr.eval, BinOp.eval, Rat.cast_one, Expr.eval_sumFin]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Expr.mul, Expr.eval, BinOp.eval, sq]

theorem Expr.valid_dirSqSum (tape : ℤ → ℝ) (d k : ℕ) (rowBase uBase : ℤ) :
    (Expr.dirSqSum d k rowBase uBase).Valid tape := by
  refine ⟨trivial, ?_, trivial⟩
  apply Expr.valid_sumFin
  intro j
  have hv := Expr.valid_rowDot tape d rowBase j.val uBase
  exact ⟨hv, hv, trivial⟩

/-- Static expression for the safe perturbation step size
`ε = a * δ / (2 * (1 + a * M + δ))`. -/
def Expr.stepEps (d k : ℕ) (rowBase pBase uBase aCell : ℤ) : Expr :=
  let δ := Expr.slackProd d k rowBase pBase
  let M := Expr.dirSqSum d k rowBase uBase
  let a := Expr.read aCell
  Expr.div (Expr.mul a δ)
    (Expr.mul (.const 2) (Expr.add (Expr.add (.const 1) (Expr.mul a M)) δ))

theorem Expr.eval_stepEps (tape : ℤ → ℝ) (d k : ℕ) (rowBase pBase uBase aCell : ℤ) :
    (Expr.stepEps d k rowBase pBase uBase aCell).eval tape =
      let δ := (Expr.slackProd d k rowBase pBase).eval tape
      let M := (Expr.dirSqSum d k rowBase uBase).eval tape
      tape aCell * δ / (2 * (1 + tape aCell * M + δ)) := by
  simp only [Expr.stepEps, Expr.div, Expr.mul, Expr.add, Expr.eval, BinOp.eval,
    Rat.cast_ofNat, Rat.cast_one]

theorem Expr.valid_stepEps (tape : ℤ → ℝ) (d k : ℕ) (rowBase pBase uBase aCell : ℤ)
    (ha : 0 < tape aCell)
    (hstrict : ∀ j : Fin k, (Expr.rowDot d rowBase j.val pBase).eval tape < 1) :
    (Expr.stepEps d k rowBase pBase uBase aCell).Valid tape := by
  have hδValid : (Expr.slackProd d k rowBase pBase).Valid tape :=
    Expr.valid_slackProd tape d k rowBase pBase hstrict
  have hMValid : (Expr.dirSqSum d k rowBase uBase).Valid tape :=
    Expr.valid_dirSqSum tape d k rowBase uBase
  have hδPos : 0 < (Expr.slackProd d k rowBase pBase).eval tape := by
    rw [Expr.eval_slackProd]
    apply Finset.prod_pos
    intro j _
    have hj := hstrict j
    exact div_pos (by linarith) (by linarith)
  have hMNonneg : 0 ≤ (Expr.dirSqSum d k rowBase uBase).eval tape := by
    rw [Expr.eval_dirSqSum]
    have hsum : 0 ≤ ∑ j : Fin k, ((Expr.rowDot d rowBase j.val uBase).eval tape) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    linarith
  have haMNonneg : 0 ≤ tape aCell * (Expr.dirSqSum d k rowBase uBase).eval tape :=
    mul_nonneg ha.le hMNonneg
  refine ⟨⟨trivial, hδValid, trivial⟩,
    ⟨trivial, ⟨⟨trivial, ⟨trivial, hMValid, trivial⟩, trivial⟩, hδValid, trivial⟩, trivial⟩, ?_⟩
  simp only [BinOp.Valid, Expr.mul, Expr.add, Expr.eval, BinOp.eval, Rat.cast_ofNat, Rat.cast_one]
  linarith

/-- Standalone straight-line program computing the safe perturbation step size `ε`
from `k` stored facet normals, point `p`, direction `u`, and scale `a`. -/
def stepEpsProgram (d k : ℕ) (rowBase pBase uBase aCell minBase : ℤ) : List RayInstruction :=
  let e := Expr.stepEps d k rowBase pBase uBase aCell
  let base := max e.readBound minBase
  e.emit base 0 ++ [.halt]

def stepEpsDest (d k : ℕ) (rowBase pBase uBase aCell minBase : ℤ) : ℤ :=
  max (Expr.stepEps d k rowBase pBase uBase aCell).readBound minBase

def stepEpsSteps (d k : ℕ) (rowBase pBase uBase aCell : ℤ) : ℕ :=
  (Expr.stepEps d k rowBase pBase uBase aCell).steps

theorem stepEpsProgram_correct {d k : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ)
    (ha : 0 < source aCell)
    (hstrict : ∀ j : Fin k,
      ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        source (pBase + (i.val : ℤ)) < 1) :
    let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
    let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
    let steps := stepEpsSteps d k rowBase pBase uBase aCell
    let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
      ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        source (xBase + (i.val : ℤ))
    let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
    let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
    minBase ≤ dst ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
      ∀ z : ℤ, z < dst → c'.tape z = source z := by
  let e := Expr.stepEps d k rowBase pBase uBase aCell
  let dst := max e.readBound minBase
  have hfresh : e.ReadFresh dst := by
    intro addr hmem
    exact lt_of_lt_of_le (e.readFresh_readBound addr hmem) (le_max_left _ _)
  have hvalid : e.Valid source := by
    apply Expr.valid_stepEps source d k rowBase pBase uBase aCell ha
    intro j
    rw [Expr.eval_rowDot]
    exact hstrict j
  obtain ⟨c', hrun, hpc, hhead, hq, hval, hframe, hhalt⟩ :=
    e.standalone_correct oracle source dst hfresh hvalid q
  refine ⟨le_max_right _ _, c', hrun, hpc, hhalt, hhead, hq, ?_, ?_⟩
  · change c'.tape dst = _
    rw [hval]
    change e.eval source = _
    rw [Expr.eval_stepEps]
    dsimp only
    rw [Expr.eval_slackProd, Expr.eval_dirSqSum]
    simp only [Expr.eval_rowDot]
  · intro z hz
    exact hframe z (Or.inl hz)

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003

theorem rayMachine_known_facet_step_eps_program_proved :
  ∃ (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z := by
  refine ⟨RayFieldExpr.stepEpsProgram, RayFieldExpr.stepEpsDest, RayFieldExpr.stepEpsSteps, ?_⟩
  intro d k oracle source rowBase pBase uBase aCell minBase q ha hstrict
  exact RayFieldExpr.stepEpsProgram_correct oracle source rowBase pBase uBase aCell minBase q ha hstrict

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  ∃ (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z :=
  Grunbaum2003.rayMachine_known_facet_step_eps_program_proved
