-- Prove2me | solution 1 for Grunbaum2003.rayMachine_vector_eval_and_perturbed_ray_query_program
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:34:02.461067+00:00
-- url     : https://prove2.me/submissions/1b16e378-a497-4420-9ca6-58636b43d42d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun

set_option autoImplicit false

open scoped BigOperators Classical
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

namespace Grunbaum2003.RayFieldExpr

/-- Emit straight-line code evaluating `m` expressions `f 0, ..., f (m - 1)` sequentially
into consecutive target cells `outBase + 0, ..., outBase + (m - 1)`. -/
def emitVec : ℕ → (ℕ → Expr) → ℤ → ℕ → List RayInstruction
  | 0, _, _, _ => []
  | m + 1, f, outBase, pc =>
    (f 0).emit outBase pc ++
      emitVec m (fun i => f (i + 1)) (outBase + 1) (pc + (f 0).steps)

/-- Total step count (and instruction length) of `emitVec m f outBase pc`. -/
def emitVecSteps : ℕ → (ℕ → Expr) → ℕ
  | 0, _ => 0
  | m + 1, f => (f 0).steps + emitVecSteps m (fun i => f (i + 1))

/-- Upper bound on all tape addresses read by `f 0, ..., f (m - 1)`. -/
def emitVecReadBound : ℕ → (ℕ → Expr) → ℤ
  | 0, _ => 0
  | m + 1, f => max (f 0).readBound (emitVecReadBound m (fun i => f (i + 1)))

@[simp]
theorem length_emitVec (m : ℕ) (f : ℕ → Expr) (outBase : ℤ) (pc : ℕ) :
    (emitVec m f outBase pc).length = emitVecSteps m f := by
  induction m generalizing f outBase pc with
  | zero => rfl
  | succ m ih =>
    simp only [emitVec, emitVecSteps, List.length_append, Expr.length_emit, ih]

theorem readFresh_of_emitVecReadBound (m : ℕ) (f : ℕ → Expr) (base : ℤ)
    (hbase : emitVecReadBound m f ≤ base) :
    ∀ i : ℕ, i < m → (f i).ReadFresh base := by
  induction m generalizing f with
  | zero =>
    intro i hi
    omega
  | succ m ih =>
    intro i hi
    simp only [emitVecReadBound, max_le_iff] at hbase
    rcases i with _ | i
    · intro addr hmem
      exact lt_of_lt_of_le ((f 0).readFresh_readBound addr hmem) hbase.1
    · exact ih (fun j => f (j + 1)) hbase.2 i (Nat.lt_of_succ_lt_succ hi)

/-- Executing `emitVec m f outBase pc` writes `(f i).eval source` into `outBase + i` for all
`i < m` in `emitVecSteps m f` steps with zero oracle queries, while preserving all cells `< outBase`. -/
theorem emitVec_correct (m : ℕ) (f : ℕ → Expr) {d : ℕ}
    (program : List RayInstruction) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (source : ℤ → ℝ) (readLimit outBase : ℤ) (pc : ℕ) (c : RayConfiguration)
    (hpc : c.pc = pc) (hhead : c.head = 0)
    (hcode : CodeAt program pc (emitVec m f outBase pc))
    (hlim : readLimit ≤ outBase)
    (hfresh : ∀ i : ℕ, i < m → (f i).ReadFresh readLimit)
    (hagree : ∀ z : ℤ, z < readLimit → c.tape z = source z)
    (hvalid : ∀ i : ℕ, i < m → (f i).Valid source) :
    ∃ c' : RayConfiguration,
      rayMachineRun program oracle (emitVecSteps m f) c = some c' ∧
      c'.pc = pc + emitVecSteps m f ∧
      c'.head = 0 ∧
      c'.queries = c.queries ∧
      (∀ i : ℕ, i < m → c'.tape (outBase + (i : ℤ)) = (f i).eval source) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = c.tape z) := by
  induction m generalizing f outBase pc c with
  | zero =>
    refine ⟨c, rfl, by simp [hpc, emitVecSteps], hhead, rfl, ?_, fun _ _ => rfl⟩
    intro i hi
    omega
  | succ m ih =>
    have hcode0 : CodeAt program pc ((f 0).emit outBase pc) := hcode.left
    have hfresh0 : (f 0).ReadFresh outBase := by
      intro addr hmem
      exact lt_of_lt_of_le (hfresh 0 (Nat.succ_pos m) addr hmem) hlim
    have hagree0 : ∀ addr ∈ (f 0).reads, c.tape addr = source addr := by
      intro addr hmem
      exact hagree addr (hfresh 0 (Nat.succ_pos m) addr hmem)
    obtain ⟨c₁, hrun₁, hpc₁, hhead₁, hq₁, hval₁, hframe₁⟩ :=
      (f 0).emit_correct program oracle source outBase pc c hpc hhead hcode0
        hfresh0 hagree0 (hvalid 0 (Nat.succ_pos m))
    have hcodeRest : CodeAt program (pc + (f 0).steps)
        (emitVec m (fun i => f (i + 1)) (outBase + 1) (pc + (f 0).steps)) := by
      simpa only [Expr.length_emit] using hcode.right
    have hagree₁ : ∀ z : ℤ, z < readLimit → c₁.tape z = source z := by
      intro z hz
      have hzOut : z < outBase := lt_of_lt_of_le hz hlim
      exact (hframe₁ z (Or.inl hzOut)).trans (hagree z hz)
    obtain ⟨c₂, hrun₂, hpc₂, hhead₂, hq₂, hvals₂, hframe₂⟩ :=
      ih (fun i => f (i + 1)) (outBase + 1) (pc + (f 0).steps) c₁
        hpc₁ hhead₁ hcodeRest (by omega)
        (fun i hi => hfresh (i + 1) (Nat.succ_lt_succ hi))
        hagree₁
        (fun i hi => hvalid (i + 1) (Nat.succ_lt_succ hi))
    refine ⟨c₂, ?_, ?_, hhead₂, hq₂.trans hq₁, ?_, ?_⟩
    · simp only [emitVecSteps]
      rw [run_add program oracle (f 0).steps (emitVecSteps m (fun i => f (i + 1))) c,
        hrun₁, Option.bind_some, hrun₂]
    · simp only [emitVecSteps]
      omega
    · intro i hi
      rcases i with _ | i
      · simp only [Nat.cast_zero, add_zero]
        have hlt : outBase < outBase + 1 := by omega
        exact (hframe₂ outBase hlt).trans hval₁
      · have hi' : i < m := Nat.lt_of_succ_lt_succ hi
        have h := hvals₂ i hi'
        have heq : outBase + ((i + 1 : ℕ) : ℤ) = outBase + 1 + (i : ℤ) := by omega
        rw [heq]
        exact h
    · intro z hz
      have hz1 : z < outBase + 1 := by omega
      exact (hframe₂ z hz1).trans (hframe₁ z (Or.inl hz))

/-- Three-instruction block that shifts the head to `qBase`, executes one oracle query in place on
`qBase .. qBase + (d - 1)`, and shifts the head back to `0`. -/
def inPlaceQuery (qBase : ℤ) (pc : ℕ) : List RayInstruction :=
  [ .shift qBase (pc + 1),
    .query (pc + 2),
    .shift (-qBase) (pc + 3) ]

@[simp]
theorem length_inPlaceQuery (qBase : ℤ) (pc : ℕ) :
    (inPlaceQuery qBase pc).length = 3 := rfl

theorem inPlaceQuery_correct {d : ℕ}
    (program : List RayInstruction) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (qBase : ℤ) (pc : ℕ) (c : RayConfiguration)
    (hpc : c.pc = pc) (hhead : c.head = 0)
    (hcode : CodeAt program pc (inPlaceQuery qBase pc))
    (hNonzero : (fun i : Fin d => c.tape (qBase + (i.val : ℤ))) ≠ 0) :
    ∃ c' : RayConfiguration,
      rayMachineRun program oracle 3 c = some c' ∧
      c'.pc = pc + 3 ∧
      c'.head = 0 ∧
      c'.queries = c.queries + 1 ∧
      (∀ i : Fin d,
        c'.tape (qBase + (i.val : ℤ)) =
          oracle (fun j : Fin d => c.tape (qBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, (z < qBase ∨ qBase + (d : ℤ) ≤ z) → c'.tape z = c.tape z) := by
  have hfetch₀ : program[c.pc]? = some (.shift qBase (pc + 1)) := by
    have h := hcode 0 (by simp [inPlaceQuery])
    simpa only [hpc, Nat.add_zero, inPlaceQuery, List.getElem?_cons_zero] using h
  let c₁ : RayConfiguration := { c with pc := pc + 1, head := qBase }
  have hstep₀ : rayMachineStep program oracle c = some c₁ := by
    simp only [rayMachineStep, hfetch₀, hhead, zero_add, c₁]
  have hfetch₁ : program[c₁.pc]? = some (.query (pc + 2)) := by
    have h := hcode 1 (by simp [inPlaceQuery])
    simpa only [c₁, inPlaceQuery, List.getElem?_cons_succ, List.getElem?_cons_zero] using h
  let v : Fin d → ℝ := fun i => c.tape (qBase + (i.val : ℤ))
  have hvne : v ≠ 0 := hNonzero
  let tape₂ : ℤ → ℝ := fun j =>
    if h : 0 ≤ j - qBase ∧ j - qBase < (d : ℤ) then
      oracle v ⟨(j - qBase).toNat, by omega⟩
    else c.tape j
  let c₂ : RayConfiguration :=
    { c₁ with pc := pc + 2, queries := c.queries + 1, tape := tape₂ }
  have hstep₁ : rayMachineStep program oracle c₁ = some c₂ := by
    simp only [rayMachineStep, hfetch₁, c₁, v, hvne, ↓reduceIte, c₂, tape₂]
  have hfetch₂ : program[c₂.pc]? = some (.shift (-qBase) (pc + 3)) := by
    have h := hcode 2 (by simp [inPlaceQuery])
    simpa only [c₂, inPlaceQuery, List.getElem?_cons_succ, List.getElem?_cons_zero] using h
  let c₃ : RayConfiguration := { c₂ with pc := pc + 3, head := 0 }
  have hstep₂ : rayMachineStep program oracle c₂ = some c₃ := by
    simp only [rayMachineStep, hfetch₂, c₂, c₁, add_neg_cancel, c₃]
  refine ⟨c₃, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · change rayMachineRun program oracle (2 + 1) c = some c₃
    rw [run_add program oracle 2 1 c, run_add program oracle 1 1 c]
    simp only [rayMachineRun, hstep₀, hstep₁, hstep₂, Option.bind_some]
  · intro i
    change tape₂ (qBase + (i.val : ℤ)) = oracle v i
    dsimp [tape₂]
    have hcond : 0 ≤ qBase + (i.val : ℤ) - qBase ∧ qBase + (i.val : ℤ) - qBase < (d : ℤ) := by
      have hi := i.isLt
      omega
    rw [dif_pos hcond]
    congr 1
    ext
    simp
  · intro z hz
    change tape₂ z = c.tape z
    dsimp [tape₂]
    have hnot : ¬ (0 ≤ z - qBase ∧ z - qBase < (d : ℤ)) := by omega
    exact dif_neg hnot

/-- Standalone program that evaluates `d` field expressions `f 0, ..., f (d - 1)` into
`outBase .. outBase + (d - 1)` and queries the ray oracle in place when `doQuery = true`. -/
def evalVecAndOptQueryProgram (d : ℕ) (f : ℕ → Expr) (minBase : ℤ) (doQuery : Bool) :
    List RayInstruction :=
  let outBase := max (emitVecReadBound d f) minBase
  let body := emitVec d f outBase 0
  if doQuery then
    body ++ inPlaceQuery outBase (emitVecSteps d f) ++ [.halt]
  else
    body ++ [.halt]

def evalVecDest (d : ℕ) (f : ℕ → Expr) (minBase : ℤ) : ℤ :=
  max (emitVecReadBound d f) minBase

def evalVecAndOptQuerySteps (d : ℕ) (f : ℕ → Expr) (doQuery : Bool) : ℕ :=
  if doQuery then emitVecSteps d f + 3 else emitVecSteps d f

theorem CodeAt.prefix_zero (block suffix : List RayInstruction) :
    CodeAt (block ++ suffix) 0 block := by
  intro i hi
  simpa only [Nat.zero_add] using List.getElem?_append_left hi

/-- Correctness of `evalVecAndOptQueryProgram` when `doQuery = false` (pure vector evaluation). -/
theorem evalVecProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (f : ℕ → Expr) (minBase : ℤ) (q : ℕ)
    (hvalid : ∀ i : ℕ, i < d → (f i).Valid source) :
    let prog := evalVecAndOptQueryProgram d f minBase false
    let outBase := evalVecDest d f minBase
    let steps := evalVecAndOptQuerySteps d f false
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ i : Fin d, c'.tape (outBase + (i.val : ℤ)) = (f i.val).eval source) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  have hmin : minBase ≤ outBase := le_max_right _ _
  have hbound : emitVecReadBound d f ≤ outBase := le_max_left _ _
  have hfresh : ∀ i : ℕ, i < d → (f i).ReadFresh outBase :=
    readFresh_of_emitVecReadBound d f outBase hbound
  have hcode : CodeAt prog 0 (emitVec d f outBase 0) :=
    CodeAt.prefix_zero (emitVec d f outBase 0) [.halt]
  obtain ⟨c', hrun, hpc, hhead, hq, hvals, hframe⟩ :=
    emitVec_correct d f prog oracle source outBase outBase 0 ⟨0, 0, source, q⟩
      rfl rfl hcode le_rfl hfresh (fun _ _ => rfl) hvalid
  refine ⟨hmin, c', hrun, ?_, ?_, hhead, hq, fun i => hvals i.val i.isLt, hframe⟩
  · simpa only [steps, evalVecAndOptQuerySteps, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      using hpc
  · have hpc' : c'.pc = emitVecSteps d f := by simpa only [Nat.zero_add] using hpc
    rw [hpc']
    change (emitVec d f outBase 0 ++ [.halt])[emitVecSteps d f]? = some .halt
    rw [← length_emitVec d f outBase 0,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

/-- Correctness of `evalVecAndOptQueryProgram` when `doQuery = true`
(vector evaluation followed by an in-place oracle query). -/
theorem evalVecAndQueryProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (f : ℕ → Expr) (minBase : ℤ) (q : ℕ)
    (hvalid : ∀ i : ℕ, i < d → (f i).Valid source)
    (hNonzero : (fun i : Fin d => (f i.val).eval source) ≠ 0) :
    let prog := evalVecAndOptQueryProgram d f minBase true
    let outBase := evalVecDest d f minBase
    let steps := evalVecAndOptQuerySteps d f true
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q + 1 ∧
      (∀ i : Fin d,
        c'.tape (outBase + (i.val : ℤ)) =
          oracle (fun j : Fin d => (f j.val).eval source) i) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  have hmin : minBase ≤ outBase := le_max_right _ _
  have hbound : emitVecReadBound d f ≤ outBase := le_max_left _ _
  have hfresh : ∀ i : ℕ, i < d → (f i).ReadFresh outBase :=
    readFresh_of_emitVecReadBound d f outBase hbound
  let body := emitVec d f outBase 0
  let qcode := inPlaceQuery outBase (emitVecSteps d f)
  have hprog : prog = (body ++ qcode) ++ [.halt] := by
    simp [prog, evalVecAndOptQueryProgram, body, qcode, outBase, evalVecDest]
  have hcodeAll : CodeAt prog 0 (body ++ qcode) := by
    rw [hprog]
    exact CodeAt.prefix_zero (body ++ qcode) [.halt]
  have hcodeBody : CodeAt prog 0 body := hcodeAll.left
  have hcodeQuery : CodeAt prog (emitVecSteps d f) qcode := by
    have h := hcodeAll.right
    simpa only [Nat.zero_add, body, length_emitVec] using h
  obtain ⟨c₁, hrun₁, hpc₁, hhead₁, hq₁, hvals₁, hframe₁⟩ :=
    emitVec_correct d f prog oracle source outBase outBase 0 ⟨0, 0, source, q⟩
      rfl rfl hcodeBody le_rfl hfresh (fun _ _ => rfl) hvalid
  have hpc₁' : c₁.pc = emitVecSteps d f := by simpa only [Nat.zero_add] using hpc₁
  have hVecEq : (fun j : Fin d => c₁.tape (outBase + (j.val : ℤ))) =
      (fun j : Fin d => (f j.val).eval source) := by
    funext j
    exact hvals₁ j.val j.isLt
  have hNonzero₁ : (fun j : Fin d => c₁.tape (outBase + (j.val : ℤ))) ≠ 0 := by
    rw [hVecEq]
    exact hNonzero
  obtain ⟨c₂, hrun₂, hpc₂, hhead₂, hq₂, hvals₂, hframe₂⟩ :=
    inPlaceQuery_correct prog oracle outBase (emitVecSteps d f) c₁
      hpc₁' hhead₁ hcodeQuery hNonzero₁
  refine ⟨hmin, c₂, ?_, ?_, ?_, hhead₂, ?_, ?_, ?_⟩
  · change rayMachineRun prog oracle (emitVecSteps d f + 3) ⟨0, 0, source, q⟩ = some c₂
    rw [run_add prog oracle (emitVecSteps d f) 3, hrun₁, Option.bind_some, hrun₂]
  · simpa only [steps, evalVecAndOptQuerySteps, ↓reduceIte] using hpc₂
  · rw [hpc₂, hprog]
    have hlen : (body ++ qcode).length = emitVecSteps d f + 3 := by
      simp [body, qcode]
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · rw [hq₂, hq₁]
  · intro i
    rw [hvals₂ i, hVecEq]
  · intro z hz
    exact (hframe₂ z (Or.inl hz)).trans (hframe₁ z hz)

/-- Coordinate `i` of the perturbed ray `p + ε u` read from `pBase + i`, `epsCell`, `uBase + i`. -/
def perturbedCoordExpr (pBase uBase epsCell : ℤ) (i : ℕ) : Expr :=
  Expr.add (.read (pBase + (i : ℤ))) (Expr.mul (.read epsCell) (.read (uBase + (i : ℤ))))

@[simp]
theorem eval_perturbedCoordExpr (source : ℤ → ℝ) (pBase uBase epsCell : ℤ) (i : ℕ) :
    (perturbedCoordExpr pBase uBase epsCell i).eval source =
      source (pBase + (i : ℤ)) + source epsCell * source (uBase + (i : ℤ)) := rfl

theorem valid_perturbedCoordExpr (source : ℤ → ℝ) (pBase uBase epsCell : ℤ) (i : ℕ) :
    (perturbedCoordExpr pBase uBase epsCell i).Valid source :=
  ⟨trivial, ⟨trivial, trivial, trivial⟩, trivial⟩

/-- Program that evaluates `p + ε u` into `outBase .. outBase + (d - 1)` and queries the ray oracle
in place, writing `oracle (p + ε u)` into `outBase .. outBase + (d - 1)`. -/
def perturbedRayQueryProgram (d : ℕ) (pBase uBase epsCell minBase : ℤ) : List RayInstruction :=
  evalVecAndOptQueryProgram d (perturbedCoordExpr pBase uBase epsCell) minBase true

def perturbedRayQueryDest (d : ℕ) (pBase uBase epsCell minBase : ℤ) : ℤ :=
  evalVecDest d (perturbedCoordExpr pBase uBase epsCell) minBase

def perturbedRayQuerySteps (d : ℕ) (pBase uBase epsCell : ℤ) : ℕ :=
  evalVecAndOptQuerySteps d (perturbedCoordExpr pBase uBase epsCell) true

theorem perturbedRayQueryProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (pBase uBase epsCell minBase : ℤ) (q : ℕ)
    (hNonzero :
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0) :
    let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
    let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
    let steps := perturbedRayQuerySteps d pBase uBase epsCell
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q + 1 ∧
      (∀ i : Fin d,
        c'.tape (outBase + (i.val : ℤ)) =
          oracle (fun j : Fin d =>
            source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) :=
  evalVecAndQueryProgram_correct oracle source
    (perturbedCoordExpr pBase uBase epsCell) minBase q
    (fun i _ => valid_perturbedCoordExpr source pBase uBase epsCell i)
    hNonzero

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003

theorem rayMachine_vector_eval_and_perturbed_ray_query_program_proved :
  ∃ (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  refine ⟨RayFieldExpr.perturbedRayQueryProgram,
    RayFieldExpr.perturbedRayQueryDest,
    RayFieldExpr.perturbedRayQuerySteps, ?_⟩
  intro d oracle source pBase uBase epsCell minBase q hNonzero
  exact RayFieldExpr.perturbedRayQueryProgram_correct
    oracle source pBase uBase epsCell minBase q hNonzero

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  ∃ (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ),
    ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) :=
  Grunbaum2003.rayMachine_vector_eval_and_perturbed_ray_query_program_proved
