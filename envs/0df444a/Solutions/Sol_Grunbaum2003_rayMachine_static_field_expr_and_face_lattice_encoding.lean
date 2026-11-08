-- Prove2me | solution 1 for Grunbaum2003.rayMachine_static_field_expr_and_face_lattice_encoding
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:28.946291+00:00
-- url     : https://prove2.me/submissions/907fe922-33c1-4b97-b331-5ae7689d5616

import Mathlib.Tactic
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finite.Set

set_option autoImplicit false
open scoped Classical

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

/-- Under the exposed-vertex hull representation, exposed faces of `P` are ordered by
inclusion of their exposed vertex sets. -/
theorem polytopeFace_le_iff_exposed_vertices_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (E₁ E₂ : PolytopeFace P) :
    E₁ ≤ E₂ ↔ ∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ E₁.val → x ∈ E₂.val := by
  constructor
  · intro h x _ hx
    exact h hx
  · intro h
    change E₁.val ⊆ E₂.val
    rw [hHull E₁, hHull E₂]
    apply convexHull_mono
    rintro x ⟨hx₁, hxExp⟩
    exact ⟨h x hxExp hx₁, hxExp⟩

/-- Under the exposed-vertex hull representation, finiteness of the exposed vertices of `P`
implies that `PolytopeFace P` is finite and admits an equivalence `Fin n ≃ PolytopeFace P`. -/
theorem exists_equiv_fin_polytopeFace {d : ℕ} {P : Set (Fin d → ℝ)}
    (hFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite)
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :
    ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P) := by
  have : Finite {x : Fin d → ℝ | IsExposed ℝ P {x}} := hFin
  let toVertSet : PolytopeFace P → Set {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    fun E => {v | v.val ∈ E.val}
  have hInj : Function.Injective toVertSet := by
    intro E₁ E₂ hEq
    apply le_antisymm
    · rw [polytopeFace_le_iff_exposed_vertices_subset hHull]
      intro x hx hx₁
      have hMem : (⟨x, hx⟩ : {x : Fin d → ℝ | IsExposed ℝ P {x}}) ∈ toVertSet E₁ := hx₁
      rw [hEq] at hMem
      exact hMem
    · rw [polytopeFace_le_iff_exposed_vertices_subset hHull]
      intro x hx hx₂
      have hMem : (⟨x, hx⟩ : {x : Fin d → ℝ | IsExposed ℝ P {x}}) ∈ toVertSet E₂ := hx₂
      rw [← hEq] at hMem
      exact hMem
  have : Finite (PolytopeFace P) := Finite.of_injective toVertSet hInj
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (PolytopeFace P)
  exact ⟨n, ⟨e.symm⟩⟩

/-- If a configuration `c` writes the unary prefix `1, ..., 1, 0` of length `n + 1` at `c.head`
followed by the `0/1` exposed-vertex subset inclusion table for an enumeration
`e : Fin n ≃ PolytopeFace P`, then `IsRayFaceLatticeOutput P c` holds. -/
theorem isRayFaceLatticeOutput_of_vertex_subset_table {d n : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (e : Fin n ≃ PolytopeFace P) (c : RayConfiguration)
    (hUnary : ∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1)
    (hDelim : c.tape (c.head + (n : ℤ)) = 0)
    (hTable : ∀ i j : Fin n,
      c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
        if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) then 1 else 0) :
    IsRayFaceLatticeOutput P c := by
  refine ⟨n, hUnary, hDelim, e, ?_⟩
  intro i j
  dsimp only
  rw [hTable i j, ← polytopeFace_le_iff_exposed_vertices_subset hHull (e i) (e j)]
  by_cases hij : e i ≤ e j
  · simp only [if_pos hij, or_true, true_iff]
    exact ⟨trivial, hij⟩
  · simp only [if_neg hij, true_or, zero_ne_one, false_iff]
    exact ⟨trivial, hij⟩

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003

theorem rayMachine_static_field_expr_and_face_lattice_encoding_proved :
  (∃ (run_add : ∀ {d : ℕ} (program : List RayInstruction)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
        rayMachineRun program oracle (a + b) c =
          (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
     (standalone_add_sub_mul_div_step :
        ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ) (base a b : ℤ) (q : ℕ),
          a < base → b < base →
          ∃ c' : RayConfiguration,
            rayMachineRun
              ([.constant base 0 1, .add base a base 2,
                .constant (base + 1) 0 3, .add (base + 1) b (base + 1) 4,
                .add base base (base + 1) 5, .halt])
              oracle 5 ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = 5 ∧ c'.head = 0 ∧ c'.queries = q ∧
            c'.tape base = source a + source b ∧
            ∀ z : ℤ, (z < base ∨ base + 2 ≤ z) → c'.tape z = source z),
     True) ∧
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      (∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E₁ E₂ : PolytopeFace P,
        E₁ ≤ E₂ ↔ ∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ E₁.val → x ∈ E₂.val) ∧
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite →
        ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) ∧
      (∀ {n : ℕ} (e : Fin n ≃ PolytopeFace P) (c : RayConfiguration),
        (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
        c.tape (c.head + (n : ℤ)) = 0 →
        (∀ i j : Fin n,
          c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) then 1 else 0) →
        IsRayFaceLatticeOutput P c)) := by
  refine ⟨⟨@RayFieldExpr.run_add, ?_, trivial⟩, ?_⟩
  · intro d oracle source base a b q ha hb
    let e : RayFieldExpr.Expr := .bin .add (.read a) (.read b)
    have hfresh : e.ReadFresh base := by
      intro addr hmem
      simp only [e, RayFieldExpr.Expr.reads, Finset.mem_union, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact ha
      · exact hb
    have hvalid : e.Valid source := ⟨trivial, trivial, trivial⟩
    obtain ⟨c', hrun, hpc, hhead, hq, hval, hframe, _⟩ :=
      e.standalone_correct oracle source base hfresh hvalid q
    exact ⟨c', hrun, hpc, hhead, hq, hval, hframe⟩
  · intro d P hHull
    refine ⟨RayFieldExpr.polytopeFace_le_iff_exposed_vertices_subset hHull,
      fun hFin => RayFieldExpr.exists_equiv_fin_polytopeFace hFin hHull,
      fun e c hUnary hDelim hTable =>
        RayFieldExpr.isRayFaceLatticeOutput_of_vertex_subset_table hHull e c hUnary hDelim hTable⟩

end Grunbaum2003

theorem solution :
  (∃ (run_add : ∀ {d : ℕ} (program : List Grunbaum2003.RayInstruction)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : Grunbaum2003.RayConfiguration),
        Grunbaum2003.rayMachineRun program oracle (a + b) c =
          (Grunbaum2003.rayMachineRun program oracle a c).bind (Grunbaum2003.rayMachineRun program oracle b))
     (standalone_add_sub_mul_div_step :
        ∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ) (base a b : ℤ) (q : ℕ),
          a < base → b < base →
          ∃ c' : Grunbaum2003.RayConfiguration,
            Grunbaum2003.rayMachineRun
              ([.constant base 0 1, .add base a base 2,
                .constant (base + 1) 0 3, .add (base + 1) b (base + 1) 4,
                .add base base (base + 1) 5, .halt])
              oracle 5 ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = 5 ∧ c'.head = 0 ∧ c'.queries = q ∧
            c'.tape base = source a + source b ∧
            ∀ z : ℤ, (z < base ∨ base + 2 ≤ z) → c'.tape z = source z),
     True) ∧
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      (∀ E : Grunbaum2003.PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E₁ E₂ : Grunbaum2003.PolytopeFace P,
        E₁ ≤ E₂ ↔ ∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ E₁.val → x ∈ E₂.val) ∧
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite →
        ∃ n : ℕ, Nonempty (Fin n ≃ Grunbaum2003.PolytopeFace P)) ∧
      (∀ {n : ℕ} (e : Fin n ≃ Grunbaum2003.PolytopeFace P) (c : Grunbaum2003.RayConfiguration),
        (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
        c.tape (c.head + (n : ℤ)) = 0 →
        (∀ i j : Fin n,
          c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) then 1 else 0) →
        Grunbaum2003.IsRayFaceLatticeOutput P c)) :=
  Grunbaum2003.rayMachine_static_field_expr_and_face_lattice_encoding_proved
