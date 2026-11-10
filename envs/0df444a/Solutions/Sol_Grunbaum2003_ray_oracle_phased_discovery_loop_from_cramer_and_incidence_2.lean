-- Prove2me | solution 2 for Grunbaum2003.ray_oracle_phased_discovery_loop_from_cramer_and_incidence
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T08:57:08.564387+00:00
-- url     : https://prove2.me/submissions/f976ac44-f5e0-42f5-a2b5-ee21e87a6081

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_rayMachineStep
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finite.Set
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
open scoped BigOperators Matrix Classical Pointwise

-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_relocate_and_section_query_adapter.lean
-- SHA256: 8be109c35db1291d0d0d7203976459c061dd6600c6d06bed4e30d42a12e6e450
namespace RayCounterfamilyInline00

open _root_.Grunbaum2003


set_option autoImplicit false

noncomputable section



namespace Grunbaum2003.RayCode

/-- Relocate every literal control-flow label, preserving all tape addresses. -/
def relocateInstruction (offset : ℕ) : RayInstruction → RayInstruction
  | .constant dst value next => .constant dst value (offset + next)
  | .add dst a b next => .add dst a b (offset + next)
  | .sub dst a b next => .sub dst a b (offset + next)
  | .mul dst a b next => .mul dst a b (offset + next)
  | .div dst a b next => .div dst a b (offset + next)
  | .branch a negative equal positive =>
      .branch a (offset + negative) (offset + equal) (offset + positive)
  | .shift shift next => .shift shift (offset + next)
  | .query next => .query (offset + next)
  | .halt => .halt

def relocateConfiguration (offset : ℕ) (c : RayConfiguration) : RayConfiguration :=
  {c with pc := offset + c.pc}

theorem relocated_fetch (pre program : List RayInstruction) (c : RayConfiguration) :
    (pre ++ program.map (relocateInstruction pre.length))[
      (relocateConfiguration pre.length c).pc]? =
      (program[c.pc]?).map (relocateInstruction pre.length) := by
  change (pre ++ program.map (relocateInstruction pre.length))[pre.length + c.pc]? = _
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_map]

/-- Actual one-step semantics of a relocated finite instruction list.
This is code relocation, not an assumption that arbitrary protocols compile. -/
theorem relocated_step {d : ℕ} (pre program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (c : RayConfiguration) :
    rayMachineStep (pre ++ program.map (relocateInstruction pre.length)) oracle
        (relocateConfiguration pre.length c) =
      (rayMachineStep program oracle c).map (relocateConfiguration pre.length) := by
  unfold rayMachineStep
  rw [relocated_fetch]
  cases hinst : program[c.pc]? with
  | none => rfl
  | some inst =>
    cases inst <;> simp only [Option.map_some, relocateInstruction, relocateConfiguration]
    all_goals first | rfl | (split_ifs <;>
      simp_all only [relocateConfiguration, Option.map_some, Option.map_none, if_true, if_false])
    all_goals first | rfl | (split_ifs <;>
      simp_all only [relocateConfiguration, Option.map_some, Option.map_none, if_true, if_false])

/-- Every finite run relocates with the same tape, head, and query count. -/
theorem relocated_run {d : ℕ} (pre program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration) :
    rayMachineRun (pre ++ program.map (relocateInstruction pre.length)) oracle t
        (relocateConfiguration pre.length c) =
      (rayMachineRun program oracle t c).map (relocateConfiguration pre.length) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [rayMachineRun, rayMachineRun, relocated_step]
    cases hs : rayMachineStep program oracle c with
    | none => rfl
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      exact ih c'

theorem relocated_halt (pre program : List RayInstruction) (c : RayConfiguration)
    (hhalt : program[c.pc]? = some .halt) :
    (pre ++ program.map (relocateInstruction pre.length))[
      (relocateConfiguration pre.length c).pc]? = some .halt := by
  rw [relocated_fetch, hhalt]
  rfl

end Grunbaum2003.RayCode




namespace Grunbaum2003.RaySection

/-- Field-only coordinate embedding of a physical plane. The first coordinate
uses a scaled ambient coordinate axis and the second uses the supplied point. -/
def coordinateSectionLinear {d : ℕ} (i : Fin d) (ε : ℝ) (p : Fin d → ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun r k := (if k = i then ε * r 0 else 0) + r 1 * p k
  map_add' r s := by
    ext k

    change (if k = i then ε * (r 0 + s 0) else 0) + (r 1 + s 1) * p k =
      ((if k = i then ε * r 0 else 0) + r 1 * p k) +
        ((if k = i then ε * s 0 else 0) + s 1 * p k)
    split_ifs <;> ring
  map_smul' a r := by
    ext k
    change (if k = i then ε * (a * r 0) else 0) + (a * r 1) * p k =
      a * ((if k = i then ε * r 0 else 0) + r 1 * p k)
    split_ifs <;> ring

/-- The two literal coordinate reads used after a physical query. The two
divisors are retained nonzero data, not oracle-dependent searches. -/
def coordinateSectionInverseLinear {d : ℕ} (i j : Fin d) (ε : ℝ)
    (p : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun y k := if k = 0 then (y i - (y j / p j) * p i) / ε else y j / p j
  map_add' y z := by
    ext k
    fin_cases k
    · change ((y i + z i) - ((y j + z j) / p j) * p i) / ε =
        (y i - (y j / p j) * p i) / ε + (z i - (z j / p j) * p i) / ε
      ring
    · change (y j + z j) / p j = y j / p j + z j / p j
      ring
  map_smul' a y := by
    ext k
    fin_cases k
    · change (a * y i - ((a * y j) / p j) * p i) / ε =
        a * ((y i - (y j / p j) * p i) / ε)
      ring
    · change (a * y j) / p j = a * (y j / p j)
      ring

def coordinateSectionMap {d : ℕ} (i : Fin d) (ε : ℝ) (p : Fin d → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin d → ℝ) :=
  (coordinateSectionLinear i ε p).toContinuousLinearMap

def coordinateSectionInverse {d : ℕ} (i j : Fin d) (ε : ℝ) (p : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (coordinateSectionInverseLinear i j ε p).toContinuousLinearMap

/-- These formulas give an actual left inverse from two distinct coordinate
reads. In particular every native nonzero ray maps to a nonzero physical ray. -/
theorem coordinateSection_leftInverse {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    {ε : ℝ} (hε : ε ≠ 0) (p : Fin d → ℝ) (hpj : p j ≠ 0) :
    Function.LeftInverse (coordinateSectionInverse i j ε p) (coordinateSectionMap i ε p) := by
  intro r
  funext k
  have hji : j ≠ i := Ne.symm hij
  fin_cases k
  · change (((if i = i then ε * r 0 else 0) + r 1 * p i) -
        ((((if j = i then ε * r 0 else 0) + r 1 * p j) / p j) * p i)) / ε = r 0
    rw [if_pos rfl, if_neg hji, zero_add, mul_div_cancel_right₀ _ hpj]
    field_simp [hε]
    <;> ring
  · change ((if j = i then ε * r 0 else 0) + r 1 * p j) / p j = r 1
    rw [if_neg hji, zero_add, mul_div_cancel_right₀ _ hpj]

end Grunbaum2003.RaySection




namespace Grunbaum2003.RayBlockQuery

private def writeVector {d : ℕ} (tape : ℤ → ℝ) (block : ℤ)
    (v : Fin d → ℝ) (z : ℤ) : ℝ :=
  if hz : 0 ≤ z - block ∧ z - block < (d : ℤ) then
    v ⟨(z - block).toNat, by omega⟩ else tape z

private theorem writeVector_at {d : ℕ} (tape : ℤ → ℝ) (block : ℤ)
    (v : Fin d → ℝ) (i : Fin d) : writeVector tape block v (block + (i.val : ℤ)) = v i := by
  have hi : 0 ≤ block + (i.val : ℤ) - block ∧
      block + (i.val : ℤ) - block < (d : ℤ) := by omega
  rw [writeVector, dif_pos hi]
  congr 1
  apply Fin.ext
  simp only [add_sub_cancel_left, Int.toNat_natCast]

private theorem writeVector_frame {d : ℕ} (tape : ℤ → ℝ) (block : ℤ)
    (v : Fin d → ℝ) (z : ℤ) (hz : z < block ∨ block + (d : ℤ) ≤ z) :
    writeVector tape block v z = tape z := by
  have hn : ¬ (0 ≤ z - block ∧ z - block < (d : ℤ)) := by omega
  simp only [writeVector, dif_neg hn]

/-- Three literal instructions shift to a stored physical direction, issue
exactly one original query, and restore head0. The response overwrites that
block and every other tape cell is preserved. This is a bounded machine block,
not an assumed compiler for an unrestricted interactive procedure. -/
theorem run_query_at_block {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (block : ℤ)
    (v : Fin d → ℝ) (hv : v ≠ 0)
    (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = 0)
    (hvector : ∀ i : Fin d, c.tape (block + (i.val : ℤ)) = v i)
    (hfetch₀ : program[base]? = some (.shift block (base + 1)))
    (hfetch₁ : program[base + 1]? = some (.query (base + 2)))
    (hfetch₂ : program[base + 2]? = some (.shift (-block) (base + 3))) :
    ∃ b : RayConfiguration, rayMachineRun program oracle 3 c = some b ∧
      b.pc = base + 3 ∧ b.head = 0 ∧ b.queries = c.queries + 1 ∧
      (∀ i : Fin d, b.tape (block + (i.val : ℤ)) = oracle v i) ∧
      (∀ z : ℤ, z < block ∨ block + (d : ℤ) ≤ z → b.tape z = c.tape z) := by
  let c₁ : RayConfiguration := {c with pc := base + 1, head := block}
  let c₂ : RayConfiguration :=
    {c₁ with
      pc := base + 2
      queries := c.queries + 1
      tape := writeVector c.tape block (oracle v)}
  let b : RayConfiguration := {c₂ with pc := base + 3, head := 0}
  have hstep₀ : rayMachineStep program oracle c = some c₁ := by
    simp only [rayMachineStep, hpc, hfetch₀, hhead, zero_add, c₁]
  have hinput : (fun i : Fin d => c.tape (block + (i.val : ℤ))) = v := funext hvector
  have hstep₁ : rayMachineStep program oracle c₁ = some c₂ := by
    simp only [rayMachineStep, c₁, hfetch₁, hinput, if_neg hv, c₂]
    rfl
  have hstep₂ : rayMachineStep program oracle c₂ = some b := by
    simp only [rayMachineStep, c₂, c₁, hfetch₂, add_neg_cancel, b]
  refine ⟨b, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [rayMachineRun, hstep₀, hstep₁, hstep₂, Option.bind_some]
  · intro i
    exact writeVector_at c.tape block (oracle v) i
  · intro z hz
    exact writeVector_frame c.tape block (oracle v) z hz

end Grunbaum2003.RayBlockQuery




namespace Grunbaum2003.RaySectionProgram

def pointBase : ℤ := 18
def queryBase (d : ℕ) : ℤ := 18 + (d : ℤ)
def scratchCell (d : ℕ) : ℤ := 18 + 2 * (d : ℤ)

def sectionQueryTail (d : ℕ) (i j : Fin d) : List RayInstruction :=
  [.add (queryBase d + (i.val : ℤ)) (queryBase d + (i.val : ℤ)) (scratchCell d) (d + 2),
   .shift (queryBase d) (d + 3),
   .query (d + 4),
   .shift (-queryBase d) (d + 5),
   .div 1 (queryBase d + (j.val : ℤ)) (pointBase + (j.val : ℤ)) (d + 6),
   .mul (scratchCell d) 1 (pointBase + (i.val : ℤ)) (d + 7),
   .sub (scratchCell d) (queryBase d + (i.val : ℤ)) (scratchCell d) (d + 8),
   .div 0 (scratchCell d) 17 (d + 9),
   .halt]

/-- A finite physical-query adapter for each pair of coordinate pivots. Its
code depends on d,i,j only; p and epsilon are retained real tape data. A uniform
full controller must dispatch among the finitely many pivot pairs explicitly. -/
def sectionQueryProgram (d : ℕ) (i j : Fin d) : List RayInstruction :=
  .mul (scratchCell d) 17 0 1 ::
    (List.ofFn (fun k : Fin d =>
      .mul (queryBase d + (k.val : ℤ)) 1 (pointBase + (k.val : ℤ)) (k.val + 2)) ++
      sectionQueryTail d i j)

theorem sectionQuery_initial_fetch {d : ℕ} (i j : Fin d) :
    (sectionQueryProgram d i j)[0]? = some (.mul (scratchCell d) 17 0 1) := rfl

theorem sectionQuery_vector_fetch {d : ℕ} (i j k : Fin d) :
    (sectionQueryProgram d i j)[1 + k.val]? =
      some (.mul (queryBase d + (k.val : ℤ)) 1 (pointBase + (k.val : ℤ)) (k.val + 2)) := by
  rw [show 1 + k.val = k.val + 1 by omega]
  simp only [sectionQueryProgram, List.getElem?_cons_succ, List.getElem?_append,
    List.length_ofFn, k.isLt, ↓reduceIte, List.getElem?_ofFn, ↓reduceDIte]

theorem sectionQuery_tail_fetch {d : ℕ} (i j : Fin d) (n : ℕ) :
    (sectionQueryProgram d i j)[1 + d + n]? = (sectionQueryTail d i j)[n]? := by
  have hn : ¬ d + n < d := by omega
  have hs : d + n - d = n := by omega
  rw [show 1 + d + n = (d + n) + 1 by omega]
  simp only [sectionQueryProgram, List.getElem?_cons_succ, List.getElem?_append,
    List.length_ofFn, hn, ↓reduceIte, hs]

theorem sectionQueryProgram_length {d : ℕ} (i j : Fin d) :
    (sectionQueryProgram d i j).length = d + 10 := by
  simp only [sectionQueryProgram, List.length_cons, List.length_append,
    List.length_ofFn, sectionQueryTail, List.length_cons, List.length_nil]

private theorem run_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

private theorem run_succ_last {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + 1) c =
      (rayMachineRun program oracle a c).bind (rayMachineStep program oracle) := by
  rw [run_add program oracle a 1 c]
  simp only [rayMachineRun, Option.bind_fun_some]

/-- The actual unrolled multiplication loop, including its frame. Source and
scalar cells are disjoint from the destination block, so every instruction
reads the original data even on an arbitrary initial tape. -/
theorem run_scaled_vector {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (source dest scalar : ℤ)
    (hsep : source + (d : ℤ) ≤ dest)
    (hscalar : scalar < dest ∨ dest + (d : ℤ) ≤ scalar)
    (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = 0)
    (hfetch : ∀ k : Fin d, program[base + k.val]? =
      some (.mul (dest + (k.val : ℤ)) scalar (source + (k.val : ℤ)) (base + k.val + 1))) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle d c = some c' ∧
      c'.pc = base + d ∧ c'.head = 0 ∧ c'.queries = c.queries ∧
      (∀ k : Fin d, c'.tape (dest + (k.val : ℤ)) =
        c.tape scalar * c.tape (source + (k.val : ℤ))) ∧
      (∀ z : ℤ, z < dest ∨ dest + (d : ℤ) ≤ z → c'.tape z = c.tape z) := by
  classical
  have hrun : ∀ n, n ≤ d → ∃ c' : RayConfiguration,
      rayMachineRun program oracle n c = some c' ∧
      c'.pc = base + n ∧ c'.head = 0 ∧ c'.queries = c.queries ∧
      (∀ k : Fin d, k.val < n → c'.tape (dest + (k.val : ℤ)) =
        c.tape scalar * c.tape (source + (k.val : ℤ))) ∧
      (∀ z : ℤ, z < dest ∨ dest + (d : ℤ) ≤ z → c'.tape z = c.tape z) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨c, rfl, ?_, hhead, rfl, ?_, ?_⟩
      · simpa only [Nat.add_zero] using hpc
      · intro _ hk
        omega
      · intro _ _
        rfl
    | succ n ih =>
      intro hn
      obtain ⟨b, hb, hbpc, hbhead, hbq, hbvalues, hbframe⟩ := ih (by omega)
      have hnd : n < d := by omega
      have hs : b.tape scalar = c.tape scalar := hbframe scalar hscalar
      have hp : b.tape (source + (n : ℤ)) = c.tape (source + (n : ℤ)) :=
        hbframe _ (Or.inl (by omega))
      let b' : RayConfiguration :=
        {b with
          pc := base + n + 1
          tape := Function.update b.tape (dest + (n : ℤ))
            (c.tape scalar * c.tape (source + (n : ℤ)))}
      have hinst : program[b.pc]? = some
          (.mul (dest + (n : ℤ)) scalar (source + (n : ℤ)) (base + n + 1)) := by
        rw [hbpc]
        exact hfetch ⟨n, hnd⟩
      have hstep : rayMachineStep program oracle b = some b' := by
        simp only [rayMachineStep, hinst, hbhead, zero_add, hs, hp, b']
      refine ⟨b', ?_, ?_, hbhead, hbq, ?_, ?_⟩
      · rw [run_succ_last, hb, Option.bind_some, hstep]
      · change base + n + 1 = base + (n + 1)
        omega
      · intro k hk
        by_cases hkn : k.val = n
        · have haddr : dest + (k.val : ℤ) = dest + (n : ℤ) := by omega
          change Function.update b.tape (dest + (n : ℤ)) _ (dest + (k.val : ℤ)) = _
          rw [haddr, Function.update_self]
          congr 2
          omega
        · have hk' : k.val < n := by omega
          have haddr : dest + (k.val : ℤ) ≠ dest + (n : ℤ) := by omega
          simpa only [b', Function.update_of_ne haddr] using hbvalues k hk'
      · intro z hz
        have haddr : z ≠ dest + (n : ℤ) := by omega
        simpa only [b', Function.update_of_ne haddr] using hbframe z hz
  obtain ⟨c', hc', hpc', hhead', hq', hvalues, hframe⟩ := hrun d le_rfl
  exact ⟨c', hc', hpc', hhead', hq', fun k => hvalues k k.isLt, hframe⟩

/-- Literal pre-query construction of the physical section direction. The
native header, p coordinates and epsilon are read from the original arbitrary
tape, all queries remain unspent, and the complete outside-block frame is
retained. This proves the actual vector sent to the later query instruction. -/
theorem sectionQuery_buildDirection {d : ℕ} (i j : Fin d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
    ∃ c : RayConfiguration,
      rayMachineRun (sectionQueryProgram d i j) oracle (d + 2)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = d + 2 ∧ c.head = 0 ∧ c.queries = q ∧
      (fun k : Fin d => c.tape (queryBase d + (k.val : ℤ))) =
        RaySection.coordinateSectionMap i (tape 17)
          (fun k => tape (pointBase + (k.val : ℤ)))
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ∧
      (∀ z : ℤ, (z < queryBase d ∨ queryBase d + (d : ℤ) ≤ z) →
        z ≠ scratchCell d → c.tape z = tape z) := by
  let c₀ : RayConfiguration := {pc := 0, head := 0, tape := tape, queries := q}
  let c₁ : RayConfiguration :=
    {c₀ with pc := 1, tape := Function.update tape (scratchCell d) (tape 17 * tape 0)}
  have hstep₀ : rayMachineStep (sectionQueryProgram d i j) oracle c₀ = some c₁ := by
    simp only [rayMachineStep, c₀, sectionQuery_initial_fetch, zero_add, c₁]
  have hrun₁ : rayMachineRun (sectionQueryProgram d i j) oracle 1 c₀ = some c₁ := by
    simp only [rayMachineRun, hstep₀, Option.bind_some]
  have hsep : pointBase + (d : ℤ) ≤ queryBase d := le_rfl
  have hscalar : (1 : ℤ) < queryBase d ∨ queryBase d + (d : ℤ) ≤ 1 := by
    left
    dsimp only [queryBase]
    omega
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbvalues, hbframe⟩ :=
    run_scaled_vector (sectionQueryProgram d i j) oracle 1 pointBase (queryBase d) 1
      hsep hscalar c₁ rfl rfl (fun k => by
        simpa only [show 1 + k.val + 1 = k.val + 2 by omega] using
          sectionQuery_vector_fetch i j k)
  have hsone : (1 : ℤ) ≠ scratchCell d := by dsimp only [scratchCell]; omega
  have hc₁one : c₁.tape 1 = tape 1 := by
    exact Function.update_of_ne hsone _ _
  have hc₁point : ∀ k : Fin d, c₁.tape (pointBase + (k.val : ℤ)) =
      tape (pointBase + (k.val : ℤ)) := by
    intro k
    have hne : pointBase + (k.val : ℤ) ≠ scratchCell d := by
      dsimp only [pointBase, scratchCell]
      omega
    exact Function.update_of_ne hne _ _
  have hdata : ∀ k : Fin d, c₁.tape 1 * c₁.tape (pointBase + (k.val : ℤ)) =
      tape 1 * tape (pointBase + (k.val : ℤ)) := by
    intro k
    rw [hc₁one, hc₁point]
  have hscratch : b.tape (scratchCell d) = tape 17 * tape 0 := by
    rw [hbframe _ (Or.inr (by dsimp only [queryBase, scratchCell]; omega))]
    exact Function.update_self _ _ _
  let c : RayConfiguration :=
    {b with
      pc := d + 2
      tape := Function.update b.tape (queryBase d + (i.val : ℤ))
        (c₁.tape 1 * c₁.tape (pointBase + (i.val : ℤ)) + tape 17 * tape 0)}
  have hinst : (sectionQueryProgram d i j)[b.pc]? = some
      (.add (queryBase d + (i.val : ℤ)) (queryBase d + (i.val : ℤ)) (scratchCell d) (d + 2)) := by
    rw [hbpc]
    simpa only [Nat.add_zero, sectionQueryTail, List.getElem?_cons_zero] using
      sectionQuery_tail_fetch i j 0
  have hstep : rayMachineStep (sectionQueryProgram d i j) oracle b = some c := by
    simp only [rayMachineStep, hinst, hbhead, zero_add, hbvalues i, hscratch, c]
  refine ⟨c, ?_, rfl, hbhead, hbq, ?_, ?_⟩
  · change rayMachineRun (sectionQueryProgram d i j) oracle (d + 2) c₀ = _
    rw [show d + 2 = 1 + (d + 1) by omega]
    rw [run_add, hrun₁, Option.bind_some, run_add, hb, Option.bind_some]
    simp only [rayMachineRun, hstep, Option.bind_some]
  · funext k
    change c.tape (queryBase d + (k.val : ℤ)) =
      (if k = i then tape 17 * tape 0 else 0) + tape 1 * tape (pointBase + (k.val : ℤ))
    by_cases hki : k = i
    · subst k
      change Function.update b.tape (queryBase d + (i.val : ℤ)) _
        (queryBase d + (i.val : ℤ)) = _
      rw [Function.update_self, hdata, if_pos rfl]
      ring
    · have haddr : queryBase d + (k.val : ℤ) ≠ queryBase d + (i.val : ℤ) := by
        intro heq
        apply hki
        apply Fin.ext
        omega
      change Function.update b.tape (queryBase d + (i.val : ℤ)) _
        (queryBase d + (k.val : ℤ)) = _
      rw [Function.update_of_ne haddr, hbvalues k, hdata, if_neg hki, zero_add]
  · intro z hz hzs
    have haddr : z ≠ queryBase d + (i.val : ℤ) := by omega
    change Function.update b.tape (queryBase d + (i.val : ℤ)) _ z = tape z
    rw [Function.update_of_ne haddr, hbframe z hz]
    exact Function.update_of_ne hzs _ _

end Grunbaum2003.RaySectionProgram




namespace Grunbaum2003.RaySectionProgram

private theorem run_add_sqi {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

/-- The concrete physical adapter constructs the actual ambient direction,
derives its nonzero query guard from the coordinate left inverse, and executes
one original oracle call. Its response, tape frame, cursor and exact cost are
all statements about the original machine run. Coordinate extraction is the
following four-instruction suffix. -/
theorem sectionQuery_issue {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ)
    (hε : tape 17 ≠ 0) (hpj : tape (pointBase + (j.val : ℤ)) ≠ 0)
    (hr : (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0) :
    ∃ c : RayConfiguration,
      rayMachineRun (sectionQueryProgram d i j) oracle (d + 5)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = d + 5 ∧ c.head = 0 ∧ c.queries = q + 1 ∧
      (∀ k : Fin d, c.tape (queryBase d + (k.val : ℤ)) =
        oracle (RaySection.coordinateSectionMap i (tape 17)
          (fun k => tape (pointBase + (k.val : ℤ)))
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1)) k) ∧
      (∀ z : ℤ, (z < queryBase d ∨ queryBase d + (d : ℤ) ≤ z) →
        z ≠ scratchCell d → c.tape z = tape z) := by
  let p : Fin d → ℝ := fun k => tape (pointBase + (k.val : ℤ))
  let r : Fin 2 → ℝ := fun k => if k = 0 then tape 0 else tape 1
  let f := RaySection.coordinateSectionMap i (tape 17) p
  have hgf := RaySection.coordinateSection_leftInverse i j hij hε p hpj
  have hnonzero : f r ≠ 0 := by
    intro hz
    apply hr
    exact hgf.injective (by simpa only [map_zero] using hz)
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbvector, hbframe⟩ :=
    sectionQuery_buildDirection i j oracle tape q
  have hf₀ : (sectionQueryProgram d i j)[d + 2]? =
      some (.shift (queryBase d) (d + 3)) := by
    have hh := sectionQuery_tail_fetch i j 1
    rw [show 1 + d + 1 = d + 2 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hf₁ : (sectionQueryProgram d i j)[d + 3]? = some (.query (d + 4)) := by
    have hh := sectionQuery_tail_fetch i j 2
    rw [show 1 + d + 2 = d + 3 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hf₂ : (sectionQueryProgram d i j)[d + 4]? =
      some (.shift (-queryBase d) (d + 5)) := by
    have hh := sectionQuery_tail_fetch i j 3
    rw [show 1 + d + 3 = d + 4 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  obtain ⟨c, hc, hcpc, hchead, hcq, hcreply, hcframe⟩ :=
    RayBlockQuery.run_query_at_block (sectionQueryProgram d i j) oracle (d + 2)
      (queryBase d) (f r) hnonzero b hbpc hbhead (fun k => congrFun hbvector k)
      hf₀ hf₁ hf₂
  refine ⟨c, ?_, hcpc, hchead, hcq.trans (congrArg (fun n => n + 1) hbq), hcreply, ?_⟩
  · rw [show d + 5 = (d + 2) + 3 by omega, run_add, hb, Option.bind_some, hc]
  · intro z hz hzs
    exact (hcframe z hz).trans (hbframe z hz hzs)

end Grunbaum2003.RaySectionProgram




namespace Grunbaum2003.RaySectionProgram

/-- The four literal field instructions after a physical query recover the
native coordinates, preserve the physical reply block, and spend no query. Only
the native header and the designated scratch cell may change. -/
theorem sectionQuery_recover {d : ℕ} (i j : Fin d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hpc : c.pc = d + 5) (hhead : c.head = 0)
    (hε : c.tape 17 ≠ 0) (hpj : c.tape (pointBase + (j.val : ℤ)) ≠ 0) :
    ∃ b : RayConfiguration,
      rayMachineRun (sectionQueryProgram d i j) oracle 4 c = some b ∧
      b.pc = d + 9 ∧ b.head = 0 ∧ b.queries = c.queries ∧
      (∀ k : Fin 2, b.tape (k.val : ℤ) =
        RaySection.coordinateSectionInverse i j (c.tape 17)
          (fun k => c.tape (pointBase + (k.val : ℤ)))
          (fun k => c.tape (queryBase d + (k.val : ℤ))) k) ∧
      (∀ k : Fin d, b.tape (queryBase d + (k.val : ℤ)) =
        c.tape (queryBase d + (k.val : ℤ))) ∧
      (∀ z : ℤ, z ≠ 0 → z ≠ 1 → z ≠ scratchCell d → b.tape z = c.tape z) := by
  let p : Fin d → ℝ := fun k => c.tape (pointBase + (k.val : ℤ))
  let v : Fin d → ℝ := fun k => c.tape (queryBase d + (k.val : ℤ))
  let ε := c.tape 17
  let β := v j / p j
  let α := (v i - β * p i) / ε
  let T₁ := Function.update c.tape (1 : ℤ) β
  let T₂ := Function.update T₁ (scratchCell d) (β * p i)
  let T₃ := Function.update T₂ (scratchCell d) (v i - β * p i)
  let T₄ := Function.update T₃ (0 : ℤ) α
  let c₁ : RayConfiguration := {pc := d + 6, head := 0, tape := T₁, queries := c.queries}
  let c₂ : RayConfiguration := {pc := d + 7, head := 0, tape := T₂, queries := c.queries}
  let c₃ : RayConfiguration := {pc := d + 8, head := 0, tape := T₃, queries := c.queries}
  let b : RayConfiguration := {pc := d + 9, head := 0, tape := T₄, queries := c.queries}
  have hpoint₁ : ∀ k : Fin d, pointBase + (k.val : ℤ) ≠ 1 := by
    intro k
    dsimp only [pointBase]
    omega
  have hreply₀ : ∀ k : Fin d, queryBase d + (k.val : ℤ) ≠ 0 := by
    intro k
    dsimp only [queryBase]
    omega
  have hreply₁ : ∀ k : Fin d, queryBase d + (k.val : ℤ) ≠ 1 := by
    intro k
    dsimp only [queryBase]
    omega
  have hreplyS : ∀ k : Fin d, queryBase d + (k.val : ℤ) ≠ scratchCell d := by
    intro k
    dsimp only [queryBase, scratchCell]
    omega
  have h₁S : (1 : ℤ) ≠ scratchCell d := by dsimp only [scratchCell]; omega
  have hεS : (17 : ℤ) ≠ scratchCell d := by dsimp only [scratchCell]; omega
  have hf₄ : (sectionQueryProgram d i j)[d + 5]? =
      some (.div 1 (queryBase d + (j.val : ℤ)) (pointBase + (j.val : ℤ)) (d + 6)) := by
    have hh := sectionQuery_tail_fetch i j 4
    rw [show 1 + d + 4 = d + 5 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hf₅ : (sectionQueryProgram d i j)[d + 6]? =
      some (.mul (scratchCell d) 1 (pointBase + (i.val : ℤ)) (d + 7)) := by
    have hh := sectionQuery_tail_fetch i j 5
    rw [show 1 + d + 5 = d + 6 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hf₆ : (sectionQueryProgram d i j)[d + 7]? =
      some (.sub (scratchCell d) (queryBase d + (i.val : ℤ)) (scratchCell d) (d + 8)) := by
    have hh := sectionQuery_tail_fetch i j 6
    rw [show 1 + d + 6 = d + 7 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hf₇ : (sectionQueryProgram d i j)[d + 8]? =
      some (.div 0 (scratchCell d) 17 (d + 9)) := by
    have hh := sectionQuery_tail_fetch i j 7
    rw [show 1 + d + 7 = d + 8 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  have hT₁one : T₁ 1 = β := Function.update_self _ _ _
  have hT₁point : T₁ (pointBase + (i.val : ℤ)) = p i :=
    Function.update_of_ne (hpoint₁ i) _ _
  have hT₂reply : T₂ (queryBase d + (i.val : ℤ)) = v i := by
    simp only [T₂, T₁, Function.update_of_ne (hreplyS i), Function.update_of_ne (hreply₁ i)]
    rfl
  have hT₂scratch : T₂ (scratchCell d) = β * p i := Function.update_self _ _ _
  have hT₃scratch : T₃ (scratchCell d) = v i - β * p i := Function.update_self _ _ _
  have hT₃epsilon : T₃ 17 = ε := by
    simp only [T₃, T₂, T₁, Function.update_of_ne hεS,
      Function.update_of_ne (by decide : (17 : ℤ) ≠ 1)]
    rfl
  have hε' : ε ≠ 0 := hε
  have hstep₀ : rayMachineStep (sectionQueryProgram d i j) oracle c = some c₁ := by
    simp only [rayMachineStep, hpc, hf₄, hhead, zero_add, if_neg hpj, c₁, T₁]
    rfl
  have hstep₁ : rayMachineStep (sectionQueryProgram d i j) oracle c₁ = some c₂ := by
    simp only [rayMachineStep, c₁, hf₅, zero_add, hT₁one, hT₁point, c₂, T₂]
  have hstep₂ : rayMachineStep (sectionQueryProgram d i j) oracle c₂ = some c₃ := by
    simp only [rayMachineStep, c₂, hf₆, zero_add, hT₂reply, hT₂scratch, c₃, T₃]
  have hstep₃ : rayMachineStep (sectionQueryProgram d i j) oracle c₃ = some b := by
    simp only [rayMachineStep, c₃, hf₇, zero_add, hT₃scratch, hT₃epsilon,
      if_neg hε', b, T₄]
    rfl
  refine ⟨b, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [rayMachineRun, hstep₀, hstep₁, hstep₂, hstep₃, Option.bind_some]
  · intro k
    fin_cases k
    · change T₄ 0 = α
      exact Function.update_self _ _ _
    · change T₄ 1 = β
      simp only [T₄, T₃, T₂, T₁, Function.update_of_ne (by decide : (1 : ℤ) ≠ 0),
        Function.update_of_ne h₁S, Function.update_self]
  · intro k
    change T₄ (queryBase d + (k.val : ℤ)) = c.tape (queryBase d + (k.val : ℤ))
    simp only [T₄, T₃, T₂, T₁, Function.update_of_ne (hreply₀ k),
      Function.update_of_ne (hreplyS k), Function.update_of_ne (hreply₁ k)]
  · intro z hz₀ hz₁ hzS
    change T₄ z = c.tape z
    simp only [T₄, T₃, T₂, T₁, Function.update_of_ne hz₀,
      Function.update_of_ne hzS, Function.update_of_ne hz₁]

end Grunbaum2003.RaySectionProgram




namespace Grunbaum2003.RaySectionProgram

private theorem run_add_sqc {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

/-- Complete literal physical section-query adapter. It constructs the
direction, executes one original ambient query, restores head0, and recovers
the native reply by the explicit guarded field formulas. All native working
cells except the input/output header are preserved. A uniform caller must still
dispatch among the finitely many coordinate pivots and wire this routine into
its own literal code; no unrestricted protocol compiler is assumed. -/
theorem sectionQueryProgram_correct {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ)
    (hε : tape 17 ≠ 0) (hpj : tape (pointBase + (j.val : ℤ)) ≠ 0)
    (hr : (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0) :
    ∃ c : RayConfiguration,
      rayMachineRun (sectionQueryProgram d i j) oracle (d + 9)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      (sectionQueryProgram d i j)[c.pc]? = some .halt ∧
      c.head = 0 ∧ c.queries = q + 1 ∧
      (∀ k : Fin 2, c.tape (k.val : ℤ) =
        RaySection.coordinateSectionInverse i j (tape 17)
          (fun k => tape (pointBase + (k.val : ℤ)))
          (oracle (RaySection.coordinateSectionMap i (tape 17)
            (fun k => tape (pointBase + (k.val : ℤ)))
            (fun k : Fin 2 => if k = 0 then tape 0 else tape 1))) k) ∧
      (∀ k : Fin d, c.tape (queryBase d + (k.val : ℤ)) =
        oracle (RaySection.coordinateSectionMap i (tape 17)
          (fun k => tape (pointBase + (k.val : ℤ)))
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1)) k) ∧
      (∀ z : ℤ, z ≠ 0 → z ≠ 1 →
        (z < queryBase d ∨ queryBase d + (d : ℤ) ≤ z) → z ≠ scratchCell d →
        c.tape z = tape z) := by
  let p : Fin d → ℝ := fun k => tape (pointBase + (k.val : ℤ))
  let r : Fin 2 → ℝ := fun k => if k = 0 then tape 0 else tape 1
  let f := RaySection.coordinateSectionMap i (tape 17) p
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbreply, hbframe⟩ :=
    sectionQuery_issue i j hij oracle tape q hε hpj hr
  have hεkeep : b.tape 17 = tape 17 := by
    apply hbframe
    · left
      dsimp only [queryBase]
      omega
    · dsimp only [scratchCell]
      omega
  have hpkeep : (fun k : Fin d => b.tape (pointBase + (k.val : ℤ))) = p := by
    funext k
    apply hbframe
    · left
      dsimp only [pointBase, queryBase]
      omega
    · dsimp only [pointBase, scratchCell]
      omega
  have hvkeep : (fun k : Fin d => b.tape (queryBase d + (k.val : ℤ))) = oracle (f r) :=
    funext hbreply
  have hεb : b.tape 17 ≠ 0 := by rw [hεkeep]; exact hε
  have hpjb : b.tape (pointBase + (j.val : ℤ)) ≠ 0 := by
    have hh := congrFun hpkeep j
    change b.tape (pointBase + (j.val : ℤ)) = p j at hh
    rw [hh]
    exact hpj
  obtain ⟨c, hc, hcpc, hchead, hcq, hcheader, hcreply, hcframe⟩ :=
    sectionQuery_recover i j oracle b hbpc hbhead hεb hpjb
  have hheader : ∀ k : Fin 2, c.tape (k.val : ℤ) =
      RaySection.coordinateSectionInverse i j (tape 17) p (oracle (f r)) k := by
    intro k
    simpa only [hεkeep, hpkeep, hvkeep] using hcheader k
  refine ⟨c, ?_, ?_, hchead, hcq.trans hbq, hheader,
    fun k => (hcreply k).trans (hbreply k), ?_⟩
  · rw [show d + 9 = (d + 5) + 4 by omega, run_add, hb, Option.bind_some, hc]
  · rw [hcpc]
    have hh := sectionQuery_tail_fetch i j 8
    rw [show 1 + d + 8 = d + 9 by omega] at hh
    simpa only [sectionQueryTail, List.getElem?_cons_succ, List.getElem?_cons_zero] using hh
  · intro z hz₀ hz₁ hzblock hzS
    exact (hcframe z hz₀ hz₁ hzS).trans (hbframe z hzblock hzS)

end Grunbaum2003.RaySectionProgram


namespace Grunbaum2003

theorem rayMachine_relocate_and_section_query_adapter :
    (∃ (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration),
      ∀ (d : ℕ) (pre program : List RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) ∧
    (∀ (d : ℕ) (i j : Fin d), i ≠ j →
      ∃ prog : List RayInstruction,
        prog.length = d + 10 ∧
        ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
          tape 17 ≠ 0 →
          tape (18 + (j.val : ℤ)) ≠ 0 →
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0 →
          ∃ c : RayConfiguration,
            rayMachineRun prog oracle (d + 9)
              {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
            prog[c.pc]? = some .halt ∧
            c.head = 0 ∧ c.queries = q + 1 ∧
            (∀ k : Fin 2, c.tape (k.val : ℤ) =
              let p : Fin d → ℝ := fun m => tape (18 + (m.val : ℤ))
              let y : Fin d → ℝ := oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) + tape 1 * p m)
              if k = 0 then (y i - (y j / p j) * p i) / tape 17 else y j / p j) ∧
            (∀ k : Fin d, c.tape (18 + (d : ℤ) + (k.val : ℤ)) =
              oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) +
                  tape 1 * tape (18 + (m.val : ℤ))) k) ∧
            (∀ z : ℤ, z ≠ 0 → z ≠ 1 →
              (z < 18 + (d : ℤ) ∨ 18 + (d : ℤ) + (d : ℤ) ≤ z) →
              z ≠ 18 + 2 * (d : ℤ) → c.tape z = tape z)) := by
  refine ⟨⟨RayCode.relocateInstruction, RayCode.relocateConfiguration, ?_⟩, ?_⟩
  · intro d pre program oracle t c
    exact ⟨rfl, rfl, rfl, rfl,
      RayCode.relocated_run pre program oracle t c,
      RayCode.relocated_halt pre program c⟩
  · intro d i j hij
    refine ⟨RaySectionProgram.sectionQueryProgram d i j,
      RaySectionProgram.sectionQueryProgram_length i j, ?_⟩
    intro oracle tape q hε hpj hr
    exact RaySectionProgram.sectionQueryProgram_correct i j hij oracle tape q hε hpj hr

end Grunbaum2003
end

theorem inline_solution :
    (∃ (relocateInst : ℕ → Grunbaum2003.RayInstruction → Grunbaum2003.RayInstruction)
       (relocateCfg : ℕ → Grunbaum2003.RayConfiguration → Grunbaum2003.RayConfiguration),
      ∀ (d : ℕ) (pre program : List Grunbaum2003.RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : Grunbaum2003.RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        Grunbaum2003.rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (Grunbaum2003.rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) ∧
    (∀ (d : ℕ) (i j : Fin d), i ≠ j →
      ∃ prog : List Grunbaum2003.RayInstruction,
        prog.length = d + 10 ∧
        ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
          tape 17 ≠ 0 →
          tape (18 + (j.val : ℤ)) ≠ 0 →
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0 →
          ∃ c : Grunbaum2003.RayConfiguration,
            Grunbaum2003.rayMachineRun prog oracle (d + 9)
              {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
            prog[c.pc]? = some .halt ∧
            c.head = 0 ∧ c.queries = q + 1 ∧
            (∀ k : Fin 2, c.tape (k.val : ℤ) =
              let p : Fin d → ℝ := fun m => tape (18 + (m.val : ℤ))
              let y : Fin d → ℝ := oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) + tape 1 * p m)
              if k = 0 then (y i - (y j / p j) * p i) / tape 17 else y j / p j) ∧
            (∀ k : Fin d, c.tape (18 + (d : ℤ) + (k.val : ℤ)) =
              oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) +
                  tape 1 * tape (18 + (m.val : ℤ))) k) ∧
            (∀ z : ℤ, z ≠ 0 → z ≠ 1 →
              (z < 18 + (d : ℤ) ∨ 18 + (d : ℤ) + (d : ℤ) ≤ z) →
              z ≠ 18 + 2 * (d : ℤ) → c.tape z = tape z)) :=
  Grunbaum2003.rayMachine_relocate_and_section_query_adapter

end RayCounterfamilyInline00

namespace Grunbaum2003

theorem rayMachine_relocate_and_section_query_adapter :
(∃ (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration),
      ∀ (d : ℕ) (pre program : List RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) ∧
    (∀ (d : ℕ) (i j : Fin d), i ≠ j →
      ∃ prog : List RayInstruction,
        prog.length = d + 10 ∧
        ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
          tape 17 ≠ 0 →
          tape (18 + (j.val : ℤ)) ≠ 0 →
          (fun k : Fin 2 => if k = 0 then tape 0 else tape 1) ≠ 0 →
          ∃ c : RayConfiguration,
            rayMachineRun prog oracle (d + 9)
              {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
            prog[c.pc]? = some .halt ∧
            c.head = 0 ∧ c.queries = q + 1 ∧
            (∀ k : Fin 2, c.tape (k.val : ℤ) =
              let p : Fin d → ℝ := fun m => tape (18 + (m.val : ℤ))
              let y : Fin d → ℝ := oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) + tape 1 * p m)
              if k = 0 then (y i - (y j / p j) * p i) / tape 17 else y j / p j) ∧
            (∀ k : Fin d, c.tape (18 + (d : ℤ) + (k.val : ℤ)) =
              oracle (fun m =>
                (if m = i then tape 17 * tape 0 else 0) +
                  tape 1 * tape (18 + (m.val : ℤ))) k) ∧
            (∀ z : ℤ, z ≠ 0 → z ≠ 1 →
              (z < 18 + (d : ℤ) ∨ 18 + (d : ℤ) + (d : ℤ) ≤ z) →
              z ≠ 18 + 2 * (d : ℤ) → c.tape z = tape z)) :=
  @RayCounterfamilyInline00.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_inner_simplex_and_signed_direction_program.lean
-- SHA256: f5c912d6281c5254a27448ecdec1681496020571b9b372facda4d705f59ec8a6
namespace RayCounterfamilyInline01

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Grunbaum2003.RayInner

def axis {d : ℕ} (i : Fin d) : Fin d → ℝ := fun j => if j = i then 1 else 0
def ones (d : ℕ) : Fin d → ℝ := fun _ => 1

theorem sum_axis_eq {d : ℕ} (c : Fin d → ℝ) :
    (∑ i : Fin d, c i • axis i) = c := by
  classical
  ext j
  simp [axis, Finset.sum_apply]

theorem convex_sum_mem_le_one {d : ℕ} {I : Type*} [Fintype I]
    {P : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    (w : I → ℝ) (z : I → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (hz : ∀ i, z i ∈ P) :
    (∑ i, w i • z i) ∈ P := by
  classical
  let w' : Option I → ℝ := fun i => match i with
    | none => 1 - ∑ j, w j
    | some j => w j
  let z' : Option I → Fin d → ℝ := fun i => match i with
    | none => 0
    | some j => z j
  have hw' : ∀ i ∈ (Finset.univ : Finset (Option I)), 0 ≤ w' i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hw i
  have hs' : ∑ i : Option I, w' i = 1 := by
    simp only [Fintype.sum_option, w']
    ring
  have hz' : ∀ i ∈ (Finset.univ : Finset (Option I)), z' i ∈ P := by
    intro i _
    cases i with
    | none => exact hzero
    | some i => exact hz i
  have h := hconv.sum_mem hw' hs' hz'
  simpa only [Fintype.sum_option, w', z', smul_zero, zero_add] using h

def samplePoint {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : Option (Fin d) → Fin d → ℝ
  | none => (-s) • ones d
  | some i => t i • axis i

def sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range (samplePoint t s))

theorem samplePoint_mem_hull {d : ℕ} (t : Fin d → ℝ) (s : ℝ) (i : Option (Fin d)) :
    samplePoint t s i ∈ sampleHull t s :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

theorem sampleHull_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (t : Fin d → ℝ) (s : ℝ)
    (hneg : (-s) • ones d ∈ P) (hpos : ∀ i, t i • axis i ∈ P) :
    sampleHull t s ⊆ P := by
  apply convexHull_min _ hconv
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hneg
  | some i => exact hpos i

theorem weighted_sample_sum {d : ℕ} (t : Fin d → ℝ) (s c : ℝ)
    (ht : ∀ i, t i ≠ 0) (hs : s ≠ 0) :
    (∑ i : Option (Fin d),
      (match i with | none => c / s | some j => c / t j) • samplePoint t s i) = 0 := by
  classical
  rw [Fintype.sum_option]
  change (c / s) • ((-s) • ones d) + ∑ i, (c / t i) • (t i • axis i) = 0
  have hpos (i : Fin d) : (c / t i) • (t i • axis i) = c • axis i := by
    rw [smul_smul, div_mul_cancel₀ c (ht i)]
  rw [smul_smul, mul_neg, div_mul_cancel₀ c hs,
    Finset.sum_congr rfl (fun i _ => hpos i), sum_axis_eq]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, ones, smul_eq_mul, mul_one, Pi.zero_apply,
    neg_add_cancel]

theorem zero_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) : (0 : Fin d → ℝ) ∈ sampleHull t s := by
  classical
  let C := s⁻¹ + ∑ i, (t i)⁻¹
  have hC : 0 < C := add_pos_of_pos_of_nonneg (inv_pos.mpr hs)
    (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (ht i).le))
  let c := C⁻¹
  let w : Option (Fin d) → ℝ := fun i => match i with
    | none => c / s
    | some j => c / t j
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact div_nonneg (inv_nonneg.mpr hC.le) hs.le
    | some i => exact div_nonneg (inv_nonneg.mpr hC.le) (ht i).le
  have hsum : ∑ i : Option (Fin d), w i = 1 := by
    simp only [Fintype.sum_option, w, div_eq_mul_inv, ← Finset.mul_sum]
    rw [← mul_add]
    exact inv_mul_cancel₀ hC.ne'
  have h := (convex_convexHull ℝ (Set.range (samplePoint t s))).sum_mem hw hsum
    (fun i _ => samplePoint_mem_hull t s i)
  change (∑ i : Option (Fin d), w i • samplePoint t s i) ∈ sampleHull t s at h
  simpa only [w, weighted_sample_sum t s c (fun i => (ht i).ne') hs.ne'] using h

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInner

def sampleScale {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : ℝ :=
  (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹

theorem sampleScale_pos_capacity {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) :
    0 < sampleScale t s ∧
      sampleScale t s / s + ∑ i, sampleScale t s / t i ≤ 1 := by
  have hsum : 0 ≤ ∑ i, (t i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (ht i).le)
  have hden : 0 < 1 + s⁻¹ + ∑ i, (t i)⁻¹ := by
    linarith only [inv_pos.mpr hs, hsum]
  have ha : 0 < sampleScale t s := inv_pos.mpr hden
  have hprod : sampleScale t s * (1 + s⁻¹ + ∑ i, (t i)⁻¹) = 1 :=
    inv_mul_cancel₀ hden.ne'
  refine ⟨ha, ?_⟩
  calc
    sampleScale t s / s + ∑ i, sampleScale t s / t i =
        sampleScale t s * (1 + s⁻¹ + ∑ i, (t i)⁻¹) - sampleScale t s := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      ring
    _ = 1 - sampleScale t s := by rw [hprod]
    _ ≤ 1 := sub_le_self 1 ha.le

theorem signed_axes_mem_of_samples {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    (t : Fin d → ℝ) (s : ℝ) (ht : ∀ i, 0 < t i) (hs : 0 < s)
    (hneg : (-s) • ones d ∈ P) (hpos : ∀ i, t i • axis i ∈ P) :
    ∀ i : Fin d, sampleScale t s • axis i ∈ P ∧ (-sampleScale t s) • axis i ∈ P := by
  classical
  let a := sampleScale t s
  have ha : 0 < a := (sampleScale_pos_capacity t s ht hs).1
  have hcap : a / s + ∑ j, a / t j ≤ 1 := (sampleScale_pos_capacity t s ht hs).2
  have hratio (j : Fin d) : 0 ≤ a / t j := div_nonneg ha.le (ht j).le
  have hrpole : 0 ≤ a / s := div_nonneg ha.le hs.le
  intro i
  constructor
  · have hiSum : a / t i ≤ ∑ j, a / t j :=
      Finset.single_le_sum (fun j _ => hratio j) (Finset.mem_univ i)
    have hiOne : a / t i ≤ 1 := by linarith only [hiSum, hcap, hrpole]
    have h := hconv hzero (hpos i) (sub_nonneg.mpr hiOne) (hratio i)
      (sub_add_cancel 1 (a / t i))
    simpa only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ a (ht i).ne'] using h
  · let w : Option (Fin d) → ℝ := fun j => match j with
      | none => a / s
      | some j => if j = i then 0 else a / t j
    have hw : ∀ j, 0 ≤ w j := by
      intro j
      cases j with
      | none => exact hrpole
      | some j =>
          dsimp only [w]
          split_ifs
          · exact le_rfl
          · exact hratio j
    have hsum : ∑ j : Option (Fin d), w j ≤ 1 := by
      rw [Fintype.sum_option]
      change a / s + ∑ j, (if j = i then 0 else a / t j) ≤ 1
      calc
        _ ≤ a / s + ∑ j, a / t j := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j = i
          · rw [if_pos hj]
            exact hratio j
          · rw [if_neg hj]
        _ ≤ 1 := hcap
    have hz : ∀ j, samplePoint t s j ∈ P := by
      intro j
      cases j with
      | none => exact hneg
      | some j => exact hpos j
    have h := convex_sum_mem_le_one hconv hzero w (samplePoint t s) hw hsum hz
    have hterm (j : Fin d) :
        (if j = i then 0 else a / t j) • (t j • axis j) =
          if j = i then 0 else a • axis j := by
      by_cases hj : j = i
      · simp only [hj, ite_true, zero_smul]
      · simp only [hj, ite_false, smul_smul, div_mul_cancel₀ a (ht j).ne']
    have hfull : (∑ j : Fin d, a • axis j) = a • ones d := by
      rw [sum_axis_eq]
      ext j
      simp only [Pi.smul_apply, ones, smul_eq_mul, mul_one]
    have hremove : (∑ j : Fin d, if j = i then 0 else a • axis j) =
        a • ones d - a • axis i := by
      have heq (j : Fin d) : (if j = i then 0 else a • axis j) =
          a • axis j - (if j = i then a • axis i else 0) := by
        by_cases hj : j = i <;> simp only [hj, ite_true, ite_false, sub_self, sub_zero]
      rw [Finset.sum_congr rfl (fun j _ => heq j), Finset.sum_sub_distrib, hfull]
      simp
    have hpoint : (∑ j : Option (Fin d), w j • samplePoint t s j) = (-a) • axis i := by
      rw [Fintype.sum_option]
      change (a / s) • ((-s) • ones d) +
        (∑ j, (if j = i then 0 else a / t j) • (t j • axis j)) = (-a) • axis i
      rw [Finset.sum_congr rfl (fun j _ => hterm j), hremove,
        smul_smul, mul_neg, div_mul_cancel₀ a hs.ne']
      simp only [neg_smul]
      abel
    exact hpoint ▸ h

theorem signed_axes_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) :
    ∀ i : Fin d, sampleScale t s • axis i ∈ sampleHull t s ∧
      (-sampleScale t s) • axis i ∈ sampleHull t s := by
  apply signed_axes_mem_of_samples (convex_convexHull ℝ _)
    (zero_mem_sampleHull t s ht hs) t s ht hs
  · exact samplePoint_mem_hull t s none
  · intro i
    exact samplePoint_mem_hull t s (some i)

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInner

def directionScale {d : ℕ} (a : ℝ) (u : Fin d → ℝ) : ℝ :=
  a / (1 + ∑ i, |u i|)

theorem directionScale_pos {d : ℕ} {a : ℝ} (ha : 0 < a) (u : Fin d → ℝ) :
    0 < directionScale a u :=
  div_pos ha (add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => abs_nonneg (u i))))

theorem directional_point_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    {a : ℝ} (ha : 0 < a)
    (haxes : ∀ i : Fin d, a • axis i ∈ P ∧ (-a) • axis i ∈ P)
    (u : Fin d → ℝ) : directionScale a u • u ∈ P := by
  classical
  let D := 1 + ∑ i, |u i|
  have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => abs_nonneg (u i)))
  let w : Fin d → ℝ := fun i => |u i| / D
  let z : Fin d → Fin d → ℝ := fun i =>
    if 0 ≤ u i then a • axis i else (-a) • axis i
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (abs_nonneg (u i)) hD.le
  have hsum : ∑ i, w i ≤ 1 := by
    change (∑ i, |u i| / D) ≤ 1
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hD).mpr
    dsimp only [D]
    linarith only [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      abs_nonneg (u i))]
  have hz : ∀ i, z i ∈ P := by
    intro i
    dsimp only [z]
    split_ifs
    · exact (haxes i).1
    · exact (haxes i).2
  have h := convex_sum_mem_le_one hconv hzero w z hw hsum hz
  have hterm (i : Fin d) : w i • z i = (a / D * u i) • axis i := by
    dsimp only [w, z]
    by_cases hi : 0 ≤ u i
    · rw [if_pos hi, abs_of_nonneg hi, smul_smul]
      congr 1
      ring
    · rw [if_neg hi, abs_of_neg (lt_of_not_ge hi), smul_smul]
      congr 1
      ring
  have hpoint : (∑ i, w i • z i) = directionScale a u • u := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), sum_axis_eq]
    rfl
  exact hpoint ▸ h

theorem signed_direction_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    {a : ℝ} (ha : 0 < a)
    (haxes : ∀ i : Fin d, a • axis i ∈ P ∧ (-a) • axis i ∈ P)
    (u : Fin d → ℝ) :
    0 < directionScale a u ∧
      (-directionScale a u) • u ∈ P ∧ directionScale a u • u ∈ P := by
  refine ⟨directionScale_pos ha u, ?_, directional_point_mem hconv hzero ha haxes u⟩
  have h := directional_point_mem hconv hzero ha haxes (-u)
  simpa only [directionScale, Pi.neg_apply, abs_neg, smul_neg, neg_smul] using h

theorem signed_direction_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) (u : Fin d → ℝ) :
    0 < directionScale (sampleScale t s) u ∧
      (-directionScale (sampleScale t s) u) • u ∈ sampleHull t s ∧
      directionScale (sampleScale t s) u • u ∈ sampleHull t s :=
  signed_direction_mem (convex_convexHull ℝ _) (zero_mem_sampleHull t s ht hs)
    (sampleScale_pos_capacity t s ht hs).1 (signed_axes_mem_sampleHull t s ht hs) u

end Grunbaum2003.RayInner

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003.RayInner

def negativeDirection (d : ℕ) : Fin d → ℝ := (-1 : ℝ) • ones d

theorem axis_ne_zero {d : ℕ} (i : Fin d) : axis i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp only [axis, ite_true, Pi.zero_apply] at hi
  exact one_ne_zero hi

theorem negativeDirection_ne_zero {d : ℕ} (j : Fin d) : negativeDirection d ≠ 0 := by
  intro h
  have hj := congrFun h j
  simp only [negativeDirection, ones, Pi.smul_apply, smul_eq_mul, mul_one,
    Pi.zero_apply, neg_eq_zero] at hj
  exact one_ne_zero hj

def initialDirections (d : ℕ) : List (Fin d → ℝ) :=
  (List.finRange d).map axis ++ [negativeDirection d]

theorem initialDirections_length (d : ℕ) : (initialDirections d).length = d + 1 := by
  simp only [initialDirections, List.length_append, List.length_map, List.length_finRange,
    List.length_singleton]

theorem initialDirections_nonzero {d : ℕ} (hd : 0 < d) :
    ∀ v ∈ initialDirections d, v ≠ 0 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact axis_ne_zero i
  · have hv' : v = negativeDirection d := List.mem_singleton.mp hv
    rw [hv']
    exact negativeDirection_ne_zero ⟨0, hd⟩

def positiveScale {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d) : ℝ :=
  oracle (axis i) i

def negativeScale {d : ℕ} (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  -oracle (negativeDirection d) j

def actualSample {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) :
    Option (Fin d) → Fin d → ℝ
  | none => oracle (negativeDirection d)
  | some i => oracle (axis i)

def actualSampleHull {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range (actualSample oracle))

def innerDirectionScale {d : ℕ} (j : Fin d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (u : Fin d → ℝ) : ℝ :=
  directionScale (sampleScale (positiveScale oracle) (negativeScale j oracle)) u

theorem rayOracle_positive_samples {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle) :
    ∀ i : Fin d, 0 < positiveScale oracle i ∧
      oracle (axis i) = positiveScale oracle i • axis i := by
  intro i
  obtain ⟨_, t, ht, hanswer⟩ := horacle (axis i) (axis_ne_zero i)
  have hcoord : positiveScale oracle i = t := by
    dsimp only [positiveScale]
    rw [hanswer]
    simp only [Pi.smul_apply, smul_eq_mul, axis, ite_true, mul_one]
  exact ⟨hcoord.symm ▸ ht, hcoord.symm ▸ hanswer⟩

theorem rayOracle_negative_sample {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) : 0 < negativeScale j oracle ∧
      oracle (negativeDirection d) = (-negativeScale j oracle) • ones d := by
  obtain ⟨_, s, hs, hanswer⟩ := horacle (negativeDirection d) (negativeDirection_ne_zero j)
  have hcoord : negativeScale j oracle = s := by
    dsimp only [negativeScale]
    rw [hanswer]
    simp only [negativeDirection, ones, Pi.smul_apply, smul_eq_mul, mul_one,
      mul_neg_one, neg_neg]
  refine ⟨hcoord.symm ▸ hs, ?_⟩
  rw [hcoord, hanswer, negativeDirection, smul_smul, mul_neg_one]

theorem actualSampleHull_eq {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) :
    actualSampleHull oracle = sampleHull (positiveScale oracle) (negativeScale j oracle) := by
  have hfamily : actualSample oracle = samplePoint (positiveScale oracle) (negativeScale j oracle) := by
    funext i
    cases i with
    | none => exact (rayOracle_negative_sample horacle j).2
    | some i => exact (rayOracle_positive_samples horacle i).2
  change convexHull ℝ (Set.range (actualSample oracle)) = _
  rw [hfamily]
  rfl

theorem actualSampleHull_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) : actualSampleHull oracle ⊆ P := by
  apply convexHull_min _ hconv
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hclosed.frontier_subset (horacle _ (negativeDirection_ne_zero j)).1
  | some i => exact hclosed.frontier_subset (horacle _ (axis_ne_zero i)).1

theorem rayOracle_inner_sample_hull {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) :
    actualSampleHull oracle ⊆ P ∧ (0 : Fin d → ℝ) ∈ actualSampleHull oracle ∧
      ∀ u : Fin d → ℝ, 0 < innerDirectionScale j oracle u ∧
        (-innerDirectionScale j oracle u) • u ∈ actualSampleHull oracle ∧
        innerDirectionScale j oracle u • u ∈ actualSampleHull oracle := by
  have ht := fun i => (rayOracle_positive_samples horacle i).1
  have hs := (rayOracle_negative_sample horacle j).1
  refine ⟨actualSampleHull_subset hconv hclosed horacle j, ?_, ?_⟩
  · rw [actualSampleHull_eq horacle j]
    exact zero_mem_sampleHull _ _ ht hs
  · intro u
    simpa only [actualSampleHull_eq horacle j, innerDirectionScale] using
      signed_direction_mem_sampleHull (positiveScale oracle) (negativeScale j oracle) ht hs u

theorem rayOracle_signed_inner_points {d : ℕ} {P : Set (Fin d → ℝ)}
    (hd : 0 < d) (hP : IsDPolytope P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (u : Fin d → ℝ) :
    0 < innerDirectionScale ⟨0, hd⟩ oracle u ∧
      (-innerDirectionScale ⟨0, hd⟩ oracle u) • u ∈ P ∧
      innerDirectionScale ⟨0, hd⟩ oracle u • u ∈ P := by
  obtain ⟨V, hV, _, hPV⟩ := hP.1
  have hconv : Convex ℝ P := by rw [hPV]; exact convex_convexHull ℝ V
  have hclosed : IsClosed P := by rw [hPV]; exact hV.isClosed_convexHull ℝ
  have h := rayOracle_inner_sample_hull hconv hclosed horacle ⟨0, hd⟩
  exact ⟨(h.2.2 u).1, h.1 (h.2.2 u).2.1, h.1 (h.2.2 u).2.2⟩

theorem zero_dimensional_inner_points {P : Set (Fin 0 → ℝ)}
    (hP : IsDPolytope P) (u : Fin 0 → ℝ) :
    (0 : ℝ) < 1 ∧ (-1 : ℝ) • u ∈ P ∧ (1 : ℝ) • u ∈ P := by
  obtain ⟨V, _, ⟨v, hv⟩, hPV⟩ := hP.1
  have hvP : v ∈ P := by
    rw [hPV]
    exact subset_convexHull ℝ V hv
  have hm : (-1 : ℝ) • u = v := by funext i; exact Fin.elim0 i
  have hp : (1 : ℝ) • u = v := by funext i; exact Fin.elim0 i
  exact ⟨zero_lt_one, hm.symm ▸ hvP, hp.symm ▸ hvP⟩

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInnerProgram

def directionEntry (d n j : ℕ) : ℚ :=
  if n < d then if j = n then 1 else 0 else -1

def bodyLength (d : ℕ) : ℕ := (d + 1) * (d + 2)

def bodyInstruction (d k : ℕ) : RayInstruction :=
  let n := k / (d + 2)
  let j := k % (d + 2)
  if j < d then .constant (j : ℤ) (directionEntry d n j) (k + 2)
  else if j = d then .query (k + 2)
  else .shift (d : ℤ) (k + 2)

def innerSampleProgram (d : ℕ) : List RayInstruction :=
  if d = 0 then [.halt] else
    .shift (d : ℤ) 1 ::
      (List.ofFn (fun k : Fin (bodyLength d) => bodyInstruction d k.val) ++
        [.shift (-(((d + 2) * d : ℕ) : ℤ)) (bodyLength d + 2), .halt])

private theorem packed_lt {m n i j : ℕ} (hi : i < m) (hj : j < n) :
    i * n + j < m * n := by
  calc
    i * n + j < i * n + n := Nat.add_lt_add_left hj _
    _ = (i + 1) * n := (Nat.succ_mul i n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)

private theorem block_div_mod (d n j : ℕ) (hj : j < d + 2) :
    (n * (d + 2) + j) / (d + 2) = n ∧
      (n * (d + 2) + j) % (d + 2) = j := by
  have hB : 0 < d + 2 := by omega
  have heq : n * (d + 2) + j = j + (d + 2) * n := by ac_rfl
  rw [heq]
  constructor
  · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem initial_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[0]? = some (.shift (d : ℤ) 1) := by
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_zero]

theorem block_fetch {d n j : ℕ} (hd : 0 < d) (hn : n < d + 1) (hj : j < d + 2) :
    (innerSampleProgram d)[1 + n * (d + 2) + j]? =
      some (if j < d then .constant (j : ℤ) (directionEntry d n j) (n * (d + 2) + j + 2)
        else if j = d then .query (n * (d + 2) + j + 2)
        else .shift (d : ℤ) (n * (d + 2) + j + 2)) := by
  have hk : n * (d + 2) + j < bodyLength d := packed_lt hn hj
  have hidx : 1 + n * (d + 2) + j = (n * (d + 2) + j) + 1 := by omega
  rw [hidx]
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, hk, ↓reduceIte,
    List.getElem?_ofFn, ↓reduceDIte, bodyInstruction,
    (block_div_mod d n j hj).1, (block_div_mod d n j hj).2]

theorem final_shift_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[1 + bodyLength d]? =
      some (.shift (-(((d + 2) * d : ℕ) : ℤ)) (bodyLength d + 2)) := by
  rw [show 1 + bodyLength d = bodyLength d + 1 by omega]
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, lt_self_iff_false, ↓reduceIte,
    Nat.sub_self, List.getElem?_cons_zero]

theorem final_halt_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[bodyLength d + 2]? = some .halt := by
  have hn : ¬ bodyLength d + 1 < bodyLength d := by omega
  have hs : bodyLength d + 1 - bodyLength d = 1 := by omega
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, hn, ↓reduceIte, hs,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

private theorem run_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

private theorem run_succ_last {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + 1) c =
      (rayMachineRun program oracle a c).bind (rayMachineStep program oracle) := by
  rw [run_add program oracle a 1 c]
  simp only [rayMachineRun, Option.bind_fun_some]

private theorem run_constants {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (h : ℤ)
    (values : Fin d → ℚ) (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = h)
    (hfetch : ∀ i : Fin d, program[base + i.val]? =
      some (.constant (i.val : ℤ) (values i) (base + i.val + 1))) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle d c = some c' ∧
      c'.pc = base + d ∧ c'.head = h ∧ c'.queries = c.queries ∧
      (∀ i : Fin d, c'.tape (h + (i.val : ℤ)) = (values i : ℝ)) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
  classical
  have hrun : ∀ n, n ≤ d → ∃ c' : RayConfiguration,
      rayMachineRun program oracle n c = some c' ∧
      c'.pc = base + n ∧ c'.head = h ∧ c'.queries = c.queries ∧
      (∀ i : Fin d, i.val < n → c'.tape (h + (i.val : ℤ)) = (values i : ℝ)) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨c, rfl, ?_, hhead, rfl, ?_, ?_⟩
        · simpa only [Nat.add_zero] using hpc
        · intro i hi
          omega
        · intro _ _
          rfl
    | succ n ih =>
        intro hn
        obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ := ih (by omega)
        have hnd : n < d := by omega
        let b' : RayConfiguration :=
          { b with
            pc := base + n + 1
            tape := Function.update b.tape (h + (n : ℤ)) (values ⟨n, hnd⟩ : ℝ) }
        have hinst : program[b.pc]? = some
            (.constant (n : ℤ) (values ⟨n, hnd⟩) (base + n + 1)) := by
          rw [hbpc]
          exact hfetch ⟨n, hnd⟩
        have hstep : rayMachineStep program oracle b = some b' := by
          simp only [rayMachineStep, hinst, hbhead, b']
        refine ⟨b', ?_, ?_, hbhead, hbq, ?_, ?_⟩
        · rw [run_succ_last, hb, Option.bind_some, hstep]
        · change base + n + 1 = base + (n + 1)
          omega
        · intro i hi
          by_cases hin : i.val = n
          · have haddr : h + (i.val : ℤ) = h + (n : ℤ) := by omega

            change Function.update b.tape (h + (n : ℤ))
              (values ⟨n, hnd⟩ : ℝ) (h + (i.val : ℤ)) = _
            rw [haddr, Function.update_self]
            exact congrArg (fun j : Fin d => (values j : ℝ)) (Fin.ext hin.symm)
          · have hi' : i.val < n := by omega
            have haddr : h + (i.val : ℤ) ≠ h + (n : ℤ) := by omega
            simpa only [b', Function.update_of_ne haddr] using hbtape i hi'
        · intro z hz
          have haddr : z ≠ h + (n : ℤ) := by omega
          simpa only [b', Function.update_of_ne haddr] using hbframe z hz
  obtain ⟨c', hc', hpc', hhead', hq', htape', hframe'⟩ := hrun d le_rfl
  exact ⟨c', hc', hpc', hhead', hq', fun i => htape' i i.isLt, hframe'⟩

private def writeVector {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ) (z : ℤ) : ℝ :=
  if hz : 0 ≤ z - h ∧ z - h < (d : ℤ) then
    v ⟨(z - h).toNat, by omega⟩ else tape z

private theorem writeVector_at {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ)
    (i : Fin d) : writeVector tape h v (h + (i.val : ℤ)) = v i := by
  have hi : 0 ≤ h + (i.val : ℤ) - h ∧ h + (i.val : ℤ) - h < (d : ℤ) := by omega
  rw [writeVector, dif_pos hi]
  congr 1
  apply Fin.ext
  simp only [add_sub_cancel_left, Int.toNat_natCast]

private theorem writeVector_frame {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ)
    (z : ℤ) (hz : z < h ∨ h + (d : ℤ) ≤ z) : writeVector tape h v z = tape z := by
  have hn : ¬ (0 ≤ z - h ∧ z - h < (d : ℤ)) := by omega
  simp only [writeVector, dif_neg hn]

private theorem run_sample_block {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (h : ℤ)
    (values : Fin d → ℚ) (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = h)
    (hfetch : ∀ i : Fin d, program[base + i.val]? =
      some (.constant (i.val : ℤ) (values i) (base + i.val + 1)))
    (hquery : program[base + d]? = some (.query (base + d + 1)))
    (hshift : program[base + d + 1]? = some (.shift (d : ℤ) (base + d + 2)))
    (hnonzero : (fun i : Fin d => (values i : ℝ)) ≠ 0) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle (d + 2) c = some c' ∧
      c'.pc = base + d + 2 ∧ c'.head = h + (d : ℤ) ∧ c'.queries = c.queries + 1 ∧
      (∀ i : Fin d, c'.tape (h + (i.val : ℤ)) = oracle (fun j => (values j : ℝ)) i) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
  classical
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_constants program oracle base h values c hpc hhead hfetch
  let v : Fin d → ℝ := fun i => (values i : ℝ)
  have hv : (fun i : Fin d => b.tape (h + (i.val : ℤ))) = v := funext hbtape
  have hvne : v ≠ 0 := hnonzero
  let b' : RayConfiguration :=
    { b with
      pc := base + d + 1
      queries := c.queries + 1
      tape := writeVector b.tape h (oracle v) }
  let b'' : RayConfiguration :=
    { b' with
      pc := base + d + 2
      head := h + (d : ℤ) }
  have hstepQuery : rayMachineStep program oracle b = some b' := by
    simp only [rayMachineStep, hbpc, hquery, hbhead, hv, hvne, ↓reduceIte,
      hbq, b']
    rfl
  have hstepShift : rayMachineStep program oracle b' = some b'' := by
    simp only [rayMachineStep, b', hshift, b'', hbhead]
  have htwo : rayMachineRun program oracle 2 b = some b'' := by
    simp only [rayMachineRun, hstepQuery, hstepShift, Option.bind_some]
  refine ⟨b'', ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [run_add program oracle d 2 c, hb, Option.bind_some, htwo]
  · intro i
    exact writeVector_at b.tape h (oracle v) i
  · intro z hz
    change writeVector b.tape h (oracle v) z = c.tape z
    rw [writeVector_frame b.tape h (oracle v) z hz]
    exact hbframe z hz

def queryVector (d n : ℕ) : Fin d → ℝ := fun i => (directionEntry d n i.val : ℝ)

theorem queryVector_axis {d : ℕ} (i : Fin d) :
    queryVector d i.val = RayInner.axis i := by
  funext j
  by_cases hj : j.val = i.val
  · have hji : j = i := Fin.ext hj
    subst j
    simp only [queryVector, directionEntry, if_pos i.isLt, ite_true,
      Rat.cast_one, RayInner.axis]
  · have hji : j ≠ i := fun h => hj (congrArg Fin.val h)
    simp only [queryVector, directionEntry, if_pos i.isLt, if_neg hj,
      Rat.cast_zero, RayInner.axis, if_neg hji]

theorem queryVector_pole (d : ℕ) :
    queryVector d d = RayInner.negativeDirection d := by
  funext j
  simp only [queryVector, directionEntry, lt_self_iff_false, ↓reduceIte,
    Rat.cast_neg, Rat.cast_one, RayInner.negativeDirection, RayInner.ones,
    Pi.smul_apply, smul_eq_mul, mul_one]

private theorem queryVector_nonzero {d n : ℕ} (hd : 0 < d) (hn : n < d + 1) :
    queryVector d n ≠ 0 := by
  by_cases hnd : n < d
  · exact (queryVector_axis ⟨n, hnd⟩).symm ▸ RayInner.axis_ne_zero ⟨n, hnd⟩
  · have heq : n = d := by omega
    rw [heq, queryVector_pole]
    exact RayInner.negativeDirection_ne_zero ⟨0, hd⟩

private theorem run_initial_block {d n : ℕ} (hd : 0 < d) (hn : n < d + 1)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hpc : c.pc = 1 + n * (d + 2)) (hhead : c.head = (((n + 1) * d : ℕ) : ℤ)) :
    ∃ c' : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (d + 2) c = some c' ∧
      c'.pc = 1 + (n + 1) * (d + 2) ∧
      c'.head = (((n + 2) * d : ℕ) : ℤ) ∧ c'.queries = c.queries + 1 ∧
      (∀ i : Fin d, c'.tape ((((n + 1) * d : ℕ) : ℤ) + (i.val : ℤ)) =
        oracle (queryVector d n) i) ∧
      ∀ z : ℤ, (z < (((n + 1) * d : ℕ) : ℤ) ∨
        (((n + 2) * d : ℕ) : ℤ) ≤ z) → c'.tape z = c.tape z := by
  have hconst : ∀ i : Fin d,
      (innerSampleProgram d)[(1 + n * (d + 2)) + i.val]? =
        some (.constant (i.val : ℤ) (directionEntry d n i.val)
          ((1 + n * (d + 2)) + i.val + 1)) := by
    intro i
    have h := block_fetch hd hn (show i.val < d + 2 by omega)
    have hnext : n * (d + 2) + i.val + 2 = (1 + n * (d + 2)) + i.val + 1 := by omega
    simpa only [if_pos i.isLt, hnext] using h
  have hquery : (innerSampleProgram d)[(1 + n * (d + 2)) + d]? =
      some (.query ((1 + n * (d + 2)) + d + 1)) := by
    have h := block_fetch hd hn (show d < d + 2 by omega)
    have hnext : n * (d + 2) + d + 2 = (1 + n * (d + 2)) + d + 1 := by omega
    simpa only [lt_self_iff_false, ↓reduceIte, hnext] using h
  have hshift : (innerSampleProgram d)[(1 + n * (d + 2)) + d + 1]? =
      some (.shift (d : ℤ) ((1 + n * (d + 2)) + d + 2)) := by
    have h := block_fetch hd hn (show d + 1 < d + 2 by omega)
    have hlt : ¬ d + 1 < d := by omega
    have hne : d + 1 ≠ d := by omega
    have hidx : 1 + n * (d + 2) + (d + 1) = (1 + n * (d + 2)) + d + 1 := by omega
    have hnext : n * (d + 2) + (d + 1) + 2 = (1 + n * (d + 2)) + d + 2 := by omega
    simpa only [if_neg hlt, if_neg hne, hidx, hnext] using h
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_sample_block (innerSampleProgram d) oracle (1 + n * (d + 2))
      (((n + 1) * d : ℕ) : ℤ) (fun i => directionEntry d n i.val)
      c hpc hhead hconst hquery hshift (queryVector_nonzero hd hn)
  have hpc' : (1 + n * (d + 2)) + d + 2 = 1 + (n + 1) * (d + 2) := by
    rw [Nat.succ_mul]
    omega
  have hhead' : (((n + 1) * d : ℕ) : ℤ) + (d : ℤ) = (((n + 2) * d : ℕ) : ℤ) := by
    exact_mod_cast (show (n + 1) * d + d = (n + 2) * d by ring)
  refine ⟨b, hb, hbpc.trans hpc', hbhead.trans hhead', hbq, hbtape, ?_⟩
  intro z hz
  apply hbframe
  simpa only [hhead'] using hz

private theorem run_blocks {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hpc : c.pc = 1) (hhead : c.head = (d : ℤ)) :
    ∀ n, n ≤ d + 1 → ∃ b : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (n * (d + 2)) c = some b ∧
      b.pc = 1 + n * (d + 2) ∧ b.head = (((n + 1) * d : ℕ) : ℤ) ∧
      b.queries = c.queries + n ∧
      (∀ i : Fin (d + 1), i.val < n → ∀ j : Fin d,
        b.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
          oracle (queryVector d i.val) j) ∧
      ∀ z : ℤ, (z < (d : ℤ) ∨ (((n + 1) * d : ℕ) : ℤ) ≤ z) →
        b.tape z = c.tape z := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Nat.zero_mul, rayMachineRun]
      · simpa only [Nat.zero_mul, Nat.add_zero] using hpc
      · simpa only [Nat.zero_add, Nat.one_mul] using hhead
      · simp only [Nat.add_zero]
      · intro i hi
        omega
      · intro _ _
        rfl
  | succ n ih =>
      intro hn
      obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ := ih (by omega)
      have hnd : n < d + 1 := by omega
      obtain ⟨b', hb', hbpc', hbhead', hbq', hbtape', hbframe'⟩ :=
        run_initial_block hd hnd oracle b hbpc hbhead
      refine ⟨b', ?_, hbpc', hbhead', ?_, ?_, ?_⟩
      · rw [Nat.succ_mul, run_add, hb, Option.bind_some, hb']
      · rw [hbq', hbq]
        omega
      · intro i hi j
        by_cases hin : i.val = n
        · simpa only [hin, Nat.cast_add] using hbtape' j
        · have hilt : i.val < n := by omega
          have haddrNat : (i.val + 1) * d + j.val < (n + 1) * d :=
            packed_lt (Nat.succ_lt_succ hilt) j.isLt
          have haddr : ((((i.val + 1) * d + j.val : ℕ) : ℤ)) <
              (((n + 1) * d : ℕ) : ℤ) := by exact_mod_cast haddrNat
          rw [hbframe' _ (Or.inl haddr)]
          exact hbtape i hilt j
      · intro z hz
        have hlowNat : d ≤ (n + 1) * d := by
          simpa only [Nat.one_mul] using
            Nat.mul_le_mul_right d (show 1 ≤ n + 1 by omega)
        have hstepNat : (n + 1) * d ≤ (n + 2) * d :=
          Nat.mul_le_mul_right d (by omega)
        have hlow : (d : ℤ) ≤ (((n + 1) * d : ℕ) : ℤ) := by exact_mod_cast hlowNat
        have hstep : (((n + 1) * d : ℕ) : ℤ) ≤ (((n + 2) * d : ℕ) : ℤ) := by
          exact_mod_cast hstepNat
        rcases hz with hz | hz
        · rw [hbframe' z (Or.inl (lt_of_lt_of_le hz hlow))]
          exact hbframe z (Or.inl hz)
        · rw [hbframe' z (Or.inr hz)]
          exact hbframe z (Or.inr (hstep.trans hz))

theorem innerSampleProgram_correct {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
    ∃ c : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 2)
        ⟨0, 0, tape, q⟩ = some c ∧
      c.pc = bodyLength d + 2 ∧
      (innerSampleProgram d)[c.pc]? = some .halt ∧ c.head = 0 ∧
      c.queries = q + (d + 1) ∧
      (∀ i : Fin (d + 1), ∀ j : Fin d,
        c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
          oracle (queryVector d i.val) j) ∧
      ∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) →
        c.tape z = tape z := by
  let start : RayConfiguration := ⟨1, (d : ℤ), tape, q⟩
  have hfirst : rayMachineStep (innerSampleProgram d) oracle ⟨0, 0, tape, q⟩ = some start := by
    simp only [rayMachineStep, initial_fetch hd, zero_add, start]
  have hrunfirst : rayMachineRun (innerSampleProgram d) oracle 1
      ⟨0, 0, tape, q⟩ = some start := by
    simp only [rayMachineRun, hfirst, Option.bind_some]
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_blocks hd oracle start rfl rfl (d + 1) le_rfl
  let finish : RayConfiguration :=
    { b with
      pc := bodyLength d + 2
      head := 0 }
  have hbpc' : b.pc = 1 + bodyLength d := hbpc
  have hbhead' : b.head = (((d + 2) * d : ℕ) : ℤ) := hbhead
  have hfinal : rayMachineStep (innerSampleProgram d) oracle b = some finish := by
    simp only [rayMachineStep, hbpc', final_shift_fetch hd, hbhead', add_neg_cancel, finish]
  have hafter : rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 1) start =
      some finish := by
    change rayMachineRun (innerSampleProgram d) oracle (((d + 1) * (d + 2)) + 1) start = _
    rw [run_succ_last, hb, Option.bind_some, hfinal]
  have htotal : rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 2)
      ⟨0, 0, tape, q⟩ = some finish := by
    rw [show bodyLength d + 2 = 1 + (bodyLength d + 1) by omega,
      run_add, hrunfirst, Option.bind_some, hafter]
  refine ⟨finish, htotal, rfl, final_halt_fetch hd, rfl, ?_, ?_, ?_⟩
  · exact hbq
  · intro i j
    exact hbtape i i.isLt j
  · intro z hz
    exact hbframe z hz

theorem all_initial_query_vectors_nonzero {d : ℕ} (hd : 0 < d) :
    ∀ i : Fin (d + 1), queryVector d i.val ≠ 0 :=
  fun i => queryVector_nonzero hd i.isLt

theorem innerSampleProgram_zero
    (oracle : (Fin 0 → ℝ) → Fin 0 → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
    rayMachineRun (innerSampleProgram 0) oracle 0 ⟨0, 0, tape, q⟩ =
      some ⟨0, 0, tape, q⟩ ∧
      (innerSampleProgram 0)[0]? = some .halt := ⟨rfl, rfl⟩

theorem stored_scales {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hstored : ∀ i : Fin (d + 1), ∀ j : Fin d,
      c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
        oracle (queryVector d i.val) j) :
    (∀ i : Fin d, c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) =
      RayInner.positiveScale oracle i) ∧
      -c.tape ((((d + 1) * d : ℕ) : ℤ)) =
        RayInner.negativeScale ⟨0, hd⟩ oracle := by
  constructor
  · intro i
    simpa only [Fin.val_castSucc, queryVector_axis, RayInner.positiveScale] using
      hstored i.castSucc i
  · have h := hstored (Fin.last d) ⟨0, hd⟩
    simp only [Fin.val_last, queryVector_pole, Nat.add_zero] at h
    exact congrArg Neg.neg h

end Grunbaum2003.RayInnerProgram

namespace Grunbaum2003

theorem rayMachine_inner_simplex_and_signed_direction_program :
    ∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : RayConfiguration,
          rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) := by
  refine ⟨@RayInner.axis, RayInner.negativeDirection, @RayInner.positiveScale,
    @RayInner.negativeScale, @RayInner.sampleScale, @RayInner.directionScale,
    RayInnerProgram.innerSampleProgram, RayInnerProgram.queryVector,
    fun _ _ _ => rfl, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro d j
    change (-1 : ℝ) * 1 = -1
    ring
  · intro d hd P hP oracle horacle u
    exact RayInner.rayOracle_signed_inner_points hd hP horacle u
  · intro d hd oracle tape q
    obtain ⟨c, hrun, hpc, hhalt, hhead, hq, hstored, hframe⟩ :=
      RayInnerProgram.innerSampleProgram_correct hd oracle tape q
    obtain ⟨hpos, hneg⟩ := RayInnerProgram.stored_scales hd oracle c hstored
    exact ⟨c, hrun, hpc, hhalt, hhead, hq, hstored, hpos, hneg, hframe⟩

end Grunbaum2003
end

theorem inline_solution :
    ∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List Grunbaum2003.RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : Grunbaum2003.IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : Grunbaum2003.RayConfiguration,
          Grunbaum2003.rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) :=
  Grunbaum2003.rayMachine_inner_simplex_and_signed_direction_program

end RayCounterfamilyInline01

namespace Grunbaum2003

theorem rayMachine_inner_simplex_and_signed_direction_program :
∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : RayConfiguration,
          rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) :=
  @RayCounterfamilyInline01.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_known_facet_step_eps_program.lean
-- SHA256: 199b8cfbb30ea1d8b746b93c6985caf0cc03e71bcdeb695ee293c2ec969c8d7d
namespace RayCounterfamilyInline02

open _root_.Grunbaum2003


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
theorem inline_solution :
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

end RayCounterfamilyInline02

namespace Grunbaum2003

theorem rayMachine_known_facet_step_eps_program :
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
  @RayCounterfamilyInline02.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_vector_eval_and_perturbed_ray_query_program.lean
-- SHA256: 5fb52d67244121ca7ee05865d38d02a0087eb0b520f0490b648fd4c69e0e4e21
namespace RayCounterfamilyInline03

open _root_.Grunbaum2003


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
theorem inline_solution :
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

end RayCounterfamilyInline03

namespace Grunbaum2003

theorem rayMachine_vector_eval_and_perturbed_ray_query_program :
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
  @RayCounterfamilyInline03.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_cramer_facet_row_and_midpoint_programs.lean
-- SHA256: e7f3fc48b53da8645db51a3bb16a940138041172099e6dbffc44c71f6df62dec
namespace RayCounterfamilyInline04

open _root_.Grunbaum2003


set_option autoImplicit false

open scoped BigOperators Matrix Classical
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

namespace Grunbaum2003.RayFieldExpr

/-- Single Leibniz permutation term `sign(σ) * ∏ i : Fin d, A (σ i) i`. -/
def permTermExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr) (σ : Equiv.Perm (Fin d)) : Expr :=
  Expr.mul (.const ((Equiv.Perm.sign σ : ℤ) : ℚ)) (Expr.prodFin (fun i => A (σ i) i))

@[simp]
theorem eval_permTermExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr)
    (σ : Equiv.Perm (Fin d)) (source : ℤ → ℝ) :
    (permTermExpr A σ).eval source =
      Equiv.Perm.sign σ • ∏ i : Fin d, (A (σ i) i).eval source := by
  simp only [permTermExpr, Expr.mul, Expr.eval, BinOp.eval, Expr.eval_prodFin,
    Rat.cast_intCast, Units.smul_def, zsmul_eq_mul]

theorem valid_permTermExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr)
    (σ : Equiv.Perm (Fin d)) (source : ℤ → ℝ)
    (hA : ∀ i j : Fin d, (A i j).Valid source) :
    (permTermExpr A σ).Valid source :=
  ⟨trivial, Expr.valid_prodFin source (fun i => A (σ i) i) (fun i => hA (σ i) i), trivial⟩

/-- Static field expression computing the Leibniz determinant of a `d × d` matrix of expressions. -/
def detExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr) : Expr :=
  let ePerm := (Fintype.equivFin (Equiv.Perm (Fin d))).symm
  Expr.sumFin (fun s => permTermExpr A (ePerm s))

@[simp]
theorem eval_detExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr) (source : ℤ → ℝ) :
    (detExpr A).eval source = (Matrix.of (fun i j : Fin d => (A i j).eval source)).det := by
  dsimp [detExpr]
  rw [Expr.eval_sumFin]
  let ePerm := (Fintype.equivFin (Equiv.Perm (Fin d))).symm
  have hsum :
      (∑ s : Fin (Fintype.card (Equiv.Perm (Fin d))), (permTermExpr A (ePerm s)).eval source) =
        ∑ σ : Equiv.Perm (Fin d), (permTermExpr A σ).eval source :=
    Equiv.sum_comp ePerm (fun σ => (permTermExpr A σ).eval source)
  rw [hsum, Matrix.det_apply]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [eval_permTermExpr]
  rfl

theorem valid_detExpr {d : ℕ} (A : Matrix (Fin d) (Fin d) Expr) (source : ℤ → ℝ)
    (hA : ∀ i j : Fin d, (A i j).Valid source) :
    (detExpr A).Valid source := by
  dsimp [detExpr]
  exact Expr.valid_sumFin source _ (fun s => valid_permTermExpr A _ source hA)

/-- Expression matrix reading a `d × d` real matrix stored row-major at `vBase + i * d + j`. -/
def tapeMatrixExpr (d : ℕ) (vBase : ℤ) : Matrix (Fin d) (Fin d) Expr :=
  fun i j => .read (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))

/-- Real `d × d` matrix stored row-major on `source` at `vBase + i * d + j`. -/
def tapeMatrixVal (d : ℕ) (source : ℤ → ℝ) (vBase : ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))

@[simp]
theorem eval_tapeMatrixExpr (d : ℕ) (source : ℤ → ℝ) (vBase : ℤ) (i j : Fin d) :
    (tapeMatrixExpr d vBase i j).eval source = tapeMatrixVal d source vBase i j := rfl

theorem valid_tapeMatrixExpr (d : ℕ) (source : ℤ → ℝ) (vBase : ℤ) (i j : Fin d) :
    (tapeMatrixExpr d vBase i j).Valid source := trivial

/-- Expression matrix obtained by replacing column `col` of `tapeMatrixExpr d vBase` with `1`. -/
def cramerNumeratorMatrixExpr (d : ℕ) (vBase : ℤ) (col : ℕ) : Matrix (Fin d) (Fin d) Expr :=
  fun i j => if j.val = col then .const 1 else tapeMatrixExpr d vBase i j

@[simp]
theorem eval_cramerNumeratorMatrixExpr {d : ℕ} (source : ℤ → ℝ) (vBase : ℤ) (k : Fin d) :
    (Matrix.of (fun i j : Fin d => (cramerNumeratorMatrixExpr d vBase k.val i j).eval source)) =
      (tapeMatrixVal d source vBase).updateCol k (fun _ => 1) := by
  ext i j
  simp only [Matrix.of_apply, cramerNumeratorMatrixExpr, Matrix.updateCol_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Expr.eval]
  · have hval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    simp [hjk, hval, eval_tapeMatrixExpr]

theorem valid_cramerNumeratorMatrixExpr (d : ℕ) (source : ℤ → ℝ) (vBase : ℤ) (col : ℕ)
    (i j : Fin d) :
    (cramerNumeratorMatrixExpr d vBase col i j).Valid source := by
  dsimp [cramerNumeratorMatrixExpr]
  split_ifs <;> trivial

/-- Expression computing the `col`-th Cramer facet-normal coefficient
`det(v.updateCol col 1) / det(v)`. -/
def cramerCoeffExpr (d : ℕ) (vBase : ℤ) (col : ℕ) : Expr :=
  Expr.div (detExpr (cramerNumeratorMatrixExpr d vBase col)) (detExpr (tapeMatrixExpr d vBase))

@[simp]
theorem eval_cramerCoeffExpr {d : ℕ} (source : ℤ → ℝ) (vBase : ℤ) (k : Fin d) :
    (cramerCoeffExpr d vBase k.val).eval source =
      ((tapeMatrixVal d source vBase).updateCol k (fun _ => 1)).det /
        (tapeMatrixVal d source vBase).det := by
  simp only [cramerCoeffExpr, Expr.div, Expr.eval, BinOp.eval, eval_detExpr,
    eval_cramerNumeratorMatrixExpr]
  rfl

theorem valid_cramerCoeffExpr {d : ℕ} (source : ℤ → ℝ) (vBase : ℤ) (col : ℕ)
    (hdet : (tapeMatrixVal d source vBase).det ≠ 0) :
    (cramerCoeffExpr d vBase col).Valid source := by
  refine ⟨valid_detExpr _ source (valid_cramerNumeratorMatrixExpr d source vBase col),
    valid_detExpr _ source (valid_tapeMatrixExpr d source vBase), ?_⟩
  simp only [BinOp.Valid, eval_detExpr]
  exact hdet

/-- Straight-line program computing all `d` Cramer facet-normal coefficients of the `d × d`
vertex matrix at `vBase` into `outBase .. outBase + (d - 1)`. -/
def cramerRowProgram (d : ℕ) (vBase minBase : ℤ) : List RayInstruction :=
  evalVecAndOptQueryProgram d (cramerCoeffExpr d vBase) minBase false

def cramerRowDest (d : ℕ) (vBase minBase : ℤ) : ℤ :=
  evalVecDest d (cramerCoeffExpr d vBase) minBase

def cramerRowSteps (d : ℕ) (vBase : ℤ) : ℕ :=
  evalVecAndOptQuerySteps d (cramerCoeffExpr d vBase) false

theorem cramerRowProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (vBase minBase : ℤ) (q : ℕ)
    (hdet : (tapeMatrixVal d source vBase).det ≠ 0) :
    let prog := cramerRowProgram d vBase minBase
    let outBase := cramerRowDest d vBase minBase
    let steps := cramerRowSteps d vBase
    let v := tapeMatrixVal d source vBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ k : Fin d,
        c'.tape (outBase + (k.val : ℤ)) =
          (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  obtain ⟨hmin, c', hrun, hpc, hhalt, hhead, hq, hvals, hframe⟩ :=
    evalVecProgram_correct oracle source (cramerCoeffExpr d vBase) minBase q
      (fun col _ => valid_cramerCoeffExpr source vBase col hdet)
  refine ⟨hmin, c', hrun, hpc, hhalt, hhead, hq, ?_, hframe⟩
  intro k
  change c'.tape (evalVecDest d (cramerCoeffExpr d vBase) minBase + (k.val : ℤ)) = _
  rw [hvals k, eval_cramerCoeffExpr]

/-- Coordinate `i` of the midpoint `(1 / 2) • (p + q)` read from `pBase + i` and `qBase + i`. -/
def midpointCoordExpr (pBase qBase : ℤ) (i : ℕ) : Expr :=
  Expr.div (Expr.add (.read (pBase + (i : ℤ))) (.read (qBase + (i : ℤ)))) (.const 2)

@[simp]
theorem eval_midpointCoordExpr (source : ℤ → ℝ) (pBase qBase : ℤ) (i : ℕ) :
    (midpointCoordExpr pBase qBase i).eval source =
      (source (pBase + (i : ℤ)) + source (qBase + (i : ℤ))) / 2 := by
  simp [midpointCoordExpr, Expr.div, Expr.add, Expr.eval, BinOp.eval]

theorem valid_midpointCoordExpr (source : ℤ → ℝ) (pBase qBase : ℤ) (i : ℕ) :
    (midpointCoordExpr pBase qBase i).Valid source := by
  refine ⟨⟨trivial, trivial, trivial⟩, trivial, ?_⟩
  simp [BinOp.Valid, Expr.eval]

/-- Straight-line program computing the midpoint `(1 / 2) • (p + q)` into
`outBase .. outBase + (d - 1)` with zero oracle queries. -/
def midpointVecProgram (d : ℕ) (pBase qBase minBase : ℤ) : List RayInstruction :=
  evalVecAndOptQueryProgram d (midpointCoordExpr pBase qBase) minBase false

def midpointVecDest (d : ℕ) (pBase qBase minBase : ℤ) : ℤ :=
  evalVecDest d (midpointCoordExpr pBase qBase) minBase

def midpointVecSteps (d : ℕ) (pBase qBase : ℤ) : ℕ :=
  evalVecAndOptQuerySteps d (midpointCoordExpr pBase qBase) false

theorem midpointVecProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (pBase qBase minBase : ℤ) (q : ℕ) :
    let prog := midpointVecProgram d pBase qBase minBase
    let outBase := midpointVecDest d pBase qBase minBase
    let steps := midpointVecSteps d pBase qBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ i : Fin d,
        c'.tape (outBase + (i.val : ℤ)) =
          (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  obtain ⟨hmin, c', hrun, hpc, hhalt, hhead, hq, hvals, hframe⟩ :=
    evalVecProgram_correct oracle source (midpointCoordExpr pBase qBase) minBase q
      (fun i _ => valid_midpointCoordExpr source pBase qBase i)
  refine ⟨hmin, c', hrun, hpc, hhalt, hhead, hq, ?_, hframe⟩
  intro i
  change c'.tape (evalVecDest d (midpointCoordExpr pBase qBase) minBase + (i.val : ℤ)) = _
  rw [hvals i, eval_midpointCoordExpr]

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003

theorem rayMachine_cramer_facet_row_and_midpoint_programs_proved :
  ∃ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ),
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) := by
  refine ⟨RayFieldExpr.cramerRowProgram,
    RayFieldExpr.cramerRowDest,
    RayFieldExpr.cramerRowSteps,
    RayFieldExpr.midpointVecProgram,
    RayFieldExpr.midpointVecDest,
    RayFieldExpr.midpointVecSteps, ?_, ?_⟩
  · intro d oracle source vBase minBase q v hdet
    exact RayFieldExpr.cramerRowProgram_correct oracle source vBase minBase q hdet
  · intro d oracle source pBase qBase minBase q
    exact RayFieldExpr.midpointVecProgram_correct oracle source pBase qBase minBase q

end Grunbaum2003

end

open Grunbaum2003 in
theorem inline_solution :
  ∃ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ),
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) :=
  Grunbaum2003.rayMachine_cramer_facet_row_and_midpoint_programs_proved

end RayCounterfamilyInline04

namespace Grunbaum2003

theorem rayMachine_cramer_facet_row_and_midpoint_programs :
∃ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ),
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z)) :=
  @RayCounterfamilyInline04.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_facet_vertex_incidence_matrix_program.lean
-- SHA256: a5d58be019d162b1baf69878d1a1a6278f64d96fdabd89711b7e3455d339cb71
namespace RayCounterfamilyInline05

open _root_.Grunbaum2003


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

namespace Grunbaum2003.RayFieldExpr

/-- Two-step zero-indicator gadget using the 3-way `.branch` instruction:
writes `1` to `dst` if `tape src = 0`, and `0` to `dst` if `tape src ≠ 0`. -/
def zeroIndicator (src dst : ℤ) (pc : ℕ) : List RayInstruction :=
  [ .branch src (pc + 1) (pc + 2) (pc + 1),
    .constant dst 0 (pc + 3),
    .constant dst 1 (pc + 3) ]

@[simp]
theorem length_zeroIndicator (src dst : ℤ) (pc : ℕ) :
    (zeroIndicator src dst pc).length = 3 := rfl

theorem zeroIndicator_correct {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (src dst : ℤ) (pc : ℕ)
    (hcode : CodeAt program pc (zeroIndicator src dst pc))
    (source : ℤ → ℝ) (q : ℕ) :
    rayMachineRun program oracle 2 ⟨pc, 0, source, q⟩ =
      some ⟨pc + 3, 0,
        Function.update source dst (if source src = 0 then (1 : ℝ) else 0), q⟩ := by
  have h0 : program[pc]? = some (.branch src (pc + 1) (pc + 2) (pc + 1)) := by
    have := hcode 0 (by simp [zeroIndicator])
    simpa [zeroIndicator] using this
  have h1 : program[pc + 1]? = some (.constant dst 0 (pc + 3)) := by
    have := hcode 1 (by simp [zeroIndicator])
    simpa [zeroIndicator] using this
  have h2 : program[pc + 2]? = some (.constant dst 1 (pc + 3)) := by
    have := hcode 2 (by simp [zeroIndicator])
    simpa [zeroIndicator] using this
  change (rayMachineStep program oracle ⟨pc, 0, source, q⟩).bind
    (fun c1 => (rayMachineStep program oracle c1).bind
      (fun c2 => some c2)) = _
  by_cases hlt : source src < 0
  · have hne : source src ≠ 0 := ne_of_lt hlt
    simp [rayMachineStep, h0, hlt, hne, h1]
  · by_cases heq : source src = 0
    · simp [rayMachineStep, h0, heq, h2]
    · simp [rayMachineStep, h0, hlt, heq, h1]

/-- Affine hyperplane slack expression `(∑ i : Fin d, L i * x i) - 1`. -/
def slackExpr (d : ℕ) (lBase xBase : ℤ) : Expr :=
  Expr.sub (Expr.dot d lBase xBase) (.const 1)

theorem eval_slackExpr (d : ℕ) (source : ℤ → ℝ) (lBase xBase : ℤ) :
    (slackExpr d lBase xBase).eval source =
      (∑ i : Fin d, source (lBase + (i.val : ℤ)) * source (xBase + (i.val : ℤ))) - 1 := by
  simp only [slackExpr, Expr.sub, Expr.eval, BinOp.eval, Expr.eval_dot, Rat.cast_one]

theorem valid_slackExpr (d : ℕ) (source : ℤ → ℝ) (lBase xBase : ℤ) :
    (slackExpr d lBase xBase).Valid source :=
  ⟨Expr.valid_dot source d lBase xBase, trivial, trivial⟩

/-- Straight-line program testing whether `∑ i : Fin d, L i * x i = 1` and writing
`1` or `0` into `outBase`. -/
def hyperplaneIncidenceDest (d : ℕ) (lBase xBase minBase : ℤ) : ℤ :=
  max (slackExpr d lBase xBase).readBound minBase

def hyperplaneIncidenceSteps (d : ℕ) (lBase xBase : ℤ) : ℕ :=
  (slackExpr d lBase xBase).steps + 2

def hyperplaneIncidenceProgram (d : ℕ) (lBase xBase minBase : ℤ) : List RayInstruction :=
  let e := slackExpr d lBase xBase
  let outBase := hyperplaneIncidenceDest d lBase xBase minBase
  (e.emit outBase 0 ++ zeroIndicator outBase outBase e.steps) ++ [.halt]

theorem hyperplaneIncidenceProgram_correct {d : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (lBase xBase minBase : ℤ) (q : ℕ) :
    let prog := hyperplaneIncidenceProgram d lBase xBase minBase
    let outBase := hyperplaneIncidenceDest d lBase xBase minBase
    let steps := hyperplaneIncidenceSteps d lBase xBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps + 1 ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      c'.tape outBase =
        (if (∑ i : Fin d, source (lBase + (i.val : ℤ)) * source (xBase + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  let e := slackExpr d lBase xBase
  have hmin : minBase ≤ outBase := le_max_right _ _
  have hbound : e.readBound ≤ outBase := le_max_left _ _
  have hfresh : e.ReadFresh outBase :=
    fun addr hmem => lt_of_lt_of_le (e.readFresh_readBound addr hmem) hbound
  let body := e.emit outBase 0 ++ zeroIndicator outBase outBase e.steps
  have hcodeAll : CodeAt prog 0 body :=
    CodeAt.prefix_zero body [.halt]
  have hcode1 : CodeAt prog 0 (e.emit outBase 0) := hcodeAll.left
  have hcode2 : CodeAt prog e.steps (zeroIndicator outBase outBase e.steps) := by
    have h := hcodeAll.right
    simpa only [Nat.zero_add, e.length_emit outBase 0] using h
  have hhalt : prog[e.steps + 3]? = some .halt := by
    change (body ++ [.halt])[e.steps + 3]? = some .halt
    have hlen : body.length = e.steps + 3 := by
      simp [body, e.length_emit outBase 0]
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨c₁, hrun₁, hpc₁, hhead₁, hq₁, hval₁, hframe₁⟩ :=
    e.emit_correct prog oracle source outBase 0 ⟨0, 0, source, q⟩
      rfl rfl hcode1 hfresh (fun _ _ => rfl) (valid_slackExpr d source lBase xBase)
  have hpc₁' : c₁.pc = e.steps := by simpa only [Nat.zero_add] using hpc₁
  have hc₁_eq : c₁ = ⟨e.steps, 0, c₁.tape, q⟩ := by
    cases c₁
    simp only [RayConfiguration.mk.injEq] at hpc₁' hhead₁ hq₁ ⊢
    exact ⟨hpc₁', hhead₁, trivial, hq₁⟩
  have hrun₂ := zeroIndicator_correct prog oracle outBase outBase e.steps hcode2 c₁.tape q
  refine ⟨hmin, ⟨e.steps + 3, 0,
    Function.update c₁.tape outBase (if c₁.tape outBase = 0 then (1 : ℝ) else 0), q⟩,
    ?_, rfl, hhalt, rfl, rfl, ?_, ?_⟩
  · change rayMachineRun prog oracle (e.steps + 2) ⟨0, 0, source, q⟩ = _
    rw [run_add prog oracle e.steps 2, hrun₁, Option.bind_some, hc₁_eq]
    exact hrun₂
  · simp only [Function.update_self]
    have hval₁' : c₁.tape outBase =
        (∑ i : Fin d, source (lBase + (i.val : ℤ)) * source (xBase + (i.val : ℤ))) - 1 := by
      rw [hval₁]
      exact eval_slackExpr d source lBase xBase
    simp only [hval₁', sub_eq_zero]
  · intro z hz
    have hne : z ≠ outBase := ne_of_lt hz
    dsimp only
    rw [Function.update_of_ne hne]
    exact hframe₁ z (Or.inl hz)

/-- Boolean implication indicator `1 - a * (1 - b)` for `0/1` tape cells. -/
def impBitExpr (V : ℕ) (fvBase : ℤ) (i j : ℕ) (k : Fin V) : Expr :=
  Expr.sub (.const 1)
    (Expr.mul (.read (fvBase + (i : ℤ) * (V : ℤ) + (k.val : ℤ)))
      (Expr.sub (.const 1) (.read (fvBase + (j : ℤ) * (V : ℤ) + (k.val : ℤ)))))

theorem eval_impBitExpr {n V : ℕ} (source : ℤ → ℝ) (fvBase : ℤ)
    (inc : Fin n → Fin V → Prop)
    (hinc : ∀ (a : Fin n) (k : Fin V),
      source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) = if inc a k then (1 : ℝ) else 0)
    (i j : Fin n) (k : Fin V) :
    (impBitExpr V fvBase i.val j.val k).eval source =
      if (inc i k → inc j k) then (1 : ℝ) else 0 := by
  simp only [impBitExpr, Expr.sub, Expr.mul, Expr.eval, BinOp.eval, hinc i k, hinc j k]
  by_cases hi : inc i k <;> by_cases hj : inc j k <;> simp [hi, hj]

theorem valid_impBitExpr (V : ℕ) (source : ℤ → ℝ) (fvBase : ℤ) (i j : ℕ) (k : Fin V) :
    (impBitExpr V fvBase i j k).Valid source :=
  ⟨trivial, ⟨trivial, ⟨trivial, trivial, trivial⟩, trivial⟩, trivial⟩

/-- Subset-inclusion indicator `∏ k : Fin V, impBitExpr V fvBase (idx / n) (idx % n) k`. -/
def subsetInclusionExpr (n V : ℕ) (fvBase : ℤ) (idx : ℕ) : Expr :=
  Expr.prodFin (impBitExpr V fvBase (idx / n) (idx % n))

theorem eval_subsetInclusionExpr {n V : ℕ} (source : ℤ → ℝ) (fvBase : ℤ)
    (inc : Fin n → Fin V → Prop)
    (hinc : ∀ (a : Fin n) (k : Fin V),
      source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) = if inc a k then (1 : ℝ) else 0)
    (i j : Fin n) :
    (subsetInclusionExpr n V fvBase (i.val * n + j.val)).eval source =
      if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hdiv : (i.val * n + j.val) / n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_zero_iff.mpr (Or.inr j.isLt),
      Nat.zero_add]
  have hmod : (i.val * n + j.val) % n = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  simp only [subsetInclusionExpr, hdiv, hmod, Expr.eval_prodFin]
  have hterm : ∀ k : Fin V,
      (impBitExpr V fvBase i.val j.val k).eval source =
        if (inc i k → inc j k) then (1 : ℝ) else 0 :=
    eval_impBitExpr source fvBase inc hinc i j
  simp_rw [hterm]
  by_cases hall : ∀ k : Fin V, inc i k → inc j k
  · rw [if_pos hall]
    exact Finset.prod_eq_one (fun k _ => if_pos (hall k))
  · rw [if_neg hall]
    have hex : ∃ k₀ : Fin V, ¬ (inc i k₀ → inc j k₀) := not_forall.mp hall
    rcases hex with ⟨k₀, hk₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ k₀) (if_neg hk₀)

theorem valid_subsetInclusionExpr (n V : ℕ) (source : ℤ → ℝ) (fvBase : ℤ) (idx : ℕ) :
    (subsetInclusionExpr n V fvBase idx).Valid source :=
  Expr.valid_prodFin source _ (valid_impBitExpr V source fvBase (idx / n) (idx % n))

/-- Combined vector expression of length `n + 1 + n * n`:
positions `0 .. n - 1` emit `1`, position `n` emits `0`, and positions `n + 1 + idx`
emit `subsetInclusionExpr n V fvBase idx`. -/
def headerAndInclusionExpr (n V : ℕ) (fvBase : ℤ) (pos : ℕ) : Expr :=
  if pos < n then .const 1
  else if pos = n then .const 0
  else subsetInclusionExpr n V fvBase (pos - (n + 1))

theorem valid_headerAndInclusionExpr (n V : ℕ) (source : ℤ → ℝ) (fvBase : ℤ) (pos : ℕ) :
    (headerAndInclusionExpr n V fvBase pos).Valid source := by
  dsimp [headerAndInclusionExpr]
  split_ifs
  · trivial
  · trivial
  · exact valid_subsetInclusionExpr n V source fvBase (pos - (n + 1))

/-- Straight-line program emitting the unary header `1, ..., 1, 0` and the `n × n`
subset-inclusion table into `outBase .. outBase + (n + n * n)` and shifting `head` to `outBase`. -/
def headerAndInclusionTableDest (n V : ℕ) (fvBase minBase : ℤ) : ℤ :=
  evalVecDest (n + 1 + n * n) (headerAndInclusionExpr n V fvBase) minBase

def headerAndInclusionTableSteps (n V : ℕ) (fvBase : ℤ) : ℕ :=
  emitVecSteps (n + 1 + n * n) (headerAndInclusionExpr n V fvBase) + 1

def headerAndInclusionTableProgram (n V : ℕ) (fvBase minBase : ℤ) : List RayInstruction :=
  let m := n + 1 + n * n
  let f := headerAndInclusionExpr n V fvBase
  let outBase := headerAndInclusionTableDest n V fvBase minBase
  let s := emitVecSteps m f
  (emitVec m f outBase 0 ++ [.shift outBase (s + 1)]) ++ [.halt]

theorem headerAndInclusionTableProgram_correct {d n V : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (fvBase minBase : ℤ) (q : ℕ)
    (inc : Fin n → Fin V → Prop)
    (hinc : ∀ (a : Fin n) (k : Fin V),
      source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) = if inc a k then (1 : ℝ) else 0) :
    let prog := headerAndInclusionTableProgram n V fvBase minBase
    let outBase := headerAndInclusionTableDest n V fvBase minBase
    let steps := headerAndInclusionTableSteps n V fvBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = outBase ∧ c'.queries = q ∧
      (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
      c'.tape (c'.head + (n : ℤ)) = 0 ∧
      (∀ i j : Fin n,
        c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
          if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < c'.head → c'.tape z = source z) := by
  intro prog outBase steps
  let m := n + 1 + n * n
  let f := headerAndInclusionExpr n V fvBase
  let s := emitVecSteps m f
  have hmin : minBase ≤ outBase := le_max_right _ _
  have hbound : emitVecReadBound m f ≤ outBase := le_max_left _ _
  have hfresh : ∀ i : ℕ, i < m → (f i).ReadFresh outBase :=
    readFresh_of_emitVecReadBound m f outBase hbound
  let body := emitVec m f outBase 0 ++ [.shift outBase (s + 1)]
  have hcodeAll : CodeAt prog 0 body :=
    CodeAt.prefix_zero body [.halt]
  have hcodeVec : CodeAt prog 0 (emitVec m f outBase 0) := hcodeAll.left
  have hshift : prog[s]? = some (.shift outBase (s + 1)) := by
    have h := hcodeAll.right 0 (by simp)
    simpa only [Nat.zero_add, Nat.add_zero, length_emitVec m f outBase 0,
      List.getElem?_cons_zero] using h
  have hhalt : prog[s + 1]? = some .halt := by
    change (body ++ [.halt])[s + 1]? = some .halt
    have hlen : body.length = s + 1 := by
      simp [body, s, length_emitVec m f outBase 0]
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨c₁, hrun₁, hpc₁, hhead₁, hq₁, hvals₁, hframe₁⟩ :=
    emitVec_correct m f prog oracle source outBase outBase 0 ⟨0, 0, source, q⟩
      rfl rfl hcodeVec le_rfl hfresh (fun _ _ => rfl)
      (fun pos _ => valid_headerAndInclusionExpr n V source fvBase pos)
  have hpc₁' : c₁.pc = s := by simpa only [Nat.zero_add] using hpc₁
  have hc₁_eq : c₁ = ⟨s, 0, c₁.tape, q⟩ := by
    cases c₁
    simp only [RayConfiguration.mk.injEq] at hpc₁' hhead₁ hq₁ ⊢
    exact ⟨hpc₁', hhead₁, trivial, hq₁⟩
  refine ⟨hmin, ⟨s + 1, outBase, c₁.tape, q⟩, ?_, rfl, hhalt, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change rayMachineRun prog oracle (s + 1) ⟨0, 0, source, q⟩ = _
    rw [run_add prog oracle s 1, hrun₁, Option.bind_some, hc₁_eq]
    simp [rayMachineRun, rayMachineStep, hshift]
  · intro i
    have hi_lt : i.val < m := by omega
    have hval := hvals₁ i.val hi_lt
    simpa [f, headerAndInclusionExpr, i.isLt, Expr.eval] using hval
  · have hn_lt : n < m := by omega
    have hval := hvals₁ n hn_lt
    have hn_irrefl : ¬ n < n := Nat.lt_irrefl n
    simpa [f, headerAndInclusionExpr, hn_irrefl, Expr.eval] using hval
  · intro i j
    have hij_lt : i.val * n + j.val < n * n := by
      have h1 : i.val + 1 ≤ n := i.isLt
      have h2 : (i.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
      have h3 : i.val * n + j.val < (i.val + 1) * n := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_lt_add_left j.isLt (i.val * n)
      exact lt_of_lt_of_le h3 h2
    let pos := n + 1 + (i.val * n + j.val)
    have hpos_lt : pos < m := by omega
    have hval := hvals₁ pos hpos_lt
    have hnot_lt : ¬ pos < n := by omega
    have hnot_eq : ¬ pos = n := by omega
    have hsub : pos - (n + 1) = i.val * n + j.val := by omega
    have hfeval : (f pos).eval source =
        if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0 := by
      dsimp [f, headerAndInclusionExpr]
      rw [if_neg hnot_lt, if_neg hnot_eq, hsub]
      exact eval_subsetInclusionExpr source fvBase inc hinc i j
    have hpos_eq : n + 1 + i.val * n + j.val = pos := by omega
    rw [hpos_eq]
    simpa [hfeval] using hval
  · intro z hz
    exact hframe₁ z hz

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003.RayFieldExpr

/-- Sequential in-place zero-indicator over `M` consecutive tape cells `base .. base + (M - 1)`. -/
def zeroIndicatorVec : ℕ → ℤ → ℕ → List RayInstruction
  | 0, _, _ => []
  | M + 1, base, pc =>
    zeroIndicator base base pc ++ zeroIndicatorVec M (base + 1) (pc + 3)

@[simp]
theorem length_zeroIndicatorVec (M : ℕ) (base : ℤ) (pc : ℕ) :
    (zeroIndicatorVec M base pc).length = 3 * M := by
  induction M generalizing base pc with
  | zero => rfl
  | succ M ih =>
    simp only [zeroIndicatorVec, List.length_append, length_zeroIndicator, ih]
    omega

theorem zeroIndicatorVec_correct (M : ℕ) {d : ℕ}
    (program : List RayInstruction) (oracle : (Fin d → ℝ) → Fin d → ℝ)
    (base : ℤ) (pc : ℕ)
    (hcode : CodeAt program pc (zeroIndicatorVec M base pc))
    (source : ℤ → ℝ) (q : ℕ) :
    ∃ tape' : ℤ → ℝ,
      rayMachineRun program oracle (2 * M) ⟨pc, 0, source, q⟩ =
        some ⟨pc + 3 * M, 0, tape', q⟩ ∧
      (∀ idx : ℕ, idx < M →
        tape' (base + (idx : ℤ)) =
          if source (base + (idx : ℤ)) = 0 then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, (z < base ∨ base + (M : ℤ) ≤ z) → tape' z = source z) := by
  induction M generalizing base pc source with
  | zero =>
    refine ⟨source, ?_, ?_, ?_⟩
    · simp [rayMachineRun]
    · intro idx hidx
      omega
    · intro _ _
      rfl
  | succ M ih =>
    have hcode0 : CodeAt program pc (zeroIndicator base base pc) := hcode.left
    have hcodeRest : CodeAt program (pc + 3) (zeroIndicatorVec M (base + 1) (pc + 3)) := by
      simpa only [length_zeroIndicator] using hcode.right
    let tape₁ := Function.update source base (if source base = 0 then (1 : ℝ) else 0)
    have hrun0 : rayMachineRun program oracle 2 ⟨pc, 0, source, q⟩ =
        some ⟨pc + 3, 0, tape₁, q⟩ :=
      zeroIndicator_correct program oracle base base pc hcode0 source q
    obtain ⟨tape₂, hrunRest, hvalsRest, hframeRest⟩ :=
      ih (base + 1) (pc + 3) hcodeRest tape₁
    refine ⟨tape₂, ?_, ?_, ?_⟩
    · have hsteps : 2 * (M + 1) = 2 + 2 * M := by omega
      have hpc : pc + 3 * (M + 1) = pc + 3 + 3 * M := by omega
      rw [hsteps, hpc, run_add program oracle 2 (2 * M), hrun0, Option.bind_some, hrunRest]
    · intro idx hidx
      rcases idx with _ | idx
      · simp only [Nat.cast_zero, add_zero]
        have hlt : base < base + 1 := by omega
        rw [hframeRest base (Or.inl hlt)]
        simp [tape₁]
      · have hidx' : idx < M := Nat.lt_of_succ_lt_succ hidx
        have h := hvalsRest idx hidx'
        have heq : base + ((idx + 1 : ℕ) : ℤ) = base + 1 + (idx : ℤ) := by omega
        have hne : base + 1 + (idx : ℤ) ≠ base := by omega
        have htape₁ : tape₁ (base + 1 + (idx : ℤ)) = source (base + 1 + (idx : ℤ)) := by
          dsimp [tape₁]
          exact Function.update_of_ne hne _ _
        rw [heq, h, htape₁]
    · intro z hz
      have hzRest : z < base + 1 ∨ base + 1 + (M : ℤ) ≤ z := by omega
      have hne : z ≠ base := by omega
      rw [hframeRest z hzRest]
      dsimp [tape₁]
      exact Function.update_of_ne hne _ _

/-- Affine slack expression for pair `(idx / V, idx % V)` in an `m × V` facet-vertex grid. -/
def matrixSlackExpr (d V : ℕ) (lBase xBase : ℤ) (idx : ℕ) : Expr :=
  slackExpr d (lBase + ((idx / V : ℕ) : ℤ) * (d : ℤ)) (xBase + ((idx % V : ℕ) : ℤ) * (d : ℤ))

theorem valid_matrixSlackExpr (d V : ℕ) (source : ℤ → ℝ) (lBase xBase : ℤ) (idx : ℕ) :
    (matrixSlackExpr d V lBase xBase idx).Valid source :=
  valid_slackExpr d source _ _

theorem eval_matrixSlackExpr {d m V : ℕ} (source : ℤ → ℝ) (lBase xBase : ℤ)
    (j : Fin m) (k : Fin V) :
    (matrixSlackExpr d V lBase xBase (j.val * V + k.val)).eval source =
      (∑ i : Fin d,
        source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) - 1 := by
  have hV : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have hdiv : (j.val * V + k.val) / V = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hV, Nat.div_eq_zero_iff.mpr (Or.inr k.isLt),
      Nat.zero_add]
  have hmod : (j.val * V + k.val) % V = k.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k.isLt]
  simp only [matrixSlackExpr, hdiv, hmod, eval_slackExpr]

/-- Straight-line program computing the entire `m × V` 0/1 facet-vertex incidence matrix
into `outBase + j * V + k`. -/
def facetVertexIncidenceMatrixDest (d m V : ℕ) (lBase xBase minBase : ℤ) : ℤ :=
  evalVecDest (m * V) (matrixSlackExpr d V lBase xBase) minBase

def facetVertexIncidenceMatrixSteps (d m V : ℕ) (lBase xBase : ℤ) : ℕ :=
  emitVecSteps (m * V) (matrixSlackExpr d V lBase xBase) + 2 * (m * V)

def facetVertexIncidenceMatrixPC (d m V : ℕ) (lBase xBase : ℤ) : ℕ :=
  emitVecSteps (m * V) (matrixSlackExpr d V lBase xBase) + 3 * (m * V)

def facetVertexIncidenceMatrixProgram (d m V : ℕ) (lBase xBase minBase : ℤ) :
    List RayInstruction :=
  let M := m * V
  let f := matrixSlackExpr d V lBase xBase
  let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
  let s := emitVecSteps M f
  (emitVec M f outBase 0 ++ zeroIndicatorVec M outBase s) ++ [.halt]

theorem facetVertexIncidenceMatrixProgram_correct {d m V : ℕ}
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
    (lBase xBase minBase : ℤ) (q : ℕ) :
    let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
    let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
    let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
    let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
    minBase ≤ outBase ∧
    ∃ c' : RayConfiguration,
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ (j : Fin m) (k : Fin V),
        c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if (∑ i : Fin d,
              source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps haltPC
  let M := m * V
  let f := matrixSlackExpr d V lBase xBase
  let s := emitVecSteps M f
  have hmin : minBase ≤ outBase := le_max_right _ _
  have hbound : emitVecReadBound M f ≤ outBase := le_max_left _ _
  have hfresh : ∀ i : ℕ, i < M → (f i).ReadFresh outBase :=
    readFresh_of_emitVecReadBound M f outBase hbound
  let body := emitVec M f outBase 0 ++ zeroIndicatorVec M outBase s
  have hcodeAll : CodeAt prog 0 body :=
    CodeAt.prefix_zero body [.halt]
  have hcodeVec : CodeAt prog 0 (emitVec M f outBase 0) := hcodeAll.left
  have hcodeZero : CodeAt prog s (zeroIndicatorVec M outBase s) := by
    have h := hcodeAll.right
    simpa only [Nat.zero_add, length_emitVec M f outBase 0] using h
  have hhalt : prog[s + 3 * M]? = some .halt := by
    change (body ++ [.halt])[s + 3 * M]? = some .halt
    have hlen : body.length = s + 3 * M := by
      simp [body, s, length_emitVec M f outBase 0]
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨c₁, hrun₁, hpc₁, hhead₁, hq₁, hvals₁, hframe₁⟩ :=
    emitVec_correct M f prog oracle source outBase outBase 0 ⟨0, 0, source, q⟩
      rfl rfl hcodeVec le_rfl hfresh (fun _ _ => rfl)
      (fun idx _ => valid_matrixSlackExpr d V source lBase xBase idx)
  have hpc₁' : c₁.pc = s := by simpa only [Nat.zero_add] using hpc₁
  have hc₁_eq : c₁ = ⟨s, 0, c₁.tape, q⟩ := by
    cases c₁
    simp only [RayConfiguration.mk.injEq] at hpc₁' hhead₁ hq₁ ⊢
    exact ⟨hpc₁', hhead₁, trivial, hq₁⟩
  obtain ⟨tape₂, hrun₂, hvals₂, hframe₂⟩ :=
    zeroIndicatorVec_correct M prog oracle outBase s hcodeZero c₁.tape q
  refine ⟨hmin, ⟨s + 3 * M, 0, tape₂, q⟩, ?_, rfl, hhalt, rfl, rfl, ?_, ?_⟩
  · change rayMachineRun prog oracle (s + 2 * M) ⟨0, 0, source, q⟩ = _
    rw [run_add prog oracle s (2 * M), hrun₁, Option.bind_some, hc₁_eq]
    exact hrun₂
  · intro j k
    have hjk_lt : j.val * V + k.val < M := by
      have h1 : j.val + 1 ≤ m := j.isLt
      have h2 : (j.val + 1) * V ≤ m * V := Nat.mul_le_mul_right V h1
      have h3 : j.val * V + k.val < (j.val + 1) * V := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_lt_add_left k.isLt (j.val * V)
      exact lt_of_lt_of_le h3 h2
    let idx := j.val * V + k.val
    have haddr : outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ) = outBase + (idx : ℤ) := by
      dsimp [idx]
      push_cast
      ring
    dsimp only
    rw [haddr, hvals₂ idx hjk_lt, hvals₁ idx hjk_lt]
    have heval := eval_matrixSlackExpr (d := d) source lBase xBase j k
    dsimp [f, idx]
    simp only [heval, sub_eq_zero]
  · intro z hz
    exact (hframe₂ z (Or.inl hz)).trans (hframe₁ z hz)

end Grunbaum2003.RayFieldExpr

namespace Grunbaum2003

theorem rayMachine_facet_vertex_incidence_matrix_program_proved :
  ∃ (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ),
    ∀ {d m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  refine ⟨RayFieldExpr.facetVertexIncidenceMatrixProgram,
    RayFieldExpr.facetVertexIncidenceMatrixDest,
    RayFieldExpr.facetVertexIncidenceMatrixSteps,
    RayFieldExpr.facetVertexIncidenceMatrixPC, ?_⟩
  intro d m V oracle source lBase xBase minBase q
  exact RayFieldExpr.facetVertexIncidenceMatrixProgram_correct oracle source lBase xBase minBase q

end Grunbaum2003

end

open Grunbaum2003 in
theorem inline_solution :
  ∃ (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ),
    ∀ {d m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) :=
  Grunbaum2003.rayMachine_facet_vertex_incidence_matrix_program_proved

end RayCounterfamilyInline05

namespace Grunbaum2003

theorem rayMachine_facet_vertex_incidence_matrix_program :
∃ (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ),
    ∀ {d m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z) :=
  @RayCounterfamilyInline05.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_rayMachine_perturbed_midpoint_cramer_and_incidence_composition.lean
-- SHA256: 3222f2be07b6f6592de0b6913f35c7081264d8718499fcaad47e10e8a9fd8d42
namespace RayCounterfamilyInline06

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators Matrix Classical

open Grunbaum2003

lemma rayMachine_prefix_and_perturbed_query_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
    (hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (hDir_ne : (fun i : Fin d =>
      c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0) :
    let prog := pre ++
      (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
    let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries + 1 ∧
      (∀ i : Fin d,
        c.tape (outBase + (i.val : ℤ)) =
          oracle (fun j : Fin d =>
            c_pre.tape (pBase + (j.val : ℤ)) +
              c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_pq := perturbedRayQuerySteps d pBase uBase epsCell
  obtain ⟨hMin, c_pq, hRun_pq, _, hHalt_pq, hHead_pq, hQ_pq, hVal_pq, hPres_pq⟩ :=
    hPerturbedQueryProg oracle c_pre.tape pBase uBase epsCell minBase c_pre.queries hDir_ne
  have hRel := hRelocate pre (perturbedRayQueryProgram d pBase uBase epsCell minBase)
    oracle t_pq ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_pq := hRelocate pre (perturbedRayQueryProgram d pBase uBase epsCell minBase)
    oracle 0 c_pq
  refine ⟨hMin, t_pre + t_pq, relocateCfg pre.length c_pq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_pq, Option.map_some]
  · exact hRel_pq.2.2.2.2.2 hHalt_pq
  · rw [hRel_pq.2.1, hHead_pq]
  · rw [hRel_pq.2.2.2.1, hQ_pq]
  · intro i
    rw [hRel_pq.2.2.1]
    exact hVal_pq i
  · intro z hz
    rw [hRel_pq.2.2.1]
    exact hPres_pq z hz

lemma rayMachine_prefix_and_midpoint_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase

      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++
      (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
    let outBase := midpointVecDest d pBase qBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ i : Fin d,
        c.tape (outBase + (i.val : ℤ)) =
          (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_mp := midpointVecSteps d pBase qBase
  obtain ⟨hMin, c_mp, hRun_mp, _, hHalt_mp, hHead_mp, hQ_mp, hVal_mp, hPres_mp⟩ :=
    hMidpointProg oracle c_pre.tape pBase qBase minBase c_pre.queries
  have hRel := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle t_mp ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_mp := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle 0 c_mp
  refine ⟨hMin, t_pre + t_mp, relocateCfg pre.length c_mp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_mp, Option.map_some]
  · exact hRel_mp.2.2.2.2.2 hHalt_mp
  · rw [hRel_mp.2.1, hHead_mp]
  · rw [hRel_mp.2.2.2.1, hQ_mp]
  · intro i
    rw [hRel_mp.2.2.1]
    exact hVal_mp i
  · intro z hz
    rw [hRel_mp.2.2.1]
    exact hPres_mp z hz

lemma rayFrame_cramer_normal_writes_true_facet_row {d m : ℕ}
    {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m))
    (hFrameCramer2 : ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
      v.det ≠ 0 ∧ ∃ i_new : Fin m,
        i_new ∉ S ∧
        L i_new p₀ = 1 ∧
        ∀ x : Fin d → ℝ,
          ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
    (vBase minBase : ℤ) (q : ℕ)
    (w : Fin d → ℝ) (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (p p₀ : Fin d → ℝ)
    (hLin : LinearIndependent ℝ
      (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))))
    (hv_P : ∀ i : Fin d,
      (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P)
    (hp_front : p ∈ frontier P)
    (hp_eq : p = ∑ i : Fin d,
      w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))))
    (hp_S : ∀ j ∈ S, L j p < 1)
    (hp_p₀ : ∀ k : Fin m, L k p = 1 → L k p₀ = 1) :
    let prog := cramerRowProgram d vBase minBase
    let outBase := cramerRowDest d vBase minBase
    let steps := cramerRowSteps d vBase
    minBase ≤ outBase ∧
    ∃ (c' : RayConfiguration) (i_new : Fin m),
      i_new ∉ S ∧
      L i_new p₀ = 1 ∧
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ x : Fin d → ℝ,
        ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  let v : Matrix (Fin d) (Fin d) ℝ :=
    fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
  obtain ⟨hdet, i_new, hi_not_S, hi_p₀, hi_row⟩ :=
    hFrameCramer2 v hLin w hw_pos hw_sum hv_P p p₀ hp_front hp_eq hp_S hp_p₀
  obtain ⟨hMin, c', hRun, hPC, hHalt, hHead, hQ, hVal, hPres⟩ :=
    hCramerProg oracle source vBase minBase q hdet
  refine ⟨hMin, c', i_new, hi_not_S, hi_p₀, hRun, hPC, hHalt, hHead, hQ, ?_, hPres⟩
  intro x
  have hcongr : (∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k) =
      ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hVal k]
  rw [hcongr, hi_row x]

lemma rayMachine_prefix_and_incidence_matrix_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    {m V : ℕ} (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++
      (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
    let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ (j : Fin m) (k : Fin V),
        c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if (∑ i : Fin d,
              c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_inc := facetVertexIncidenceMatrixSteps d m V lBase xBase
  obtain ⟨hMin, c_inc, hRun_inc, _, hHalt_inc, hHead_inc, hQ_inc, hVal_inc, hPres_inc⟩ :=
    @hIncMatrixProg m V oracle c_pre.tape lBase xBase minBase c_pre.queries
  have hRel := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle t_inc ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_inc := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle 0 c_inc
  refine ⟨hMin, t_pre + t_inc, relocateCfg pre.length c_inc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_inc, Option.map_some]
  · exact hRel_inc.2.2.2.2.2 hHalt_inc
  · rw [hRel_inc.2.1, hHead_inc]
  · rw [hRel_inc.2.2.2.1, hQ_inc]
  · intro j k
    rw [hRel_inc.2.2.1]
    exact hVal_inc j k
  · intro z hz
    rw [hRel_inc.2.2.1]
    exact hPres_inc z hz

theorem inline_solution (d : ℕ) :
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
       (_hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ),
      rayMachineRun (pre ++
          (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      (fun i : Fin d =>
        c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries + 1 ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              c_pre.tape (pBase + (j.val : ℤ)) +
                c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
       (S : Finset (Fin m)),
      (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        v.det ≠ 0 ∧ ∃ i_new : Fin m,
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          ∀ x : Fin d → ℝ,
            ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) →
      ∀ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
        (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
        (cramerRowSteps : ℕ → ℤ → ℕ),
      (∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ),
        let v : Matrix (Fin d) (Fin d) ℝ :=
          fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
        v.det ≠ 0 →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ c' : RayConfiguration,
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ k : Fin d,
            c'.tape (outBase + (k.val : ℤ)) =
              (v.updateCol k (fun _ => 1)).det / v.det) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ)
        (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      ∀ (p p₀ : Fin d → ℝ),
        LinearIndependent ℝ
          (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ i : Fin d,
          (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P) →
        p ∈ frontier P →
        p = ∑ i : Fin d,
          w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ (c' : RayConfiguration) (i_new : Fin m),
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ x : Fin d → ℝ,
            ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro run_add relocateInst relocateCfg hRelocate perturbedRayQueryProgram perturbedRayQueryDest
      perturbedRayQuerySteps hPerturbedQueryProg pre oracle t_pre c_pre pBase uBase epsCell minBase
      hRun_pre hDir_ne
    exact rayMachine_prefix_and_perturbed_query_composition run_add relocateInst relocateCfg hRelocate
      perturbedRayQueryProgram perturbedRayQueryDest perturbedRayQuerySteps hPerturbedQueryProg
      pre oracle t_pre c_pre pBase uBase epsCell minBase hRun_pre hDir_ne
  · intro run_add relocateInst relocateCfg hRelocate midpointVecProgram midpointVecDest
      midpointVecSteps hMidpointProg pre oracle t_pre c_pre pBase qBase minBase hRun_pre
    exact rayMachine_prefix_and_midpoint_composition run_add relocateInst relocateCfg hRelocate
      midpointVecProgram midpointVecDest midpointVecSteps hMidpointProg
      pre oracle t_pre c_pre pBase qBase minBase hRun_pre
  · intro m P L S hFrameCramer2 cramerRowProgram cramerRowDest cramerRowSteps hCramerProg
      oracle source vBase minBase q w hw_pos hw_sum p p₀ hLin hv_P hp_front hp_eq hp_S hp_p₀
    exact rayFrame_cramer_normal_writes_true_facet_row L S hFrameCramer2 cramerRowProgram
      cramerRowDest cramerRowSteps hCramerProg oracle source vBase minBase q w hw_pos hw_sum
      p p₀ hLin hv_P hp_front hp_eq hp_S hp_p₀
  · intro run_add relocateInst relocateCfg hRelocate facetVertexIncidenceMatrixProgram
      facetVertexIncidenceMatrixDest facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC
      hIncMatrixProg m V pre oracle t_pre c_pre lBase xBase minBase hRun_pre
    exact rayMachine_prefix_and_incidence_matrix_composition run_add relocateInst relocateCfg hRelocate
      facetVertexIncidenceMatrixProgram facetVertexIncidenceMatrixDest
      facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC hIncMatrixProg
      pre oracle t_pre c_pre lBase xBase minBase hRun_pre

end RayCounterfamilyInline06

namespace Grunbaum2003

theorem rayMachine_perturbed_midpoint_cramer_and_incidence_composition :
∀ (d : ℕ),
(∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
       (_hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ),
      rayMachineRun (pre ++
          (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      (fun i : Fin d =>
        c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries + 1 ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              c_pre.tape (pBase + (j.val : ℤ)) +
                c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
       (S : Finset (Fin m)),
      (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        v.det ≠ 0 ∧ ∃ i_new : Fin m,
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          ∀ x : Fin d → ℝ,
            ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) →
      ∀ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
        (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
        (cramerRowSteps : ℕ → ℤ → ℕ),
      (∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ),
        let v : Matrix (Fin d) (Fin d) ℝ :=
          fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
        v.det ≠ 0 →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ c' : RayConfiguration,
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ k : Fin d,
            c'.tape (outBase + (k.val : ℤ)) =
              (v.updateCol k (fun _ => 1)).det / v.det) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ)
        (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      ∀ (p p₀ : Fin d → ℝ),
        LinearIndependent ℝ
          (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ i : Fin d,
          (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P) →
        p ∈ frontier P →
        p = ∑ i : Fin d,
          w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ (c' : RayConfiguration) (i_new : Fin m),
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ x : Fin d → ℝ,
            ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) :=
  @RayCounterfamilyInline06.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayOracle_local_sector_and_known_facet_exclusion.lean
-- SHA256: fef697de5964e7ae01aca6a1254556d942bac5e452cf2020ca153a436754bee8
namespace RayCounterfamilyInline07

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_outer_vertex_fixed_iff {d : ℕ} (hd : 0 < d)
    {P Q : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P) (hPQ : P ⊆ Q)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ∈ Q.extremePoints ℝ) :
    x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hzeroQ : (0 : Fin d → ℝ) ∈ interior Q := interior_mono hPQ hzero
  have hxne : x ≠ 0 := by
    intro heq
    have hzext : (0 : Fin d → ℝ) ∈ Q.extremePoints ℝ := heq ▸ hx
    exact Set.disjoint_left.mp (disjoint_interior_extremePoints Q) hzeroQ hzext
  refine ⟨hxne, ?_⟩
  constructor
  · intro hfixed
    have hxP : x ∈ P := hclosed.frontier_subset
      ((rayOracle_eq_self_iff_frontier hconv hclosed hzero horacle hxne).mp hfixed)
    exact isExtreme_singleton.mp
      ((isExtreme_singleton.mpr hx).mono hPQ (Set.singleton_subset_iff.mpr hxP))
  · intro hxP
    have hxNot : x ∉ interior P := by
      intro hi
      exact Set.disjoint_left.mp (disjoint_interior_extremePoints P) hi hxP
    have hxFront : x ∈ frontier P :=
      (mem_frontier_iff_notMem_interior (extremePoints_subset hxP)).mpr hxNot
    exact (rayOracle_eq_self_iff_frontier hconv hclosed hzero horacle hxne).mpr hxFront

end Grunbaum2003

namespace Grunbaum2003

theorem perturb_frontier_ne_zero_of_negative_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P) : p + s • u ≠ 0 := by
  intro hz
  have hc : 0 ≤ s / a := div_nonneg hs ha.le
  have hc1 : s / a < 1 := (div_lt_one ha).mpr hsa
  have hi := hconv.combo_interior_self_mem_interior hzero hminus
    (sub_pos.mpr hc1) hc (sub_add_cancel 1 (s / a))
  have heq : (s / a) • ((-a) • u) = p := by
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    field_simp
    nlinarith only [hj]
  have hpint : p ∈ interior P := by
    simpa only [smul_zero, zero_add, heq] using hi
  exact hp.2 hpint

theorem rayOracle_perturb_scale_upper {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + s • u) = t • (p + s • u) ∧
      t * (a - s) ≤ a := by
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + s • u) hr
  refine ⟨t, ht, heq, ?_⟩
  have hden : 0 < a + t * s := add_pos_of_pos_of_nonneg ha (mul_nonneg ht.le hs)
  have hc : 0 ≤ a / (a + t * s) := div_nonneg ha.le hden.le
  have hc1 : a / (a + t * s) ≤ 1 := (div_le_one hden).mpr (by linarith [mul_nonneg ht.le hs])
  have hcombo := hconv (hclosed.frontier_subset hq) hminus hc
    (sub_nonneg.mpr hc1) (add_sub_cancel (a / (a + t * s)) 1)
  have hceq : (a / (a + t * s)) • oracle (p + s • u) +
      (1 - a / (a + t * s)) • ((-a) • u) =
      (t * a / (a + t * s)) • p := by
    rw [heq]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [hceq] at hcombo
  have hscaleNonneg : 0 ≤ t * a / (a + t * s) :=
    div_nonneg (mul_nonneg ht.le ha.le) hden.le
  have hscaleLe := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hp hscaleNonneg).mp hcombo
  have hnum : t * a ≤ a + t * s := (div_le_one hden).mp hscaleLe
  nlinarith only [hnum]

theorem facet_local_step_bounds {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    0 < ε ∧ ε < a ∧ ε * (1 + a * M) < a * δ := by
  have haM : 0 ≤ a * M := mul_nonneg ha.le hM
  have hD : 0 < 2 * (1 + a * M + δ) := by linarith
  dsimp only
  refine ⟨div_pos (mul_pos ha hδ) hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).mpr
    have hh : δ < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh ha
  · rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).mpr
    have hh : 1 + a * M < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh (mul_pos ha hδ)

theorem rayOracle_perturb_avoids_halfspace_boundary {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P)
    (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ℓ p ≤ 1 - δ) (huBound : ℓ u ≤ M)
    (hs : 0 ≤ s) (hsε : s ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ℓ (oracle (p + s • u)) < 1 := by
  obtain ⟨hεpos, hεa, hεgap⟩ := facet_local_step_bounds ha hδ hM
  have hsa : s < a := hsε.trans_lt hεa
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  refine ⟨hr, ?_⟩
  obtain ⟨t, ht, heq, hupper⟩ :=
    rayOracle_perturb_scale_upper hconv hclosed hzero hp ha hs hsa hminus horacle
  have hgap : s * (1 + a * M) < a * δ :=
    (mul_le_mul_of_nonneg_right hsε (by positivity)).trans_lt hεgap
  have hbase : a * (1 - δ + s * M) < a - s := by
    nlinarith only [hgap]
  have hℓ : ℓ p + s * ℓ u ≤ 1 - δ + s * M :=
    add_le_add hpSlack (mul_le_mul_of_nonneg_left huBound hs)
  have hℓa : a * (ℓ p + s * ℓ u) < a - s :=
    (mul_le_mul_of_nonneg_left hℓ ha.le).trans_lt hbase
  have hscaled : a * (t * (ℓ p + s * ℓ u)) < a := by
    calc
      a * (t * (ℓ p + s * ℓ u)) = t * (a * (ℓ p + s * ℓ u)) := by ring
      _ < t * (a - s) := mul_lt_mul_of_pos_left hℓa ht
      _ ≤ a := hupper
  rw [heq, map_smul, map_add, map_smul]
  change t * (ℓ p + s * ℓ u) < 1
  nlinarith only [ha, hscaled]

theorem rayOracle_perturb_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hsε : |s| ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ∀ j, L j (oracle (p + s • u)) < 1 := by
  have hsa : |s| < a := hsε.trans_lt (facet_local_step_bounds ha hδ hM).2.1
  by_cases hs : 0 ≤ s
  · have hsε' : s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (le_abs_self s).trans hsε
    refine ⟨perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs
      ((le_abs_self s).trans_lt hsa) hminus, ?_⟩
    intro j
    exact (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus (L j) (hpSlack j) ((le_abs_self _).trans (huBound j))
      hs hsε' horacle).2
  · have hs' : 0 ≤ -s := by linarith
    have hsε' : -s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (neg_le_abs s).trans hsε
    have hsa' : -s < a := (neg_le_abs s).trans_lt hsa
    have hminus' : (-a) • (-u) ∈ P := by
      simpa only [smul_neg, neg_smul, neg_neg] using hplus
    have heq : p + (-s) • (-u) = p + s • u := by
      simp only [smul_neg, neg_smul, neg_neg]
    refine ⟨heq ▸ perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp
      ha hs' hsa' hminus', ?_⟩
    intro j
    have huBound' : L j (-u) ≤ M := by
      rw [map_neg]
      exact (neg_le_abs _).trans (huBound j)
    have h := (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus' (L j) (hpSlack j) huBound' hs' hsε' horacle).2
    simpa only [heq] using h

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_pos_smul_eq {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    oracle (c • x) = oracle x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  obtain ⟨hq, t, ht, hqt⟩ := horacle (c • x) hcx
  obtain ⟨hp, s, hs, hps⟩ := horacle x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hp hq (div_pos (mul_pos ht hc) hs)
  rw [hqt, hps, smul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']

theorem facet_local_step_lt_half {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    a * δ / (2 * (1 + a * M + δ)) < a / 2 := by
  have hden : 0 < 2 * (1 + a * M + δ) := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hm : 0 ≤ a * M := mul_nonneg ha.le hM
  have hh : δ < 1 + a * M + δ := by linarith
  have hk := mul_lt_mul_of_pos_left hh ha
  nlinarith only [hk]

theorem scaled_planar_first_two_queries_avoid_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    p - ε • u ≠ 0 ∧
    ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
      oracle (p - ε • u) = τ • (p - ε • u) ∧
      (∀ j, L j (oracle (p - ε • u)) < 1) ∧
      let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
      r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hεhalf : ε < a / 2 := facet_local_step_lt_half ha hδ hM
  have hfirst := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := -ε) (by rw [abs_neg, abs_of_pos hε]) horacle
  have heq₁ : p + (-ε) • u = p - ε • u := by simp only [neg_smul, sub_eq_add_neg]
  rw [heq₁] at hfirst
  refine ⟨hfirst.1, ?_⟩
  obtain ⟨hq, τ, hτ, hreply⟩ := horacle (p - ε • u) hfirst.1
  have hminus' : (-a) • (-u) ∈ P := by simpa only [smul_neg, neg_smul, neg_neg] using hplus
  have hεa : ε < a := (facet_local_step_bounds ha hδ hM).2.1
  obtain ⟨t, ht, hteq, hupper⟩ := rayOracle_perturb_scale_upper hconv hclosed hzero hp
    ha hε.le hεa hminus' horacle
  have heq₂ : p + ε • (-u) = p - ε • u := by simp only [smul_neg, sub_eq_add_neg]
  rw [heq₂] at hteq
  have htτ : t = τ := by
    apply (smul_left_injective ℝ hfirst.1)
    exact hteq.symm.trans hreply
  rw [htτ] at hupper
  have hτtwo : τ < 2 := by
    have hm := mul_lt_mul_of_pos_left hεhalf hτ
    nlinarith only [hupper, hm, ha]
  refine ⟨τ, hτ, hτtwo, hreply, hfirst.2, ?_⟩
  let s₂ := τ * ε / 2
  have hs₂ : 0 ≤ s₂ := by dsimp [s₂]; positivity
  have hs₂ε : s₂ ≤ ε := by
    dsimp only [s₂]
    have hm := mul_lt_mul_of_pos_right hτtwo hε
    linarith
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := s₂) (by rw [abs_of_nonneg hs₂]; exact hs₂ε) horacle
  have hc : 0 < 2 / (1 + τ) := by positivity
  have hr₂ : (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p =
      (2 / (1 + τ)) • (p + s₂ • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s₂]
    ring
  rw [hr₂]
  refine ⟨smul_ne_zero hc.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hc]
  exact hsafe.2

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_local_cone_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    α • p + β • u ≠ 0 ∧ ∀ j, L j (oracle (α • p + β • u)) < 1 := by
  have hs : |β / α| ≤ a * δ / (2 * (1 + a * M + δ)) := by
    rw [abs_div, abs_of_pos hα]
    apply (div_le_iff₀ hα).mpr
    simpa only [mul_comm] using hβ
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hs horacle
  have heq : α • p + β • u = α • (p + (β / α) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [heq]
  refine ⟨smul_ne_zero hα.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hα]
  exact hsafe.2

theorem local_cone_convex_coefficients {α β γ η ε θ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * ε) (hη : |η| ≤ γ * ε)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    0 < (1 - θ) * α + θ * γ ∧
      |(1 - θ) * β + θ * η| ≤ ((1 - θ) * α + θ * γ) * ε := by
  have hcomp : 0 ≤ 1 - θ := sub_nonneg.mpr hθone
  constructor
  · by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hα
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hcomp hα.le)
        (mul_pos (lt_of_le_of_ne hθ (Ne.symm hz)) hγ)
  · calc
      |(1 - θ) * β + θ * η| ≤ |(1 - θ) * β| + |θ * η| := abs_add_le _ _
      _ = (1 - θ) * |β| + θ * |η| := by
        rw [abs_mul, abs_of_nonneg hcomp, abs_mul, abs_of_nonneg hθ]
      _ ≤ (1 - θ) * (α * ε) + θ * (γ * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left hβ hcomp)
          (mul_le_mul_of_nonneg_left hη hθ)
      _ = ((1 - θ) * α + θ * γ) * ε := by ring

theorem rayOracle_safe_reference_segment {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β γ η θ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    (hη : |η| ≤ γ * (a * δ / (2 * (1 + a * M + δ))))
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let r := (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  obtain ⟨hpos, hbound⟩ := local_cone_convex_coefficients hα hγ hβ hη hθ hθone
  have hsafe := rayOracle_local_cone_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hpos hbound horacle
  have heq : (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u) =
      ((1 - θ) * α + θ * γ) • p + ((1 - θ) * β + θ * η) • u := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [heq] using hsafe

end Grunbaum2003

namespace Grunbaum2003.RayPlanar

theorem known_slack_product_bounds {k : ℕ} (s : Fin k → ℝ) (hs : ∀ j, 0 < s j) :
    let δ := ∏ j, s j / (1 + s j)
    0 < δ ∧ ∀ j, δ ≤ s j := by
  have hden : ∀ j, 0 < 1 + s j := fun j => by linarith only [hs j]
  have hfactor : ∀ j, 0 < s j / (1 + s j) := fun j => div_pos (hs j) (hden j)
  have hfactorOne : ∀ j, s j / (1 + s j) ≤ 1 := by
    intro j
    apply (div_le_one (hden j)).mpr
    linarith
  have hfactorSlack : ∀ j, s j / (1 + s j) ≤ s j := by
    intro j
    apply (div_le_iff₀ (hden j)).mpr
    nlinarith only [sq_nonneg (s j)]
  dsimp only
  refine ⟨Finset.prod_pos (fun j _ => hfactor j), ?_⟩
  intro j
  have hrest : (∏ i ∈ Finset.univ.erase j, s i / (1 + s i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hfactor i).le) (fun i _ => hfactorOne i)
  rw [← Finset.mul_prod_erase Finset.univ (fun i => s i / (1 + s i)) (Finset.mem_univ j)]
  exact (mul_le_mul_of_nonneg_left hrest (hfactor j).le).trans (by simpa only [mul_one] using hfactorSlack j)

theorem known_direction_square_sum_bounds {k : ℕ} (v : Fin k → ℝ) :
    0 ≤ 1 + ∑ j, (v j) ^ 2 ∧ ∀ j, |v j| ≤ 1 + ∑ i, (v i) ^ 2 := by
  have hsum : 0 ≤ ∑ j, (v j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (v j))
  refine ⟨by linarith only [hsum], ?_⟩
  intro j
  have hsingle : (v j) ^ 2 ≤ ∑ i, (v i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j)
  have habs : |v j| ≤ 1 + (v j) ^ 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg (v j + 1 / 2)]
    · nlinarith only [sq_nonneg (v j - 1 / 2)]
  linarith only [habs, hsingle]

theorem known_facet_field_parameters {d k : ℕ}
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ)
    (hstrict : ∀ j, L j p < 1) :
    let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
    let M := 1 + ∑ j, (L j u) ^ 2
    0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M) := by
  obtain ⟨hδ, hδbound⟩ := known_slack_product_bounds (fun j => 1 - L j p)
    (fun j => sub_pos.mpr (hstrict j))
  obtain ⟨hM, hMbound⟩ := known_direction_square_sum_bounds (fun j => L j u)
  refine ⟨hδ, hM, ?_, hMbound⟩
  intro j
  have hj := hδbound j
  linarith only [hj]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem rayOracle_scale_lt_one_of_not_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) (hxP : x ∉ P) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ oracle x = t • x := by
  obtain ⟨hq, t, ht, heq⟩ := horacle x hx
  refine ⟨t, ht, ?_, heq⟩
  by_contra hn
  have htge : 1 ≤ t := le_of_not_gt hn
  have hsnonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hsle : t⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one ht]
    exact htge
  have hscaled := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hq hsnonneg).mpr hsle
  have hxmem : x ∈ P := by
    simpa only [heq, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hscaled
  exact hxP hxmem

theorem outer_vertex_probe_known_facets_strict {d k : ℕ} (hd : 0 < d)
    {P Q : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P) (hPQ : P ⊆ Q)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ∈ Q.extremePoints ℝ) (hnonfixed : oracle x ≠ x)
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (hxBound : ∀ j, L j x ≤ 1) :
    x ≠ 0 ∧ (∀ j, L j (oracle x) < 1) := by
  obtain ⟨hxne, hfixed⟩ := rayOracle_outer_vertex_fixed_iff hd hconv hclosed hzero hPQ horacle hx
  have hxNotP : x ∉ P := by
    intro hxP
    apply hnonfixed
    apply hfixed.mpr
    exact isExtreme_singleton.mp
      ((isExtreme_singleton.mpr hx).mono hPQ (Set.singleton_subset_iff.mpr hxP))
  obtain ⟨t, ht, htone, heq⟩ := rayOracle_scale_lt_one_of_not_mem hconv hclosed hzero horacle hxne hxNotP
  refine ⟨hxne, ?_⟩
  intro j
  rw [heq, map_smul]
  change t * L j x < 1
  exact (mul_le_mul_of_nonneg_left (hxBound j) ht.le).trans_lt (by simpa only [mul_one] using htone)

theorem rayOracle_known_nonpositive_direction_strict {d k : ℕ}
    {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    {x : Fin d → ℝ} (hx : x ≠ 0) (hdir : ∀ j, L j x ≤ 0) :
    ∀ j, L j (oracle x) < 1 := by
  obtain ⟨_, t, ht, heq⟩ := horacle x hx
  intro j
  rw [heq, map_smul]
  change t * L j x < 1
  have hle : t * L j x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (hdir j)
  linarith only [hle]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem convex_secant_zero_progress {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x) :
    0 < h y - h x ∧
      0 ≤ (x * h y - y * h x) / (h y - h x) ∧
      (x * h y - y * h x) / (h y - h x) < x := by
  have hcross := hconv.secant_mono_aux1 (Set.mem_univ 0) (Set.mem_univ y) hx hxy
  simp only [sub_zero, hzero, mul_zero, zero_add] at hcross
  have hprod : 0 < (y - x) * h x := mul_pos (sub_pos.mpr hxy) hhx
  have hden : 0 < h y - h x := by
    by_contra hn
    have hle : h y ≤ h x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle hx.le
    nlinarith only [hcross, hprod, hmul]
  refine ⟨hden, div_nonneg (by linarith only [hcross]) hden.le, ?_⟩
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [hprod]

theorem secant_zero_of_common_affine_piece {h : ℝ → ℝ} {x y a b : ℝ}
    (hden : h y - h x ≠ 0)
    (hx : h x = a * x + b) (hy : h y = a * y + b) :
    a * ((x * h y - y * h x) / (h y - h x)) + b = 0 := by
  have hz : ((x * h y - y * h x) / (h y - h x)) * (h y - h x) =
      x * h y - y * h x := div_mul_cancel₀ _ hden
  have hp : (a * ((x * h y - y * h x) / (h y - h x)) + b) *
      (h y - h x) = 0 := by
    calc
      _ = a * (((x * h y - y * h x) / (h y - h x)) * (h y - h x)) +
          b * (h y - h x) := by ring
      _ = a * (x * h y - y * h x) + b * (h y - h x) := by rw [hz]
      _ = 0 := by rw [hx, hy]; ring
  exact (mul_eq_zero.mp hp).resolve_right hden

theorem convex_affine_piece_active_between {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) {a b x z y : ℝ}
    (hmajor : ∀ t, a * t + b ≤ h t)
    (hx : h x = a * x + b) (hy : h y = a * y + b)
    (hxz : x ≤ z) (hzy : z ≤ y) : h z = a * z + b := by
  rcases eq_or_lt_of_le hxz with rfl | hxz
  · exact hx
  rcases eq_or_lt_of_le hzy with rfl | hzy
  · exact hy
  apply le_antisymm ?_ (hmajor z)
  have hk := hconv.secant_mono_aux1 (Set.mem_univ x) (Set.mem_univ y) hxz hzy
  rw [hx, hy] at hk
  by_contra hn
  have hp : 0 < (y - x) * (h z - (a * z + b)) :=
    mul_pos (sub_pos.mpr (hxz.trans hzy)) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem third_secant_response_leaves_common_piece {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y a b : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x)
    (hax : h x = a * x + b) (hay : h y = a * y + b)
    (hnext : 0 < h ((x * h y - y * h x) / (h y - h x))) :
    h ((x * h y - y * h x) / (h y - h x)) ≠
      a * ((x * h y - y * h x) / (h y - h x)) + b := by
  have hden := (convex_secant_zero_progress hconv hzero hx hxy hhx).1
  have hz := secant_zero_of_common_affine_piece hden.ne' hax hay
  rw [hz]
  exact ne_of_gt hnext

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def finiteAffineEnvelope {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => a j * x + b j)

lemma finiteAffineEnvelope_major {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (j : Fin m) (x : ℝ) : a j * x + b j ≤ finiteAffineEnvelope hm a b x :=
  Finset.le_sup' (fun k => a k * x + b k) (Finset.mem_univ j)

lemma finiteAffineEnvelope_attained {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (x : ℝ) : ∃ j, finiteAffineEnvelope hm a b x = a j * x + b j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin m))) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun j => a j * x + b j)
  exact ⟨j, hj⟩

lemma finiteAffineEnvelope_convex {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (finiteAffineEnvelope hm a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hab
  simp only [smul_eq_mul]
  apply Finset.sup'_le
  intro j _
  have hx := finiteAffineEnvelope_major hm a b j x
  have hy := finiteAffineEnvelope_major hm a b j y
  calc
    a j * (α * x + β * y) + b j =
        α * (a j * x + b j) + β * (a j * y + b j) := by
      linear_combination -b j * hab
    _ ≤ α * finiteAffineEnvelope hm a b x + β * finiteAffineEnvelope hm a b y :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)

theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)

theorem rayOracle_halfspace_envelope_eq {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + x • u) = t • (p + x • u) ∧
      finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 1 / t - 1 := by
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + x • u) hr
  obtain ⟨hineq, j, hj⟩ := frontier_finite_halfspaces_active L hP hq
  refine ⟨t, ht, heq, le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro k _
    have hk := hineq k
    rw [heq, map_smul, map_add, map_smul] at hk
    change t * (L k p + x * L k u) ≤ 1 at hk
    have hdiv : L k p + x * L k u ≤ 1 / t := (le_div_iff₀ ht).mpr (by nlinarith only [hk])
    linarith only [hdiv]
  · have hj' := hj
    rw [heq, map_smul, map_add, map_smul] at hj'
    change t * (L j p + x * L j u) = 1 at hj'
    have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj'])
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hdiv, hmajor]

theorem halfspace_envelope_zero_at_boundary {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (hp : p ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) 0 = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    dsimp only
    simp only [mul_zero, zero_add]
    linarith only [hle k]
  · have h := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j 0
    simpa only [mul_zero, zero_add, hj, sub_self] using h

theorem convex_gap_nonneg_positive_of_negative_zero {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {z x : ℝ} (hz : z < 0) (hzval : h z = 0) (hx : 0 ≤ x) : 0 ≤ h x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa only [hzero] using (le_refl (0 : ℝ))
  have hk := hconv.secant_mono_aux1 (Set.mem_univ z) (Set.mem_univ x) hz hx
  rw [hzero, hzval] at hk
  simp only [mul_zero, add_zero, zero_add, zero_sub] at hk
  by_contra hn
  have hp : 0 < (-z) * (-h x) := mul_pos (neg_pos.mpr hz) (neg_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem rayOracle_active_halfspace_envelope {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0)
    (j : Fin m) (hj : L j (oracle (p + x • u)) = 1) :
    finiteAffineEnvelope hm (fun k => L k u) (fun k => L k p - 1) x =
      L j u * x + (L j p - 1) := by
  obtain ⟨t, ht, heq, henv⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p u x hr
  rw [heq, map_smul, map_add, map_smul] at hj
  change t * (L j p + x * L j u) = 1 at hj
  have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj])
  linarith only [henv, hdiv]

theorem rayOracle_common_halfspace_opposite_sides_incident {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hrx : p + x • u ≠ 0) (hry : p + y • u ≠ 0)
    (j : Fin m)
    (hjx : L j (oracle (p + x • u)) = 1)
    (hjy : L j (oracle (p + y • u)) = 1) : L j p = 1 := by
  have hax := rayOracle_active_halfspace_envelope hm L hP horacle p u x hrx j hjx
  have hay := rayOracle_active_halfspace_envelope hm L hP horacle p u y hry j hjy
  have hconv := finiteAffineEnvelope_convex hm (fun k => L k u) (fun k => L k p - 1)
  have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j
  have hact := convex_affine_piece_active_between hconv hmajor hax hay hx.le hy.le
  rw [halfspace_envelope_zero_at_boundary hm L hP p u hp] at hact
  simp only [mul_zero, zero_add] at hact
  linarith only [hact]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem envelope_zero_at_frontier {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (x : ℝ) (hp : p + x • u ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    have hk := hle k
    rw [map_add, map_smul] at hk
    change L k p + x * L k u ≤ 1 at hk
    linarith only [hk]
  · have hj' := hj
    rw [map_add, map_smul] at hj'
    change L j p + x * L j u = 1 at hj'
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hmajor, hj']

theorem first_reference_chord_data {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {ε τ : ℝ} (hτ : 0 < τ) (hr : p - ε • u ≠ 0)
    (hreply : oracle (p - ε • u) = τ • (p - ε • u)) :
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let B := r₂ - p
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
    H 0 = 0 ∧ H (-(1 + τ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → 0 ≤ H x) ∧
      oracle (p - ε • u) = p + (-(1 + τ)) • B ∧
      (1 / 2 : ℝ) • (p + r₂) = p + (1 / 2 : ℝ) • B := by
  dsimp only
  let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
  let B := r₂ - p
  have hden : 1 + τ ≠ 0 := ne_of_gt (by linarith)
  have hanchor : p + (-(1 + τ)) • B = τ • (p - ε • u) := by
    ext j
    dsimp [B, r₂]
    field_simp
    <;> ring
  have hp₁ : p + (-(1 + τ)) • B ∈ frontier P := by
    rw [hanchor, ← hreply]
    exact (horacle (p - ε • u) hr).1
  have hzero := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hnegative := envelope_zero_at_frontier hm L hP p B (-(1 + τ)) hp₁
  refine ⟨hzero, hnegative, ?_, hreply.trans hanchor.symm, ?_⟩
  · intro x hx
    exact convex_gap_nonneg_positive_of_negative_zero
      (finiteAffineEnvelope_convex hm _ _) hzero (by linarith) hnegative hx
  · ext j
    dsimp [B]
    ring

theorem first_reference_segment_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M τ x : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hτ : 0 < τ) (hτtwo : τ ≤ 2) (hx : 0 ≤ x) (hxone : x ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let r := p + x • (r₂ - p)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hden : 0 < 1 + τ := by linarith
  have hc : 0 < 2 / (1 + τ) := div_pos (by norm_num) hden
  have hβ : |(0 : ℝ)| ≤ 1 * ε := by simpa only [abs_zero, one_mul] using hε.le
  have hη : |τ * ε / (1 + τ)| ≤ (2 / (1 + τ)) * ε := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hτ.le hε.le) hden.le)]
    have hm := mul_le_mul_of_nonneg_right hτtwo (div_nonneg hε.le hden.le)
    calc
      τ * ε / (1 + τ) = τ * (ε / (1 + τ)) := by ring
      _ ≤ 2 * (ε / (1 + τ)) := hm
      _ = (2 / (1 + τ)) * ε := by ring
  have hsafe := rayOracle_safe_reference_segment hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound (by norm_num : (0 : ℝ) < 1)
    hc hβ hη hx hxone horacle
  have heq : p + x • ((τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p - p) =
      (1 - x) • ((1 : ℝ) • p + (0 : ℝ) • u) +
        x • ((2 / (1 + τ)) • p + (τ * ε / (1 + τ)) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heq] at hsafe
  exact hsafe

end Grunbaum2003.RayPlanar

namespace Grunbaum2003

theorem rayOracle_local_sector_and_known_facet_exclusion :
    (∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd P Q hconv hclosed hzero hPQ oracle horacle x hx
    exact rayOracle_outer_vertex_fixed_iff hd hconv hclosed hzero hPQ horacle hx
  · intro d k hd P Q hconv hclosed hzero hPQ oracle horacle x hx hnonfixed L hxBound
    exact RayPlanar.outer_vertex_probe_known_facets_strict hd hconv hclosed hzero hPQ horacle hx hnonfixed L hxBound
  · intro d k P oracle horacle L x hx hdir
    exact RayPlanar.rayOracle_known_nonpositive_direction_strict horacle L hx hdir
  · intro d k L p u hstrict
    exact RayPlanar.known_facet_field_parameters L p u hstrict
  · intro d ι P hconv hclosed hzero p u hp a δ M ha hδ hM hminus hplus L hpSlack huBound oracle horacle
    obtain ⟨hfirstNe, τ, hτ, hτtwo, hreply, hfirstSlack, hr₂Ne, hr₂Slack⟩ :=
      scaled_planar_first_two_queries_avoid_known_facets hconv hclosed hzero hp ha hδ hM hminus hplus L hpSlack huBound horacle
    refine ⟨hfirstNe, τ, hτ, hτtwo, hreply, hfirstSlack, hr₂Ne, hr₂Slack, ?_⟩
    intro x hx0 hx1
    exact RayPlanar.first_reference_segment_avoids_known_facets hconv hclosed hzero hp ha hδ hM hminus hplus L hpSlack huBound hτ hτtwo.le hx0 hx1 horacle

end Grunbaum2003
end

theorem inline_solution :
    (∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) :=
  Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion

end RayCounterfamilyInline07

namespace Grunbaum2003

theorem rayOracle_local_sector_and_known_facet_exclusion :
(∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →

      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) :=
  @RayCounterfamilyInline07.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayFrame_boundary_extension_axes_and_cramer_normal.lean
-- SHA256: 3230b14164981a5e9a464fb4f349736443f60a74413d74cc37eca8e378a6c814
namespace RayCounterfamilyInline08

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators Matrix

noncomputable section

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003

theorem perturb_frontier_ne_zero_of_negative_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P) : p + s • u ≠ 0 := by
  intro hz
  have hc : 0 ≤ s / a := div_nonneg hs ha.le
  have hc1 : s / a < 1 := (div_lt_one ha).mpr hsa
  have hi := hconv.combo_interior_self_mem_interior hzero hminus
    (sub_pos.mpr hc1) hc (sub_add_cancel 1 (s / a))
  have heq : (s / a) • ((-a) • u) = p := by
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    field_simp
    nlinarith only [hj]
  have hpint : p ∈ interior P := by
    simpa only [smul_zero, zero_add, heq] using hi
  exact hp.2 hpint

theorem rayOracle_perturb_scale_upper {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + s • u) = t • (p + s • u) ∧
      t * (a - s) ≤ a := by
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + s • u) hr
  refine ⟨t, ht, heq, ?_⟩
  have hden : 0 < a + t * s := add_pos_of_pos_of_nonneg ha (mul_nonneg ht.le hs)
  have hc : 0 ≤ a / (a + t * s) := div_nonneg ha.le hden.le
  have hc1 : a / (a + t * s) ≤ 1 := (div_le_one hden).mpr (by linarith [mul_nonneg ht.le hs])
  have hcombo := hconv (hclosed.frontier_subset hq) hminus hc
    (sub_nonneg.mpr hc1) (add_sub_cancel (a / (a + t * s)) 1)
  have hceq : (a / (a + t * s)) • oracle (p + s • u) +
      (1 - a / (a + t * s)) • ((-a) • u) =
      (t * a / (a + t * s)) • p := by
    rw [heq]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [hceq] at hcombo
  have hscaleNonneg : 0 ≤ t * a / (a + t * s) :=
    div_nonneg (mul_nonneg ht.le ha.le) hden.le
  have hscaleLe := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hp hscaleNonneg).mp hcombo
  have hnum : t * a ≤ a + t * s := (div_le_one hden).mp hscaleLe
  nlinarith only [hnum]

theorem facet_local_step_bounds {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    0 < ε ∧ ε < a ∧ ε * (1 + a * M) < a * δ := by
  have haM : 0 ≤ a * M := mul_nonneg ha.le hM
  have hD : 0 < 2 * (1 + a * M + δ) := by linarith
  dsimp only
  refine ⟨div_pos (mul_pos ha hδ) hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).mpr
    have hh : δ < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh ha
  · rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).mpr
    have hh : 1 + a * M < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh (mul_pos ha hδ)

theorem rayOracle_perturb_avoids_halfspace_boundary {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P)
    (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ℓ p ≤ 1 - δ) (huBound : ℓ u ≤ M)
    (hs : 0 ≤ s) (hsε : s ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ℓ (oracle (p + s • u)) < 1 := by
  obtain ⟨hεpos, hεa, hεgap⟩ := facet_local_step_bounds ha hδ hM
  have hsa : s < a := hsε.trans_lt hεa
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  refine ⟨hr, ?_⟩
  obtain ⟨t, ht, heq, hupper⟩ :=
    rayOracle_perturb_scale_upper hconv hclosed hzero hp ha hs hsa hminus horacle
  have hgap : s * (1 + a * M) < a * δ :=
    (mul_le_mul_of_nonneg_right hsε (by positivity)).trans_lt hεgap
  have hbase : a * (1 - δ + s * M) < a - s := by
    nlinarith only [hgap]
  have hℓ : ℓ p + s * ℓ u ≤ 1 - δ + s * M :=
    add_le_add hpSlack (mul_le_mul_of_nonneg_left huBound hs)
  have hℓa : a * (ℓ p + s * ℓ u) < a - s :=
    (mul_le_mul_of_nonneg_left hℓ ha.le).trans_lt hbase
  have hscaled : a * (t * (ℓ p + s * ℓ u)) < a := by
    calc
      a * (t * (ℓ p + s * ℓ u)) = t * (a * (ℓ p + s * ℓ u)) := by ring
      _ < t * (a - s) := mul_lt_mul_of_pos_left hℓa ht
      _ ≤ a := hupper
  rw [heq, map_smul, map_add, map_smul]
  change t * (ℓ p + s * ℓ u) < 1
  nlinarith only [ha, hscaled]

theorem rayOracle_perturb_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hsε : |s| ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ∀ j, L j (oracle (p + s • u)) < 1 := by
  have hsa : |s| < a := hsε.trans_lt (facet_local_step_bounds ha hδ hM).2.1
  by_cases hs : 0 ≤ s
  · have hsε' : s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (le_abs_self s).trans hsε
    refine ⟨perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs
      ((le_abs_self s).trans_lt hsa) hminus, ?_⟩
    intro j
    exact (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus (L j) (hpSlack j) ((le_abs_self _).trans (huBound j))
      hs hsε' horacle).2
  · have hs' : 0 ≤ -s := by linarith
    have hsε' : -s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (neg_le_abs s).trans hsε
    have hsa' : -s < a := (neg_le_abs s).trans_lt hsa
    have hminus' : (-a) • (-u) ∈ P := by
      simpa only [smul_neg, neg_smul, neg_neg] using hplus
    have heq : p + (-s) • (-u) = p + s • u := by
      simp only [smul_neg, neg_smul, neg_neg]
    refine ⟨heq ▸ perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp
      ha hs' hsa' hminus', ?_⟩
    intro j
    have huBound' : L j (-u) ≤ M := by
      rw [map_neg]
      exact (neg_le_abs _).trans (huBound j)
    have h := (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus' (L j) (hpSlack j) huBound' hs' hsε' horacle).2
    simpa only [heq] using h

end Grunbaum2003

namespace Grunbaum2003.RayPlanar

theorem convex_secant_zero_progress {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x) :
    0 < h y - h x ∧
      0 ≤ (x * h y - y * h x) / (h y - h x) ∧
      (x * h y - y * h x) / (h y - h x) < x := by
  have hcross := hconv.secant_mono_aux1 (Set.mem_univ 0) (Set.mem_univ y) hx hxy
  simp only [sub_zero, hzero, mul_zero, zero_add] at hcross
  have hprod : 0 < (y - x) * h x := mul_pos (sub_pos.mpr hxy) hhx
  have hden : 0 < h y - h x := by
    by_contra hn
    have hle : h y ≤ h x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle hx.le
    nlinarith only [hcross, hprod, hmul]
  refine ⟨hden, div_nonneg (by linarith only [hcross]) hden.le, ?_⟩
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [hprod]

theorem secant_zero_of_common_affine_piece {h : ℝ → ℝ} {x y a b : ℝ}
    (hden : h y - h x ≠ 0)
    (hx : h x = a * x + b) (hy : h y = a * y + b) :
    a * ((x * h y - y * h x) / (h y - h x)) + b = 0 := by
  have hz : ((x * h y - y * h x) / (h y - h x)) * (h y - h x) =
      x * h y - y * h x := div_mul_cancel₀ _ hden
  have hp : (a * ((x * h y - y * h x) / (h y - h x)) + b) *
      (h y - h x) = 0 := by
    calc
      _ = a * (((x * h y - y * h x) / (h y - h x)) * (h y - h x)) +
          b * (h y - h x) := by ring
      _ = a * (x * h y - y * h x) + b * (h y - h x) := by rw [hz]
      _ = 0 := by rw [hx, hy]; ring
  exact (mul_eq_zero.mp hp).resolve_right hden

theorem convex_affine_piece_active_between {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) {a b x z y : ℝ}
    (hmajor : ∀ t, a * t + b ≤ h t)
    (hx : h x = a * x + b) (hy : h y = a * y + b)
    (hxz : x ≤ z) (hzy : z ≤ y) : h z = a * z + b := by
  rcases eq_or_lt_of_le hxz with rfl | hxz
  · exact hx
  rcases eq_or_lt_of_le hzy with rfl | hzy
  · exact hy
  apply le_antisymm ?_ (hmajor z)
  have hk := hconv.secant_mono_aux1 (Set.mem_univ x) (Set.mem_univ y) hxz hzy
  rw [hx, hy] at hk
  by_contra hn
  have hp : 0 < (y - x) * (h z - (a * z + b)) :=
    mul_pos (sub_pos.mpr (hxz.trans hzy)) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem third_secant_response_leaves_common_piece {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y a b : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x)
    (hax : h x = a * x + b) (hay : h y = a * y + b)
    (hnext : 0 < h ((x * h y - y * h x) / (h y - h x))) :
    h ((x * h y - y * h x) / (h y - h x)) ≠
      a * ((x * h y - y * h x) / (h y - h x)) + b := by
  have hden := (convex_secant_zero_progress hconv hzero hx hxy hhx).1
  have hz := secant_zero_of_common_affine_piece hden.ne' hax hay
  rw [hz]
  exact ne_of_gt hnext

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def finiteAffineEnvelope {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => a j * x + b j)

lemma finiteAffineEnvelope_major {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (j : Fin m) (x : ℝ) : a j * x + b j ≤ finiteAffineEnvelope hm a b x :=
  Finset.le_sup' (fun k => a k * x + b k) (Finset.mem_univ j)

lemma finiteAffineEnvelope_attained {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (x : ℝ) : ∃ j, finiteAffineEnvelope hm a b x = a j * x + b j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin m))) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun j => a j * x + b j)
  exact ⟨j, hj⟩

lemma finiteAffineEnvelope_convex {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (finiteAffineEnvelope hm a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hab
  simp only [smul_eq_mul]
  apply Finset.sup'_le
  intro j _
  have hx := finiteAffineEnvelope_major hm a b j x
  have hy := finiteAffineEnvelope_major hm a b j y
  calc
    a j * (α * x + β * y) + b j =
        α * (a j * x + b j) + β * (a j * y + b j) := by
      linear_combination -b j * hab
    _ ≤ α * finiteAffineEnvelope hm a b x + β * finiteAffineEnvelope hm a b y :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)

theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)

theorem rayOracle_halfspace_envelope_eq {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + x • u) = t • (p + x • u) ∧
      finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 1 / t - 1 := by
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + x • u) hr
  obtain ⟨hineq, j, hj⟩ := frontier_finite_halfspaces_active L hP hq
  refine ⟨t, ht, heq, le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro k _
    have hk := hineq k
    rw [heq, map_smul, map_add, map_smul] at hk
    change t * (L k p + x * L k u) ≤ 1 at hk
    have hdiv : L k p + x * L k u ≤ 1 / t := (le_div_iff₀ ht).mpr (by nlinarith only [hk])
    linarith only [hdiv]
  · have hj' := hj
    rw [heq, map_smul, map_add, map_smul] at hj'
    change t * (L j p + x * L j u) = 1 at hj'
    have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj'])
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hdiv, hmajor]

theorem halfspace_envelope_zero_at_boundary {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (hp : p ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) 0 = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    dsimp only
    simp only [mul_zero, zero_add]
    linarith only [hle k]
  · have h := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j 0
    simpa only [mul_zero, zero_add, hj, sub_self] using h

theorem convex_gap_nonneg_positive_of_negative_zero {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {z x : ℝ} (hz : z < 0) (hzval : h z = 0) (hx : 0 ≤ x) : 0 ≤ h x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa only [hzero] using (le_refl (0 : ℝ))
  have hk := hconv.secant_mono_aux1 (Set.mem_univ z) (Set.mem_univ x) hz hx
  rw [hzero, hzval] at hk
  simp only [mul_zero, add_zero, zero_add, zero_sub] at hk
  by_contra hn
  have hp : 0 < (-z) * (-h x) := mul_pos (neg_pos.mpr hz) (neg_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem rayOracle_active_halfspace_envelope {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0)
    (j : Fin m) (hj : L j (oracle (p + x • u)) = 1) :
    finiteAffineEnvelope hm (fun k => L k u) (fun k => L k p - 1) x =
      L j u * x + (L j p - 1) := by
  obtain ⟨t, ht, heq, henv⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p u x hr
  rw [heq, map_smul, map_add, map_smul] at hj
  change t * (L j p + x * L j u) = 1 at hj
  have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj])
  linarith only [henv, hdiv]

theorem rayOracle_common_halfspace_opposite_sides_incident {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hrx : p + x • u ≠ 0) (hry : p + y • u ≠ 0)
    (j : Fin m)
    (hjx : L j (oracle (p + x • u)) = 1)
    (hjy : L j (oracle (p + y • u)) = 1) : L j p = 1 := by
  have hax := rayOracle_active_halfspace_envelope hm L hP horacle p u x hrx j hjx
  have hay := rayOracle_active_halfspace_envelope hm L hP horacle p u y hry j hjy
  have hconv := finiteAffineEnvelope_convex hm (fun k => L k u) (fun k => L k p - 1)
  have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j
  have hact := convex_affine_piece_active_between hconv hmajor hax hay hx.le hy.le
  rw [halfspace_envelope_zero_at_boundary hm L hP p u hp] at hact
  simp only [mul_zero, zero_add] at hact
  linarith only [hact]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RaySection

theorem frontier_of_normalized_support {n : ℕ} {Q : Set (Fin n → ℝ)}
    (F : (Fin n → ℝ) →L[ℝ] ℝ) {q : Fin n → ℝ}
    (hq : q ∈ Q) (hFq : F q = 1) (hbound : ∀ x ∈ Q, F x ≤ 1) :
    q ∈ frontier Q := by
  refine ⟨subset_closure hq, ?_⟩
  intro hqint
  have hsurj : Function.Surjective F := by
    intro s
    refine ⟨s • q, ?_⟩
    rw [map_smul, hFq]
    exact mul_one s
  have hopen : IsOpen (F '' interior Q) := F.isOpenMap hsurj _ isOpen_interior
  have hsub : F '' interior Q ⊆ Set.Iic (1 : ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbound x (interior_subset hx)
  have hmem : (1 : ℝ) ∈ interior (Set.Iic (1 : ℝ)) :=
    interior_maximal hsub hopen ⟨q, hqint, hFq⟩
  simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hmem

theorem induced_rayOracle_of_leftInverse {d n m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))
    (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ))
    (hgf : Function.LeftInverse g f) :
    IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
      (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r)) := by
  have hf : Function.Injective f := hgf.injective
  have hrnonzero : ∀ r : Fin n → ℝ, r ≠ 0 → f r ≠ 0 := by
    intro r hr hz
    apply hr
    exact hf (by simpa only [map_zero] using hz)
  have hreply : ∀ r : Fin n → ℝ, r ≠ 0 →
      ∃ t : ℝ, 0 < t ∧ oracle (f r) = t • f r ∧ g (oracle (f r)) = t • r := by
    intro r hr
    obtain ⟨_, t, ht, heq⟩ := horacle (f r) (hrnonzero r hr)
    refine ⟨t, ht, heq, ?_⟩
    rw [heq, map_smul, hgf r]
  constructor
  · intro r hr
    obtain ⟨t, ht, heq, hcoord⟩ := hreply r hr
    obtain ⟨hle, j, hj⟩ := RayPlanar.frontier_finite_halfspaces_active L hP
      (horacle (f r) (hrnonzero r hr)).1
    have hrecover : f (g (oracle (f r))) = oracle (f r) := by
      rw [hcoord, map_smul, ← heq]
    refine ⟨?_, t, ht, hcoord⟩
    apply frontier_of_normalized_support ((L j).comp f)
    · change f (g (oracle (f r))) ∈ P
      rw [hrecover, hP]
      exact hle
    · change L j (f (g (oracle (f r)))) = 1
      rw [hrecover]
      exact hj
    · intro x hx
      change L j (f x) ≤ 1
      have hmem : f x ∈ P := hx
      rw [hP] at hmem
      exact hmem j
  · intro r hr
    obtain ⟨t, _, heq, hcoord⟩ := hreply r hr
    rw [hcoord, map_smul, ← heq]

end Grunbaum2003.RaySection

namespace Grunbaum2003.RayFrame

theorem active_contains_positive_frame {d n : ℕ}
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin n → Fin d → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (p : Fin d → ℝ) (hp : p = ∑ i, w i • v i)
    (hbound : ∀ i, l (v i) ≤ 1) (hactive : l p = 1) :
    ∀ i, l (v i) = 1 := by
  have hsumL : ∑ i, w i * l (v i) = 1 := by
    simpa only [hp, map_sum, map_smul, smul_eq_mul] using hactive
  have hsumgap : ∑ i, w i * (1 - l (v i)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum, hsumL, sub_self]
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ w i * (1 - l (v i)) :=
    fun i _ => mul_nonneg (hw i).le (sub_nonneg.mpr (hbound i))
  intro i
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumgap i (Finset.mem_univ i)
  have hgap : 1 - l (v i) = 0 := (mul_eq_zero.mp hz).resolve_left (hw i).ne'
  linarith only [hgap]

theorem transverse_reply_outside_span {d : ℕ} (W : Submodule ℝ (Fin d → ℝ))
    {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {p u : Fin d → ℝ} (hp : p ∈ W) (hu : u ∉ W)
    (a b : ℝ) (hb : b ≠ 0) :
    oracle (a • p + b • u) ∈ frontier P ∧ oracle (a • p + b • u) ∉ W := by
  have hdir : a • p + b • u ∉ W := by
    intro hmem
    have hsub := W.sub_mem hmem (W.smul_mem a hp)
    have hbu : b • u ∈ W := by simpa only [add_sub_cancel_left] using hsub
    exact hu ((W.smul_mem_iff hb).mp hbu)
  have hne : a • p + b • u ≠ 0 := by
    intro hz
    apply hdir
    rw [hz]
    exact W.zero_mem
  obtain ⟨hfront, t, ht, heq⟩ := horacle (a • p + b • u) hne
  refine ⟨hfront, ?_⟩
  intro hmem
  rw [heq] at hmem
  exact hdir ((W.smul_mem_iff ht.ne').mp hmem)

theorem common_support_midpoint {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ P)
    (j : Fin m) (hjp : L j p = 1) (hjq : L j q = 1) :
    (1 / 2 : ℝ) • (p + q) ∈ frontier P ∧
      ∀ k : Fin m, L k p < 1 → L k q < 1 → L k ((1 / 2 : ℝ) • (p + q)) < 1 := by
  have hpRows : ∀ k, L k p ≤ 1 := by rwa [hP] at hp
  have hqRows : ∀ k, L k q ≤ 1 := by rwa [hP] at hq
  have hmid : (1 / 2 : ℝ) • (p + q) ∈ P := by
    rw [hP]
    intro k
    rw [map_smul, map_add]
    change (1 / 2 : ℝ) * (L k p + L k q) ≤ 1
    linarith only [hpRows k, hqRows k]
  have hactive : L j ((1 / 2 : ℝ) • (p + q)) = 1 := by
    rw [map_smul, map_add, hjp, hjq]
    norm_num
  refine ⟨RaySection.frontier_of_normalized_support (L j) hmid hactive
    (fun x hx => (by rw [hP] at hx; exact hx j)), ?_⟩
  intro k hkp hkq
  rw [map_smul, map_add]
  change (1 / 2 : ℝ) * (L k p + L k q) < 1
  linarith only [hkp, hkq]

theorem extend_positive_boundary_frame {d n m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (v : Fin n → Fin d → ℝ) (hv : LinearIndependent ℝ v)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hV : ∀ i, v i ∈ P)
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ P)
    (hpcombo : p = ∑ i, w i • v i)
    (hqspan : q ∉ Submodule.span ℝ (Set.range v))
    (j : Fin m) (hjp : L j p = 1) (hjq : L j q = 1) :
    let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
    let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
    let p' := (1 / 2 : ℝ) • (p + q)
    LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
      p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
      (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1) := by
  dsimp only
  let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
  let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
  let p' := (1 / 2 : ℝ) • (p + q)
  have hWpos : ∀ i, 0 < W i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · change 0 < (1 / 2 : ℝ)
      norm_num
    · change 0 < w k / 2
      exact div_pos (hw k) (by norm_num)
  have hWsum : ∑ i, W i = 1 := by
    change ∑ i, (Fin.cons (1 / 2 : ℝ) (fun k => w k / 2)) i = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, div_eq_mul_inv]
    rw [← Finset.sum_mul, hsum]
    norm_num
  have hhalf : ∑ i, (w i / 2) • v i = (1 / 2 : ℝ) • p := by
    rw [hpcombo, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  have hcombo : p' = ∑ i, W i • V i := by
    change (1 / 2 : ℝ) • (p + q) =
      ∑ i : Fin (n + 1), (Fin.cons (1 / 2 : ℝ) (fun k => w k / 2) : Fin (n + 1) → ℝ) i •
        (Fin.cons q v : Fin (n + 1) → Fin d → ℝ) i
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hhalf, smul_add]
    exact add_comm _ _
  have hVP : ∀ i, V i ∈ P := by
    intro i
    exact Fin.cases hq (fun k => hV k) i
  have hfront : p' ∈ frontier P := (common_support_midpoint L hP p q hp hq j hjp hjq).1
  refine ⟨hv.finCons hqspan, hWpos, hWsum, hcombo, hVP, hfront, ?_⟩
  intro k hk
  apply active_contains_positive_frame (L k) V W hWpos hWsum p' hcombo
  · intro i
    have hmem := hVP i
    rw [hP] at hmem
    exact hmem k
  · exact hk

end Grunbaum2003.RayFrame

namespace Grunbaum2003.RayFrame

def coordinateAxis {d : ℕ} (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem sum_coordinate_axes {d : ℕ} (p : Fin d → ℝ) :
    ∑ i, p i • coordinateAxis i = p := by
  calc
    ∑ i, p i • coordinateAxis i = ∑ i, Pi.single i (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [coordinateAxis, smul_eq_mul, mul_one] using
        (Pi.single_smul' i (p i) (1 : ℝ)).symm
    _ = p := LinearMap.sum_single_apply (fun _ : Fin d => ℝ) p

theorem exists_coordinate_axis_outside_frame {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (hv : LinearIndependent ℝ v) (hn : n < d) :
    ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v) := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  have hdim : Module.finrank ℝ W = n := by
    simpa only [W, Fintype.card_fin] using finrank_span_eq_card hv
  by_contra hnone
  have haxes : ∀ i : Fin d, coordinateAxis i ∈ W := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hall : ∀ p : Fin d → ℝ, p ∈ W := by
    intro p
    rw [← sum_coordinate_axes p]
    exact W.sum_mem (fun i _ => W.smul_mem (p i) (haxes i))
  have htop : W = ⊤ := by
    apply le_antisymm le_top
    intro p _
    exact hall p
  rw [htop, finrank_top, Module.finrank_fin_fun] at hdim
  omega

theorem exists_off_axis_pivot {d : ℕ} (W : Submodule ℝ (Fin d → ℝ))
    (p : Fin d → ℝ) (hp : p ∈ W) (hpne : p ≠ 0) (i : Fin d)
    (hi : coordinateAxis i ∉ W) : ∃ j : Fin d, j ≠ i ∧ p j ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ j : Fin d, j ≠ i → p j = 0 := by
    intro j hji
    by_contra hpj
    exact hnone ⟨j, hji, hpj⟩
  have heq : p = p i • coordinateAxis i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [coordinateAxis]
    · simp [coordinateAxis, hzero j hji, hji, Ne.symm hji]
  have hpi : p i ≠ 0 := by
    intro hz
    apply hpne
    rw [heq, hz, zero_smul]
  rw [heq] at hp
  exact hi ((W.smul_mem_iff hpi).mp hp)

end Grunbaum2003.RayFrame

namespace Grunbaum2003.RayFrame

def frameCramerCoefficients {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  v.det⁻¹ • Matrix.cramer v (fun _ => 1)

theorem frameCramerCoefficients_apply {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det := by
  simp only [frameCramerCoefficients, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    div_eq_mul_inv]
  ring

def frameNormalLinear {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ k, frameCramerCoefficients v k * x k
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ k, frameCramerCoefficients v k * (a * x k)) =
      a * ∑ k, frameCramerCoefficients v k * x k
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

def frameNormal {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  (frameNormalLinear v).toContinuousLinearMap

theorem frame_det_ne_zero {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) : v.det ≠ 0 :=
  Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hv)

theorem frameCramer_equations {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) : v *ᵥ frameCramerCoefficients v = (fun _ => 1) := by
  rw [frameCramerCoefficients, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    smul_smul, inv_mul_cancel₀ (frame_det_ne_zero v hv), one_smul]

theorem frameNormal_on_frame {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) (i : Fin d) : frameNormal v (v i) = 1 := by
  have hi := congrFun (frameCramer_equations v hv) i
  change (∑ k, v i k * frameCramerCoefficients v k) = 1 at hi
  change (∑ k, frameCramerCoefficients v k * v i k) = 1
  simpa only [mul_comm] using hi

theorem frameNormal_eq_of_values {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) (l : (Fin d → ℝ) →L[ℝ] ℝ)
    (hl : ∀ i, l (v i) = 1) : frameNormal v = l := by
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Fintype.card_fin, Module.finrank_fin_fun] using finrank_span_eq_card hv
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.ext_on_range hspan
  intro i
  exact (frameNormal_on_frame v hv i).trans (hl i).symm

theorem frameNormal_eq_original_active_row {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (v : Matrix (Fin d) (Fin d) ℝ) (hv : LinearIndependent ℝ v)
    (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hV : ∀ i, v i ∈ P)
    (p : Fin d → ℝ) (hp : p ∈ frontier P) (hpcombo : p = ∑ i, w i • v i) :
    ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1 := by
  obtain ⟨_, j, hj⟩ := RayPlanar.frontier_finite_halfspaces_active L hP hp
  have hvalues : ∀ i, L j (v i) = 1 := by
    apply active_contains_positive_frame (L j) v w hw hsum p hpcombo
    · intro i
      have hi := hV i
      rw [hP] at hi
      exact hi j
    · exact hj
  exact ⟨j, frameNormal_eq_of_values v hv (L j) hvalues, hj⟩

end Grunbaum2003.RayFrame

namespace Grunbaum2003

theorem rayFrame_boundary_extension_axes_and_cramer_normal :
    ∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) := by
  refine ⟨@RayFrame.coordinateAxis, @RayFrame.frameCramerCoefficients, @RayFrame.frameNormal,
    fun _ _ => rfl,
    fun d v k => RayFrame.frameCramerCoefficients_apply v k,
    fun _ _ _ => rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro d n m L P hP oracle horacle f g hgf
    exact RaySection.induced_rayOracle_of_leftInverse L hP horacle f g hgf
  · intro d n v hv hn
    exact RayFrame.exists_coordinate_axis_outside_frame v hv hn
  · intro d W p hp hpne i hi
    exact RayFrame.exists_off_axis_pivot W p hp hpne i hi
  · intro d n m L P hP v hv w hw hsum hV p q hp hq hpcombo hqspan j hjp hjq
    exact RayFrame.extend_positive_boundary_frame L hP v hv w hw hsum hV p q hp hq hpcombo hqspan j hjp hjq
  · intro d m L P hP v hv w hw hsum hV p hp hpcombo
    exact ⟨RayFrame.frame_det_ne_zero v hv,
      RayFrame.frameNormal_eq_original_active_row L hP v hv w hw hsum hV p hp hpcombo⟩

end Grunbaum2003
end

theorem inline_solution :
    ∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          Grunbaum2003.IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) :=
  Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal

end RayCounterfamilyInline08

namespace Grunbaum2003

theorem rayFrame_boundary_extension_axes_and_cramer_normal :
∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) :=
  @RayCounterfamilyInline08.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_repaired_ray_query_budget_bound.lean
-- SHA256: e804a60deb63368ce3a89c43e5958c9bdcc657b0f52173684a552fa1fc7c9acf
namespace RayCounterfamilyInline09

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003


/-- Summing the corrected two-charge detector costs over a decreasing unknown
facet pool retains the original leading quadratic coefficient. -/
theorem sum_twice_remaining_add_three (m : ℕ) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : ∀ k ∈ Finset.range m,
        2 * (m + 1 - k) + 3 = (2 * (m - k) + 3) + 2 := by
      intro k hk
      have hk' : k ≤ m := (Finset.mem_range.mp hk).le
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.add_sub_cancel_left]
    ring

/-- Exact original query budget, including the d+1 paid inner-simplex queries.
The geometric/controller premise to establish separately is at most2u+3 detector
calls when u facets remain unknown. -/
theorem corrected_discovery_budget_fits {d m f₀ : ℕ} (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m := by
  have hsum : (∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3))) =
      m + (d - 1) * (m * m + 4 * m) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_twice_remaining_add_three]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, mul_one]
  rw [hsum]
  have hcoefficient : 5 * d - 4 = 5 * (d - 1) + 1 := by omega
  have hspare : d + 1 ≤ (d - 1) * m := by
    have hdm : 1 ≤ d - 1 := by omega
    have hmul := Nat.mul_le_mul_right m hdm
    have hmm : m ≤ (d - 1) * m := by simpa only [one_mul] using hmul
    exact hm.trans hmm
  rw [hcoefficient]
  nlinarith only [hspare]


theorem repaired_ray_query_budget_bound (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m :=
  ⟨sum_twice_remaining_add_three m, corrected_discovery_budget_fits hd hm⟩

end Grunbaum2003

theorem inline_solution (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m :=
  Grunbaum2003.repaired_ray_query_budget_bound d m f₀ hd hm

end RayCounterfamilyInline09

namespace Grunbaum2003

theorem repaired_ray_query_budget_bound :
∀ (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m),
(∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m :=
  @RayCounterfamilyInline09.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_polytope_face_eq_convexHull_exposed_vertices.lean
-- SHA256: 19dd017c8e1892b590342e4826861c1c8caa7dc58ba9c1594d95bbe44a2f52f2
namespace RayCounterfamilyInline10

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Every extreme point of a finite convex hull is an exposed singleton. -/
lemma extremePoints_eq_exposedSingletons {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

/-- Grünbaum (2003), Theorem 3.2.2 (p. 36): for every `d`-polytope `P`, the set of exposed
vertices `{x | IsExposed ℝ P {x}}` is finite, and every exposed face `F` of `P` equals the
convex hull of the exposed vertices of `P` contained in `F`. -/
theorem polytope_face_eq_convexHull_exposed_vertices (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
  intro F
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
  have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
    ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

end Grunbaum2003

theorem inline_solution (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : Grunbaum2003.PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) :=
  Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP

end RayCounterfamilyInline10

namespace Grunbaum2003

theorem polytope_face_eq_convexHull_exposed_vertices :
∀ (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P),
{x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) :=
  @RayCounterfamilyInline10.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound.lean
-- SHA256: 4e85474b13b39e47113a2d186e87b12c1af252e9b87f8e75ea55220c9751d57c
namespace RayCounterfamilyInline11

open _root_.Grunbaum2003


set_option autoImplicit false

open scoped Classical


namespace Grunbaum2003

/-- A nonempty exposed face of `P` has affine direction finrank `0` if and only if
it is a singleton exposed vertex `{x}`. -/
theorem nonempty_exposed_finrank_zero_iff_singleton {d : ℕ}
    (P F : Set (Fin d → ℝ)) :
    (F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 0) ↔
    ∃ x : Fin d → ℝ, IsExposed ℝ P {x} ∧ F = {x} := by
  constructor
  · rintro ⟨hne, hF, hRank⟩
    have hDir : (affineSpan ℝ F).direction = ⊥ := Submodule.finrank_eq_zero.mp hRank
    have hSpan : vectorSpan ℝ F = ⊥ := by rwa [direction_affineSpan] at hDir
    have hSub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hSpan
    obtain ⟨x, hx⟩ := hne
    have hEq : F = {x} := hSub.eq_singleton_of_mem hx
    refine ⟨x, hEq ▸ hF, hEq⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Set.singleton_nonempty x, hx, ?_⟩
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]

/-- The zero-dimensional face count `faceCount P 0` equals the `Set.ncard` of singleton
exposed vertices of `P`. -/
theorem faceCount_zero_eq_exposed_vertices_ncard {d : ℕ}
    (P : Set (Fin d → ℝ)) :
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard := by
  have hImg :
      (fun x : Fin d → ℝ => ({x} : Set (Fin d → ℝ))) ''
        {x : Fin d → ℝ | IsExposed ℝ P {x}} =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 0} := by
    ext F
    change F ∈ (fun x : Fin d → ℝ => ({x} : Set (Fin d → ℝ))) ''
        {x : Fin d → ℝ | IsExposed ℝ P {x}} ↔
      (F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 0)
    rw [nonempty_exposed_finrank_zero_iff_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  unfold faceCount
  rw [← hImg]
  exact Set.ncard_image_of_injective _ Set.singleton_injective

/-- Every full-dimensional `d`-polytope `P ⊆ ℝ^d` satisfying the exposed-vertex hull
representation has at least `d + 1` zero-dimensional exposed faces (`d + 1 ≤ faceCount P 0`). -/
theorem d_add_one_le_faceCount_zero {d : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P)
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :
    d + 1 ≤ faceCount P 0 := by
  let V : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hPEq : P = convexHull ℝ (P ∩ V) := hHull.2 ⟨P, IsExposed.refl P⟩
  have hPne : P.Nonempty := by
    obtain ⟨W, _, hWne, hPW⟩ := hP.1
    rw [hPW]
    exact hWne.convexHull
  have hPVne : (P ∩ V).Nonempty := by
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rwa [← hPEq]
  obtain ⟨v₀, _, hv₀⟩ := hPVne
  have hAffV : affineSpan ℝ V = ⊤ := by
    apply top_unique
    calc (⊤ : AffineSubspace ℝ (Fin d → ℝ))
      _ = affineSpan ℝ P := hP.2.symm
      _ = affineSpan ℝ (convexHull ℝ (P ∩ V)) := by rw [← hPEq]
      _ = affineSpan ℝ (P ∩ V) := affineSpan_convexHull (P ∩ V)
      _ ≤ affineSpan ℝ V := affineSpan_mono ℝ Set.inter_subset_right
  have hRankDir : Module.finrank ℝ (affineSpan ℝ V).direction = d := by
    rw [hAffV, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let S : Finset (Fin d → ℝ) := hHull.1.toFinset
  let T : Finset (Fin d → ℝ) := (S.erase v₀).image (fun x => x -ᵥ v₀)
  have hSpanLe : (affineSpan ℝ V).direction ≤ Submodule.span ℝ (T : Set (Fin d → ℝ)) := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hv₀, Submodule.span_le]
    rintro u ⟨x, hxV, rfl⟩
    dsimp only
    by_cases hxv : x = v₀
    · subst x
      rw [vsub_self]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      change x -ᵥ v₀ ∈ (T : Set (Fin d → ℝ))
      rw [Finset.coe_image]
      refine ⟨x, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨hxv, hHull.1.mem_toFinset.mpr hxV⟩
  have hRankLe : d ≤ (S.erase v₀).card := by
    calc d = Module.finrank ℝ (affineSpan ℝ V).direction := hRankDir.symm
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (T : Set (Fin d → ℝ))) :=
          Submodule.finrank_mono hSpanLe
      _ ≤ T.card := finrank_span_finset_le_card T
      _ ≤ (S.erase v₀).card := Finset.card_image_le
  have hv₀S : v₀ ∈ S := hHull.1.mem_toFinset.mpr hv₀
  have hCardS : (S.erase v₀).card + 1 = S.card := Finset.card_erase_add_one hv₀S
  have hNcardV : V.ncard = S.card := Set.ncard_eq_toFinset_card V hHull.1
  rw [faceCount_zero_eq_exposed_vertices_ncard P]
  change d + 1 ≤ V.ncard
  omega

end Grunbaum2003

namespace Grunbaum2003

theorem polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound_proved :
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (IsDPolytope P → d + 1 ≤ faceCount P 0) := by
  intro d P
  refine ⟨faceCount_zero_eq_exposed_vertices_ncard P, fun hP => ?_⟩
  exact d_add_one_le_faceCount_zero P hP
    (polytope_face_eq_convexHull_exposed_vertices d P hP)

end Grunbaum2003

theorem inline_solution :
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    Grunbaum2003.faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (Grunbaum2003.IsDPolytope P → d + 1 ≤ Grunbaum2003.faceCount P 0) :=
  Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound_proved

end RayCounterfamilyInline11

namespace Grunbaum2003

theorem polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound :
∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (IsDPolytope P → d + 1 ≤ faceCount P 0) :=
  @RayCounterfamilyInline11.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_ray_oracle_outer_polytope_invariants_and_phased_trace_bound.lean
-- SHA256: 1d225df039ad287595c222a46b549f6cd3192840446b71f6d1998e94be1a9626
namespace RayCounterfamilyInline12

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Grunbaum2003

/-- Outer halfspace approximation defined by a subset `S` of facet indices. -/
def outerHalfspacePolytope {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m)) : Set (Fin d → ℝ) :=
  {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}

lemma subset_outerHalfspacePolytope {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    (S : Finset (Fin m)) :
    P ⊆ outerHalfspacePolytope L S := by
  intro x hx i hi
  rw [hP] at hx
  exact hx i

lemma outerHalfspacePolytope_antitone {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {S S' : Finset (Fin m)} (hSS' : S ⊆ S') :
    outerHalfspacePolytope L S' ⊆ outerHalfspacePolytope L S := by
  intro x hx i hi
  exact hx i (hSS' hi)

lemma certified_extremePoints_persist {d : ℕ} {P Q Q' : Set (Fin d → ℝ)}
    (hPQ' : P ⊆ Q') (hQ'Q : Q' ⊆ Q) :
    P ∩ Q.extremePoints ℝ ⊆ P ∩ Q'.extremePoints ℝ ∧
    P ∩ Q'.extremePoints ℝ ⊆ P.extremePoints ℝ := by
  refine ⟨?_, inter_extremePoints_subset_extremePoints_of_subset hPQ'⟩
  intro x ⟨hxP, hxQ⟩
  exact ⟨hxP, inter_extremePoints_subset_extremePoints_of_subset hQ'Q ⟨hPQ' hxP, hxQ⟩⟩

lemma fresh_facet_of_failed_extreme_verification {d m : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hConv : Convex ℝ P) (hClosed : IsClosed P)
    (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) {v : Fin d → ℝ}
    (hv : v ∈ (outerHalfspacePolytope L S).extremePoints ℝ)
    (hne : oracle v ≠ v) {i_new : Fin m} (hi_new : L i_new (oracle v) = 1) :
    i_new ∉ S ∧ (insert i_new S).card = S.card + 1 := by
  have hPQ : P ⊆ outerHalfspacePolytope L S := subset_outerHalfspacePolytope L hP S
  let k := S.card
  let e : Fin k ≃ S := (Finset.equivFin S).symm
  let L_S : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (e j).val).toLinearMap
  have hv_le : ∀ j : Fin k, L_S j v ≤ 1 := by
    intro j
    exact hv.1 (e j).val (e j).property
  have hexcl := (rayOracle_local_sector_and_known_facet_exclusion.{0}.2.1
    hd hConv hClosed h0 hPQ hOracle hv hne L_S hv_le).2
  have hnot_mem : i_new ∉ S := by
    intro hmem
    let j : Fin k := e.symm ⟨i_new, hmem⟩
    have hj : (e j).val = i_new := by
      simp [j]
    have hlt : L (e j).val (oracle v) < 1 := hexcl j
    rw [hj, hi_new] at hlt
    exact lt_irrefl 1 hlt
  exact ⟨hnot_mem, Finset.card_insert_of_notMem hnot_mem⟩

lemma outer_polytope_and_certified_vertices_eq_of_all_verified {d : ℕ}
    {P Q V_Q C : Set (Fin d → ℝ)}
    (hConv : Convex ℝ P) (hPQ : P ⊆ Q) (hQ : Q = convexHull ℝ V_Q)
    (hVQ_C : V_Q ⊆ C) (hC_extP : C ⊆ P.extremePoints ℝ)
    (hExtQ_C : Q.extremePoints ℝ ⊆ C) :
    Q = P ∧ C = P.extremePoints ℝ := by
  have hC_P : C ⊆ P := fun x hx => (hC_extP hx).1
  have hQP : Q ⊆ P := by
    rw [hQ]
    exact convexHull_min (hVQ_C.trans hC_P) hConv
  have hQP_eq : Q = P := Set.Subset.antisymm hQP hPQ
  refine ⟨hQP_eq, Set.Subset.antisymm hC_extP ?_⟩
  rw [← hQP_eq]
  exact hExtQ_C

lemma extremePoints_eq_exposed_singletons_of_isDPolytope {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
    faceCount P 0 = (P.extremePoints ℝ).ncard := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
  let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hP_eq_V : P = convexHull ℝ V_set := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    have hsub : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
    rw [Set.inter_eq_self_of_subset_right hsub] at h1
    exact h1
  have heq : P.extremePoints ℝ = V_set := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hP_eq_V] at hx
      exact extremePoints_convexHull_subset hx
    · intro v hv
      obtain ⟨l, hvl⟩ := hv (Set.singleton_nonempty v)
      have hv_mem : v ∈ {z ∈ P | ∀ w ∈ P, l w ≤ l z} := by
        rw [← hvl]; exact Set.mem_singleton v
      rw [mem_extremePoints_iff_left]
      refine ⟨hv_mem.1, fun x hx y hy hseg => ?_⟩
      rcases hseg with ⟨a, b, ha, hb, hab, hcomb⟩
      have hlx : l x ≤ l v := hv_mem.2 x hx
      have hly : l y ≤ l v := hv_mem.2 y hy
      have hcomb_l : a * l x + b * l y = l v := by
        calc a * l x + b * l y
            = l (a • x + b • y) := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          _ = l v := by rw [hcomb]
      have hsum_zero : a * (l v - l x) + b * (l v - l y) = 0 := by
        calc a * (l v - l x) + b * (l v - l y)
            = (a + b) * l v - (a * l x + b * l y) := by ring
          _ = 1 * l v - l v := by rw [hab, hcomb_l]
          _ = 0 := by ring
      have hlx_eq : l x = l v := by nlinarith
      have hx_in : x ∈ ({v} : Set (Fin d → ℝ)) := by
        rw [hvl]
        exact ⟨hx, fun w hw => by linarith [hv_mem.2 w hw]⟩
      exact Set.mem_singleton_iff.1 hx_in
  refine ⟨heq, ?_⟩
  rw [heq, hVBound.1]

lemma face_subset_hyperplane_iff_exposed_vertices_eq_one {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (F : PolytopeFace P) (l : (Fin d → ℝ) →L[ℝ] ℝ) :
    F.val ⊆ {x : Fin d → ℝ | l x = 1} ↔
      ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → l v = 1 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  constructor
  · intro hsub v _ hvF
    exact hsub hvF
  · intro hv
    rw [hHull.2 F]
    refine convexHull_min ?_ (convex_hyperplane l.toLinearMap.isLinear 1)
    rintro v ⟨hvF, hvExp⟩
    exact hv v hvExp hvF

/-- Cost bound for a single facet-discovery phase with `k` already discovered facets. -/
def facetPhaseCost (d m k : ℕ) : ℕ :=
  1 + (d - 1) * (2 * (m - k) + 3)

/-- Potential function for a phased vertex-certification and facet-discovery execution. -/
def phasePotential (d m V_card : ℕ) (S : Finset (Fin m)) (C_card q : ℕ) : ℕ :=
  q + (V_card - C_card) + ∑ k ∈ Finset.Ico S.card m, facetPhaseCost d m k

lemma phasePotential_certify_step {d m : ℕ} {V : Finset (Fin d → ℝ)}
    (S : Finset (Fin m)) {C : Finset (Fin d → ℝ)} (hCV : C ⊆ V)
    {v : Fin d → ℝ} (hvV : v ∈ V) (hvC : v ∉ C)
    {q q' : ℕ} (hq' : q' ≤ q + 1) :
    insert v C ⊆ V ∧
    phasePotential d m V.card S (insert v C).card q' ≤
      phasePotential d m V.card S C.card q := by
  have hins : insert v C ⊆ V := Finset.insert_subset_iff.2 ⟨hvV, hCV⟩
  have hcard_ins : (insert v C).card = C.card + 1 := Finset.card_insert_of_notMem hvC
  have hcard_le : C.card + 1 ≤ V.card := by
    rw [← hcard_ins]
    exact Finset.card_le_card hins
  refine ⟨hins, ?_⟩
  unfold phasePotential
  rw [hcard_ins]
  omega

lemma phasePotential_discover_step {d m : ℕ} (V_card : ℕ)
    (S : Finset (Fin m)) {i_new : Fin m} (hi : i_new ∉ S)
    (C_card : ℕ) {q q' : ℕ} (hq' : q' ≤ q + facetPhaseCost d m S.card) :
    phasePotential d m V_card (insert i_new S) C_card q' ≤
      phasePotential d m V_card S C_card q := by
  have hcard_ins : (insert i_new S).card = S.card + 1 := Finset.card_insert_of_notMem hi
  have hcard_lt : S.card < m := by
    have hle : (insert i_new S).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_univ (insert i_new S)
    rw [Finset.card_fin, hcard_ins] at hle
    omega
  have hsum_split : ∑ k ∈ Finset.Ico S.card m, facetPhaseCost d m k =
      facetPhaseCost d m S.card +
        ∑ k ∈ Finset.Ico (S.card + 1) m, facetPhaseCost d m k := by
    rw [← Finset.sum_Ico_consecutive _ (Nat.le_succ S.card) hcard_lt, Nat.Ico_succ_singleton,
      Finset.sum_singleton]
  unfold phasePotential
  rw [hcard_ins, hsum_split]
  omega

lemma phasePotential_init_bound (d m V_card : ℕ) (S₀ : Finset (Fin m)) (C₀_card q₀ : ℕ)
    (hq₀ : q₀ ≤ d + 1) :
    phasePotential d m V_card S₀ C₀_card q₀ ≤
      V_card + (d + 1) + ∑ k ∈ Finset.range m, facetPhaseCost d m k := by
  have hsub : Finset.Ico S₀.card m ⊆ Finset.range m := by
    intro k hk
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hk).2
  have hsum_le : ∑ k ∈ Finset.Ico S₀.card m, facetPhaseCost d m k ≤
      ∑ k ∈ Finset.range m, facetPhaseCost d m k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  unfold phasePotential
  omega

/-- Inductive query bound for any sequence of `N` phases, each either certifying a fresh
exposed vertex of `P` at query cost `≤ 1` or discovering a fresh facet of `P` at query cost
`≤ 1 + (d - 1) * (2 * (m - S_t.card) + 3)`. -/
lemma phased_trace_query_bound {d m : ℕ} (V : Finset (Fin d → ℝ))
    (N : ℕ)
    (S_seq : ℕ → Finset (Fin m))
    (C_seq : ℕ → Finset (Fin d → ℝ))
    (q_seq : ℕ → ℕ)
    (hC₀ : C_seq 0 ⊆ V)
    (hq₀ : q_seq 0 ≤ d + 1)
    (hStep : ∀ t < N,
      (S_seq (t + 1) = S_seq t ∧
        ∃ v ∈ V, v ∉ C_seq t ∧ C_seq (t + 1) = insert v (C_seq t) ∧
          q_seq (t + 1) ≤ q_seq t + 1) ∨
      (C_seq (t + 1) = C_seq t ∧
        ∃ i_new : Fin m, i_new ∉ S_seq t ∧ S_seq (t + 1) = insert i_new (S_seq t) ∧
          q_seq (t + 1) ≤ q_seq t + facetPhaseCost d m (S_seq t).card)) :
    C_seq N ⊆ V ∧
    q_seq N ≤ V.card + (d + 1) + ∑ k ∈ Finset.range m, facetPhaseCost d m k := by
  have h_inv : ∀ t ≤ N,
      C_seq t ⊆ V ∧
      phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) ≤
        phasePotential d m V.card (S_seq 0) (C_seq 0).card (q_seq 0) := by
    intro t ht
    induction t with
    | zero => exact ⟨hC₀, le_rfl⟩
    | succ t ih =>
      obtain ⟨hCt, hPot_t⟩ := ih (Nat.le_of_succ_le ht)
      rcases hStep t (Nat.lt_of_succ_le ht) with
        ⟨hS_eq, v, hvV, hvC, hC_eq, hq_le⟩ | ⟨hC_eq, i_new, hi, hS_eq, hq_le⟩
      · obtain ⟨hC_next, hPot_step⟩ :=
          phasePotential_certify_step (S_seq t) hCt hvV hvC hq_le
        have hPot_step' :
            phasePotential d m V.card (S_seq (t + 1)) (C_seq (t + 1)).card (q_seq (t + 1)) ≤
              phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) := by
          rw [hS_eq, hC_eq]
          exact hPot_step
        exact ⟨hC_eq ▸ hC_next, hPot_step'.trans hPot_t⟩
      · have hPot_step :=
          phasePotential_discover_step V.card (S_seq t) hi (C_seq t).card hq_le
        have hPot_step' :
            phasePotential d m V.card (S_seq (t + 1)) (C_seq (t + 1)).card (q_seq (t + 1)) ≤
              phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) := by
          rw [hS_eq, hC_eq]
          exact hPot_step
        exact ⟨hC_eq ▸ hCt, hPot_step'.trans hPot_t⟩
  obtain ⟨hCN, hPotN⟩ := h_inv N le_rfl
  have hInit := phasePotential_init_bound d m V.card (S_seq 0) (C_seq 0).card (q_seq 0) hq₀
  have hq_le_pot : q_seq N ≤ phasePotential d m V.card (S_seq N) (C_seq N).card (q_seq N) := by
    unfold phasePotential
    omega
  exact ⟨hCN, (hq_le_pot.trans hPotN).trans hInit⟩

lemma isDPolytope_convex_and_isClosed {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1}) :
    Convex ℝ P ∧ IsClosed P := by
  rcases hP.1 with ⟨V, _, _, rfl⟩
  refine ⟨convex_convexHull ℝ V, ?_⟩
  rw [hP_L]
  have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
      ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by
    ext x; simp
  rw [h_eq]
  exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)

end Grunbaum2003

open Grunbaum2003

theorem inline_solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          (P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            faceCount P 0 = (P.extremePoints ℝ).ncard) ∧
          (∀ (F : PolytopeFace P) (i : Fin m),
            F.val ⊆ {x : Fin d → ℝ | L i x = 1} ↔
              ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → L i v = 1) ∧
          (∀ S : Finset (Fin m),
            P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} ∧
            P ∩ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ P.extremePoints ℝ ∧
            ∀ {v : Fin d → ℝ},
              v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
              oracle v ≠ v →
              ∀ {i_new : Fin m}, L i_new (oracle v) = 1 →
                i_new ∉ S ∧ (insert i_new S).card = S.card + 1) ∧
          (∀ (S : Finset (Fin m)) (V_Q C : Set (Fin d → ℝ)),
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = convexHull ℝ V_Q →
            V_Q ⊆ C → C ⊆ P.extremePoints ℝ →
            ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ C →
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = P ∧ C = P.extremePoints ℝ)) ∧
    (∀ (program : List RayInstruction) (P : Set (Fin d → ℝ)),
      IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)), IsPolytopeRayOracle P oracle →
        ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
          P = {x | ∀ i, L i x ≤ 1} →
          ∀ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c →
            program[c.pc]? = some .halt →
            C_seq 0 = ∅ →
            q_seq 0 ≤ d + 1 →
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin (faceCount P (d - 1)),
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
            c.queries ≤ q_seq N →
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
            c.tape (c.head + (n : ℤ)) = 0 →
            (∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) →
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d + 1) +
              ∑ k ∈ Finset.range (faceCount P (d - 1)),
                (1 + (d - 1) * (2 * (faceCount P (d - 1) - k) + 3)) ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) := by
  have hd_pos : 0 < d := by omega
  refine ⟨?_, ?_⟩
  · intro m P hP h0 L hP_L oracle hOracle
    obtain ⟨hConv, hClosed⟩ := isDPolytope_convex_and_isClosed hP L hP_L
    refine ⟨extremePoints_eq_exposed_singletons_of_isDPolytope hP,
      fun F i => face_subset_hyperplane_iff_exposed_vertices_eq_one hP F (L i),
      fun S => ?_, fun S V_Q C hQ hVQ_C hC_ext hExt_C => ?_⟩
    · have hPQ := subset_outerHalfspacePolytope L hP_L S
      have hPersist := (certified_extremePoints_persist hPQ (Set.Subset.refl _)).2
      refine ⟨hPQ, hPersist, fun hv hne _ hi_new => ?_⟩
      exact fresh_facet_of_failed_extreme_verification hd_pos hConv hClosed h0 L hP_L
        hOracle S hv hne hi_new
    · exact outer_polytope_and_certified_vertices_eq_of_all_verified
        hConv (subset_outerHalfspacePolytope L hP_L S) hQ hVQ_C hC_ext hExt_C
  · intro program P hP h0 oracle hOracle L hP_L t c n e N S_seq C_seq q_seq
      hRun hHalt hC₀ hq₀ hStep hqN hHead1 hHead0 hTable
    obtain ⟨hConv, hClosed⟩ := isDPolytope_convex_and_isClosed hP L hP_L
    have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
    have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
    have hExtEq := (extremePoints_eq_exposed_singletons_of_isDPolytope hP).1
    let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
    have hV_fin : V_set.Finite := hHull.1
    let V : Finset (Fin d → ℝ) := hV_fin.toFinset
    have hCardV : faceCount P 0 = V.card := by
      rw [hVBound.1, Set.ncard_eq_toFinset_card V_set hV_fin]
    have hC₀_sub : C_seq 0 ⊆ V := by
      rw [hC₀]; exact Finset.empty_subset V
    have hStep' : ∀ s < N,
        (S_seq (s + 1) = S_seq s ∧
          ∃ v ∈ V, v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
            q_seq (s + 1) ≤ q_seq s + 1) ∨
        (C_seq (s + 1) = C_seq s ∧
          ∃ i_new : Fin (faceCount P (d - 1)),
            i_new ∉ S_seq s ∧ S_seq (s + 1) = insert i_new (S_seq s) ∧
            q_seq (s + 1) ≤ q_seq s +
              facetPhaseCost d (faceCount P (d - 1)) (S_seq s).card) := by
      intro s hs
      rcases hStep s hs with
        ⟨hS_eq, v, hv_extQ, hvP, hvC, hC_eq, hq_le⟩ |
        ⟨hC_eq, v, hv_extQ, hne, i_new, hi_new, hS_eq, hq_le⟩
      · left
        have hPQ := subset_outerHalfspacePolytope L hP_L (S_seq s)
        have hv_extP : v ∈ P.extremePoints ℝ :=
          (certified_extremePoints_persist hPQ (Set.Subset.refl _)).2 ⟨hvP, hv_extQ⟩
        rw [hExtEq] at hv_extP
        have hvV : v ∈ V := hV_fin.mem_toFinset.2 hv_extP
        exact ⟨hS_eq, v, hvV, hvC, hC_eq, hq_le⟩
      · right
        have hFresh := fresh_facet_of_failed_extreme_verification hd_pos hConv hClosed h0
          L hP_L hOracle (S_seq s) hv_extQ hne hi_new
        exact ⟨hC_eq, i_new, hFresh.1, hS_eq, hq_le⟩
    have hBound := (phased_trace_query_bound V N S_seq C_seq q_seq hC₀_sub hq₀ hStep').2
    rw [← hCardV] at hBound
    exact ⟨hRun, hHalt, hqN.trans hBound, hHead1, hHead0, hTable⟩

end RayCounterfamilyInline12

namespace Grunbaum2003

theorem ray_oracle_outer_polytope_invariants_and_phased_trace_bound :
∀ (d : ℕ) (hd : 2 ≤ d),
(∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          (P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            faceCount P 0 = (P.extremePoints ℝ).ncard) ∧
          (∀ (F : PolytopeFace P) (i : Fin m),
            F.val ⊆ {x : Fin d → ℝ | L i x = 1} ↔
              ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → L i v = 1) ∧
          (∀ S : Finset (Fin m),
            P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} ∧
            P ∩ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ P.extremePoints ℝ ∧
            ∀ {v : Fin d → ℝ},
              v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
              oracle v ≠ v →
              ∀ {i_new : Fin m}, L i_new (oracle v) = 1 →
                i_new ∉ S ∧ (insert i_new S).card = S.card + 1) ∧
          (∀ (S : Finset (Fin m)) (V_Q C : Set (Fin d → ℝ)),
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = convexHull ℝ V_Q →
            V_Q ⊆ C → C ⊆ P.extremePoints ℝ →
            ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ C →
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = P ∧ C = P.extremePoints ℝ)) ∧
    (∀ (program : List RayInstruction) (P : Set (Fin d → ℝ)),
      IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)), IsPolytopeRayOracle P oracle →
        ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
          P = {x | ∀ i, L i x ≤ 1} →
          ∀ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c →
            program[c.pc]? = some .halt →
            C_seq 0 = ∅ →
            q_seq 0 ≤ d + 1 →
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin (faceCount P (d - 1)),
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
            c.queries ≤ q_seq N →
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
            c.tape (c.head + (n : ℤ)) = 0 →
            (∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) →
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d + 1) +
              ∑ k ∈ Finset.range (faceCount P (d - 1)),
                (1 + (d - 1) * (2 * (faceCount P (d - 1) - k) + 3)) ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) :=
  @RayCounterfamilyInline12.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_rayMachine_relocated_discovery_gadgets_and_frame_cramer.lean
-- SHA256: 0f30aea8b5c8322c90f7338a34e9a84cacc5f841d52960bfe4742b6231ba3ca4
namespace RayCounterfamilyInline13

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators Matrix Classical

open Grunbaum2003

lemma rayMachine_prefix_and_cramer_row_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (hDet : Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0) :
    let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
    let outBase := cramerRowDest d vBase minBase
    let v : Matrix (Fin d) (Fin d) ℝ :=
      fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ k : Fin d,
        c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧

      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase v
  let t_cr := cramerRowSteps d vBase
  obtain ⟨hMin, c_cr, hRun_cr, _, hHalt_cr, hHead_cr, hQ_cr, hRow_cr, hPres_cr⟩ :=
    hCramerProg oracle c_pre.tape vBase minBase c_pre.queries hDet
  have hRel := hRelocate pre (cramerRowProgram d vBase minBase)
    oracle t_cr ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_cr := hRelocate pre (cramerRowProgram d vBase minBase) oracle 0 c_cr
  refine ⟨hMin, t_pre + t_cr, relocateCfg pre.length c_cr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_cr, Option.map_some]
  · exact hRel_cr.2.2.2.2.2 hHalt_cr
  · rw [hRel_cr.2.1, hHead_cr]
  · rw [hRel_cr.2.2.2.1, hQ_cr]
  · intro k
    rw [hRel_cr.2.2.1]
    exact hRow_cr k
  · intro z hz
    rw [hRel_cr.2.2.1]
    exact hPres_cr z hz

lemma rayMachine_prefix_and_midpoint_vec_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
    let outBase := midpointVecDest d pBase qBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ i : Fin d,
        c.tape (outBase + (i.val : ℤ)) =
          (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_mid := midpointVecSteps d pBase qBase
  obtain ⟨hMin, c_mid, hRun_mid, _, hHalt_mid, hHead_mid, hQ_mid, hVec_mid, hPres_mid⟩ :=
    hMidpointProg oracle c_pre.tape pBase qBase minBase c_pre.queries
  have hRel := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle t_mid ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_mid := hRelocate pre (midpointVecProgram d pBase qBase minBase) oracle 0 c_mid
  refine ⟨hMin, t_pre + t_mid, relocateCfg pre.length c_mid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_mid, Option.map_some]
  · exact hRel_mid.2.2.2.2.2 hHalt_mid
  · rw [hRel_mid.2.1, hHead_mid]
  · rw [hRel_mid.2.2.2.1, hQ_mid]
  · intro i
    rw [hRel_mid.2.2.1]
    exact hVec_mid i
  · intro z hz
    rw [hRel_mid.2.2.1]
    exact hPres_mid z hz

lemma rayMachine_prefix_and_incidence_matrix_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    {m V : ℕ} (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++
      (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
    let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ (j : Fin m) (k : Fin V),
        c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if (∑ i : Fin d,
              c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_inc := facetVertexIncidenceMatrixSteps d m V lBase xBase
  obtain ⟨hMin, c_inc, hRun_inc, _, hHalt_inc, hHead_inc, hQ_inc, hMat_inc, hPres_inc⟩ :=
    @hIncMatrixProg m V oracle c_pre.tape lBase xBase minBase c_pre.queries
  have hRel := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle t_inc ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_inc := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle 0 c_inc
  refine ⟨hMin, t_pre + t_inc, relocateCfg pre.length c_inc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_inc, Option.map_some]
  · exact hRel_inc.2.2.2.2.2 hHalt_inc
  · rw [hRel_inc.2.1, hHead_inc]
  · rw [hRel_inc.2.2.2.1, hQ_inc]
  · intro j k
    rw [hRel_inc.2.2.1]
    exact hMat_inc j k
  · intro z hz
    rw [hRel_inc.2.2.1]
    exact hPres_inc z hz

lemma rayFrame_step_and_cramer_facet_identification {d m : ℕ}
    {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x | ∀ j, L j x ≤ 1}) (S : Finset (Fin m)) :
    (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
      p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      q ∉ Submodule.span ℝ (Set.range v) →
      ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
      let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
      let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
      let p' := (1 / 2 : ℝ) • (p + q)
      LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
        p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
        (∀ j ∈ S, L j p' < 1) ∧
        (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
    (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
      v.det ≠ 0 ∧ ∃ i_new : Fin m,
        i_new ∉ S ∧
        L i_new p₀ = 1 ∧
        ∀ x : Fin d → ℝ,
          ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) := by
  obtain ⟨coordinateAxis, frameCramerCoefficients, frameNormal,
    _, hCramer, hNormal, _, _, _, hStep, hFinal⟩ :=
    Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
  refine ⟨?_, ?_⟩
  · intro n v hLin w hw_pos hw_sum hvP p q hpP hqP hp_eq hpS hq_span j_act hjp hjq
    have hRes := hStep L hP_L v hLin w hw_pos hw_sum hvP p q hpP hqP hp_eq hq_span j_act hjp hjq
    refine ⟨hRes.1, hRes.2.1, hRes.2.2.1, hRes.2.2.2.1, hRes.2.2.2.2.1, hRes.2.2.2.2.2.1, ?_,
      hRes.2.2.2.2.2.2⟩
    intro j hjS
    have hjp_lt : L j p < 1 := hpS j hjS
    have hjq_le : L j q ≤ 1 := by rw [hP_L] at hqP; exact hqP j
    change L j ((1 / 2 : ℝ) • (p + q)) < 1
    rw [map_smul, map_add, smul_eq_mul]
    linarith
  · intro v hLin w hw_pos hw_sum hvP p p₀ hp_front hp_eq hpS hp₀
    obtain ⟨hDet, i_new, hNorm_eq, hi_new_p⟩ :=
      hFinal L hP_L v hLin w hw_pos hw_sum hvP p hp_front hp_eq
    have hi_new_not_S : i_new ∉ S := by
      intro hmem
      have hlt := hpS i_new hmem
      linarith
    refine ⟨hDet, i_new, hi_new_not_S, hp₀ i_new hi_new_p, ?_⟩
    intro x
    have h1 := hNormal d v x
    rw [hNorm_eq] at h1
    rw [h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hCramer d v k]

theorem inline_solution (d : ℕ) :
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
       (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
       (cramerRowSteps : ℕ → ℤ → ℕ)
       (_hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (vBase minBase : ℤ) (q : ℕ),
          let v : Matrix (Fin d) (Fin d) ℝ :=
            fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
          v.det ≠ 0 →
          let prog := cramerRowProgram d vBase minBase
          let outBase := cramerRowDest d vBase minBase
          let steps := cramerRowSteps d vBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ k : Fin d,
              c'.tape (outBase + (k.val : ℤ)) =
                (v.updateCol k (fun _ => 1)).det / v.det) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ),
      rayMachineRun (pre ++
          (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0 →
      let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
      let outBase := cramerRowDest d vBase minBase
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ k : Fin d,
          c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)) :=
  ⟨fun run_add relocateInst relocateCfg hRelocate cramerRowProgram cramerRowDest cramerRowSteps
      hCramerProg pre oracle t_pre c_pre vBase minBase hRun_pre hDet =>
     rayMachine_prefix_and_cramer_row_composition run_add relocateInst relocateCfg hRelocate
       cramerRowProgram cramerRowDest cramerRowSteps hCramerProg pre oracle t_pre c_pre vBase minBase
       hRun_pre hDet,
   fun run_add relocateInst relocateCfg hRelocate midpointVecProgram midpointVecDest midpointVecSteps
      hMidpointProg pre oracle t_pre c_pre pBase qBase minBase hRun_pre =>
     rayMachine_prefix_and_midpoint_vec_composition run_add relocateInst relocateCfg hRelocate
       midpointVecProgram midpointVecDest midpointVecSteps hMidpointProg pre oracle t_pre c_pre
       pBase qBase minBase hRun_pre,
   fun run_add relocateInst relocateCfg hRelocate facetVertexIncidenceMatrixProgram
      facetVertexIncidenceMatrixDest facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC
      hIncMatrixProg _ _ pre oracle t_pre c_pre lBase xBase minBase hRun_pre =>
     rayMachine_prefix_and_incidence_matrix_composition run_add relocateInst relocateCfg hRelocate
       facetVertexIncidenceMatrixProgram facetVertexIncidenceMatrixDest
       facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC hIncMatrixProg pre oracle t_pre
       c_pre lBase xBase minBase hRun_pre,
   fun L hP_L S => rayFrame_step_and_cramer_facet_identification L hP_L S⟩

end RayCounterfamilyInline13

namespace Grunbaum2003

theorem rayMachine_relocated_discovery_gadgets_and_frame_cramer :
∀ (d : ℕ),
(∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
       (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
       (cramerRowSteps : ℕ → ℤ → ℕ)
       (_hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (vBase minBase : ℤ) (q : ℕ),
          let v : Matrix (Fin d) (Fin d) ℝ :=
            fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
          v.det ≠ 0 →
          let prog := cramerRowProgram d vBase minBase
          let outBase := cramerRowDest d vBase minBase
          let steps := cramerRowSteps d vBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ k : Fin d,
              c'.tape (outBase + (k.val : ℤ)) =
                (v.updateCol k (fun _ => 1)).det / v.det) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ),
      rayMachineRun (pre ++
          (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0 →
      let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
      let outBase := cramerRowDest d vBase minBase
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ k : Fin d,
          c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)) :=
  @RayCounterfamilyInline13.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_rayFrame_init_extension_axis_and_step_eps_composition.lean
-- SHA256: fa445d27a2d8459b0379083394f5bff7f9ddcbcf1eaa96aa9ba7fbfa31fd896e
namespace RayCounterfamilyInline14

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators Matrix Classical

open Grunbaum2003

lemma exists_face_and_exposed_vertex_equiv {d : ℕ} {P : Set (Fin d → ℝ)}
    (hFaces : ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P))
    (V : Finset (Fin d → ℝ))
    (hV_exp : (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}})
    (hV_card : V.card = faceCount P 0) :
    ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
      (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
      ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V := by
  obtain ⟨n, ⟨e⟩⟩ := hFaces
  let eFin : Fin (faceCount P 0) ≃ V := (Finset.equivFinOfCardEq hV_card).symm
  let eSet : V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}} := Equiv.setCongr hV_exp
  let vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}} := eFin.trans eSet
  refine ⟨n, e, vEnum, fun k => ?_⟩
  exact (eFin k).property

lemma rayFrame_init_of_uncertified_extremePoint {d m : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x | ∀ i, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) {v : Fin d → ℝ}
    (hv : v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ)
    (hne : oracle v ≠ v) :
    let p₀ := oracle v
    let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
    let w₁ : Fin 1 → ℝ := fun _ => 1
    v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
      LinearIndependent ℝ v₁ ∧
      (∀ i : Fin 1, 0 < w₁ i) ∧
      (∑ i : Fin 1, w₁ i = 1) ∧
      p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
      (∀ i : Fin 1, v₁ i ∈ P) ∧
      (∀ j ∈ S, L j p₀ < 1) ∧
      (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1) := by
  intro p₀ v₁ w₁
  have hd_pos : 0 < d := by omega
  have hP_conv : Convex ℝ P := by
    rcases hP.1 with ⟨W, _, _, rfl⟩
    exact convex_convexHull ℝ W
  have hP_closed : IsClosed P := by
    rw [hP_L]
    have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
        ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
    rw [h_eq]
    exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
  have hPQ : P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} := by
    intro x hx i hi; rw [hP_L] at hx; exact hx i
  let eS : Fin S.card ≃ S := (Finset.equivFin S).symm
  let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
  have hv_LS : ∀ j : Fin S.card, LS j v ≤ 1 := by
    intro j
    exact hv.1 (eS j).val (eS j).property
  have hSector := Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.1
    hd_pos hP_conv hP_closed h0 hPQ hOracle hv hne LS hv_LS
  have hv_ne : v ≠ 0 := hSector.1
  have hp₀_front : p₀ ∈ frontier P := (hOracle v hv_ne).1
  have hp₀_P : p₀ ∈ P := by
    rw [hP_closed.frontier_eq] at hp₀_front
    exact hp₀_front.1
  have hp₀_ne : p₀ ≠ 0 := by
    intro hzero
    exact hp₀_front.2 (hzero ▸ h0)
  have hLin : LinearIndependent ℝ v₁ := by
    rw [linearIndependent_unique_iff]
    exact hp₀_ne
  have hp₀_S : ∀ j ∈ S, L j p₀ < 1 := by
    intro j hj
    have hlt := hSector.2 (eS.symm ⟨j, hj⟩)
    simpa [LS, eS] using hlt
  refine ⟨hv_ne, hp₀_ne, hp₀_P, hp₀_front, hLin, ?_, ?_, ?_, ?_, hp₀_S, ?_⟩
  · intro _; norm_num [w₁]
  · simp [w₁]
  · simp [w₁, v₁]
  · intro _; exact hp₀_P
  · intro k hk _; exact hk

lemma rayFrame_exists_extension_axis_and_coord {d r : ℕ}
    {P : Set (Fin d → ℝ)} (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (v : Fin r → Fin d → ℝ) (hLin : LinearIndependent ℝ v) (hr : r < d)
    (w : Fin r → ℝ) (p : Fin d → ℝ) (hp_front : p ∈ frontier P)
    (hp_eq : p = ∑ i : Fin r, w i • v i) :
    ∃ (i_axis j_coord : Fin d),
      Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
      j_coord ≠ i_axis ∧
      p j_coord ≠ 0 := by
  obtain ⟨coordinateAxis, _, _, hAxis, _, _, _, hExtAxis, hCoord, _, _⟩ :=
    Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
  obtain ⟨i_axis, hi_not_span⟩ := hExtAxis v hLin hr
  have hp_ne : p ≠ 0 := by
    intro hzero
    exact hp_front.2 (hzero ▸ h0)
  have hp_mem : p ∈ Submodule.span ℝ (Set.range v) := by
    rw [hp_eq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨j_coord, hj_ne, hpj_ne⟩ :=
    hCoord (Submodule.span ℝ (Set.range v)) p hp_mem hp_ne i_axis hi_not_span
  rw [hAxis d i_axis] at hi_not_span
  exact ⟨i_axis, j_coord, hi_not_span, hj_ne, hpj_ne⟩

lemma rayMachine_prefix_and_step_eps_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
    (hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
        ∀ z : ℤ, z < dst → c'.tape z = source z)
    {k : ℕ} (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (ha_pos : 0 < c_pre.tape aCell)
    (hSlack : ∀ j : Fin k,
      ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        c_pre.tape (pBase + (i.val : ℤ)) < 1) :
    let prog := pre ++
      (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
    let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
    let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
      ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        c_pre.tape (xBase + (i.val : ℤ))
    let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
    let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
    minBase ≤ dst ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
      (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z) := by
  intro prog dst rowVal δ M
  let t_se := stepEpsSteps d k rowBase pBase uBase aCell
  obtain ⟨hMin, c_se, hRun_se, _, hHalt_se, hHead_se, hQ_se, hVal_se, hPres_se⟩ :=
    @hStepEpsProg k oracle c_pre.tape rowBase pBase uBase aCell minBase c_pre.queries ha_pos hSlack
  have hRel := hRelocate pre (stepEpsProgram d k rowBase pBase uBase aCell minBase)
    oracle t_se ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_se := hRelocate pre (stepEpsProgram d k rowBase pBase uBase aCell minBase)
    oracle 0 c_se
  refine ⟨hMin, t_pre + t_se, relocateCfg pre.length c_se, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_se, Option.map_some]
  · exact hRel_se.2.2.2.2.2 hHalt_se
  · rw [hRel_se.2.1, hHead_se]
  · rw [hRel_se.2.2.2.1, hQ_se]
  · rw [hRel_se.2.2.1]
    exact hVal_se
  · intro z hz
    rw [hRel_se.2.2.1]
    exact hPres_se z hz

theorem inline_solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)},
      (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
      ∀ (V : Finset (Fin d → ℝ)),
        (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
        V.card = faceCount P 0 →
        ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
          (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
          ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x | ∀ i, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∀ (S : Finset (Fin m)) {v : Fin d → ℝ},
            v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
            oracle v ≠ v →
            let p₀ := oracle v
            let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
            let w₁ : Fin 1 → ℝ := fun _ => 1
            v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
              LinearIndependent ℝ v₁ ∧
              (∀ i : Fin 1, 0 < w₁ i) ∧
              (∑ i : Fin 1, w₁ i = 1) ∧
              p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
              (∀ i : Fin 1, v₁ i ∈ P) ∧
              (∀ j ∈ S, L j p₀ < 1) ∧
              (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1)) ∧
    (∀ {r : ℕ} {P : Set (Fin d → ℝ)}, (0 : Fin d → ℝ) ∈ interior P →
      ∀ (v : Fin r → Fin d → ℝ), LinearIndependent ℝ v → r < d →
        ∀ (w : Fin r → ℝ) (p : Fin d → ℝ),
          p ∈ frontier P → p = ∑ i : Fin r, w i • v i →
          ∃ (i_axis j_coord : Fin d),
            Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
            j_coord ≠ i_axis ∧
            p j_coord ≠ 0) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
       (_hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
            ∀ z : ℤ, z < dst → c'.tape z = source z)
       {k : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ),
      rayMachineRun (pre ++
          (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      0 < c_pre.tape aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (pBase + (i.val : ℤ)) < 1) →
      let prog := pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
        (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hFaces V hV_exp hV_card
    exact exists_face_and_exposed_vertex_equiv hFaces V hV_exp hV_card
  · intro m P hP h0 L hP_L oracle hOracle S v hv hne
    exact rayFrame_init_of_uncertified_extremePoint hd hP h0 L hP_L hOracle S hv hne
  · intro r P h0 v hLin hr w p hp_front hp_eq
    exact rayFrame_exists_extension_axis_and_coord h0 v hLin hr w p hp_front hp_eq
  · intro run_add relocateInst relocateCfg hRelocate stepEpsProgram stepEpsDest stepEpsSteps
      hStepEpsProg k pre oracle t_pre c_pre rowBase pBase uBase aCell minBase hRun_pre ha_pos hSlack
    exact rayMachine_prefix_and_step_eps_composition run_add relocateInst relocateCfg hRelocate
      stepEpsProgram stepEpsDest stepEpsSteps hStepEpsProg pre oracle t_pre c_pre
      rowBase pBase uBase aCell minBase hRun_pre ha_pos hSlack

end RayCounterfamilyInline14

namespace Grunbaum2003

theorem rayFrame_init_extension_axis_and_step_eps_composition :
∀ (d : ℕ) (hd : 2 ≤ d),
(∀ {P : Set (Fin d → ℝ)},
      (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
      ∀ (V : Finset (Fin d → ℝ)),
        (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
        V.card = faceCount P 0 →
        ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
          (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
          ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x | ∀ i, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∀ (S : Finset (Fin m)) {v : Fin d → ℝ},
            v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
            oracle v ≠ v →
            let p₀ := oracle v
            let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
            let w₁ : Fin 1 → ℝ := fun _ => 1
            v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
              LinearIndependent ℝ v₁ ∧
              (∀ i : Fin 1, 0 < w₁ i) ∧
              (∑ i : Fin 1, w₁ i = 1) ∧
              p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
              (∀ i : Fin 1, v₁ i ∈ P) ∧
              (∀ j ∈ S, L j p₀ < 1) ∧
              (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1)) ∧
    (∀ {r : ℕ} {P : Set (Fin d → ℝ)}, (0 : Fin d → ℝ) ∈ interior P →
      ∀ (v : Fin r → Fin d → ℝ), LinearIndependent ℝ v → r < d →
        ∀ (w : Fin r → ℝ) (p : Fin d → ℝ),
          p ∈ frontier P → p = ∑ i : Fin r, w i • v i →
          ∃ (i_axis j_coord : Fin d),
            Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
            j_coord ≠ i_axis ∧
            p j_coord ≠ 0) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
       (_hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
            ∀ z : ℤ, z < dst → c'.tape z = source z)
       {k : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ),
      rayMachineRun (pre ++
          (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      0 < c_pre.tape aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (pBase + (i.val : ℤ)) < 1) →
      let prog := pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
        (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z)) :=
  @RayCounterfamilyInline14.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_rayFrame_local_sector_exclusion_and_phase_query_budget.lean
-- SHA256: 59306dc4840837a071aaa8ef11c61d54e8f873e26e5b3fbd345d3675794cffc5
namespace RayCounterfamilyInline15

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators Classical

open Grunbaum2003

lemma single_extension_step_query_bound (m cardS n q : ℕ)
    (hWalk : 3 + n ≤ 2 * (m - cardS) + 2) :
    q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3) := by
  omega

lemma multi_step_extension_query_bound (B : ℕ) (q_step : ℕ → ℕ) :
    ∀ K : ℕ, (∀ r < K, q_step (r + 1) ≤ q_step r + B) →
      q_step K ≤ q_step 0 + K * B := by
  intro K
  induction K with
  | zero =>
    intro _
    simp
  | succ K ih =>
    intro hStep
    have hIH := ih (fun r hr => hStep r (by omega))
    have hLast := hStep K (by omega)
    calc
      q_step (K + 1) ≤ q_step K + B := hLast
      _ ≤ (q_step 0 + K * B) + B := Nat.add_le_add_right hIH B
      _ = q_step 0 + (K + 1) * B := by
        rw [Nat.succ_mul, Nat.add_assoc]

lemma facet_discovery_phase_query_bound (d m cardS q_start : ℕ) (q_step : ℕ → ℕ)
    (hInit : q_step 0 ≤ q_start + 1)
    (hSteps : ∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) :
    q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3)) := by
  have hMulti := multi_step_extension_query_bound (2 * (m - cardS) + 3) q_step (d - 1) hSteps
  omega

lemma local_sector_known_facet_exclusion_of_finset {d m : ℕ}
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP_L : P = {x | ∀ i, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
    {p u : Fin d → ℝ} (hp_front : p ∈ frontier P)
    (hp_S : ∀ j ∈ S, L j p < 1)
    {a : ℝ} (ha : 0 < a) (hu_neg : (-a) • u ∈ P) (hu_pos : a • u ∈ P) :
    let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
    let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
    let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
    let ε := a * δ / (2 * (1 + a * M + δ))
    p - ε • u ≠ 0 ∧
      ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
        oracle (p - ε • u) = τ • (p - ε • u) ∧
        (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
        let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
        r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
        ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
          p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1 := by
  intro LS δ M ε
  have hP_conv : Convex ℝ P := by
    rcases hP.1 with ⟨W, _, _, rfl⟩
    exact convex_convexHull ℝ W
  have hP_closed : IsClosed P := by
    rw [hP_L]
    have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
        ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
    rw [h_eq]
    exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
  have hp_LS : ∀ j : Fin S.card, LS j p < 1 :=
    fun j => hp_S (eS j).val (eS j).property
  obtain ⟨hδ, hM, hp_δ, hu_M⟩ :=
    Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.1 LS p u hp_LS
  obtain ⟨hne, τ, hτ0, hτ2, horacle, h1, hr₂_ne, hr₂_S, hseg⟩ :=
    Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.2
      hP_conv hP_closed h0 hp_front ha hδ hM hu_neg hu_pos LS hp_δ hu_M hOracle
  have hLS_apply : ∀ (j : Fin m) (hj : j ∈ S) (q : Fin d → ℝ),
      LS (eS.symm ⟨j, hj⟩) q = L j q := by
    intro j hj q
    change (L (eS (eS.symm ⟨j, hj⟩)).val) q = L j q
    rw [Equiv.apply_symm_apply]
  refine ⟨hne, τ, hτ0, hτ2, horacle, ?_, hr₂_ne, ?_, ?_⟩
  · intro j hj
    rw [← hLS_apply j hj]
    exact h1 (eS.symm ⟨j, hj⟩)
  · intro j hj
    rw [← hLS_apply j hj]
    exact hr₂_S (eS.symm ⟨j, hj⟩)
  · intro x hx0 hx1
    refine ⟨(hseg x hx0 hx1).1, fun j hj => ?_⟩
    rw [← hLS_apply j hj]
    exact (hseg x hx0 hx1).2 (eS.symm ⟨j, hj⟩)

theorem inline_solution (d : ℕ) :
    (∀ (m cardS n q : ℕ),
      3 + n ≤ 2 * (m - cardS) + 2 →
      q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3)) ∧
    (∀ (m cardS q_start : ℕ) (q_step : ℕ → ℕ),
      q_step 0 ≤ q_start + 1 →
      (∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) →
      q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3))) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ), P = {x | ∀ i, L i x ≤ 1} →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
        {p u : Fin d → ℝ}, p ∈ frontier P →
      (∀ j ∈ S, L j p < 1) →
      ∀ {a : ℝ}, 0 < a → (-a) • u ∈ P → a • u ∈ P →
      let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
      let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
      let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
      let ε := a * δ / (2 * (1 + a * M + δ))
      p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1) := by
  refine ⟨single_extension_step_query_bound, facet_discovery_phase_query_bound d, ?_⟩
  intro m P hP h0 L hP_L oracle hOracle S eS p u hp_front hp_S a ha hu_neg hu_pos
  exact local_sector_known_facet_exclusion_of_finset hP h0 L hP_L hOracle S eS
    hp_front hp_S ha hu_neg hu_pos

end RayCounterfamilyInline15

namespace Grunbaum2003

theorem rayFrame_local_sector_exclusion_and_phase_query_budget :
∀ (d : ℕ),
(∀ (m cardS n q : ℕ),
      3 + n ≤ 2 * (m - cardS) + 2 →
      q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3)) ∧
    (∀ (m cardS q_start : ℕ) (q_step : ℕ → ℕ),
      q_step 0 ≤ q_start + 1 →
      (∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) →
      q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3))) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ), P = {x | ∀ i, L i x ≤ 1} →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
        {p u : Fin d → ℝ}, p ∈ frontier P →
      (∀ j ∈ S, L j p < 1) →
      ∀ {a : ℝ}, 0 < a → (-a) • u ∈ P → a • u ∈ P →
      let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
      let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
      let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
      let ε := a * δ / (2 * (1 + a * M + δ))
      p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1) :=
  @RayCounterfamilyInline15.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_polytope_normalized_halfspace_presentation_and_facet_lower_bound.lean
-- SHA256: c9269dd3c4612982385ea89ca0938ef1e3b7478315824e392f1ae49ecba99403
namespace RayCounterfamilyInline16

open _root_.Grunbaum2003


set_option autoImplicit false

noncomputable section

namespace Grunbaum2003


theorem aux_pp_int_step {d : ℕ} {P : Set (Fin d → ℝ)} {c : Fin d → ℝ} (hc : c ∈ interior P)
    (u : Fin d → ℝ) : ∃ ε : ℝ, 0 < ε ∧ c + ε • u ∈ P := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨r / (2 * (‖u‖ + 1)), by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h1 : ‖u‖ < ‖u‖ + 1 := by linarith
  calc r / (2 * (‖u‖ + 1)) * ‖u‖ ≤ r / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by
        gcongr
    _ = r / 2 := by field_simp
    _ < r := by linarith

theorem aux_pp_hull_le {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (l : Module.Dual ℝ (Fin d → ℝ)) (β : ℝ) (hl : ∀ v ∈ V, l (v - c) ≤ β) :
    ∀ y ∈ convexHull ℝ (V : Set (Fin d → ℝ)), l (y - c) ≤ β := by
  intro y hy
  have hsub : convexHull ℝ (V : Set (Fin d → ℝ)) ⊆ {w | l w ≤ β + l c} :=
    convexHull_min (fun v hv => by
      have := hl v hv; rw [map_sub] at this; show l v ≤ β + l c; linarith)
      (convex_halfSpace_le l.isLinear _)
  have := hsub hy
  simp only [Set.mem_setOf_eq] at this
  rw [map_sub]; linarith

/-- Polar-vertex step: a separating normalized functional can be moved until its tight
vertices span the space. -/
theorem aux_pp_polar {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hc : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ)))) (x : Fin d → ℝ) :
    ∀ n : ℕ, ∀ l : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l (v - c) ≤ 1) → 1 < l (x - c) →
      (V.filter (fun v => l (v - c) < 1)).card = n →
      ∃ l' : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l' (v - c) ≤ 1) ∧ 1 < l' (x - c) ∧
        Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l' (v - c) = 1))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hx hn
  by_cases hW : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤
  · exact ⟨l, hl, hx, hW⟩
  obtain ⟨h0, h0ne, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
  have hk : ∀ v ∈ V, l (v - c) = 1 → h0 (v - c) = 0 := fun v hv hv1 =>
    hle (Submodule.subset_span ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hv, hv1⟩), rfl⟩)
  obtain ⟨h, hne, hker, hhx⟩ : ∃ h : Module.Dual ℝ (Fin d → ℝ), h ≠ 0 ∧
      (∀ v ∈ V, l (v - c) = 1 → h (v - c) = 0) ∧ 0 ≤ h (x - c) := by
    by_cases hs : 0 ≤ h0 (x - c)
    · exact ⟨h0, h0ne, hk, hs⟩
    · refine ⟨-h0, neg_ne_zero.mpr h0ne, fun v hv hv1 => by simp [hk v hv hv1], ?_⟩
      simp only [LinearMap.neg_apply]; linarith [not_le.mp hs]
  have hexists : ∃ v ∈ V, 0 < h (v - c) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hP := aux_pp_hull_le V c h 0 hcon
    refine LinearMap.ext (fun u => ?_)
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
    obtain ⟨ε', hε', hεu'⟩ := aux_pp_int_step hc (-u)
    have h1 := hP _ hεu
    have h2 := hP _ hεu'
    simp only [add_sub_cancel_left, map_smul, map_neg, smul_eq_mul] at h1 h2
    have h3 : h u ≤ 0 := by nlinarith
    have h4 : 0 ≤ h u := by nlinarith
    rw [LinearMap.zero_apply]
    linarith
  set S := V.filter (fun v => 0 < h (v - c)) with hS
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hpos⟩ := hexists
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hpos⟩⟩
  obtain ⟨vs, hvsS, hvsmin⟩ := S.exists_min_image (fun v => (1 - l (v - c)) / h (v - c)) hSne
  have hvs : vs ∈ V ∧ 0 < h (vs - c) := Finset.mem_filter.mp hvsS
  set t := (1 - l (vs - c)) / h (vs - c) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hl vs hvs.1]) hvs.2.le
  set l' := l + t • h with hl'def
  have hl'app : ∀ z, l' z = l z + t * h z := fun z => by
    simp [hl'def, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hl' : ∀ v ∈ V, l' (v - c) ≤ 1 := by
    intro v hv
    rw [hl'app]
    by_cases hpos : 0 < h (v - c)
    · have := hvsmin v (Finset.mem_filter.mpr ⟨hv, hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push Not at hpos
      nlinarith [hl v hv]
  have hx' : 1 < l' (x - c) := by rw [hl'app]; nlinarith
  have hvs1 : l' (vs - c) = 1 := by
    rw [hl'app, ht, div_mul_cancel₀ _ hvs.2.ne']; ring
  have hvslt : l (vs - c) < 1 := by
    rcases lt_or_eq_of_le (hl vs hvs.1) with h' | h'
    · exact h'
    · exfalso; have := hker vs hvs.1 h'; linarith [hvs.2]
  have hsub : V.filter (fun v => l' (v - c) < 1) ⊂ V.filter (fun v => l (v - c) < 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨vs, Finset.mem_filter.mpr ⟨hvs.1, hvslt⟩, ?_⟩
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      linarith
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      by_contra hcon
      have heq : l (v - c) = 1 := le_antisymm (hl v hv.1) (not_lt.mp hcon)
      have h5 := hker v hv.1 heq
      have : l' (v - c) = 1 := by rw [hl'app, h5, heq]; ring
      linarith [hv.2]
  exact ih _ (hn ▸ Finset.card_lt_card hsub) l' hl' hx' rfl

/-- The face cut out by a polar vertex is a facet, and every exposing functional of it
separates `x`. -/
theorem aux_pp_facet {d : ℕ} (hd : 0 < d) (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hcP : c ∈ convexHull ℝ (V : Set (Fin d → ℝ))) (l : Module.Dual ℝ (Fin d → ℝ))
    (hl : ∀ v ∈ V, l (v - c) ≤ 1)
    (hspan : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤)
    (x : Fin d → ℝ) (hx : 1 < l (x - c)) :
    ∃ G ∈ {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1},
      ∀ g : StrongDual ℝ (Fin d → ℝ),
        G = {y ∈ convexHull ℝ (V : Set (Fin d → ℝ)) |
          ∀ y' ∈ convexHull ℝ (V : Set (Fin d → ℝ)), g y' ≤ g y} →
        ∀ f ∈ G, g f < g x := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set T := V.filter (fun v => l (v - c) = 1) with hT
  have hPle : ∀ y ∈ P, l (y - c) ≤ 1 := aux_pp_hull_le V c l 1 hl
  have hTne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    rw [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
    have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = 0 := by rw [← hspan, finrank_bot]
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨t0, ht0⟩ := hTne
  have ht0' := Finset.mem_filter.mp ht0
  set lc : StrongDual ℝ (Fin d → ℝ) := LinearMap.toContinuousLinearMap l with hlcdef
  have hlc : ∀ z, lc z = l z := fun z => by simp [hlcdef]
  set G := {y ∈ P | ∀ y' ∈ P, lc y' ≤ lc y} with hG
  have hTG : ∀ t ∈ T, t ∈ G := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ht'.1), fun y' hy' => ?_⟩
    rw [hlc, hlc]
    have h1 := hPle y' hy'
    have h2 := ht'.2
    rw [map_sub] at h1 h2
    linarith
  have hG1 : ∀ y ∈ G, l (y - c) = 1 := by
    intro y hy
    have h1 := hy.2 t0 (hTG t0 ht0).1
    rw [hlc, hlc] at h1
    have h2 := hPle y hy.1
    have h3 := ht0'.2
    rw [map_sub] at h2 h3 ⊢
    linarith
  refine ⟨G, ⟨⟨t0, hTG t0 ht0⟩, fun _ => ⟨lc, rfl⟩, ?_⟩, ?_⟩
  · have hl0 : l ≠ 0 := by
      intro h0; have := ht0'.2; rw [h0, LinearMap.zero_apply] at this; norm_num at this
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at hker
    set D := (affineSpan ℝ G).direction with hD
    have hDle : D ≤ LinearMap.ker l := by
      rw [hD, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨y, hy, y', hy', rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
      have h1 := hG1 y hy
      have h2 := hG1 y' hy'
      rw [map_sub] at h1 h2 ⊢
      linarith
    have hup : Module.finrank ℝ D ≤ d - 1 := by
      have := Submodule.finrank_mono hDle
      omega
    have hdown : d ≤ Module.finrank ℝ D + 1 := by
      have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ D ⊔ Submodule.span ℝ {t0 - c} := by
        rw [← hspan, Submodule.span_le]
        rintro z ⟨t, ht, rfl⟩
        have hsplit : t - c = (t - t0) + (t0 - c) := by abel
        simp only [SetLike.mem_coe]
        rw [hsplit]
        refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton_self _)
        rw [hD, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hTG t ht) (hTG t0 ht0)
      have h1 := Submodule.finrank_mono htop
      rw [finrank_top, Module.finrank_fin_fun] at h1
      have h2 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span ℝ {t0 - c})
      have h3 : Module.finrank ℝ (Submodule.span ℝ ({t0 - c} : Set (Fin d → ℝ))) ≤ 1 := by
        have := finrank_span_le_card (R := ℝ) ({t0 - c} : Set (Fin d → ℝ))
        simpa using this
      omega
    omega
  · intro g hg f hf
    have hGg : ∀ y ∈ G, ∀ y' ∈ P, g y' ≤ g y := by
      intro y hy; rw [hg] at hy; exact hy.2
    have hGP : ∀ y ∈ G, y ∈ P := fun y hy => hy.1
    have hTeq : ∀ t ∈ T, g t = g f := fun t ht =>
      le_antisymm (hGg f hf t (hGP t (hTG t ht))) (hGg t (hTG t ht) f (hGP f hf))
    set β := g f - g c with hβ
    have hlin : (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) = β • l := by
      refine LinearMap.ext_on hspan ?_
      rintro z ⟨t, ht, rfl⟩
      have ht' := Finset.mem_filter.mp ht
      simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, smul_eq_mul]
      rw [ht'.2, mul_one, map_sub, hTeq t ht]
    have happ : ∀ z, g z = β * l z := fun z => by
      have := congrArg (fun φ : (Fin d → ℝ) →ₗ[ℝ] ℝ => φ z) hlin
      simpa using this
    have hβ0 : 0 ≤ β := by
      have := hGg f hf c hcP
      rw [hβ]; linarith
    have hβpos : 0 < β := by
      rcases lt_or_eq_of_le hβ0 with h | h
      · exact h
      · exfalso
        have hcG : c ∈ G := by
          rw [hg]
          exact ⟨hcP, fun y' _ => by rw [happ, happ, ← h]; simp⟩
        have := hG1 c hcG
        simp at this
    have hgx := happ (x - c)
    rw [map_sub] at hgx
    nlinarith

/-- A convex hull of finitely many points has finitely many exposed faces of each dimension. -/
theorem aux_pp_finite {d k : ℕ} (V : Finset (Fin d → ℝ)) :
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}.Finite := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  have key : ∀ F F' : Set (Fin d → ℝ), F.Nonempty → IsExposed ℝ P F → F'.Nonempty →
      IsExposed ℝ P F' → F ∩ ↑V ⊆ F' → F ⊆ F' := by
    intro F F' hF hFe hF' hF'e hsub y hy
    obtain ⟨g, hg⟩ := hFe hF
    have hyP : y ∈ P := by rw [hg] at hy; exact hy.1
    have hymax : ∀ y' ∈ P, g y' ≤ g y := by rw [hg] at hy; exact hy.2
    obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull'.mp hyP
    have hVP : ∀ v ∈ V, v ∈ P := fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hsum0 : ∑ v ∈ V, w v * (g y - g v) = 0 := by
      have h1 : g y = ∑ v ∈ V, w v * g v := by
        rw [← hwy, map_sum]; simp [map_smul, smul_eq_mul]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv =>
      mul_nonneg (hw0 v hv) (by linarith [hymax v (hVP v hv)]))).mp hsum0
    have hF'c : Convex ℝ F' := hF'e.convex (convex_convexHull ℝ _)
    have hmem : ∀ v ∈ V.filter (fun v => w v ≠ 0), v ∈ F' := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have h1 := hterm v hv.1
      have h2 : g y - g v = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hv.2
        · exact h
      apply hsub
      refine ⟨?_, Finset.mem_coe.mpr hv.1⟩
      rw [hg]
      refine ⟨hVP v hv.1, fun y' hy' => ?_⟩
      linarith [hymax y' hy']
    have hsum1 : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v = 1 := by
      rw [Finset.sum_filter_ne_zero]; exact hw1
    have hsumy : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v • v = y := by
      rw [← hwy]
      refine Finset.sum_filter_of_ne (fun v _ hne => ?_)
      intro h0; rw [h0, zero_smul] at hne; exact hne rfl
    rw [← hsumy]
    exact hF'c.sum_mem (fun v hv => hw0 v (Finset.mem_filter.mp hv).1) hsum1 hmem
  refine Set.Finite.of_finite_image (f := fun F => F ∩ (V : Set (Fin d → ℝ))) ?_ ?_
  · refine (V.finite_toSet.finite_subsets).subset ?_
    rintro _ ⟨F, _, rfl⟩
    exact Set.inter_subset_right
  · intro F hF F' hF' heq
    simp only at heq
    apply subset_antisymm
    · exact key F F' hF.1 hF.2.1 hF'.1 hF'.2.1 (heq ▸ Set.inter_subset_left)
    · exact key F' F hF'.1 hF'.2.1 hF.1 hF.2.1 (heq.symm ▸ Set.inter_subset_left)

/-- Enumerate a finite set of size at most `k+1`, padding with a default value. -/
theorem aux_pp_enum {α β : Type} {k : ℕ} (S : Set α) (hS : S.Finite) (hc : S.ncard ≤ k + 1)
    (φ : α → β) (z : β) :
    ∃ q : Fin (k+1) → β, (∀ i, q i = z ∨ ∃ F ∈ S, q i = φ F) ∧ ∀ F ∈ S, ∃ i, q i = φ F := by
  set L := hS.toFinset.toList with hL
  have hlen : L.length ≤ k + 1 := by
    rw [hL, Finset.length_toList, ← Set.ncard_eq_toFinset_card S hS]; exact hc
  refine ⟨fun i => (L.map φ).getD i z, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) < L.length
    · right
      refine ⟨L[(i : ℕ)], ?_, ?_⟩
      · have := List.getElem_mem hi
        exact (Set.Finite.mem_toFinset hS).mp (Finset.mem_toList.mp this)
      · simp [List.getD_eq_getElem?_getD, hi]
    · left
      simp [List.getD_eq_getElem?_getD, not_lt.mp hi]
  · intro F hF
    have hFL : F ∈ L := by rw [hL, Finset.mem_toList, Set.Finite.mem_toFinset]; exact hF
    obtain ⟨j, hj, hjF⟩ := List.getElem_of_mem hFL
    refine ⟨⟨j, lt_of_lt_of_le hj hlen⟩, ?_⟩
    simp [List.getD_eq_getElem?_getD, hj, hjF]

/-- H-representation of a full-dimensional polytope by at most `k+1` facet inequalities
(padded with trivial ones), together with a strictly feasible point. -/
theorem halfspace_representation_at_zero {d k : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1) :
    ∃ (a : Fin (k+1) → StrongDual ℝ (Fin d → ℝ)) (b : Fin (k+1) → ℝ),
      P = {x | ∀ i, a i x ≤ b i} ∧ (∀ i, a i 0 < b i) ∧
      ∀ i, a i = 0 ∨
        ({y ∈ P | a i y = b i}.Nonempty ∧ IsExposed ℝ P {y ∈ P | a i y = b i} ∧
          Module.finrank ℝ (affineSpan ℝ {y ∈ P | a i y = b i}).direction = d - 1) := by
  obtain ⟨⟨V0, hV0fin, hV0ne, hPV⟩, hspan⟩ := hP
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, 1, ?_, (fun i => by simp), (fun i => Or.inl rfl)⟩
    ext x
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.zero_apply, Pi.zero_apply, Pi.one_apply,
      zero_le_one, implies_true, iff_true]
    obtain ⟨v, hv⟩ := hV0ne
    have : x = v := Subsingleton.elim _ _
    rw [hPV, this]; exact subset_convexHull ℝ _ hv
  have hd0 : d ≠ 0 := by omega
  rw [if_neg hd0] at hf
  set V := hV0fin.toFinset with hVdef
  have hVeq : (V : Set (Fin d → ℝ)) = V0 := hV0fin.coe_toFinset
  rw [← hVeq] at hPV
  subst hPV
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set 𝓕 := {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = d - 1} with h𝓕
  have hfin : 𝓕.Finite := aux_pp_finite V
  have hcard : 𝓕.ncard ≤ k + 1 := hf
  have hex : ∀ F : Set (Fin d → ℝ), ∃ g : StrongDual ℝ (Fin d → ℝ), ∃ f : Fin d → ℝ,
      F ∈ 𝓕 → f ∈ F ∧ F = {y ∈ P | ∀ y' ∈ P, g y' ≤ g y} := by
    intro F
    by_cases hF : F ∈ 𝓕
    · obtain ⟨g, hg⟩ := hF.2.1 hF.1
      exact ⟨g, hF.1.some, fun _ => ⟨hF.1.some_mem, hg⟩⟩
    · exact ⟨0, 0, fun h => absurd h hF⟩
  choose g f hgf using hex
  let c : Fin d → ℝ := 0
  have hc : c ∈ interior P := hzero
  have hcP : c ∈ P := interior_subset hc
  obtain ⟨q, hq1, hq2⟩ := aux_pp_enum 𝓕 hfin hcard (fun F => (g F, g F (f F)))
    ((0 : StrongDual ℝ (Fin d → ℝ)), (1 : ℝ))
  have hfmax : ∀ F ∈ 𝓕, ∀ y ∈ P, g F y ≤ g F (f F) := by
    intro F hF y hy
    obtain ⟨h1, h2⟩ := hgf F hF
    have h3 : f F ∈ {y ∈ P | ∀ y' ∈ P, g F y' ≤ g F y} := by rw [← h2]; exact h1
    exact h3.2 y hy
  refine ⟨fun i => (q i).1, fun i => (q i).2, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx i
      rcases hq1 i with h | ⟨F, hF, h⟩
      · rw [h]; simp
      · rw [h]; exact hfmax F hF x hx
    · intro hx
      by_contra hxP
      obtain ⟨φ, u, hφP, hφx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
        ((V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed) hxP
      have hφc := hφP c hcP
      set l0 : Module.Dual ℝ (Fin d → ℝ) := (u - φ c)⁻¹ • (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) with hl0
      have hl0app : ∀ z, l0 z = (φ z) / (u - φ c) := fun z => by
        simp [hl0, div_eq_inv_mul]
      have hl0V : ∀ v ∈ V, l0 (v - c) ≤ 1 := by
        intro v hv
        rw [hl0app, div_le_one (by linarith), map_sub]
        have := hφP v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
        linarith
      have hl0x : 1 < l0 (x - c) := by
        rw [hl0app, one_lt_div (by linarith), map_sub]; linarith
      obtain ⟨l, hl, hlx, hlspan⟩ := aux_pp_polar V c hc x _ l0 hl0V hl0x rfl
      obtain ⟨G, hG, hGsep⟩ := aux_pp_facet hd V c hcP l hl hlspan x hlx
      obtain ⟨i, hi⟩ := hq2 G hG
      have h1 := hx i
      simp only [hi] at h1
      obtain ⟨hfG, hGeq⟩ := hgf G hG
      have h2 := hGsep (g G) hGeq (f G) hfG
      linarith
  · intro i
    show (q i).1 c < (q i).2
    rcases hq1 i with h | ⟨F, hF, h⟩
    · rw [h]; simp
    · rw [h]
      simp only
      have hne : g F ≠ 0 := by
        intro h0
        have hFP : F = P := by
          rw [(hgf F hF).2, h0]; ext y; simp
        have := hF.2.2
        rw [hFP, hspan, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at this
        omega
      obtain ⟨u, hu⟩ : ∃ u, 0 < g F u := by
        by_contra hcon
        push Not at hcon
        apply hne
        ext u
        have h1 := hcon u
        have h2 := hcon (-u)
        rw [map_neg] at h2
        rw [ContinuousLinearMap.zero_apply]
        linarith
      obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
      have := hfmax F hF _ hεu
      rw [map_add, map_smul, smul_eq_mul] at this
      nlinarith

  · intro i
    rcases hq1 i with h | ⟨F, hF, h⟩
    · left
      change (q i).1 = 0
      rw [h]
    · right
      change ({y ∈ P | (q i).1 y = (q i).2}.Nonempty ∧
        IsExposed ℝ P {y ∈ P | (q i).1 y = (q i).2} ∧
        Module.finrank ℝ (affineSpan ℝ {y ∈ P | (q i).1 y = (q i).2}).direction = d - 1)
      rw [h]
      have hFlevel : F = {y ∈ P | g F y = g F (f F)} := by
        ext y
        constructor
        · intro hy
          have hy' := hy
          rw [(hgf F hF).2] at hy'
          have hff := (hgf F hF).1
          have hffP : f F ∈ P :=
            (((Set.ext_iff.mp (hgf F hF).2) (f F)).mp hff).1
          exact ⟨hy'.1, le_antisymm (hfmax F hF y hy'.1) (hy'.2 (f F) hffP)⟩
        · intro hy
          rw [(hgf F hF).2]
          refine ⟨hy.1, ?_⟩
          intro y' hy'
          rw [hy.2]
          exact hfmax F hF y' hy'
      rw [← hFlevel]
      exact hF



theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)



/-- Normalize the accepted finite facet presentation using the prescribed
interior origin. Defaults stay zero and every nondefault inequality cuts an
actual facet in the original face-count convention. -/
theorem normalized_halfspace_representation {d k : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P) (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1) :
    ∃ L : Fin (k + 1) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) := by
  obtain ⟨a, b, hrep, hstrict, hmeta⟩ := halfspace_representation_at_zero P hP hzero hf
  have hb : ∀ i, 0 < b i := by
    intro i
    simpa only [map_zero] using hstrict i
  let L : Fin (k + 1) → (Fin d → ℝ) →L[ℝ] ℝ := fun i => (b i)⁻¹ • a i
  have hL : ∀ i x, L i x = a i x / b i := by
    intro i x
    simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
  refine ⟨L, ?_, ?_⟩
  · ext x
    rw [hrep]
    change (∀ i, a i x ≤ b i) ↔ ∀ i, L i x ≤ 1
    constructor
    · intro hx i
      rw [hL, div_le_one (hb i)]
      exact hx i
    · intro hx i
      have hi := hx i
      rwa [hL, div_le_one (hb i)] at hi
  · intro i
    rcases hmeta i with hz | hf
    · left
      simp only [L, hz, smul_zero]
    · right
      have hlevel : {x ∈ P | L i x = 1} = {x ∈ P | a i x = b i} := by
        ext x
        simp only [Set.mem_setOf_eq, hL, div_eq_one_iff_eq (hb i).ne']
      rw [hlevel]
      exact hf

/-- Finiteness in exactly the original faceCount predicate. -/
theorem original_facets_finite {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}.Finite := by
  obtain ⟨⟨V, hV, _, hPV⟩, _⟩ := hP
  rw [hPV]
  simpa only [Set.Finite.coe_toFinset] using (aux_pp_finite (k := d - 1) hV.toFinset)

/-- A genuine original ray oracle supplies a boundary point, which forces a
nondefault facet inequality and hence positive facet count in positive dimension.
This is a geometric proof fact; it adds no executed program query. -/
theorem original_facet_count_pos_of_rayOracle {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) : 0 < faceCount P (d - 1) := by
  have hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ faceCount P (d - 1) + 1 := by
    split_ifs <;> omega
  obtain ⟨L, hrep, hmeta⟩ := normalized_halfspace_representation P hP hzero hf
  let v : Fin d → ℝ := fun _ => 1
  have hv : v ≠ 0 := by
    intro hz
    have hi := congrFun hz ⟨0, hd⟩
    norm_num [v] at hi
  have hq := (horacle v hv).1
  obtain ⟨_, i, hi⟩ := frontier_finite_halfspaces_active L hrep hq
  rcases hmeta i with hz | hfacet
  · rw [hz, ContinuousLinearMap.zero_apply] at hi
    norm_num at hi
  · unfold faceCount
    exact (Set.ncard_pos (original_facets_finite hP)).mpr
      ⟨{x ∈ P | L i x = 1}, hfacet⟩

/-- The original ray problem admits a normalized finite presentation indexed by
exactly its original facet count, with explicit default-or-actual-facet metadata. -/
theorem normalized_halfspaces_indexed_by_facet_count {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    0 < faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) := by
  have hm := original_facet_count_pos_of_rayOracle hd P hP hzero horacle
  have hcard : faceCount P (d - 1) - 1 + 1 = faceCount P (d - 1) := by omega
  have hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ faceCount P (d - 1) - 1 + 1 := by
    rw [if_neg (Nat.ne_of_gt hd), hcard]
  refine ⟨hm, ?_⟩
  have hrep := normalized_halfspace_representation (k := faceCount P (d - 1) - 1) P hP hzero hf
  rw [hcard] at hrep
  exact hrep




/-- A bounded normalized halfspace intersection has no nonzero common
nonpositive direction. This is a geometric certificate, not a new oracle query. -/
theorem bounded_halfspaces_nonpositive_direction {d : ℕ} {ι : Type*}
    (L : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1})
    (u : Fin d → ℝ) (hu : ∀ i, L i u ≤ 0) : u = 0 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hB
  have hR0 : 0 ≤ R := by
    have h0 : (0 : Fin d → ℝ) ∈ {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
      intro i
      simp only [map_zero, zero_le_one]
    simpa only [norm_zero] using hR 0 h0
  by_contra hne
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hne
  let t : ℝ := (R + 1) / ‖u‖
  have ht : 0 < t := div_pos (by linarith only [hR0]) hnu
  have hmem : t • u ∈ {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
    intro i
    rw [map_smul]
    change t * L i u ≤ 1
    have hle := mul_nonpos_of_nonneg_of_nonpos ht.le (hu i)
    linarith only [hle]
  have hbound := hR (t • u) hmem
  have hnorm : ‖t • u‖ = R + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    exact div_mul_cancel₀ _ hnu.ne'
  rw [hnorm] at hbound
  linarith only [hbound]

/-- Differences from one facet functional separate points, so a bounded body
needs at least dimension+one normalized inequalities. -/
theorem dimension_le_halfspace_count_pred {d n : ℕ}
    (L : Fin (n + 1) → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1}) : d ≤ n := by
  let A : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun u i => L i.succ u - L 0 u
      map_add' := by
        intro u v
        ext i
        simp only [map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c u
        ext i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hker : ∀ u, A u = 0 → u = 0 := by
    intro u hAu
    have hsame : ∀ i : Fin (n + 1), L i u = L 0 u := by
      intro i
      refine Fin.cases rfl (fun j => ?_) i
      have hj := congrFun hAu j
      change L j.succ u - L 0 u = 0 at hj
      linarith only [hj]
    by_cases hn : L 0 u ≤ 0
    · exact bounded_halfspaces_nonpositive_direction L hB u (fun i => (hsame i).trans_le hn)
    · have hneg : -u = 0 := bounded_halfspaces_nonpositive_direction L hB (-u) (by
        intro i
        rw [map_neg, hsame]
        linarith only [hn])
      exact neg_eq_zero.mp hneg
  have hinj : Function.Injective A := by
    intro u v huv
    have hz : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) hz)
  have hrank := A.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using hrank

theorem dimension_add_one_le_normalized_halfspace_count {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1}) : d + 1 ≤ m := by
  cases m with
  | zero => omega
  | succ n =>
    have hdim := dimension_le_halfspace_count_pred L hB
    omega

/-- The exact original facet count supplies the margin paying for d+1 initial
ray samples in the corrected global budget. -/
theorem dimension_add_one_le_original_facet_count {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) : d + 1 ≤ faceCount P (d - 1) := by
  obtain ⟨hm, L, hrep, _⟩ := normalized_halfspaces_indexed_by_facet_count hd P hP hzero horacle
  have hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
    rw [← hrep]
    obtain ⟨⟨V, hV, _, hPV⟩, _⟩ := hP
    rw [hPV]
    exact (hV.isCompact_convexHull (𝕜 := ℝ)).isBounded
  exact dimension_add_one_le_normalized_halfspace_count hm L hB


theorem polytope_normalized_halfspace_presentation_and_facet_lower_bound
    (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : IsPolytopeRayOracle P oracle) :
    d + 1 ≤ faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) :=
  ⟨dimension_add_one_le_original_facet_count hd P hP hzero horacle,
   (normalized_halfspaces_indexed_by_facet_count hd P hP hzero horacle).2⟩

end Grunbaum2003
end

theorem inline_solution (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : Grunbaum2003.IsPolytopeRayOracle P oracle) :
    d + 1 ≤ Grunbaum2003.faceCount P (d - 1) ∧
    ∃ L : Fin (Grunbaum2003.faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) :=
  Grunbaum2003.polytope_normalized_halfspace_presentation_and_facet_lower_bound d hd P hP hzero oracle horacle

end RayCounterfamilyInline16

namespace Grunbaum2003

theorem polytope_normalized_halfspace_presentation_and_facet_lower_bound :
∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : IsPolytopeRayOracle P oracle),
d + 1 ≤ faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) :=
  @RayCounterfamilyInline16.inline_solution

end Grunbaum2003


-- Inlined checked source: ../convex-polytopes-2026-10-31/Solutions/Sol_rayMachine_static_field_expr_and_face_lattice_encoding.lean
-- SHA256: 3d6b9494525d69d344bba998cae8d981fe3a06f61087fabc33cc6a3e788e3df6
namespace RayCounterfamilyInline17

open _root_.Grunbaum2003


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
      True) := by
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
      trivial⟩

end Grunbaum2003

theorem inline_solution :
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
      True) :=
  Grunbaum2003.rayMachine_static_field_expr_and_face_lattice_encoding_proved

end

end RayCounterfamilyInline17

namespace Grunbaum2003

theorem rayMachine_static_field_expr_and_face_lattice_encoding :
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
      True) :=
  @RayCounterfamilyInline17.inline_solution

end Grunbaum2003


-- Inlined checked source: work/Sol_exists_polygon_vertex_count.lean
-- SHA256: 67e6c59363bdfc748337b6c7f8a491643273c2fc5bed50a37057a14e81e9ef3a
namespace RayCounterfamilyInline18

open _root_.Grunbaum2003


set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003Moment
open Grunbaum2003

/-- Moment-curve point `(s, s^2, …, s^d)`. -/
def mc (d : ℕ) (s : ℝ) : Fin d → ℝ := fun i => s ^ (i.val + 1)

/-- A point of a finite set that is the unique maximiser of a linear functional is an
exposed point of the convex hull. -/
lemma isExposed_convexHull_of_strict {d : ℕ} (V : Set (Fin d → ℝ)) (a : Fin d → ℝ)
    (ha : a ∈ V) (l : StrongDual ℝ (Fin d → ℝ)) (hl : ∀ v ∈ V, v ≠ a → l v < l a) :
    IsExposed ℝ (convexHull ℝ V) {a} := by
  intro _
  refine ⟨l, ?_⟩
  have hle : convexHull ℝ V ⊆ {y | l y ≤ l a} := by
    refine convexHull_min ?_ (convex_halfSpace_le (l : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (l a))
    intro v hv
    by_cases h : v = a
    · subst h; show l v ≤ l v; exact le_rfl
    · show l v ≤ l a; exact (hl v hv h).le
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ V ha, fun y hy => hle hy⟩
  · rintro ⟨hx, hmax⟩
    have hxa : l a ≤ l x := hmax a (subset_convexHull ℝ V ha)
    have hax : l x ≤ l a := hle hx
    by_cases hW : (V \ {a}).Nonempty
    · have hV : V = insert a (V \ {a}) := by
        ext y; by_cases hy : y = a <;> simp [hy, ha]
      rw [hV, convexHull_insert hW] at hx
      obtain ⟨a', ha', w, hw, hxs⟩ := mem_convexJoin.1 hx
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      have hwlt : convexHull ℝ (V \ {a'}) ⊆ {y | l y < l a'} := by
        refine convexHull_min ?_ (convex_halfSpace_lt (l : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (l a'))
        intro v hv
        exact hl v hv.1 hv.2
      have hlw : l w < l a' := hwlt hw
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hxs
      have hlx : l (p • a' + q • w) = p * l a' + q * l w := by
        simp [map_add, map_smul, smul_eq_mul]
      have hq0 : q = 0 := by
        rw [hlx] at hxa
        have : p = 1 - q := by linarith
        subst this
        by_contra hq0
        have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
        nlinarith
      subst hq0
      have : p = 1 := by linarith
      subst this
      simp
    · have hV : V = {a} := by
        ext y; constructor
        · intro hy; by_contra hne
          exact hW ⟨y, hy, hne⟩
        · rintro rfl; exact ha
      rw [hV, convexHull_singleton] at hx
      exact hx

/-- The linear functional `x ↦ 2 t x₀ - x₁`. -/
noncomputable def lt2 (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : StrongDual ℝ (Fin d → ℝ) :=
  (2 * t) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ⟨0, by omega⟩ -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ⟨1, by omega⟩

lemma lt2_mc (d : ℕ) (hd : 2 ≤ d) (t s : ℝ) : lt2 d hd t (mc d s) = 2 * t * s - s ^ 2 := by
  simp [lt2, mc]

lemma mc_injective (d : ℕ) (hd : 1 ≤ d) : Function.Injective (mc d) := by
  intro s t h
  have := congrFun h ⟨0, by omega⟩
  simpa [mc] using this

/-- Any `k ≤ d + 1` distinct moment-curve points are affinely independent. -/
lemma affineIndependent_mc (d k : ℕ) (hk : k ≤ d + 1) (s : Fin k → ℝ)
    (hs : Function.Injective s) : AffineIndependent ℝ (fun i => mc d (s i)) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv
  have hlin : ∑ i, w i • mc d (s i) = 0 := by
    rw [← Finset.weightedVSub_eq_linear_combination _ hw0]; exact hwv
  have hvec : Matrix.vecMul w (Matrix.vandermonde s) = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · simp only [hj, pow_zero, mul_one]; exact hw0
    · have hjd : j.val - 1 < d := by omega
      have := congrFun hlin ⟨j.val - 1, hjd⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mc, Pi.zero_apply] at this
      have he : j.val - 1 + 1 = j.val := by omega
      rw [he] at this
      exact this
  have hdet : (Matrix.vandermonde s).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hs
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  exact congrFun this i

/-- The moment polytope: convex hull of `m` integer moment-curve points. -/
def mcSet (d m : ℕ) : Set (Fin d → ℝ) := Set.range (fun i : Fin m => mc d (i : ℝ))

lemma mcSet_finite (d m : ℕ) : (mcSet d m).Finite := Set.finite_range _

lemma natCast_fin_injective (m : ℕ) : Function.Injective (fun i : Fin m => ((i : ℕ) : ℝ)) := by
  intro i j h
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
  exact Fin.ext (by exact_mod_cast h')

lemma exposed_mcSet (d m : ℕ) (hd : 2 ≤ d) (a : Fin d → ℝ) :
    IsExposed ℝ (convexHull ℝ (mcSet d m)) {a} ↔ a ∈ mcSet d m := by
  constructor
  · intro h
    have hext : a ∈ Set.extremePoints ℝ (convexHull ℝ (mcSet d m)) := by
      exact h.isExtreme.mem_extremePoints
    exact extremePoints_convexHull_subset hext
  · rintro ⟨i, rfl⟩
    refine isExposed_convexHull_of_strict _ _ ⟨i, rfl⟩ (lt2 d hd (i : ℝ)) ?_
    rintro v ⟨j, rfl⟩ hne
    rw [lt2_mc, lt2_mc]
    have hij : ((j : ℕ) : ℝ) ≠ ((i : ℕ) : ℝ) := by
      intro h; apply hne; simp [h]
    have : 0 < (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2 := by
      have := sub_ne_zero.2 hij; positivity
    nlinarith

lemma exposedSet_mcSet (d m : ℕ) (hd : 2 ≤ d) :
    {x : Fin d → ℝ | IsExposed ℝ (convexHull ℝ (mcSet d m)) {x}} = mcSet d m := by
  ext a; exact exposed_mcSet d m hd a

lemma ncard_mcSet (d m : ℕ) (hd : 1 ≤ d) : (mcSet d m).ncard = m := by
  unfold mcSet
  rw [Set.ncard_range_of_injective]
  · simp
  · exact (mc_injective d hd).comp (natCast_fin_injective m)

lemma isDPolytope_mcSet (d m : ℕ) (hm : d + 1 ≤ m) : IsDPolytope (convexHull ℝ (mcSet d m)) := by
  refine ⟨⟨mcSet d m, mcSet_finite d m, ⟨mc d 0, ⟨⟨0, by omega⟩, by simp⟩⟩, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  let s : Fin (d + 1) → ℝ := fun i => ((i : ℕ) : ℝ)
  have hs : Function.Injective s := by
    intro i j h
    have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (by exact_mod_cast h')
  have hind := affineIndependent_mc d (d + 1) le_rfl s hs
  have htop : affineSpan ℝ (Set.range (fun i => mc d (s i))) = ⊤ := by
    rw [hind.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  rw [eq_top_iff, ← htop]
  apply affineSpan_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, by omega⟩, rfl⟩

lemma faceCount_zero_mcSet (d m : ℕ) (hd : 2 ≤ d) :
    faceCount (convexHull ℝ (mcSet d m)) 0 = m := by
  rw [(polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d _).1,
    exposedSet_mcSet d m hd, ncard_mcSet d m (by omega)]


end Grunbaum2003Moment

open Grunbaum2003 Grunbaum2003Moment in
theorem inline_solution (n : ℕ) :
    ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3 :=
  ⟨convexHull ℝ (mcSet 2 (n + 3)), isDPolytope_mcSet 2 (n + 3) (by omega),
    faceCount_zero_mcSet 2 (n + 3) le_rfl⟩

end RayCounterfamilyInline18

namespace Grunbaum2003

theorem exists_polygon_vertex_count :
∀ (n : ℕ),
∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3 :=
  @RayCounterfamilyInline18.inline_solution

end Grunbaum2003


set_option autoImplicit false
open scoped Pointwise Classical BigOperators Matrix

namespace Grunbaum2003

private theorem exposed_translate {d : ℕ} (P F : Set (Fin d → ℝ)) (z : Fin d → ℝ)
    (hF : IsExposed ℝ P F) : IsExposed ℝ (z +ᵥ P) (z +ᵥ F) := by
  intro hne
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy⟩
  obtain ⟨l, hl⟩ := hF hFne
  refine ⟨l, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hl] at hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro w ⟨v, hv, rfl⟩
    simpa only [vadd_eq_add, map_add, add_le_add_iff_left] using hy.2 v hv
  · rintro ⟨⟨y, hy, rfl⟩, hmax⟩
    refine ⟨y, ?_, rfl⟩
    rw [hl]
    refine ⟨hy, ?_⟩
    intro v hv
    have := hmax (z + v) ⟨v, hv, rfl⟩
    simpa only [vadd_eq_add, map_add, add_le_add_iff_left] using this

private theorem exposed_singleton_translate_iff {d : ℕ} (P : Set (Fin d → ℝ))
    (z x : Fin d → ℝ) : IsExposed ℝ (z +ᵥ P) {z + x} ↔ IsExposed ℝ P {x} := by
  constructor
  · intro h
    have := exposed_translate (z +ᵥ P) {z + x} (-z) h
    simpa using this
  · intro h
    simpa using exposed_translate P {x} z h

private theorem exposed_points_translate {d : ℕ} (P : Set (Fin d → ℝ)) (z : Fin d → ℝ) :
    {x | IsExposed ℝ (z +ᵥ P) {x}} = (fun x => z + x) '' {x | IsExposed ℝ P {x}} := by
  ext x
  constructor
  · intro hx
    refine ⟨x - z, ?_, by simp [sub_eq_add_neg]⟩
    apply (exposed_singleton_translate_iff P z (x - z)).1
    simpa [sub_eq_add_neg] using hx
  · rintro ⟨y, hy, rfl⟩
    exact (exposed_singleton_translate_iff P z y).2 hy

private theorem faceCount_zero_translate {d : ℕ} (P : Set (Fin d → ℝ)) (z : Fin d → ℝ) :
    faceCount (z +ᵥ P) 0 = faceCount P 0 := by
  rw [(polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d _).1,
    (polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d _).1,
    exposed_points_translate]
  exact Set.ncard_image_of_injective _ (add_right_injective z)

private theorem isDPolytope_translate {d : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P) (z : Fin d → ℝ) : IsDPolytope (z +ᵥ P) := by
  obtain ⟨⟨V, hVfin, hVne, rfl⟩, htop⟩ := hP
  refine ⟨⟨z +ᵥ V, ?_, ?_, (convexHull_vadd z V).symm⟩, ?_⟩
  · exact hVfin.image _
  · exact hVne.image _
  · apply (by
      exact ((convex_convexHull ℝ V).vadd z).interior_nonempty_iff_affineSpan_eq_top.1)
    obtain ⟨x, hx⟩ := (convex_convexHull ℝ V).interior_nonempty_iff_affineSpan_eq_top.2 htop
    refine ⟨z + x, ?_⟩
    rw [interior_vadd]
    exact ⟨x, hx, rfl⟩

theorem exists_centered_polygon_vertex_count (n : ℕ) :
    ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧
      (0 : Fin 2 → ℝ) ∈ interior P ∧ faceCount P 0 = n + 3 := by
  obtain ⟨P, hP, hcard⟩ := exists_polygon_vertex_count n
  have hconv : Convex ℝ P := by
    obtain ⟨V, hfin, hne, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  obtain ⟨z, hz⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.2 hP.2
  refine ⟨(-z) +ᵥ P, isDPolytope_translate P hP (-z), ?_, ?_⟩
  · rw [interior_vadd]
    exact ⟨z, hz, neg_add_cancel z⟩
  · rw [faceCount_zero_translate, hcard]


/-- Radial projection through the Minkowski gauge supplies a valid ray oracle
for every full-dimensional polytope containing zero in its interior. -/
theorem exists_polytope_ray_oracle {d : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P) (hzero : (0 : Fin d → ℝ) ∈ interior P) :
    ∃ oracle : (Fin d → ℝ) → Fin d → ℝ, IsPolytopeRayOracle P oracle := by
  have hconv : Convex ℝ P := by
    obtain ⟨V, hfin, hne, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  have hcompact : IsCompact P := by
    obtain ⟨V, hfin, hne, rfl⟩ := hP.1
    exact hfin.isCompact_convexHull ℝ
  have habs : Absorbent ℝ P := absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hzero)
  have hb : Bornology.IsVonNBounded ℝ P := hcompact.isVonNBounded ℝ
  refine ⟨fun v => (gauge P v)⁻¹ • v, ?_⟩
  intro v hv
  have hg : 0 < gauge P v := (gauge_pos habs hb).2 hv
  refine ⟨mem_frontier_of_gauge_eq_one hconv (interior_subset hzero) habs ?_,
    (gauge P v)⁻¹, inv_pos.2 hg, rfl⟩
  rw [gauge_smul_of_nonneg (inv_nonneg.2 hg.le)]
  simp [hg.ne']


/-- Arbitrarily large centered polygons with the exact finite facet, face, and
vertex metadata required by the ray reconstruction leaf. -/
theorem exists_ray_input_polygon (n : ℕ) :
    ∃ (P : Set (Fin 2 → ℝ)) (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ)
      (L : Fin (faceCount P (2 - 1)) → (Fin 2 → ℝ) →L[ℝ] ℝ)
      (V : Finset (Fin 2 → ℝ)),
      IsDPolytope P ∧ (0 : Fin 2 → ℝ) ∈ interior P ∧
      IsPolytopeRayOracle P oracle ∧
      2 + 1 ≤ faceCount P (2 - 1) ∧
      P = {x | ∀ i, L i x ≤ 1} ∧
      (∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = 2 - 1)) ∧
      (∃ m : ℕ, Nonempty (Fin m ≃ PolytopeFace P)) ∧

      (V : Set (Fin 2 → ℝ)) = P.extremePoints ℝ ∧
      (V : Set (Fin 2 → ℝ)) = {x : Fin 2 → ℝ | IsExposed ℝ P {x}} ∧
      V.card = faceCount P 0 ∧ faceCount P 0 = n + 3 := by
  classical
  obtain ⟨P, hP, hzero, hcard⟩ := exists_centered_polygon_vertex_count n
  obtain ⟨oracle, horacle⟩ := exists_polytope_ray_oracle P hP hzero
  obtain ⟨hfacets, L, hrep, hfacemeta⟩ :=
    polytope_normalized_halfspace_presentation_and_facet_lower_bound 2 (by omega) P hP
      hzero oracle horacle
  have hfaces := polytope_face_eq_convexHull_exposed_vertices 2 P hP
  have hfinite := (rayMachine_static_field_expr_and_face_lattice_encoding.2 hfaces.2).2.1 hfaces.1
  let vertices : Set (Fin 2 → ℝ) := {x | IsExposed ℝ P {x}}
  let V : Finset (Fin 2 → ℝ) := hfaces.1.toFinset
  have hV : (V : Set (Fin 2 → ℝ)) = vertices := hfaces.1.coe_toFinset
  have hPeq : P = convexHull ℝ vertices := by
    have h := hfaces.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ vertices) at h
    have hvP : vertices ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
    rwa [Set.inter_eq_self_of_subset_right hvP] at h
  have hext : P.extremePoints ℝ = vertices := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hPeq] at hx
      exact extremePoints_convexHull_subset hx
    · intro x hx
      exact hx.isExtreme.mem_extremePoints
  refine ⟨P, oracle, L, V, hP, hzero, horacle, hfacets, hrep, hfacemeta, hfinite,
    hV.trans hext.symm, hV, ?_, hcard⟩
  rw [(polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 2 P).1]
  exact (Set.ncard_coe_finset V).symm.trans (congrArg Set.ncard hV)



/-- Every finite set has a certification-only enumeration by fresh insertions. -/
theorem rayResolve_fresh_insertion_trace {E : Type*} (V : Finset E) :
    ∃ C : ℕ → Finset E, C 0 = ∅ ∧ C V.card = V ∧
      ∀ s < V.card, ∃ v ∈ V, v ∉ C s ∧ C (s + 1) = insert v (C s) := by
  classical
  let e : Fin V.card ≃ V := (Fintype.equivFinOfCardEq (by simp)).symm
  let C : ℕ → Finset E := fun t =>
    (Finset.univ.filter (fun i : Fin V.card => i.val < t)).image (fun i => (e i).val)
  have hCmem (x : E) (t : ℕ) : x ∈ C t ↔
      ∃ i : Fin V.card, i.val < t ∧ (e i).val = x := by
    simp only [C, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  have hzero : C 0 = ∅ := by
    ext x
    simp only [hCmem, Finset.notMem_empty, iff_false, not_exists, not_and]
    intro i hi
    omega
  have hfull : C V.card = V := by
    ext x
    rw [hCmem]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).isLt,
        congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  refine ⟨C, hzero, hfull, fun s hs => ?_⟩
  let j : Fin V.card := ⟨s, hs⟩
  let v : E := (e j).val
  have hnot : v ∉ C s := by
    rw [hCmem]
    rintro ⟨i, hi, heq⟩
    have hij : i = j := e.injective (Subtype.ext heq)
    have hval := congrArg Fin.val hij
    dsimp [j] at hval
    omega
  refine ⟨v, (e j).property, hnot, ?_⟩
  ext x
  rw [hCmem, Finset.mem_insert, hCmem]
  constructor
  · rintro ⟨i, hi, heq⟩
    by_cases his : i.val < s
    · exact Or.inr ⟨i, his, heq⟩
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      left
      simpa [v, hij] using heq.symm
  · rintro (hx | ⟨i, hi, heq⟩)
    · exact ⟨j, by dsimp [j]; omega, hx.symm⟩
    · exact ⟨i, by omega, heq⟩

/-- All trace premises of the remaining ray-program leaf allow zero budgets:
start from the complete facet set and certify the old vertices one by one. -/
theorem rayResolve_zero_budget_complete_facet_trace {d m : ℕ}
    (P : Set (Fin d → ℝ))
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hrep : P = {x | ∀ i, L i x ≤ 1})
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (V : Finset (Fin d → ℝ))
    (hV : (V : Set (Fin d → ℝ)) = P.extremePoints ℝ) :
    ∃ (N : ℕ) (S_seq : ℕ → Finset (Fin m))
      (C_seq : ℕ → Finset (Fin d → ℝ)) (q_seq : ℕ → ℕ),
      C_seq 0 = ∅ ∧ q_seq 0 ≤ d + 1 ∧
      (∀ s < N,
        (S_seq (s + 1) = S_seq s ∧
          ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
            v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
            q_seq (s + 1) ≤ q_seq s + 1) ∨
        (C_seq (s + 1) = C_seq s ∧
          ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
            oracle v ≠ v ∧ ∃ i_new : Fin m,
              L i_new (oracle v) = 1 ∧
              S_seq (s + 1) = insert i_new (S_seq s) ∧
              q_seq (s + 1) ≤ q_seq s +
                (1 + (d - 1) * (2 * (m - (S_seq s).card) + 3)))) ∧
      {x : Fin d → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P ∧
      C_seq N = V ∧ (∀ s, q_seq s = 0) := by
  classical
  obtain ⟨C, hC0, hCN, hstep⟩ := rayResolve_fresh_insertion_trace V
  refine ⟨V.card, fun _ => Finset.univ, C, fun _ => 0, hC0, by simp, ?_, ?_, hCN,
    fun _ => rfl⟩
  · intro s hs
    obtain ⟨v, hvV, hvC, hCnext⟩ := hstep s hs
    have hvExt : v ∈ P.extremePoints ℝ := by rw [← hV]; exact hvV
    left
    refine ⟨rfl, v, ?_, hvExt.1, hvC, ?_, by simp⟩
    · have houter : {x : Fin d → ℝ | ∀ i ∈ (Finset.univ : Finset (Fin m)), L i x ≤ 1} = P := by
        simpa only [Finset.mem_univ, forall_const] using hrep.symm
      exact houter.symm ▸ hvExt
    · ext x
      simpa only [Finset.mem_insert] using (Finset.ext_iff.mp hCnext x)
  · simpa only [Finset.mem_univ, forall_const] using hrep.symm


/-- The exact conclusion of the unresolved ray-program leaf fails for the
allowed header family consisting of one halt per vertex. The finite program is
quantified before the input polygon, whose vertex count is unbounded.
This theorem does not instantiate the preceding gadget hypotheses of that leaf. -/
theorem ray_counterfamily_no_uniform_specialized_suffix
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration) :
    ¬ (∃ program : List RayInstruction,
      ∀ P : Set (Fin 2 → ℝ), IsDPolytope P → (0 : Fin 2 → ℝ) ∈ interior P →
        ∀ oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ), IsPolytopeRayOracle P oracle →
          2 + 1 ≤ faceCount P (2 - 1) →
          ∀ (L : Fin (faceCount P (2 - 1)) → (Fin 2 → ℝ) →L[ℝ] ℝ),
            P = {x | ∀ i, L i x ≤ 1} →
            (∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = 2 - 1)) →
            (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
            ∀ (V : Finset (Fin 2 → ℝ))
              (N : ℕ)
              (S_seq : ℕ → Finset (Fin (faceCount P (2 - 1))))
              (C_seq : ℕ → Finset (Fin 2 → ℝ))
              (q_seq : ℕ → ℕ),
              (V : Set (Fin 2 → ℝ)) = P.extremePoints ℝ →
              (V : Set (Fin 2 → ℝ)) = {x : Fin 2 → ℝ | IsExposed ℝ P {x}} →
              V.card = faceCount P 0 →
              C_seq 0 = ∅ →
              q_seq 0 ≤ 2 + 1 →
              (∀ s < N,
                (S_seq (s + 1) = S_seq s ∧
                  ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s + 1) ∨
                (C_seq (s + 1) = C_seq s ∧
                  ∃ v ∈ ({x : Fin 2 → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    oracle v ≠ v ∧
                    ∃ i_new : Fin (faceCount P (2 - 1)),
                      L i_new (oracle v) = 1 ∧
                      S_seq (s + 1) = insert i_new (S_seq s) ∧
                      q_seq (s + 1) ≤ q_seq s +
                        (1 + (2 - 1) * (2 * (faceCount P (2 - 1) - (S_seq s).card) + 3)))) →
              {x : Fin 2 → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P →
              C_seq N = V →
              ∃ (n : ℕ) (e : Fin n ≃ PolytopeFace P)
                (vEnum : Fin (faceCount P 0) ≃ {x : Fin 2 → ℝ | IsExposed ℝ P {x}})
                (pre : List RayInstruction) (t_pre : ℕ) (c_pre : RayConfiguration)
                (fvBase minBase : ℤ),
                program = pre ++
                  ((fun (_ V : ℕ) (_ _ : ℤ) => List.replicate V RayInstruction.halt) n (faceCount P 0) fvBase minBase).map
                    (relocateInst pre.length) ∧
                rayMachineRun program oracle t_pre
                  { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
                    some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) ∧
                c_pre.queries ≤ q_seq N ∧
                ∀ (a : Fin n) (k : Fin (faceCount P 0)),
                  c_pre.tape (fvBase + (a.val : ℤ) * ((faceCount P 0 : ℕ) : ℤ) + (k.val : ℤ)) =
                    if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0) := by
  rintro ⟨program, hprogram⟩
  obtain ⟨P, oracle, L, V, hP, hzero, horacle, hfacets, hrep, hfacemeta,
    hfinite, hVext, hVexp, hVcard, hcard⟩ := exists_ray_input_polygon program.length
  obtain ⟨N, S, C, q, hC0, hq0, hstep, hterminal, hCV, _⟩ :=
    rayResolve_zero_budget_complete_facet_trace P L hrep oracle V hVext
  obtain ⟨n, e, vEnum, pre, t, c, fv, minBase, hprog, _⟩ :=
    hprogram P hP hzero oracle horacle hfacets L hrep hfacemeta hfinite
      V N S C q hVext hVexp hVcard hC0 hq0 hstep hterminal hCV
  have hlength := congrArg List.length hprog
  simp only [List.length_append, List.length_map, List.length_replicate] at hlength
  omega

end Grunbaum2003

open Grunbaum2003 in
theorem solution :
¬ (∀ (d : ℕ) (hd : 2 ≤ d)
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (innerSampleProgram : ℕ → List RayInstruction)
    (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ)
    (hInnerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
      ∃ c : RayConfiguration,
        rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
          {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
        c.pc = (d + 1) * (d + 2) + 2 ∧
        (innerSampleProgram d)[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = q + (d + 1) ∧
        (∀ i : Fin (d + 1), ∀ j : Fin d,
          c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
        (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z))
    (frameCramerCoefficients : Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
    (frameNormal : Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ)
    (hFrameNormal : ∀ (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
      frameNormal v x = ∑ k, frameCramerCoefficients v k * x k)
    (hLocalSlack : ∀ {k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M))
    (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
    (hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
        ∀ z : ℤ, z < dst → c'.tape z = source z)
    (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
    (hPerturbedQueryComp : ∀ (pre : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ),
      rayMachineRun (pre ++
          (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      (fun i : Fin d =>
        c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries + 1 ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              c_pre.tape (pBase + (j.val : ℤ)) +
                c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z))
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerWritesRow : ∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
      (S : Finset (Fin m)),
      (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        v.det ≠ 0 ∧ ∃ i_new : Fin m,
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          ∀ x : Fin d → ℝ,
            ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ)
        (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      ∀ (p p₀ : Fin d → ℝ),
        LinearIndependent ℝ
          (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ i : Fin d,
          (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P) →
        p ∈ frontier P →
        p = ∑ i : Fin d,
          w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ (c' : RayConfiguration) (i_new : Fin m),
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ x : Fin d → ℝ,
            ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointComp : ∀ (pre : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixComp : ∀ {m V : ℕ} (pre : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z))
    (hFrameCramer : ∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x))
    (hFrameInit : ∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x | ∀ i, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∀ (S : Finset (Fin m)) {v : Fin d → ℝ},
            v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
            oracle v ≠ v →
            let p₀ := oracle v
            let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
            let w₁ : Fin 1 → ℝ := fun _ => 1
            v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
              LinearIndependent ℝ v₁ ∧
              (∀ i : Fin 1, 0 < w₁ i) ∧
              (∑ i : Fin 1, w₁ i = 1) ∧
              p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
              (∀ i : Fin 1, v₁ i ∈ P) ∧
              (∀ j ∈ S, L j p₀ < 1) ∧
              (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1))
    (hAxisCoord : ∀ {r : ℕ} {P : Set (Fin d → ℝ)}, (0 : Fin d → ℝ) ∈ interior P →
      ∀ (v : Fin r → Fin d → ℝ), LinearIndependent ℝ v → r < d →
        ∀ (w : Fin r → ℝ) (p : Fin d → ℝ),
          p ∈ frontier P → p = ∑ i : Fin r, w i • v i →
          ∃ (i_axis j_coord : Fin d),
            Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
            j_coord ≠ i_axis ∧
            p j_coord ≠ 0)
    (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
    (secondQueryProgram firstMidpointProgram referenceWalkProgram : List RayInstruction),
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          d + 1 ≤ faceCount P (d - 1) →
          ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
            P = {x | ∀ i, L i x ≤ 1} →
            (∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1)) →
            (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
            ∀ (V : Finset (Fin d → ℝ))
              (N : ℕ)
              (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
              (C_seq : ℕ → Finset (Fin d → ℝ))
              (q_seq : ℕ → ℕ),
              (V : Set (Fin d → ℝ)) = P.extremePoints ℝ →
              (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
              V.card = faceCount P 0 →
              C_seq 0 = ∅ →
              q_seq 0 ≤ d + 1 →
              (∀ s < N,
                (S_seq (s + 1) = S_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s + 1) ∨
                (C_seq (s + 1) = C_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    oracle v ≠ v ∧
                    ∃ i_new : Fin (faceCount P (d - 1)),
                      L i_new (oracle v) = 1 ∧
                      S_seq (s + 1) = insert i_new (S_seq s) ∧
                      q_seq (s + 1) ≤ q_seq s +
                        (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
              {x : Fin d → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P →
              C_seq N = V →
              ∃ (n : ℕ) (e : Fin n ≃ PolytopeFace P)
                (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
                (pre : List RayInstruction) (t_pre : ℕ) (c_pre : RayConfiguration)
                (fvBase minBase : ℤ),
                program = pre ++
                  (headerAndInclusionTableProgram n (faceCount P 0) fvBase minBase).map
                    (relocateInst pre.length) ∧
                rayMachineRun program oracle t_pre
                  { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
                    some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) ∧
                c_pre.queries ≤ q_seq N ∧
                ∀ (a : Fin n) (k : Fin (faceCount P 0)),
                  c_pre.tape (fvBase + (a.val : ℤ) * ((faceCount P 0 : ℕ) : ℤ) + (k.val : ℤ)) =
                    if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0) := by
  intro hLeaf
  obtain ⟨⟨run_add, _, _⟩, _⟩ := rayMachine_static_field_expr_and_face_lattice_encoding
  obtain ⟨⟨relocateInst, relocateCfg, hRel⟩, _⟩ := rayMachine_relocate_and_section_query_adapter
  obtain ⟨_, _, _, _, _, _, innerSampleProgram, queryVector, _, _, _, _, _, _, _, hInner⟩ :=
    rayMachine_inner_simplex_and_signed_direction_program
  obtain ⟨stepEpsProgram, stepEpsDest, stepEpsSteps, hStepEps⟩ :=
    rayMachine_known_facet_step_eps_program
  obtain ⟨perturbedRayQueryProgram, perturbedRayQueryDest, perturbedRayQuerySteps, hPerturbed⟩ :=
    rayMachine_vector_eval_and_perturbed_ray_query_program
  obtain ⟨cramerRowProgram, cramerRowDest, cramerRowSteps,
    midpointVecProgram, midpointVecDest, midpointVecSteps, hCramer, hMidpoint⟩ :=
    rayMachine_cramer_facet_row_and_midpoint_programs
  obtain ⟨incMatProg, incMatDest, incMatSteps, incMatPC, hIncMat⟩ :=
    rayMachine_facet_vertex_incidence_matrix_program
  obtain ⟨hPertComp, hMidComp, hCramRow, hIncComp⟩ :=
    rayMachine_perturbed_midpoint_cramer_and_incidence_composition 2
  have hInit := rayFrame_init_extension_axis_and_step_eps_composition 2 (by omega)
  have hGad := rayMachine_relocated_discovery_gadgets_and_frame_cramer 2
  apply ray_counterfamily_no_uniform_specialized_suffix relocateInst relocateCfg
  exact hLeaf 2 (by omega) run_add relocateInst relocateCfg (hRel 2)
    innerSampleProgram queryVector (fun oracle tape q => by
      obtain ⟨c, h1, h2, h3, h4, h5, h6, _, _, h9⟩ := hInner 2 (by omega) oracle tape q
      exact ⟨c, h1, h2, h3, h4, h5, h6, h9⟩)
    (fun _ _ => 0) (fun _ => 0) (fun _ _ => by simp)
    (@rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.1 2)
    stepEpsProgram stepEpsDest stepEpsSteps hStepEps
    perturbedRayQueryProgram perturbedRayQueryDest perturbedRayQuerySteps
    (hPertComp run_add relocateInst relocateCfg (hRel 2)
      perturbedRayQueryProgram perturbedRayQueryDest perturbedRayQuerySteps hPerturbed)
    cramerRowProgram cramerRowDest cramerRowSteps
    (fun L S hFC2 => hCramRow L S hFC2 cramerRowProgram cramerRowDest cramerRowSteps hCramer)
    midpointVecProgram midpointVecDest midpointVecSteps
    (hMidComp run_add relocateInst relocateCfg (hRel 2)
      midpointVecProgram midpointVecDest midpointVecSteps hMidpoint)
    incMatProg incMatDest incMatSteps incMatPC
    (fun pre oracle t_pre c_pre lBase xBase minBase =>
      hIncComp run_add relocateInst relocateCfg (hRel 2)
        incMatProg incMatDest incMatSteps incMatPC hIncMat
        pre oracle t_pre c_pre lBase xBase minBase)
    hGad.2.2.2 hInit.2.1 hInit.2.2.1
    (fun (_ V : ℕ) (_ _ : ℤ) => List.replicate V RayInstruction.halt) [] [] []
