-- Prove2me | solution 1 for Grunbaum2003.rayMachine_relocate_and_section_query_adapter
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:16:02.758037+00:00
-- url     : https://prove2.me/submissions/5c2c1cc8-00ab-4d6f-b0dc-39bf83f51edb

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

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

theorem solution :
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
