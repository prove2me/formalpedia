-- Prove2me | solution 3 for Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:49:30.431823+00:00
-- url     : https://prove2.me/submissions/53c88c84-72ff-45c1-97fd-98c169bbcdae

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Theorems.Thm_Grunbaum2003_polytope_normalized_halfspace_presentation_and_facet_lower_bound
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_ray_oracle_outer_polytope_invariants_and_phased_trace_bound
import Theorems.Thm_Grunbaum2003_rayMachine_static_field_expr_and_face_lattice_encoding
import Theorems.Thm_Grunbaum2003_repaired_ray_query_budget_bound
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
open scoped BigOperators

/-! ### Module: Ray.Machine -/

namespace Grunbaum2003
namespace RayAlg

/-! ## Layer A: a structured language for the ray machine -/

/-- Tape-level state: everything in a configuration except the program counter. -/
structure TS where
  head : ℤ
  tape : ℤ → ℝ
  queries : ℕ

def TS.cfg (s : TS) (pc : ℕ) : RayConfiguration := ⟨pc, s.head, s.tape, s.queries⟩

inductive Cmd where
  | const (dst : ℤ) (v : ℚ)
  | add (dst a b : ℤ)
  | sub (dst a b : ℤ)
  | mul (dst a b : ℤ)
  | div (dst a b : ℤ)
  | shift (off : ℤ)
  | query
  | skip
  | seq (c₁ c₂ : Cmd)
  | ite (a : ℤ) (cn cz cp : Cmd)
  | while (a : ℤ) (body : Cmd)

def queryVec (d : ℕ) (s : TS) : Fin d → ℝ := fun i => s.tape (s.head + (i.val : ℤ))

noncomputable def queryTape {d : ℕ} (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (s : TS) : ℤ → ℝ :=
  fun j =>
    if h : 0 ≤ j - s.head ∧ j - s.head < (d : ℤ) then
      oracle (queryVec d s) ⟨(j - s.head).toNat, by omega⟩
    else s.tape j

inductive Cmd.Exec {d : ℕ} (oracle : (Fin d → ℝ) → (Fin d → ℝ)) : Cmd → TS → TS → Prop
  | const (dst : ℤ) (v : ℚ) (s : TS) :
      Exec oracle (.const dst v) s
        ⟨s.head, Function.update s.tape (s.head + dst) (v : ℝ), s.queries⟩
  | add (dst a b : ℤ) (s : TS) :
      Exec oracle (.add dst a b) s
        ⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) + s.tape (s.head + b)), s.queries⟩
  | sub (dst a b : ℤ) (s : TS) :
      Exec oracle (.sub dst a b) s
        ⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) - s.tape (s.head + b)), s.queries⟩
  | mul (dst a b : ℤ) (s : TS) :
      Exec oracle (.mul dst a b) s
        ⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) * s.tape (s.head + b)), s.queries⟩
  | div (dst a b : ℤ) (s : TS) (h : s.tape (s.head + b) ≠ 0) :
      Exec oracle (.div dst a b) s
        ⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) / s.tape (s.head + b)), s.queries⟩
  | shift (off : ℤ) (s : TS) :
      Exec oracle (.shift off) s ⟨s.head + off, s.tape, s.queries⟩
  | query (s : TS) (h : queryVec d s ≠ 0) :
      Exec oracle .query s
        ⟨s.head, queryTape oracle s, s.queries + 1⟩
  | skip (s : TS) : Exec oracle .skip s s
  | seq {c₁ c₂ : Cmd} {s m s' : TS} :
      Exec oracle c₁ s m → Exec oracle c₂ m s' → Exec oracle (.seq c₁ c₂) s s'
  | ite_neg {a : ℤ} {cn cz cp : Cmd} {s s' : TS} :
      s.tape (s.head + a) < 0 → Exec oracle cn s s' → Exec oracle (.ite a cn cz cp) s s'
  | ite_zero {a : ℤ} {cn cz cp : Cmd} {s s' : TS} :
      s.tape (s.head + a) = 0 → Exec oracle cz s s' → Exec oracle (.ite a cn cz cp) s s'
  | ite_pos {a : ℤ} {cn cz cp : Cmd} {s s' : TS} :
      0 < s.tape (s.head + a) → Exec oracle cp s s' → Exec oracle (.ite a cn cz cp) s s'
  | while_done {a : ℤ} {body : Cmd} {s : TS} :
      s.tape (s.head + a) = 0 → Exec oracle (.while a body) s s
  | while_step {a : ℤ} {body : Cmd} {s m s' : TS} :
      s.tape (s.head + a) ≠ 0 → Exec oracle body s m → Exec oracle (.while a body) m s' →
      Exec oracle (.while a body) s s'

def Cmd.size : Cmd → ℕ
  | .const _ _ => 1
  | .add _ _ _ => 1
  | .sub _ _ _ => 1
  | .mul _ _ _ => 1
  | .div _ _ _ => 1
  | .shift _ => 1
  | .query => 1
  | .skip => 0
  | .seq a b => a.size + b.size
  | .ite _ n z p => 1 + n.size + 1 + z.size + 1 + p.size
  | .while _ b => 1 + b.size + 1

def Cmd.code : Cmd → ℕ → List RayInstruction
  | .const dst v, p => [.constant dst v (p + 1)]
  | .add dst a b, p => [.add dst a b (p + 1)]
  | .sub dst a b, p => [.sub dst a b (p + 1)]
  | .mul dst a b, p => [.mul dst a b (p + 1)]
  | .div dst a b, p => [.div dst a b (p + 1)]
  | .shift off, p => [.shift off (p + 1)]
  | .query, p => [.query (p + 1)]
  | .skip, _ => []
  | .seq a b, p => a.code p ++ b.code (p + a.size)
  | .ite a n z q, p =>
      [.branch a (p + 1) (p + 1 + n.size + 1) (p + 1 + n.size + 1 + z.size + 1)] ++
        (n.code (p + 1) ++
          ([.shift 0 (p + 1 + n.size + 1 + z.size + 1 + q.size)] ++
            (z.code (p + 1 + n.size + 1) ++
              ([.shift 0 (p + 1 + n.size + 1 + z.size + 1 + q.size)] ++
                q.code (p + 1 + n.size + 1 + z.size + 1)))))
  | .while a b, p =>
      [.branch a (p + 1) (p + 1 + b.size + 1) (p + 1)] ++ (b.code (p + 1) ++ [.shift 0 p])

theorem Cmd.code_length : ∀ (c : Cmd) (p : ℕ), (c.code p).length = c.size
  | .const _ _, _ => rfl
  | .add _ _ _, _ => rfl
  | .sub _ _ _, _ => rfl
  | .mul _ _ _, _ => rfl
  | .div _ _ _, _ => rfl
  | .shift _, _ => rfl
  | .query, _ => rfl
  | .skip, _ => rfl
  | .seq a b, p => by
      simp [Cmd.code, Cmd.size, Cmd.code_length a, Cmd.code_length b]
  | .ite a n z q, p => by
      simp [Cmd.code, Cmd.size, Cmd.code_length n, Cmd.code_length z, Cmd.code_length q]
      omega
  | .while a b, p => by
      simp [Cmd.code, Cmd.size, Cmd.code_length b]
      omega

/-- `prog` contains the instruction list `l` starting at address `p`. -/
def Has (prog : List RayInstruction) (p : ℕ) (l : List RayInstruction) : Prop :=
  ∀ i (h : i < l.length), prog[p + i]? = some l[i]

theorem has_append {prog : List RayInstruction} {p : ℕ} {l₁ l₂ : List RayInstruction} :
    Has prog p (l₁ ++ l₂) ↔ Has prog p l₁ ∧ Has prog (p + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rw [this, List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [← Nat.add_assoc] at this
      rw [this, List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hlt : i < l₁.length
    · rw [h₁ i hlt, List.getElem_append_left hlt]
    · have hi' : i - l₁.length < l₂.length := by
        simp at hi; omega
      have := h₂ (i - l₁.length) hi'
      have e : p + l₁.length + (i - l₁.length) = p + i := by omega
      rw [e] at this
      rw [this, List.getElem_append_right (by omega)]

theorem has_singleton {prog : List RayInstruction} {p : ℕ} {x : RayInstruction} :
    Has prog p [x] ↔ prog[p]? = some x := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h i hi
    have : i = 0 := by simpa using hi
    subst this
    simpa using h

theorem has_self (l : List RayInstruction) (post : List RayInstruction) :
    Has (l ++ post) 0 l := by
  intro i hi
  simp [List.getElem?_append_left hi]

/-! ### Running -/

theorem run_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp [rayMachineRun]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [rayMachineRun]
    cases hs : rayMachineStep program oracle c with
    | none => simp
    | some c₁ => simp [ih]

theorem run_trans {d : ℕ} {program : List RayInstruction}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} {a b : ℕ} {c c₁ c₂ : RayConfiguration}
    (h₁ : rayMachineRun program oracle a c = some c₁)
    (h₂ : rayMachineRun program oracle b c₁ = some c₂) :
    rayMachineRun program oracle (a + b) c = some c₂ := by
  rw [run_add, h₁]; simpa using h₂

theorem run_one {d : ℕ} {program : List RayInstruction}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} {c c₁ : RayConfiguration}
    (h : rayMachineStep program oracle c = some c₁) :
    rayMachineRun program oracle 1 c = some c₁ := by
  simp [rayMachineRun, h]

section Steps
variable {d : ℕ} {prog : List RayInstruction} {oracle : (Fin d → ℝ) → Fin d → ℝ}

theorem step_const {p : ℕ} {s : TS} {dst : ℤ} {v : ℚ} {next : ℕ}
    (h : prog[p]? = some (.constant dst v next)) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, Function.update s.tape (s.head + dst) (v : ℝ), s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_add {p : ℕ} {s : TS} {dst a b : ℤ} {next : ℕ}
    (h : prog[p]? = some (.add dst a b next)) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) + s.tape (s.head + b)), s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_sub {p : ℕ} {s : TS} {dst a b : ℤ} {next : ℕ}
    (h : prog[p]? = some (.sub dst a b next)) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) - s.tape (s.head + b)), s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_mul {p : ℕ} {s : TS} {dst a b : ℤ} {next : ℕ}
    (h : prog[p]? = some (.mul dst a b next)) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) * s.tape (s.head + b)), s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_div {p : ℕ} {s : TS} {dst a b : ℤ} {next : ℕ}
    (h : prog[p]? = some (.div dst a b next)) (hb : s.tape (s.head + b) ≠ 0) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, Function.update s.tape (s.head + dst) (s.tape (s.head + a) / s.tape (s.head + b)), s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h, hb]

theorem step_shift {p : ℕ} {s : TS} {off : ℤ} {next : ℕ}
    (h : prog[p]? = some (.shift off next)) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head + off, s.tape, s.queries⟩ : TS) next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_jump {p : ℕ} {s : TS} {next : ℕ}
    (h : prog[p]? = some (.shift 0 next)) :
    rayMachineStep prog oracle (s.cfg p) = some (s.cfg next) := by
  simp [rayMachineStep, TS.cfg, h]

theorem step_branch_neg {p : ℕ} {s : TS} {a : ℤ} {n z q : ℕ}
    (h : prog[p]? = some (.branch a n z q)) (ha : s.tape (s.head + a) < 0) :
    rayMachineStep prog oracle (s.cfg p) = some (s.cfg n) := by
  simp [rayMachineStep, TS.cfg, h, ha]

theorem step_branch_zero {p : ℕ} {s : TS} {a : ℤ} {n z q : ℕ}
    (h : prog[p]? = some (.branch a n z q)) (ha : s.tape (s.head + a) = 0) :
    rayMachineStep prog oracle (s.cfg p) = some (s.cfg z) := by
  simp [rayMachineStep, TS.cfg, h, ha]

theorem step_branch_pos {p : ℕ} {s : TS} {a : ℤ} {n z q : ℕ}
    (h : prog[p]? = some (.branch a n z q)) (ha : 0 < s.tape (s.head + a)) :
    rayMachineStep prog oracle (s.cfg p) = some (s.cfg q) := by
  have h1 : ¬ s.tape (s.head + a) < 0 := not_lt.2 ha.le
  have h2 : ¬ s.tape (s.head + a) = 0 := ha.ne'
  simp [rayMachineStep, TS.cfg, h, h1, h2]

theorem step_query {p : ℕ} {s : TS} {next : ℕ}
    (h : prog[p]? = some (.query next)) (hv : queryVec d s ≠ 0) :
    rayMachineStep prog oracle (s.cfg p) =
      some (TS.cfg (⟨s.head, queryTape oracle s, s.queries + 1⟩ : TS) next) := by
  have hv' : ¬ (fun i : Fin d => s.tape (s.head + (i.val : ℤ))) = 0 := hv
  simp only [rayMachineStep, TS.cfg, h, hv']
  simp only [if_false, Option.some.injEq, RayConfiguration.mk.injEq, true_and, and_true]
  funext j
  rfl

end Steps

/-- Compiler correctness: a big-step execution is realized by the machine. -/
theorem Cmd.exec_run {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ} {prog : List RayInstruction}
    {c : Cmd} {s s' : TS} (hx : Cmd.Exec oracle c s s') :
    ∀ p, Has prog p (c.code p) →
      ∃ t, rayMachineRun prog oracle t (s.cfg p) = some (s'.cfg (p + c.size)) := by
  induction hx with
  | const dst v s =>
    intro p hp
    exact ⟨1, run_one (step_const (has_singleton.1 hp))⟩
  | add dst a b s =>
    intro p hp
    exact ⟨1, run_one (step_add (has_singleton.1 hp))⟩
  | sub dst a b s =>
    intro p hp
    exact ⟨1, run_one (step_sub (has_singleton.1 hp))⟩
  | mul dst a b s =>
    intro p hp
    exact ⟨1, run_one (step_mul (has_singleton.1 hp))⟩
  | div dst a b s h =>
    intro p hp
    exact ⟨1, run_one (step_div (has_singleton.1 hp) h)⟩
  | shift off s =>
    intro p hp
    exact ⟨1, run_one (step_shift (has_singleton.1 hp))⟩
  | query s h =>
    intro p hp
    exact ⟨1, run_one (step_query (has_singleton.1 hp) h)⟩
  | skip s =>
    intro p _
    exact ⟨0, by simp [rayMachineRun, Cmd.size]⟩
  | @seq c₁ c₂ s m s' _ _ ih₁ ih₂ =>
    intro p hp
    simp only [Cmd.code] at hp
    rw [has_append, Cmd.code_length] at hp
    obtain ⟨t₁, h₁⟩ := ih₁ p hp.1
    obtain ⟨t₂, h₂⟩ := ih₂ (p + c₁.size) hp.2
    refine ⟨t₁ + t₂, ?_⟩
    have := run_trans h₁ h₂
    simpa [Cmd.size, Nat.add_assoc] using this
  | @ite_neg a cn cz cp s s' hneg _ ih =>
    intro p hp
    simp only [Cmd.code] at hp
    rw [has_append, has_append, has_append] at hp
    obtain ⟨hb, hn, hj, -⟩ := hp
    simp only [List.length_singleton, Cmd.code_length] at hn hj
    obtain ⟨t, ht⟩ := ih (p + 1) hn
    have hstep := step_branch_neg (oracle := oracle) (s := s) (has_singleton.1 hb) hneg
    have hjmp := step_jump (oracle := oracle) (s := s') (has_singleton.1 hj)
    refine ⟨1 + t + 1, ?_⟩
    have := run_trans (run_trans (run_one hstep) ht) (run_one hjmp)
    simpa [Cmd.size, Nat.add_assoc] using this
  | @ite_zero a cn cz cp s s' hzero _ ih =>
    intro p hp
    simp only [Cmd.code] at hp
    rw [has_append, has_append, has_append, has_append, has_append] at hp
    obtain ⟨hb, -, -, hz, hj, -⟩ := hp
    simp only [List.length_singleton, Cmd.code_length] at hz hj
    obtain ⟨t, ht⟩ := ih (p + 1 + cn.size + 1) hz
    have hstep := step_branch_zero (oracle := oracle) (s := s) (has_singleton.1 hb) hzero
    have hjmp := step_jump (oracle := oracle) (s := s') (has_singleton.1 hj)
    refine ⟨1 + t + 1, ?_⟩
    have := run_trans (run_trans (run_one hstep) ht) (run_one hjmp)
    simpa [Cmd.size, Nat.add_assoc] using this
  | @ite_pos a cn cz cp s s' hpos _ ih =>
    intro p hp
    simp only [Cmd.code] at hp
    rw [has_append, has_append, has_append, has_append, has_append] at hp
    obtain ⟨hb, -, -, -, -, hq⟩ := hp
    simp only [List.length_singleton, Cmd.code_length] at hq
    obtain ⟨t, ht⟩ := ih (p + 1 + cn.size + 1 + cz.size + 1) hq
    have hstep := step_branch_pos (oracle := oracle) (s := s) (has_singleton.1 hb) hpos
    refine ⟨1 + t, ?_⟩
    have := run_trans (run_one hstep) ht
    simpa [Cmd.size, Nat.add_assoc] using this
  | @while_done a body s hzero =>
    intro p hp
    simp only [Cmd.code] at hp
    rw [has_append] at hp
    have hstep := step_branch_zero (oracle := oracle) (s := s) (has_singleton.1 hp.1) hzero
    refine ⟨1, ?_⟩
    have := run_one hstep
    simpa [Cmd.size, Nat.add_assoc] using this
  | @while_step a body s m s' hne _ _ ih₁ ih₂ =>
    intro p hp
    have hp0 := hp
    simp only [Cmd.code] at hp
    rw [has_append, has_append] at hp
    obtain ⟨hb, hbody, hj⟩ := hp
    simp only [List.length_singleton, Cmd.code_length] at hbody hj
    obtain ⟨t₁, ht₁⟩ := ih₁ (p + 1) hbody
    obtain ⟨t₂, ht₂⟩ := ih₂ p hp0
    have hstep : rayMachineStep prog oracle (s.cfg p) = some (s.cfg (p + 1)) := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact step_branch_neg (has_singleton.1 hb) h
      · exact step_branch_pos (has_singleton.1 hb) h
    have hjmp := step_jump (oracle := oracle) (s := m) (has_singleton.1 hj)
    refine ⟨1 + t₁ + 1 + t₂, ?_⟩
    exact run_trans (run_trans (run_trans (run_one hstep) ht₁) (run_one hjmp)) ht₂

/-- The complete program for a command: its code followed by `halt`. -/
def Cmd.program (c : Cmd) : List RayInstruction := c.code 0 ++ [.halt]

theorem Cmd.program_run {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    {c : Cmd} {s s' : TS} (hx : Cmd.Exec oracle c s s') :
    ∃ t, rayMachineRun c.program oracle t (s.cfg 0) = some (s'.cfg c.size) ∧
      c.program[c.size]? = some .halt := by
  obtain ⟨t, ht⟩ := Cmd.exec_run (prog := c.program) hx 0 (has_self _ _)
  refine ⟨t, by simpa using ht, ?_⟩
  simp [Cmd.program, Cmd.code_length]

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Frame -/

namespace Grunbaum2003
namespace RayAlg

/-! ## Layer B, part 1: polynomial expressions, frame layout, tape macros -/

inductive BinOp where
  | add | sub | mul
  deriving DecidableEq

def BinOp.eval : BinOp → ℝ → ℝ → ℝ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

def BinOp.cmd : BinOp → ℤ → ℤ → ℤ → Cmd
  | .add, dst, a, b => .add dst a b
  | .sub, dst, a, b => .sub dst a b
  | .mul, dst, a, b => .mul dst a b

theorem exec_binop {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ} (op : BinOp) (dst a b : ℤ) (t : TS) :
    Cmd.Exec oracle (op.cmd dst a b) t
      ⟨t.head, Function.update t.tape (t.head + dst)
        (op.eval (t.tape (t.head + a)) (t.tape (t.head + b))), t.queries⟩ := by
  cases op
  · exact Cmd.Exec.add dst a b t
  · exact Cmd.Exec.sub dst a b t
  · exact Cmd.Exec.mul dst a b t

inductive PExpr (α : Type) where
  | const (q : ℚ)
  | reg (r : α)
  | bin (op : BinOp) (a b : PExpr α)

namespace PExpr
variable {α : Type}

def eval (g : α → ℝ) : PExpr α → ℝ
  | const q => (q : ℝ)
  | reg r => g r
  | bin op a b => op.eval (a.eval g) (b.eval g)

/-- number of stack slots used, including the result slot -/
def depth : PExpr α → ℕ
  | const _ => 1
  | reg _ => 1
  | bin _ a b => max a.depth (b.depth + 1)

theorem depth_pos (e : PExpr α) : 1 ≤ e.depth := by
  cases e <;> simp [depth]

end PExpr

/-- Frame layout: register `r` lives at offset `enc r`, the position register at offset `R`,
a temporary at `R+1`, and `S` expression-stack slots at `R+2 ..`. -/
structure Layout (α : Type) where
  enc : α → ℕ
  R : ℕ
  S : ℕ
  enc_inj : Function.Injective enc
  enc_lt : ∀ r, enc r < R
  hS : 1 ≤ S

namespace Layout
variable {α : Type} (L : Layout α)

def G : ℕ := L.R + 2 + L.S
def slot (k : ℕ) : ℤ := ((L.R + 2 + k : ℕ) : ℤ)
def re (r : α) : ℤ := ((L.enc r : ℕ) : ℤ)

end Layout

def Cmd.copy (dst src : ℤ) : Cmd := .seq (.const dst 0) (.add dst dst src)

section
variable {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}

theorem exec_copy (dst src : ℤ) (h : dst ≠ src) (t : TS) :
    Cmd.Exec oracle (Cmd.copy dst src) t
      ⟨t.head, Function.update t.tape (t.head + dst) (t.tape (t.head + src)), t.queries⟩ := by
  have h1 := Cmd.Exec.const (oracle := oracle) dst 0 t
  have h2 := Cmd.Exec.add (oracle := oracle) dst dst src
    ⟨t.head, Function.update t.tape (t.head + dst) ((0 : ℚ) : ℝ), t.queries⟩
  have hne : t.head + src ≠ t.head + dst := fun e => h (by omega)
  have := Cmd.Exec.seq h1 h2
  unfold Cmd.copy
  simpa [Function.update_of_ne hne] using this

variable {α : Type}

def Layout.evalTo (L : Layout α) : PExpr α → ℕ → Cmd
  | .const q, k => .const (L.slot k) q
  | .reg r, k => Cmd.copy (L.slot k) (L.re r)
  | .bin op a b, k =>
      .seq (Layout.evalTo L a k)
        (.seq (Layout.evalTo L b (k + 1)) (op.cmd (L.slot k) (L.slot k) (L.slot (k + 1))))

variable (L : Layout α)

theorem Layout.evalTo_spec (g : α → ℝ) :
    ∀ (e : PExpr α) (k : ℕ) (t : TS), (∀ r, t.tape (t.head + L.re r) = g r) →
      ∃ t', Cmd.Exec oracle (L.evalTo e k) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
        t'.tape (t.head + L.slot k) = e.eval g ∧
        ∀ c, (c < t.head + L.slot k ∨ t.head + L.slot k + e.depth ≤ c) → t'.tape c = t.tape c := by
  intro e
  induction e with
  | const q =>
    intro k t _
    refine ⟨_, Cmd.Exec.const _ q t, rfl, rfl, by simp [PExpr.eval], ?_⟩
    intro c hc
    have : c ≠ t.head + L.slot k := by
      simp only [PExpr.depth] at hc; omega
    simp [Function.update_of_ne this]
  | reg r =>
    intro k t hg
    have hne : L.slot k ≠ L.re r := by
      have := L.enc_lt r
      simp only [Layout.slot, Layout.re]; omega
    refine ⟨_, exec_copy _ _ hne t, rfl, rfl, by simp [PExpr.eval, hg], ?_⟩
    intro c hc
    have : c ≠ t.head + L.slot k := by
      simp only [PExpr.depth] at hc; omega
    simp [Function.update_of_ne this]
  | bin op a b iha ihb =>
    intro k t hg
    obtain ⟨t1, hx1, hh1, hq1, hv1, hf1⟩ := iha k t hg
    have hg1 : ∀ r, t1.tape (t1.head + L.re r) = g r := by
      intro r
      rw [hh1, hf1 _ (Or.inl ?_), hg]
      have := L.enc_lt r
      simp only [Layout.slot, Layout.re]; omega
    obtain ⟨t2, hx2, hh2, hq2, hv2, hf2⟩ := ihb (k + 1) t1 hg1
    have hx3 := exec_binop (oracle := oracle) op (L.slot k) (L.slot k) (L.slot (k + 1)) t2
    refine ⟨_, Cmd.Exec.seq hx1 (Cmd.Exec.seq hx2 hx3), ?_, ?_, ?_, ?_⟩
    · simp [hh2, hh1]
    · simp [hq2, hq1]
    · have e1 : t2.tape (t.head + L.slot k) = a.eval g := by
        rw [hf2 _ (Or.inl ?_), hv1]
        rw [hh1]; simp only [Layout.slot]; omega
      have e2 : t2.tape (t.head + L.slot (k + 1)) = b.eval g := by
        rw [← hh1]; exact hv2
      simp [hh2, hh1, e1, e2, PExpr.eval]
    · intro c hc
      have hd : (PExpr.bin op a b).depth = max a.depth (b.depth + 1) := rfl
      have hs : L.slot (k + 1) = L.slot k + 1 := by simp only [Layout.slot]; omega
      have hne : c ≠ t2.head + L.slot k := by
        rw [hh2, hh1]
        have := PExpr.depth_pos a
        rcases hc with hc | hc
        · omega
        · rw [hd] at hc; omega
      have h2 : t2.tape c = t1.tape c := by
        apply hf2
        rw [hh1, hs]
        rcases hc with hc | hc
        · left; omega
        · right; rw [hd] at hc; omega
      have h1 : t1.tape c = t.tape c := by
        apply hf1
        rcases hc with hc | hc
        · left; omega
        · right; rw [hd] at hc; omega
      simp [Function.update_of_ne hne, h2, h1]

/-! ### Frame shifting -/

/-- cells `1..n` receive the old contents of cells `0..n-1` -/
def copyUp : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (Cmd.copy ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ)) (copyUp n)

theorem copyUp_spec : ∀ (n : ℕ) (t : TS),
    ∃ t', Cmd.Exec oracle (copyUp n) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ n → t'.tape (t.head + i) = t.tape (t.head + i - 1)) ∧
      ∀ c, (c < t.head + 1 ∨ t.head + n < c) → t'.tape c = t.tape c := by
  intro n
  induction n with
  | zero =>
    intro t
    exact ⟨t, Cmd.Exec.skip t, rfl, rfl, fun i h1 h2 => by omega, fun c _ => rfl⟩
  | succ n ih =>
    intro t
    have hc := exec_copy (oracle := oracle) ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ) (by omega) t
    obtain ⟨t', hx, hh, hq, hv, hf⟩ := ih
      ⟨t.head, Function.update t.tape (t.head + ((n + 1 : ℕ) : ℤ)) (t.tape (t.head + ((n : ℕ) : ℤ))),
        t.queries⟩
    dsimp only at hh hq hv hf
    refine ⟨t', Cmd.Exec.seq hc hx, hh, hq, ?_, ?_⟩
    · intro i h1 h2
      by_cases hi : i ≤ n
      · rw [hv i h1 hi]
        have hne : t.head + (i : ℤ) - 1 ≠ t.head + ((n + 1 : ℕ) : ℤ) := by omega
        exact Function.update_of_ne hne _ _
      · have hi' : i = n + 1 := by omega
        subst hi'
        rw [hf _ (Or.inr (by omega)), Function.update_self]
        congr 1; omega
    · intro c hc'
      rw [hf c (by rcases hc' with h | h
                   · left; omega
                   · right; omega)]
      have hne : c ≠ t.head + ((n + 1 : ℕ) : ℤ) := by omega
      exact Function.update_of_ne hne _ _

/-- cells `j-1 .. j+n-2` receive the old contents of cells `j .. j+n-1` -/
def copyDown : ℤ → ℕ → Cmd
  | _, 0 => .skip
  | j, n + 1 => .seq (Cmd.copy (j - 1) j) (copyDown (j + 1) n)

theorem copyDown_spec : ∀ (n : ℕ) (j : ℤ) (t : TS),
    ∃ t', Cmd.Exec oracle (copyDown j n) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      (∀ i : ℤ, j ≤ i → i < j + n → t'.tape (t.head + i - 1) = t.tape (t.head + i)) ∧
      ∀ c, (c < t.head + j - 1 ∨ t.head + j + n - 1 ≤ c) → t'.tape c = t.tape c := by
  intro n
  induction n with
  | zero =>
    intro j t
    exact ⟨t, Cmd.Exec.skip t, rfl, rfl, fun i h1 h2 => by omega, fun c _ => rfl⟩
  | succ n ih =>
    intro j t
    have hc := exec_copy (oracle := oracle) (j - 1) j (by omega) t
    obtain ⟨t', hx, hh, hq, hv, hf⟩ := ih (j + 1)
      ⟨t.head, Function.update t.tape (t.head + (j - 1)) (t.tape (t.head + j)), t.queries⟩
    dsimp only at hh hq hv hf
    refine ⟨t', Cmd.Exec.seq hc hx, hh, hq, ?_, ?_⟩
    · intro i h1 h2
      by_cases hi : i = j
      · subst hi
        rw [hf _ (Or.inl (by omega))]
        have e : t.head + i - 1 = t.head + (i - 1) := by omega
        rw [e, Function.update_self]
      · rw [hv i (by omega) (by omega)]
        have hne : t.head + i ≠ t.head + (j - 1) := by omega
        exact Function.update_of_ne hne _ _
    · intro c hc'
      rw [hf c (by rcases hc' with h | h
                   · left; omega
                   · right; omega)]
      have hne : c ≠ t.head + (j - 1) := by omega
      exact Function.update_of_ne hne _ _

end

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Ram -/

namespace Grunbaum2003
namespace RayAlg

/-! ## Layer B, part 2: the RAM language and its tape representation -/

structure RS (α : Type) where
  regs : α → ℝ
  mem : ℕ → ℝ
  queries : ℕ

inductive Stmt (α : Type) where
  | par (l : List (α × PExpr α))
  | div (dst a b : α)
  | load (dst idx : α)
  | store (idx src : α)
  | query
  | skip
  | seq (a b : Stmt α)
  | ite (a : α) (sn sz sp : Stmt α)
  | while (a : α) (body : Stmt α)

def parUpd {α : Type} [DecidableEq α] (base : α → ℝ) :
    List (α × PExpr α) → (α → ℝ) → (α → ℝ)
  | [], g => g
  | p :: l, g => parUpd base l (Function.update g p.1 (p.2.eval base))

inductive Stmt.Exec {α : Type} [DecidableEq α] {d : ℕ} (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (qr : Fin d → α) : Stmt α → RS α → RS α → Prop
  | par (l : List (α × PExpr α)) (s : RS α) :
      Exec oracle qr (.par l) s ⟨parUpd s.regs l s.regs, s.mem, s.queries⟩
  | div (dst a b : α) (s : RS α) (h : s.regs b ≠ 0) :
      Exec oracle qr (.div dst a b) s
        ⟨Function.update s.regs dst (s.regs a / s.regs b), s.mem, s.queries⟩
  | load (dst idx : α) (s : RS α) (n : ℕ) (h : s.regs idx = n) :
      Exec oracle qr (.load dst idx) s ⟨Function.update s.regs dst (s.mem n), s.mem, s.queries⟩
  | store (idx src : α) (s : RS α) (n : ℕ) (h : s.regs idx = n) :
      Exec oracle qr (.store idx src) s ⟨s.regs, Function.update s.mem n (s.regs src), s.queries⟩
  | query (s : RS α) (h : (fun i => s.regs (qr i)) ≠ 0) :
      Exec oracle qr .query s
        ⟨Function.extend qr (oracle (fun i => s.regs (qr i))) s.regs, s.mem, s.queries + 1⟩
  | skip (s : RS α) : Exec oracle qr .skip s s
  | seq {a b : Stmt α} {s m s' : RS α} :
      Exec oracle qr a s m → Exec oracle qr b m s' → Exec oracle qr (.seq a b) s s'
  | ite_neg {a : α} {sn sz sp : Stmt α} {s s' : RS α} :
      s.regs a < 0 → Exec oracle qr sn s s' → Exec oracle qr (.ite a sn sz sp) s s'
  | ite_zero {a : α} {sn sz sp : Stmt α} {s s' : RS α} :
      s.regs a = 0 → Exec oracle qr sz s s' → Exec oracle qr (.ite a sn sz sp) s s'
  | ite_pos {a : α} {sn sz sp : Stmt α} {s s' : RS α} :
      0 < s.regs a → Exec oracle qr sp s s' → Exec oracle qr (.ite a sn sz sp) s s'
  | while_done {a : α} {body : Stmt α} {s : RS α} :
      s.regs a = 0 → Exec oracle qr (.while a body) s s
  | while_step {a : α} {body : Stmt α} {s m s' : RS α} :
      s.regs a ≠ 0 → Exec oracle qr body s m → Exec oracle qr (.while a body) m s' →
      Exec oracle qr (.while a body) s s'

/-! ### Pointwise forms of the primitive tape steps -/

section
variable {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}

theorem exec_copy' (dst src : ℤ) (h : dst ≠ src) (t : TS) :
    ∃ t', Cmd.Exec oracle (Cmd.copy dst src) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      ∀ c, t'.tape c = if c = t.head + dst then t.tape (t.head + src) else t.tape c :=
  ⟨_, exec_copy dst src h t, rfl, rfl, fun c => by simp [Function.update_apply]⟩

theorem exec_const' (dst : ℤ) (v : ℚ) (t : TS) :
    ∃ t', Cmd.Exec oracle (.const dst v) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      ∀ c, t'.tape c = if c = t.head + dst then (v : ℝ) else t.tape c :=
  ⟨_, Cmd.Exec.const dst v t, rfl, rfl, fun c => by simp [Function.update_apply]⟩

theorem exec_binop' (op : BinOp) (dst a b : ℤ) (t : TS) :
    ∃ t', Cmd.Exec oracle (op.cmd dst a b) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      ∀ c, t'.tape c =
        if c = t.head + dst then op.eval (t.tape (t.head + a)) (t.tape (t.head + b))
        else t.tape c :=
  ⟨_, exec_binop op dst a b t, rfl, rfl, fun c => by simp [Function.update_apply]⟩

theorem exec_shift' (off : ℤ) (t : TS) :
    ∃ t', Cmd.Exec oracle (.shift off) t t' ∧ t'.head = t.head + off ∧ t'.queries = t.queries ∧
      ∀ c, t'.tape c = t.tape c :=
  ⟨_, Cmd.Exec.shift off t, rfl, rfl, fun _ => rfl⟩

theorem copyUp_spec' (n : ℕ) (t : TS) :
    ∃ t', Cmd.Exec oracle (copyUp n) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      (∀ c, t.head + 1 ≤ c → c ≤ t.head + n → t'.tape c = t.tape (c - 1)) ∧
      ∀ c, (c < t.head + 1 ∨ t.head + n < c) → t'.tape c = t.tape c := by
  obtain ⟨t', hx, hh, hq, hv, hf⟩ := copyUp_spec (oracle := oracle) n t
  refine ⟨t', hx, hh, hq, ?_, hf⟩
  intro c h1 h2
  have := hv (c - t.head).toNat (by omega) (by omega)
  have e : t.head + ((c - t.head).toNat : ℤ) = c := by omega
  rw [e] at this
  exact this

theorem copyDown_spec' (n : ℕ) (j : ℤ) (t : TS) :
    ∃ t', Cmd.Exec oracle (copyDown j n) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
      (∀ c, t.head + j - 1 ≤ c → c < t.head + j + n - 1 → t'.tape c = t.tape (c + 1)) ∧
      ∀ c, (c < t.head + j - 1 ∨ t.head + j + n - 1 ≤ c) → t'.tape c = t.tape c := by
  obtain ⟨t', hx, hh, hq, hv, hf⟩ := copyDown_spec (oracle := oracle) n j t
  refine ⟨t', hx, hh, hq, ?_, hf⟩
  intro c h1 h2
  have := hv (c + 1 - t.head) (by omega) (by omega)
  have e : t.head + (c + 1 - t.head) - 1 = c := by omega
  have e' : t.head + (c + 1 - t.head) = c + 1 := by omega
  rw [e, e'] at this
  exact this

end

/-! ### Representation of a RAM state on the tape -/

variable {α : Type}

def RepAt (L : Layout α) (s : RS α) (t : TS) (pos : ℕ) : Prop :=
  t.head = (pos : ℤ) ∧ (∀ r, t.tape ((pos : ℤ) + (L.enc r : ℤ)) = s.regs r) ∧
  t.tape ((pos : ℤ) + (L.R : ℤ)) = (pos : ℝ) ∧
  (∀ k : ℕ, k < pos → t.tape (k : ℤ) = s.mem k) ∧
  (∀ k : ℕ, pos ≤ k → t.tape ((k : ℤ) + (L.G : ℤ)) = s.mem k) ∧
  t.queries = s.queries

theorem Layout.G_eq (L : Layout α) : (L.G : ℤ) = (L.R : ℤ) + 2 + (L.S : ℤ) := by
  simp [Layout.G]

/-- Changing only scratch cells of the frame preserves the representation. -/
theorem RepAt.of_frame {L : Layout α} {s : RS α} {t t' : TS} {pos : ℕ} (h : RepAt L s t pos)
    (hh : t'.head = t.head) (hq : t'.queries = t.queries)
    (hf : ∀ c, (c < (pos : ℤ) + (L.R : ℤ) + 1 ∨ (pos : ℤ) + (L.G : ℤ) ≤ c) → t'.tape c = t.tape c) :
    RepAt L s t' pos := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hG := L.G_eq
  refine ⟨hh.trans h1, ?_, ?_, ?_, ?_, hq.trans h6⟩
  · intro r
    have := L.enc_lt r
    rw [hf _ (Or.inl (by omega)), h2]
  · rw [hf _ (Or.inl (by omega)), h3]
  · intro k hk
    rw [hf _ (Or.inl (by omega)), h4 k hk]
  · intro k hk
    rw [hf _ (Or.inr (by omega)), h5 k hk]

/-- Writing a register cell. -/
theorem RepAt.set_reg [DecidableEq α] {L : Layout α} {s : RS α} {t t' : TS} {pos : ℕ}
    (h : RepAt L s t pos) (dst : α) (v : ℝ)
    (hh : t'.head = t.head) (hq : t'.queries = t.queries)
    (ht : ∀ c, t'.tape c = if c = t.head + (L.enc dst : ℤ) then v else t.tape c) :
    RepAt L ⟨Function.update s.regs dst v, s.mem, s.queries⟩ t' pos := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hG := L.G_eq
  have hd := L.enc_lt dst
  refine ⟨hh.trans h1, ?_, ?_, ?_, ?_, hq.trans h6⟩
  · intro r
    by_cases hr : r = dst
    · subst hr
      rw [ht, if_pos (by omega)]; simp
    · have hne : L.enc r ≠ L.enc dst := fun e => hr (L.enc_inj e)
      rw [ht, if_neg (by omega), h2]
      simp [Function.update_of_ne hr]
  · rw [ht, if_neg (by omega), h3]
  · intro k hk
    rw [ht, if_neg (by omega), h4 k hk]
  · intro k hk
    rw [ht, if_neg (by omega), h5 k hk]

section Moves
variable {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}

def Layout.moveRight (L : Layout α) : Cmd :=
  .seq (Cmd.copy ((L.R : ℤ) + 1) (L.G : ℤ)) <|
  .seq (Cmd.copy ((L.R : ℤ) + 2) ((L.R : ℤ) + 1)) <|
  .seq (copyUp (L.R + 1)) <|
  .seq (Cmd.copy 0 ((L.R : ℤ) + 2)) <|
  .seq (.shift 1) <|
  .seq (.const ((L.R : ℤ) + 1) 1) (BinOp.add.cmd (L.R : ℤ) (L.R : ℤ) ((L.R : ℤ) + 1))

theorem Layout.moveRight_spec (L : Layout α) {s : RS α} {t : TS} {pos : ℕ}
    (h : RepAt L s t pos) :
    ∃ t', Cmd.Exec oracle L.moveRight t t' ∧ RepAt L s t' (pos + 1) := by
  obtain ⟨hh, hr, hp, hlo, hhi, hq⟩ := h
  have hS := L.hS
  have hG := L.G_eq
  obtain ⟨t1, e1, H1, Q1, T1⟩ :=
    exec_copy' (oracle := oracle) ((L.R : ℤ) + 1) (L.G : ℤ) (by omega) t
  obtain ⟨t2, e2, H2, Q2, T2⟩ :=
    exec_copy' (oracle := oracle) ((L.R : ℤ) + 2) ((L.R : ℤ) + 1) (by omega) t1
  obtain ⟨t3, e3, H3, Q3, V3, F3⟩ := copyUp_spec' (oracle := oracle) (L.R + 1) t2
  obtain ⟨t4, e4, H4, Q4, T4⟩ := exec_copy' (oracle := oracle) 0 ((L.R : ℤ) + 2) (by omega) t3
  obtain ⟨t5, e5, H5, Q5, T5⟩ := exec_shift' (oracle := oracle) 1 t4
  obtain ⟨t6, e6, H6, Q6, T6⟩ := exec_const' (oracle := oracle) ((L.R : ℤ) + 1) 1 t5
  obtain ⟨t7, e7, H7, Q7, T7⟩ :=
    exec_binop' (oracle := oracle) .add (L.R : ℤ) (L.R : ℤ) ((L.R : ℤ) + 1) t6
  refine ⟨t7, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
    (Cmd.Exec.seq e5 (Cmd.Exec.seq e6 e7))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H7, H6, H5, H4, H3, H2, H1, hh]; push_cast; ring
  · intro r
    have := L.enc_lt r
    rw [← hr r]
    simp (disch := omega) only [T7, T6, T5, T4, V3, T2, T1, if_pos, if_neg]; congr 1; omega
  · have e : t7.tape (((pos + 1 : ℕ) : ℤ) + (L.R : ℤ)) =
        BinOp.add.eval (t.tape ((pos : ℤ) + (L.R : ℤ))) ((1 : ℚ) : ℝ) := by
      simp (disch := omega) only [T7, T6, T5, T4, V3, T2, T1, if_pos, if_neg]; congr 2; omega
    rw [e, hp]; simp [BinOp.eval]
  · intro k hk
    by_cases hk' : k < pos
    · rw [← hlo k hk']
      simp (disch := omega) only [T7, T6, T5, T4, V3, F3, T2, T1, if_pos, if_neg]
    · have hk'' : k = pos := by omega
      subst hk''
      rw [← hhi k le_rfl]
      simp (disch := omega) only [T7, T6, T5, T4, V3, F3, T2, T1, if_pos, if_neg]; congr 1; omega
  · intro k hk
    rw [← hhi k (by omega)]
    simp (disch := omega) only [T7, T6, T5, T4, V3, F3, T2, T1, if_pos, if_neg]
  · rw [Q7, Q6, Q5, Q4, Q3, Q2, Q1, hq]

def Layout.moveLeft (L : Layout α) : Cmd :=
  .seq (Cmd.copy ((L.R : ℤ) + 1) (-1)) <|
  .seq (copyDown 0 (L.R + 1)) <|
  .seq (Cmd.copy ((L.G : ℤ) - 1) ((L.R : ℤ) + 1)) <|
  .seq (.shift (-1)) <|
  .seq (.const ((L.R : ℤ) + 1) 1) (BinOp.sub.cmd (L.R : ℤ) (L.R : ℤ) ((L.R : ℤ) + 1))

theorem Layout.moveLeft_spec (L : Layout α) {s : RS α} {t : TS} {pos : ℕ}
    (h : RepAt L s t (pos + 1)) :
    ∃ t', Cmd.Exec oracle L.moveLeft t t' ∧ RepAt L s t' pos := by
  obtain ⟨hh, hr, hp, hlo, hhi, hq⟩ := h
  have hS := L.hS
  have hG := L.G_eq
  obtain ⟨t1, e1, H1, Q1, T1⟩ :=
    exec_copy' (oracle := oracle) ((L.R : ℤ) + 1) (-1) (by omega) t
  obtain ⟨t2, e2, H2, Q2, V2, F2⟩ := copyDown_spec' (oracle := oracle) (L.R + 1) 0 t1
  obtain ⟨t3, e3, H3, Q3, T3⟩ :=
    exec_copy' (oracle := oracle) ((L.G : ℤ) - 1) ((L.R : ℤ) + 1) (by omega) t2
  obtain ⟨t4, e4, H4, Q4, T4⟩ := exec_shift' (oracle := oracle) (-1) t3
  obtain ⟨t5, e5, H5, Q5, T5⟩ := exec_const' (oracle := oracle) ((L.R : ℤ) + 1) 1 t4
  obtain ⟨t6, e6, H6, Q6, T6⟩ :=
    exec_binop' (oracle := oracle) .sub (L.R : ℤ) (L.R : ℤ) ((L.R : ℤ) + 1) t5
  refine ⟨t6, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
    (Cmd.Exec.seq e5 e6)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H6, H5, H4, H3, H2, H1, hh]; push_cast; ring
  · intro r
    have := L.enc_lt r
    rw [← hr r]
    simp (disch := omega) only [T6, T5, T4, T3, V2, T1, if_pos, if_neg]; congr 1; omega
  · have e : t6.tape ((pos : ℤ) + (L.R : ℤ)) =
        BinOp.sub.eval (t.tape (((pos + 1 : ℕ) : ℤ) + (L.R : ℤ))) ((1 : ℚ) : ℝ) := by
      simp (disch := omega) only [T6, T5, T4, T3, V2, T1, if_pos, if_neg]; congr 2; omega
    rw [e, hp]; simp [BinOp.eval]
  · intro k hk
    rw [← hlo k (by omega)]
    simp (disch := omega) only [T6, T5, T4, T3, V2, F2, T1, if_pos, if_neg]
  · intro k hk
    by_cases hk' : pos + 1 ≤ k
    · rw [← hhi k hk']
      simp (disch := omega) only [T6, T5, T4, T3, V2, F2, T1, if_pos, if_neg]
    · have hk'' : k = pos := by omega
      subst hk''
      rw [← hlo k (by omega)]
      simp (disch := omega) only [T6, T5, T4, T3, V2, F2, T1, if_pos, if_neg]; congr 1; omega
  · rw [Q6, Q5, Q4, Q3, Q2, Q1, hq]

/-- Recompute `tmp := regs idx - pos`. -/
def Layout.diff (L : Layout α) (idx : α) : Cmd :=
  BinOp.sub.cmd ((L.R : ℤ) + 1) (L.enc idx : ℤ) (L.R : ℤ)

theorem Layout.diff_spec (L : Layout α) (idx : α) {s : RS α} {t : TS} {pos : ℕ}
    (h : RepAt L s t pos) :
    ∃ t', Cmd.Exec oracle (L.diff idx) t t' ∧ RepAt L s t' pos ∧
      t'.tape (t'.head + ((L.R : ℤ) + 1)) = s.regs idx - (pos : ℝ) := by
  obtain ⟨t1, e1, H1, Q1, T1⟩ :=
    exec_binop' (oracle := oracle) .sub ((L.R : ℤ) + 1) (L.enc idx : ℤ) (L.R : ℤ) t
  have hG := L.G_eq
  have hS := L.hS
  have hh := h.1
  refine ⟨t1, e1, h.of_frame H1 Q1 ?_, ?_⟩
  · intro c hc
    rw [T1, if_neg (by omega)]
  · rw [T1, if_pos (by omega), hh, h.2.1 idx, h.2.2.1]; rfl

def Layout.goto (L : Layout α) (idx : α) : Cmd :=
  .seq (L.diff idx)
    (.while ((L.R : ℤ) + 1) (.seq (.ite ((L.R : ℤ) + 1) L.moveLeft .skip L.moveRight) (L.diff idx)))

theorem Layout.goto_loop (L : Layout α) (idx : α) {s : RS α} {n : ℕ} (hn : s.regs idx = n) :
    ∀ (k : ℕ) (pos : ℕ) (t : TS), (n - pos) + (pos - n) = k → RepAt L s t pos →
      t.tape (t.head + ((L.R : ℤ) + 1)) = s.regs idx - (pos : ℝ) →
      ∃ t', Cmd.Exec oracle
        (.while ((L.R : ℤ) + 1) (.seq (.ite ((L.R : ℤ) + 1) L.moveLeft .skip L.moveRight) (L.diff idx)))
        t t' ∧ RepAt L s t' n := by
  intro k
  induction k with
  | zero =>
    intro pos t hk h ht
    have : pos = n := by omega
    subst this
    refine ⟨t, Cmd.Exec.while_done ?_, h⟩
    rw [ht, hn]; simp
  | succ k ih =>
    intro pos t hk h ht
    rcases Nat.lt_or_ge pos n with hlt | hge
    · have hpos : 0 < t.tape (t.head + ((L.R : ℤ) + 1)) := by
        rw [ht, hn]
        have : (pos : ℝ) < (n : ℝ) := by exact_mod_cast hlt
        linarith
      obtain ⟨t1, e1, h1⟩ := L.moveRight_spec (oracle := oracle) h
      obtain ⟨t2, e2, h2, ht2⟩ := L.diff_spec (oracle := oracle) idx h1
      obtain ⟨t', e', h'⟩ := ih (pos + 1) t2 (by omega) h2 ht2
      exact ⟨t', Cmd.Exec.while_step hpos.ne' (Cmd.Exec.seq (Cmd.Exec.ite_pos hpos e1) e2) e', h'⟩
    · have hgt : n < pos := by omega
      obtain ⟨p, rfl⟩ : ∃ p, pos = p + 1 := ⟨pos - 1, by omega⟩
      have hneg : t.tape (t.head + ((L.R : ℤ) + 1)) < 0 := by
        rw [ht, hn]
        have : (n : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hgt
        linarith
      obtain ⟨t1, e1, h1⟩ := L.moveLeft_spec (oracle := oracle) h
      obtain ⟨t2, e2, h2, ht2⟩ := L.diff_spec (oracle := oracle) idx h1
      obtain ⟨t', e', h'⟩ := ih p t2 (by omega) h2 ht2
      exact ⟨t', Cmd.Exec.while_step hneg.ne (Cmd.Exec.seq (Cmd.Exec.ite_neg hneg e1) e2) e', h'⟩

theorem Layout.goto_spec (L : Layout α) (idx : α) {s : RS α} {t : TS} {pos n : ℕ}
    (h : RepAt L s t pos) (hn : s.regs idx = n) :
    ∃ t', Cmd.Exec oracle (L.goto idx) t t' ∧ RepAt L s t' n := by
  obtain ⟨t1, e1, h1, ht1⟩ := L.diff_spec (oracle := oracle) idx h
  obtain ⟨t', e', h'⟩ := L.goto_loop (oracle := oracle) idx hn _ pos t1 rfl h1 ht1
  exact ⟨t', Cmd.Exec.seq e1 e', h'⟩

end Moves

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Sim -/

namespace Grunbaum2003
namespace RayAlg

/-! ## Layer B, part 3: compiling the RAM language and the simulation theorem -/

variable {α : Type}

def parNeed : List (α × PExpr α) → ℕ
  | [] => 0
  | p :: l => max p.2.depth (parNeed l + 1)

def Stmt.need : Stmt α → ℕ
  | .par l => parNeed l
  | .seq a b => max a.need b.need
  | .ite _ a b c => max a.need (max b.need c.need)
  | .while _ b => b.need
  | _ => 0

def Layout.parEval (L : Layout α) : List (α × PExpr α) → ℕ → Cmd
  | [], _ => .skip
  | p :: l, k => .seq (L.evalTo p.2 k) (Layout.parEval L l (k + 1))

def Layout.parCopy (L : Layout α) : List (α × PExpr α) → ℕ → Cmd
  | [], _ => .skip
  | p :: l, k => .seq (Cmd.copy (L.enc p.1 : ℤ) (L.slot k)) (Layout.parCopy L l (k + 1))

def Layout.compile (L : Layout α) : Stmt α → Cmd
  | .par l => .seq (L.parEval l 0) (L.parCopy l 0)
  | .div dst a b => .div (L.enc dst : ℤ) (L.enc a : ℤ) (L.enc b : ℤ)
  | .load dst idx => .seq (L.goto idx) (Cmd.copy (L.enc dst : ℤ) (L.G : ℤ))
  | .store idx src => .seq (L.goto idx) (Cmd.copy (L.G : ℤ) (L.enc src : ℤ))
  | .query => .query
  | .skip => .skip
  | .seq a b => .seq (Layout.compile L a) (Layout.compile L b)
  | .ite a n z p => .ite (L.enc a : ℤ) (Layout.compile L n) (Layout.compile L z) (Layout.compile L p)
  | .while a b => .while (L.enc a : ℤ) (Layout.compile L b)

section
variable {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}

theorem Layout.parEval_spec (L : Layout α) (g : α → ℝ) :
    ∀ (l : List (α × PExpr α)) (k : ℕ) (t : TS), (∀ r, t.tape (t.head + L.re r) = g r) →
      ∃ t', Cmd.Exec oracle (L.parEval l k) t t' ∧ t'.head = t.head ∧ t'.queries = t.queries ∧
        (∀ i (hi : i < l.length), t'.tape (t.head + L.slot (k + i)) = (l[i]).2.eval g) ∧
        ∀ c, (c < t.head + L.slot k ∨ t.head + L.slot k + parNeed l ≤ c) → t'.tape c = t.tape c := by
  intro l
  induction l with
  | nil =>
    intro k t _
    exact ⟨t, Cmd.Exec.skip t, rfl, rfl, fun i hi => by simp at hi, fun _ _ => rfl⟩
  | cons p l ih =>
    intro k t hg
    obtain ⟨t1, e1, H1, Q1, V1, F1⟩ := L.evalTo_spec (oracle := oracle) g p.2 k t hg
    have hg1 : ∀ r, t1.tape (t1.head + L.re r) = g r := by
      intro r
      have := L.enc_lt r
      rw [H1, F1 _ (Or.inl (by simp only [Layout.slot, Layout.re]; omega)), hg]
    obtain ⟨t2, e2, H2, Q2, V2, F2⟩ := ih (k + 1) t1 hg1
    have hs : L.slot (k + 1) = L.slot k + 1 := by simp only [Layout.slot]; omega
    have hdp := PExpr.depth_pos p.2
    have hneed : parNeed (p :: l) = max p.2.depth (parNeed l + 1) := rfl
    refine ⟨t2, Cmd.Exec.seq e1 e2, H2.trans H1, Q2.trans Q1, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        rw [F2 _ (Or.inl (by rw [H1, hs]; simp)), Nat.add_zero, V1]; rfl
      | succ i =>
        have := V2 i (by simpa using hi)
        rw [H1] at this
        have e : k + (i + 1) = k + 1 + i := by omega
        rw [e, this]; rfl
    · intro c hc
      have hc2 : c < t1.head + L.slot (k + 1) ∨ t1.head + L.slot (k + 1) + parNeed l ≤ c := by
        rw [H1, hs]
        rcases hc with h | h
        · left; omega
        · right; rw [hneed] at h; omega
      have hc1 : c < t.head + L.slot k ∨ t.head + L.slot k + p.2.depth ≤ c := by
        rcases hc with h | h
        · left; omega
        · right; rw [hneed] at h; omega
      rw [F2 c hc2, F1 c hc1]

theorem Layout.parCopy_spec [DecidableEq α] (L : Layout α) (base : α → ℝ) :
    ∀ (l : List (α × PExpr α)) (k : ℕ) (s : RS α) (t : TS) (pos : ℕ), RepAt L s t pos →
      (∀ i (hi : i < l.length), t.tape (t.head + L.slot (k + i)) = (l[i]).2.eval base) →
      ∃ t', Cmd.Exec oracle (L.parCopy l k) t t' ∧
        RepAt L ⟨parUpd base l s.regs, s.mem, s.queries⟩ t' pos := by
  intro l
  induction l with
  | nil =>
    intro k s t pos h _
    exact ⟨t, Cmd.Exec.skip t, h⟩
  | cons p l ih =>
    intro k s t pos h hv
    have hlt := L.enc_lt p.1
    obtain ⟨t1, e1, H1, Q1, T1⟩ := exec_copy' (oracle := oracle) (L.enc p.1 : ℤ) (L.slot k)
      (by simp only [Layout.slot]; omega) t
    have hv0 : t.tape (t.head + L.slot k) = p.2.eval base := hv 0 (by simp)
    rw [hv0] at T1
    have h1 := h.set_reg p.1 (p.2.eval base) H1 Q1 T1
    obtain ⟨t', e', h'⟩ := ih (k + 1) _ t1 pos h1 (by
      intro i hi
      have := hv (i + 1) (by simpa using hi)
      have e : k + (i + 1) = k + 1 + i := by omega
      rw [H1, T1, if_neg (by simp only [Layout.slot]; omega), ← e, this]; rfl)
    exact ⟨t', Cmd.Exec.seq e1 e', h'⟩

theorem Layout.par_spec [DecidableEq α] (L : Layout α) (l : List (α × PExpr α))
    (hneed : parNeed l ≤ L.S) {s : RS α} {t : TS} {pos : ℕ} (h : RepAt L s t pos) :
    ∃ t', Cmd.Exec oracle (.seq (L.parEval l 0) (L.parCopy l 0)) t t' ∧
      RepAt L ⟨parUpd s.regs l s.regs, s.mem, s.queries⟩ t' pos := by
  have hh := h.1
  have hG := L.G_eq
  obtain ⟨t1, e1, H1, Q1, V1, F1⟩ := L.parEval_spec (oracle := oracle) s.regs l 0 t (by
    intro r; rw [hh]; exact h.2.1 r)
  have h1 : RepAt L s t1 pos := h.of_frame H1 Q1 (by
    intro c hc
    apply F1
    simp only [Layout.slot]
    rcases hc with hc | hc
    · left; omega
    · right; omega)
  obtain ⟨t', e', h'⟩ := L.parCopy_spec (oracle := oracle) s.regs l 0 s t1 pos h1 (by
    intro i hi; rw [H1]; exact V1 i hi)
  exact ⟨t', Cmd.Exec.seq e1 e', h'⟩

/-- The simulation theorem: RAM executions are realized on the tape. -/
theorem Layout.sim [DecidableEq α] (L : Layout α) (qr : Fin d → α)
    (hqr : ∀ i : Fin d, L.enc (qr i) = i.val) {st : Stmt α} {s s' : RS α}
    (hx : Stmt.Exec oracle qr st s s') :
    st.need ≤ L.S → ∀ (t : TS) (pos : ℕ), RepAt L s t pos →
      ∃ t' pos', Cmd.Exec oracle (L.compile st) t t' ∧ RepAt L s' t' pos' := by
  have hG := L.G_eq
  induction hx with
  | par l s =>
    intro hn t pos h
    obtain ⟨t', e', h'⟩ := L.par_spec (oracle := oracle) l hn h
    exact ⟨t', pos, e', h'⟩
  | div dst a b s hb =>
    intro _ t pos h
    have hh := h.1
    have hb' : t.tape (t.head + (L.enc b : ℤ)) ≠ 0 := by rw [hh, h.2.1]; exact hb
    refine ⟨_, pos, Cmd.Exec.div (L.enc dst : ℤ) (L.enc a : ℤ) (L.enc b : ℤ) t hb', ?_⟩
    refine h.set_reg dst _ rfl rfl ?_
    intro c
    simp only [Function.update_apply]
    rw [hh, h.2.1, h.2.1]
  | load dst idx s n hn' =>
    intro _ t pos h
    obtain ⟨t1, e1, h1⟩ := L.goto_spec (oracle := oracle) idx h hn'
    have hlt := L.enc_lt dst
    obtain ⟨t2, e2, H2, Q2, T2⟩ := exec_copy' (oracle := oracle) (L.enc dst : ℤ) (L.G : ℤ)
      (by omega) t1
    have hm : t1.tape (t1.head + (L.G : ℤ)) = s.mem n := by
      rw [h1.1]; exact h1.2.2.2.2.1 n le_rfl
    rw [hm] at T2
    exact ⟨t2, n, Cmd.Exec.seq e1 e2, h1.set_reg dst _ H2 Q2 T2⟩
  | store idx src s n hn' =>
    intro _ t pos h
    obtain ⟨t1, e1, h1⟩ := L.goto_spec (oracle := oracle) idx h hn'
    have hlt := L.enc_lt src
    obtain ⟨t2, e2, H2, Q2, T2⟩ := exec_copy' (oracle := oracle) (L.G : ℤ) (L.enc src : ℤ)
      (by omega) t1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h1
    refine ⟨t2, n, Cmd.Exec.seq e1 e2, H2.trans g1, ?_, ?_, ?_, ?_, Q2.trans g6⟩
    · intro r
      have := L.enc_lt r
      rw [T2, if_neg (by omega), g2]
    · rw [T2, if_neg (by omega), g3]
    · intro k hk
      rw [T2, if_neg (by omega), g4 k hk]
      have : k ≠ n := by omega
      simp [Function.update_of_ne this]
    · intro k hk
      by_cases hkn : k = n
      · subst hkn
        rw [T2, if_pos (by omega), g1, g2]; simp
      · rw [T2, if_neg (by omega), g5 k hk]
        simp [Function.update_of_ne hkn]
  | query s hv =>
    intro _ t pos h
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h
    have hvec : queryVec d t = fun i => s.regs (qr i) := by
      funext i
      simp only [queryVec]
      rw [g1, ← hqr i, g2]
    have hqinj : Function.Injective qr := by
      intro i j hij
      have := congrArg L.enc hij
      rw [hqr, hqr] at this
      exact Fin.ext this
    have hdR : d ≤ L.R := by
      by_contra hcon
      have hR : L.R < d := by omega
      have := L.enc_lt (qr ⟨L.R, hR⟩)
      rw [hqr] at this
      simp at this
    refine ⟨_, pos, Cmd.Exec.query t (by rw [hvec]; exact hv), g1, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      by_cases hr : L.enc r < d
      · have hrq : qr ⟨L.enc r, hr⟩ = r := L.enc_inj (by rw [hqr])
        have hcond : 0 ≤ ((pos : ℤ) + (L.enc r : ℤ)) - t.head ∧
            ((pos : ℤ) + (L.enc r : ℤ)) - t.head < (d : ℤ) := by omega
        simp only [queryTape, dif_pos hcond, hvec]
        have hidx : (⟨(((pos : ℤ) + (L.enc r : ℤ)) - t.head).toNat, by omega⟩ : Fin d) =
            ⟨L.enc r, hr⟩ := by
          apply Fin.ext; simp only; omega
        rw [hidx]
        conv_rhs => rw [← hrq]
        rw [hqinj.extend_apply]
      · have hcond : ¬ (0 ≤ ((pos : ℤ) + (L.enc r : ℤ)) - t.head ∧
            ((pos : ℤ) + (L.enc r : ℤ)) - t.head < (d : ℤ)) := by omega
        simp only [queryTape, dif_neg hcond]
        rw [g2, Function.extend_apply']
        rintro ⟨i, hi⟩
        apply hr
        rw [← hi, hqr]
        exact i.isLt
    · have hcond : ¬ (0 ≤ ((pos : ℤ) + (L.R : ℤ)) - t.head ∧
          ((pos : ℤ) + (L.R : ℤ)) - t.head < (d : ℤ)) := by omega
      simp only [queryTape, dif_neg hcond]
      exact g3
    · intro k hk
      have hcond : ¬ (0 ≤ (k : ℤ) - t.head ∧ (k : ℤ) - t.head < (d : ℤ)) := by omega
      simp only [queryTape, dif_neg hcond]
      exact g4 k hk
    · intro k hk
      have hcond : ¬ (0 ≤ ((k : ℤ) + (L.G : ℤ)) - t.head ∧
          ((k : ℤ) + (L.G : ℤ)) - t.head < (d : ℤ)) := by omega
      simp only [queryTape, dif_neg hcond]
      exact g5 k hk
    · simp [g6]
  | skip s =>
    intro _ t pos h
    exact ⟨t, pos, Cmd.Exec.skip t, h⟩
  | @seq a b s m s' _ _ ih₁ ih₂ =>
    intro hn t pos h
    have hn' : max a.need b.need ≤ L.S := hn
    obtain ⟨t1, p1, e1, h1⟩ := ih₁ (le_trans (le_max_left _ _) hn') t pos h
    obtain ⟨t2, p2, e2, h2⟩ := ih₂ (le_trans (le_max_right _ _) hn') t1 p1 h1
    exact ⟨t2, p2, Cmd.Exec.seq e1 e2, h2⟩
  | @ite_neg a sn sz sp s s' ha _ ih =>
    intro hn t pos h
    have hn' : max sn.need (max sz.need sp.need) ≤ L.S := hn
    obtain ⟨t1, p1, e1, h1⟩ := ih (le_trans (le_max_left _ _) hn') t pos h
    refine ⟨t1, p1, Cmd.Exec.ite_neg ?_ e1, h1⟩
    rw [h.1, h.2.1]; exact ha
  | @ite_zero a sn sz sp s s' ha _ ih =>
    intro hn t pos h
    have hn' : max sn.need (max sz.need sp.need) ≤ L.S := hn
    obtain ⟨t1, p1, e1, h1⟩ :=
      ih (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn') t pos h
    refine ⟨t1, p1, Cmd.Exec.ite_zero ?_ e1, h1⟩
    rw [h.1, h.2.1]; exact ha
  | @ite_pos a sn sz sp s s' ha _ ih =>
    intro hn t pos h
    have hn' : max sn.need (max sz.need sp.need) ≤ L.S := hn
    obtain ⟨t1, p1, e1, h1⟩ :=
      ih (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn') t pos h
    refine ⟨t1, p1, Cmd.Exec.ite_pos ?_ e1, h1⟩
    rw [h.1, h.2.1]; exact ha
  | @while_done a body s ha =>
    intro _ t pos h
    refine ⟨t, pos, Cmd.Exec.while_done ?_, h⟩
    rw [h.1, h.2.1]; exact ha
  | @while_step a body s m s' ha _ _ ih₁ ih₂ =>
    intro hn t pos h
    have hn' : body.need ≤ L.S := hn
    obtain ⟨t1, p1, e1, h1⟩ := ih₁ hn' t pos h
    obtain ⟨t2, p2, e2, h2⟩ := ih₂ hn t1 p1 h1
    refine ⟨t2, p2, Cmd.Exec.while_step ?_ e1 e2, h2⟩
    rw [h.1, h.2.1]; exact ha

end

/-! ### Existence of a layout and the final realization theorem -/

theorem exists_layout [Fintype α] [DecidableEq α] {d : ℕ} (qr : Fin d → α)
    (hqr : Function.Injective qr) (S : ℕ) :
    ∃ L : Layout α, L.S = S + 1 ∧ ∀ i : Fin d, L.enc (qr i) = i.val := by
  classical
  let enc : α → ℕ := fun r =>
    if h : ∃ i, qr i = r then (Classical.choose h).val else d + (Fintype.equivFin α r).val
  have henc_q : ∀ i, enc (qr i) = i.val := by
    intro i
    have h : ∃ j, qr j = qr i := ⟨i, rfl⟩
    simp only [enc, dif_pos h]
    exact congrArg Fin.val (hqr (Classical.choose_spec h))
  have hinj : Function.Injective enc := by
    intro r r' hrr
    by_cases h : ∃ i, qr i = r <;> by_cases h' : ∃ i, qr i = r'
    · obtain ⟨i, rfl⟩ := h
      obtain ⟨j, rfl⟩ := h'
      rw [henc_q, henc_q] at hrr
      rw [Fin.ext hrr]
    · obtain ⟨i, rfl⟩ := h
      rw [henc_q] at hrr
      simp only [enc, dif_neg h'] at hrr
      have := i.isLt
      omega
    · obtain ⟨j, rfl⟩ := h'
      rw [henc_q] at hrr
      simp only [enc, dif_neg h] at hrr
      have := j.isLt
      omega
    · simp only [enc, dif_neg h, dif_neg h'] at hrr
      have : (Fintype.equivFin α r).val = (Fintype.equivFin α r').val := by omega
      exact (Fintype.equivFin α).injective (Fin.ext this)
  refine ⟨⟨enc, d + Fintype.card α, S + 1, hinj, ?_, by omega⟩, rfl, henc_q⟩
  intro r
  by_cases h : ∃ i, qr i = r
  · simp only [enc, dif_pos h]
    have := (Classical.choose h).isLt
    omega
  · simp only [enc, dif_neg h]
    have := (Fintype.equivFin α r).isLt
    omega

/-- Every RAM statement is realized by a single ray-machine program: whenever the statement
runs from the blank state to `s'` with `s'.regs o = n`, the program halts with head at a cell
from which the tape reads `s'.mem n, s'.mem (n+1), …`, having made `s'.queries` queries. -/
theorem Stmt.realize [Fintype α] [DecidableEq α] {d : ℕ} (qr : Fin d → α)
    (hqr : Function.Injective qr) (st : Stmt α) (o : α) :
    ∃ program : List RayInstruction,
      ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (s' : RS α) (n : ℕ),
        Stmt.Exec oracle qr st ⟨fun _ => 0, fun _ => 0, 0⟩ s' → s'.regs o = n →
        ∃ (t : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle t
            { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
          program[c.pc]? = some .halt ∧ c.queries = s'.queries ∧
          ∀ i : ℕ, c.tape (c.head + (i : ℤ)) = s'.mem (n + i) := by
  obtain ⟨L, hS, henc⟩ := exists_layout qr hqr st.need
  let cmd : Cmd := .seq (L.compile st) (.seq (L.goto o) (.shift (L.G : ℤ)))
  refine ⟨cmd.program, ?_⟩
  intro oracle s' n hx hn
  have h0 : RepAt L (⟨fun _ => 0, fun _ => 0, 0⟩ : RS α) (⟨0, fun _ => 0, 0⟩ : TS) 0 := by
    refine ⟨rfl, fun _ => rfl, by simp, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  obtain ⟨t1, p1, e1, h1⟩ := L.sim (oracle := oracle) qr henc hx (by omega) _ 0 h0
  obtain ⟨t2, e2, h2⟩ := L.goto_spec (oracle := oracle) o h1 hn
  have e3 := Cmd.Exec.shift (oracle := oracle) (L.G : ℤ) t2
  obtain ⟨t, ht, hhalt⟩ := Cmd.program_run (Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3))
  refine ⟨t, _, ht, hhalt, h2.2.2.2.2.2, ?_⟩
  intro i
  have := h2.2.2.2.2.1 (n + i) (by omega)
  rw [← this]
  simp only [TS.cfg, h2.1]
  congr 1
  push_cast
  ring

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Prog -/

namespace Grunbaum2003
namespace RayAlg

open scoped BigOperators

/-! ## Layer C toolkit: reasoning about RAM programs -/

variable {α β : Type}

namespace PExpr

def map (f : α → β) : PExpr α → PExpr β
  | const q => const q
  | reg r => reg (f r)
  | bin op a b => bin op (map f a) (map f b)

theorem eval_map (f : α → β) (g : β → ℝ) : ∀ e : PExpr α, (e.map f).eval g = e.eval (g ∘ f)
  | const q => rfl
  | reg r => rfl
  | bin op a b => by simp [map, eval, eval_map f g a, eval_map f g b]

instance : Add (PExpr α) := ⟨bin .add⟩
instance : Sub (PExpr α) := ⟨bin .sub⟩
instance : Mul (PExpr α) := ⟨bin .mul⟩

@[simp] theorem eval_add (g : α → ℝ) (a b : PExpr α) : (a + b).eval g = a.eval g + b.eval g := rfl
@[simp] theorem eval_sub (g : α → ℝ) (a b : PExpr α) : (a - b).eval g = a.eval g - b.eval g := rfl
@[simp] theorem eval_mul (g : α → ℝ) (a b : PExpr α) : (a * b).eval g = a.eval g * b.eval g := rfl
@[simp] theorem eval_const (g : α → ℝ) (q : ℚ) : (const q : PExpr α).eval g = (q : ℝ) := rfl
@[simp] theorem eval_reg (g : α → ℝ) (r : α) : (reg r).eval g = g r := rfl

def nat (n : ℕ) : PExpr α := const (n : ℚ)

@[simp] theorem eval_nat (g : α → ℝ) (n : ℕ) : (nat n : PExpr α).eval g = (n : ℝ) := by
  simp [nat]

def sumL : List (PExpr α) → PExpr α
  | [] => const 0
  | a :: l => a + sumL l

@[simp] theorem eval_sumL (g : α → ℝ) : ∀ l : List (PExpr α), (sumL l).eval g = (l.map (eval g)).sum
  | [] => by simp [sumL]
  | a :: l => by simp [sumL, eval_sumL g l]

def prodL : List (PExpr α) → PExpr α
  | [] => const 1
  | a :: l => a * prodL l

@[simp] theorem eval_prodL (g : α → ℝ) : ∀ l : List (PExpr α), (prodL l).eval g = (l.map (eval g)).prod
  | [] => by simp [prodL]
  | a :: l => by simp [prodL, eval_prodL g l]

def sumFin (n : ℕ) (f : Fin n → PExpr α) : PExpr α := sumL (List.ofFn f)

@[simp] theorem eval_sumFin (g : α → ℝ) (n : ℕ) (f : Fin n → PExpr α) :
    (sumFin n f).eval g = ∑ i, (f i).eval g := by
  simp [sumFin, List.map_ofFn, List.sum_ofFn, Function.comp_def]

def prodFin (n : ℕ) (f : Fin n → PExpr α) : PExpr α := prodL (List.ofFn f)

@[simp] theorem eval_prodFin (g : α → ℝ) (n : ℕ) (f : Fin n → PExpr α) :
    (prodFin n f).eval g = ∏ i, (f i).eval g := by
  simp [prodFin, List.map_ofFn, List.prod_ofFn, Function.comp_def]

noncomputable def det {n : ℕ} (M : Fin n → Fin n → PExpr α) : PExpr α :=
  sumL ((Finset.univ : Finset (Equiv.Perm (Fin n))).toList.map fun σ =>
    const (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * prodFin n fun i => M (σ i) i)

@[simp] theorem eval_det (g : α → ℝ) {n : ℕ} (M : Fin n → Fin n → PExpr α) :
    (det M).eval g = Matrix.det (Matrix.of fun i j => (M i j).eval g) := by
  simp only [det, eval_sumL, List.map_map, Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Units.smul_def]

end PExpr

/-! ### Derived statements -/

def Stmt.assign (dst : α) (e : PExpr α) : Stmt α := .par [(dst, e)]

def Stmt.seqList : List (Stmt α) → Stmt α
  | [] => .skip
  | a :: l => .seq a (seqList l)

def Stmt.seqFin (n : ℕ) (f : Fin n → Stmt α) : Stmt α := Stmt.seqList (List.ofFn f)

def Stmt.vset {n : ℕ} (X : Fin n → α) (e : Fin n → PExpr α) : Stmt α :=
  .par (List.ofFn fun i => (X i, e i))

def Stmt.loadFam {n : ℕ} (X : Fin n → α) (ix : α) (e : Fin n → PExpr α) : Stmt α :=
  Stmt.seqFin n fun i => .seq (.par [(ix, e i)]) (.load (X i) ix)

def Stmt.storeFam {n : ℕ} (X : Fin n → α) (ix : α) (e : Fin n → PExpr α) : Stmt α :=
  Stmt.seqFin n fun i => .seq (.par [(ix, e i)]) (.store ix (X i))

def Stmt.map (f : α → β) : Stmt α → Stmt β
  | .par l => .par (l.map fun p => (f p.1, p.2.map f))
  | .div dst a b => .div (f dst) (f a) (f b)
  | .load dst idx => .load (f dst) (f idx)
  | .store idx src => .store (f idx) (f src)
  | .query => .query
  | .skip => .skip
  | .seq a b => .seq (Stmt.map f a) (Stmt.map f b)
  | .ite a n z p => .ite (f a) (Stmt.map f n) (Stmt.map f z) (Stmt.map f p)
  | .while a b => .while (f a) (Stmt.map f b)

/-! ### `parUpd` lemmas -/

section parUpd
variable [DecidableEq α]

theorem parUpd_of_notMem (base : α → ℝ) :
    ∀ (l : List (α × PExpr α)) (g : α → ℝ) (r : α), (∀ p ∈ l, p.1 ≠ r) → parUpd base l g r = g r
  | [], g, r, _ => rfl
  | p :: l, g, r, h => by
      simp only [parUpd]
      rw [parUpd_of_notMem base l _ r (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      exact Function.update_of_ne (fun e => h p List.mem_cons_self e.symm) _ _

theorem parUpd_of_mem (base : α → ℝ) :
    ∀ (l : List (α × PExpr α)) (g : α → ℝ) (r : α) (e : PExpr α),
      (l.map Prod.fst).Nodup → (r, e) ∈ l → parUpd base l g r = e.eval base
  | [], g, r, e, _, h => by simp at h
  | p :: l, g, r, e, hnd, h => by
      simp only [parUpd]
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h with h | h
      · subst h
        rw [parUpd_of_notMem base l _ _ (by
          intro q hq e'
          exact hnd.1 (by rw [← e']; exact List.mem_map.2 ⟨q, hq, rfl⟩))]
        simp
      · exact parUpd_of_mem base l _ r e hnd.2 h

end parUpd

/-! ### Extension lemmas for register embeddings -/

section ext
variable [DecidableEq α] [DecidableEq β]

theorem ext_update {f : α → β} (hf : Function.Injective f) (a : α → ℝ) (g : β → ℝ)
    (x : α) (v : ℝ) :
    Function.update (Function.extend f a g) (f x) v =
      Function.extend f (Function.update a x v) g := by
  funext y
  by_cases hy : ∃ z, f z = y
  · obtain ⟨z, rfl⟩ := hy
    rw [hf.extend_apply]
    by_cases hz : z = x
    · subst hz; simp
    · rw [Function.update_of_ne (fun e => hz (hf e)), hf.extend_apply, Function.update_of_ne hz]
  · rw [Function.extend_apply' _ _ _ hy, Function.update_of_ne (fun e => hy ⟨x, e.symm⟩),
      Function.extend_apply' _ _ _ hy]

omit [DecidableEq α] [DecidableEq β] in
theorem ext_self {f : α → β} (hf : Function.Injective f) (g : β → ℝ) :
    Function.extend f (g ∘ f) g = g := by
  funext y
  by_cases hy : ∃ z, f z = y
  · obtain ⟨z, rfl⟩ := hy
    rw [hf.extend_apply]; rfl
  · rw [Function.extend_apply' _ _ _ hy]

omit [DecidableEq α] [DecidableEq β] in
theorem ext_ext {f : α → β} (hf : Function.Injective f) (a b : α → ℝ) (g : β → ℝ) :
    Function.extend f a (Function.extend f b g) = Function.extend f a g := by
  funext y
  by_cases hy : ∃ z, f z = y
  · obtain ⟨z, rfl⟩ := hy
    rw [hf.extend_apply, hf.extend_apply]
  · rw [Function.extend_apply' _ _ _ hy, Function.extend_apply' _ _ _ hy,
      Function.extend_apply' _ _ _ hy]

omit [DecidableEq α] [DecidableEq β] in
theorem ext_comp {f : α → β} (hf : Function.Injective f) (a : α → ℝ) (g : β → ℝ) :
    Function.extend f a g ∘ f = a := by
  funext z
  simp [hf.extend_apply]

theorem parUpd_map {f : α → β} (hf : Function.Injective f) (g : β → ℝ) :
    ∀ (l : List (α × PExpr α)) (a : α → ℝ),
      parUpd g (l.map fun p => (f p.1, p.2.map f)) (Function.extend f a g) =
        Function.extend f (parUpd (g ∘ f) l a) g
  | [], a => rfl
  | p :: l, a => by
      simp only [List.map_cons, parUpd]
      rw [PExpr.eval_map, ext_update hf, parUpd_map hf g l]

end ext

/-! ### Execution rules -/

section Exec
variable [DecidableEq α] {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ} {qr : Fin d → α}

theorem Stmt.Exec.assign (dst : α) (e : PExpr α) (s : RS α) :
    Stmt.Exec oracle qr (Stmt.assign dst e) s
      ⟨Function.update s.regs dst (e.eval s.regs), s.mem, s.queries⟩ :=
  Stmt.Exec.par [(dst, e)] s

theorem Stmt.Exec.vset {n : ℕ} {X : Fin n → α} (hX : Function.Injective X)
    (e : Fin n → PExpr α) (s : RS α) :
    Stmt.Exec oracle qr (Stmt.vset X e) s
      ⟨Function.extend X (fun i => (e i).eval s.regs) s.regs, s.mem, s.queries⟩ := by
  have h := Stmt.Exec.par (oracle := oracle) (qr := qr) (List.ofFn fun i => (X i, e i)) s
  have e' : parUpd s.regs (List.ofFn fun i => (X i, e i)) s.regs =
      Function.extend X (fun i => (e i).eval s.regs) s.regs := by
    funext r
    by_cases hr : ∃ i, X i = r
    · obtain ⟨i, rfl⟩ := hr
      rw [hX.extend_apply]
      apply parUpd_of_mem
      · rw [List.map_ofFn]
        exact List.nodup_ofFn.2 hX
      · exact (List.mem_ofFn' _ _).2 ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ hr]
      apply parUpd_of_notMem
      intro p hp e''
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      exact hr ⟨i, e''⟩
  rw [e'] at h
  exact h

/-- Total-correctness rule for `while`. -/
theorem Stmt.Exec.while_inv {a : α} {body : Stmt α} (Inv : RS α → Prop) (μ : RS α → ℕ)
    (hbody : ∀ s, Inv s → s.regs a ≠ 0 →
      ∃ m, Stmt.Exec oracle qr body s m ∧ Inv m ∧ μ m < μ s) :
    ∀ s, Inv s → ∃ s', Stmt.Exec oracle qr (.while a body) s s' ∧ Inv s' ∧ s'.regs a = 0 := by
  intro s
  induction h : μ s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    intro hs
    by_cases ha : s.regs a = 0
    · exact ⟨s, Stmt.Exec.while_done ha, hs, ha⟩
    · obtain ⟨m, hm, hI, hlt⟩ := hbody s hs ha
      obtain ⟨s', hs', hI', ha'⟩ := ih (μ m) (h ▸ hlt) m rfl hI
      exact ⟨s', Stmt.Exec.while_step ha hm hs', hI', ha'⟩

theorem Stmt.Exec.seqList_inv :
    ∀ (l : List (Stmt α)) (Inv : ℕ → RS α → Prop),
      (∀ i (hi : i < l.length) s, Inv i s → ∃ m, Stmt.Exec oracle qr l[i] s m ∧ Inv (i + 1) m) →
      ∀ s, Inv 0 s → ∃ s', Stmt.Exec oracle qr (Stmt.seqList l) s s' ∧ Inv l.length s'
  | [], Inv, _, s, hs => ⟨s, Stmt.Exec.skip s, hs⟩
  | a :: l, Inv, h, s, hs => by
      obtain ⟨m, hm, hI⟩ := h 0 (by simp) s hs
      obtain ⟨s', hs', hI'⟩ := Stmt.Exec.seqList_inv l (fun i => Inv (i + 1))
        (fun i hi s hs => h (i + 1) (by simpa using hi) s hs) m hI
      exact ⟨s', Stmt.Exec.seq hm hs', hI'⟩

theorem Stmt.Exec.seqFin_inv {n : ℕ} (f : Fin n → Stmt α) (Inv : ℕ → RS α → Prop)
    (h : ∀ (i : Fin n) s, Inv i.val s → ∃ m, Stmt.Exec oracle qr (f i) s m ∧ Inv (i.val + 1) m) :
    ∀ s, Inv 0 s → ∃ s', Stmt.Exec oracle qr (Stmt.seqFin n f) s s' ∧ Inv n s' := by
  intro s hs
  have := Stmt.Exec.seqList_inv (oracle := oracle) (qr := qr) (List.ofFn f) Inv (by
    intro i hi s hs
    have hi' : i < n := by simpa using hi
    have := h ⟨i, hi'⟩ s hs
    simpa using this) s hs
  simpa [Stmt.seqFin] using this

theorem Stmt.Exec.loadFam {n : ℕ} {X : Fin n → α} (hX : Function.Injective X) {ix : α}
    (hix : ∀ i, X i ≠ ix) (e : Fin n → PExpr α) (s : RS α) (addr : Fin n → ℕ)
    (he : ∀ i (regs' : α → ℝ), (∀ r, r ≠ ix → (∀ j, r ≠ X j) → regs' r = s.regs r) →
      (e i).eval regs' = (addr i : ℝ)) :
    ∃ s', Stmt.Exec oracle qr (Stmt.loadFam X ix e) s s' ∧
      (∀ i, s'.regs (X i) = s.mem (addr i)) ∧
      (∀ r, r ≠ ix → (∀ j, r ≠ X j) → s'.regs r = s.regs r) ∧
      s'.mem = s.mem ∧ s'.queries = s.queries := by
  have := Stmt.Exec.seqFin_inv (oracle := oracle) (qr := qr)
    (fun i => Stmt.seq (.par [(ix, e i)]) (.load (X i) ix))
    (fun k s' => (∀ i : Fin n, i.val < k → s'.regs (X i) = s.mem (addr i)) ∧
      (∀ r, r ≠ ix → (∀ j : Fin n, k ≤ j.val → r ≠ X j) →
        (∀ j : Fin n, j.val < k → r ≠ X j) → s'.regs r = s.regs r) ∧
      s'.mem = s.mem ∧ s'.queries = s.queries) (by
    intro i s1 ⟨h1, h2, h3, h4⟩
    have hev : (e i).eval s1.regs = (addr i : ℝ) := by
      apply he
      intro r hr hrX
      exact h2 r hr (fun j _ => hrX j) (fun j _ => hrX j)
    refine ⟨_, Stmt.Exec.seq (Stmt.Exec.par _ s1)
      (Stmt.Exec.load (X i) ix _ (addr i) (by simp [parUpd, hev])), ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        simp [parUpd, h3]
      · have hjlt : j.val < i.val := by
          have : j.val ≠ i.val := fun e => hji (Fin.ext e)
          omega
        have hne : X j ≠ X i := fun e => hji (hX e)
        simp only [parUpd]
        rw [Function.update_of_ne hne, Function.update_of_ne (hix j)]
        exact h1 j hjlt
    · intro r hr hge hlt
      have hne : r ≠ X i := hlt i (by omega)
      simp only [parUpd]
      rw [Function.update_of_ne hne, Function.update_of_ne hr]
      refine h2 r hr (fun j hj => ?_) (fun j hj => hlt j (by omega))
      by_cases hji : j = i
      · subst hji; exact hne
      · have : j.val ≠ i.val := fun e => hji (Fin.ext e)
        exact hge j (by omega)
    · exact h3
    · exact h4) s ⟨fun i hi => by omega, fun r _ _ _ => rfl, rfl, rfl⟩
  obtain ⟨s', hx, h1, h2, h3, h4⟩ := this
  exact ⟨s', hx, fun i => h1 i i.isLt, fun r hr hrX => h2 r hr (fun j hj => by
    have := j.isLt; omega) (fun j _ => hrX j), h3, h4⟩

theorem Stmt.Exec.storeFam {n : ℕ} (X : Fin n → α) {ix : α}
    (hix : ∀ i, X i ≠ ix) (e : Fin n → PExpr α) (s : RS α) (addr : Fin n → ℕ)
    (haddr : Function.Injective addr)
    (he : ∀ i (regs' : α → ℝ), (∀ r, r ≠ ix → regs' r = s.regs r) →
      (e i).eval regs' = (addr i : ℝ)) :
    ∃ s', Stmt.Exec oracle qr (Stmt.storeFam X ix e) s s' ∧
      (∀ i, s'.mem (addr i) = s.regs (X i)) ∧
      (∀ k, (∀ i, k ≠ addr i) → s'.mem k = s.mem k) ∧
      (∀ r, r ≠ ix → s'.regs r = s.regs r) ∧ s'.queries = s.queries := by
  have := Stmt.Exec.seqFin_inv (oracle := oracle) (qr := qr)
    (fun i => Stmt.seq (.par [(ix, e i)]) (.store ix (X i)))
    (fun k s' => (∀ i : Fin n, i.val < k → s'.mem (addr i) = s.regs (X i)) ∧
      (∀ c, (∀ i : Fin n, i.val < k → c ≠ addr i) → s'.mem c = s.mem c) ∧
      (∀ r, r ≠ ix → s'.regs r = s.regs r) ∧ s'.queries = s.queries) (by
    intro i s1 ⟨h1, h2, h3, h4⟩
    have hev : (e i).eval s1.regs = (addr i : ℝ) := he i _ h3
    refine ⟨_, Stmt.Exec.seq (Stmt.Exec.par _ s1)
      (Stmt.Exec.store ix (X i) _ (addr i) (by simp [parUpd, hev])), ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        simp only [parUpd, Function.update_self]
        rw [Function.update_of_ne (hix j)]
        exact h3 _ (hix j)
      · have hjlt : j.val < i.val := by
          have : j.val ≠ i.val := fun e => hji (Fin.ext e)
          omega
        have hne : addr j ≠ addr i := fun e => hji (haddr e)
        simp only
        rw [Function.update_of_ne hne]
        exact h1 j hjlt
    · intro c hc
      have hne : c ≠ addr i := hc i (by omega)
      simp only
      rw [Function.update_of_ne hne]
      exact h2 c (fun j hj => hc j (by omega))
    · intro r hr
      simp only [parUpd]
      rw [Function.update_of_ne hr]
      exact h3 r hr
    · exact h4) s ⟨fun i hi => by omega, fun c _ => rfl, fun r _ => rfl, rfl⟩
  obtain ⟨s', hx, h1, h2, h3, h4⟩ := this
  exact ⟨s', hx, fun i => h1 i i.isLt, fun k hk => h2 k (fun i _ => hk i), h3, h4⟩

end Exec

/-- Running a program on an embedded copy of its registers. -/
theorem Stmt.Exec.map [DecidableEq α] [DecidableEq β] {d : ℕ}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} {f : α → β} (hf : Function.Injective f)
    {qr : Fin d → α} (hqr : Function.Injective qr) {st : Stmt α} {s s' : RS α}
    (hx : Stmt.Exec oracle qr st s s') :
    ∀ g : β → ℝ, g ∘ f = s.regs →
      Stmt.Exec oracle (f ∘ qr) (st.map f) ⟨g, s.mem, s.queries⟩
        ⟨Function.extend f s'.regs g, s'.mem, s'.queries⟩ := by
  induction hx with
  | par l s =>
    intro g hg
    have h := Stmt.Exec.par (oracle := oracle) (qr := f ∘ qr)
      (l.map fun p => (f p.1, p.2.map f)) ⟨g, s.mem, s.queries⟩
    have key := parUpd_map hf g l s.regs
    rw [← hg, ext_self hf, hg] at key
    simp only at h
    rw [key] at h
    exact h
  | div dst a b s hb =>
    intro g hg
    have ha' : g (f a) = s.regs a := by rw [← hg]; rfl
    have hb' : g (f b) = s.regs b := by rw [← hg]; rfl
    have h := Stmt.Exec.div (oracle := oracle) (qr := f ∘ qr) (f dst) (f a) (f b)
      ⟨g, s.mem, s.queries⟩ (by simpa [hb'] using hb)
    simp only [ha', hb'] at h
    have key := ext_update hf s.regs g dst (s.regs a / s.regs b)
    rw [← hg, ext_self hf, hg] at key
    rw [key] at h
    exact h
  | load dst idx s n hn =>
    intro g hg
    have hi' : g (f idx) = s.regs idx := by rw [← hg]; rfl
    have h := Stmt.Exec.load (oracle := oracle) (qr := f ∘ qr) (f dst) (f idx)
      ⟨g, s.mem, s.queries⟩ n (by simpa [hi'] using hn)
    simp only at h
    have key := ext_update hf s.regs g dst (s.mem n)
    rw [← hg, ext_self hf, hg] at key
    rw [key] at h
    exact h
  | store idx src s n hn =>
    intro g hg
    have hi' : g (f idx) = s.regs idx := by rw [← hg]; rfl
    have hs' : g (f src) = s.regs src := by rw [← hg]; rfl
    have h := Stmt.Exec.store (oracle := oracle) (qr := f ∘ qr) (f idx) (f src)
      ⟨g, s.mem, s.queries⟩ n (by simpa [hi'] using hn)
    simp only [hs'] at h
    have key : Function.extend f s.regs g = g := by rw [← hg, ext_self hf]
    rw [key]
    exact h
  | query s hv =>
    intro g hg
    have hvec : (fun i => g ((f ∘ qr) i)) = fun i => s.regs (qr i) := by
      funext i; rw [← hg]; rfl
    have h := Stmt.Exec.query (oracle := oracle) (qr := f ∘ qr) ⟨g, s.mem, s.queries⟩
      (by simp only; rw [hvec]; exact hv)
    simp only [hvec] at h
    have key : Function.extend (f ∘ qr) (oracle fun i => s.regs (qr i)) g =
        Function.extend f (Function.extend qr (oracle fun i => s.regs (qr i)) s.regs) g := by
      funext y
      by_cases hy : ∃ z, f z = y
      · obtain ⟨z, rfl⟩ := hy
        rw [hf.extend_apply]
        by_cases hz : ∃ i, qr i = z
        · obtain ⟨i, rfl⟩ := hz
          rw [hqr.extend_apply]
          exact (hf.comp hqr).extend_apply _ _ i
        · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
          · rw [← hg]; rfl
          · rintro ⟨i, hi⟩
            exact hz ⟨i, hf hi⟩
      · rw [Function.extend_apply' _ _ _ hy, Function.extend_apply']
        rintro ⟨i, hi⟩
        exact hy ⟨qr i, hi⟩
    rw [key] at h
    exact h
  | skip s =>
    intro g hg
    have key : Function.extend f s.regs g = g := by rw [← hg, ext_self hf]
    rw [key]
    exact Stmt.Exec.skip _
  | @seq a b s m s' _ _ ih₁ ih₂ =>
    intro g hg
    have h1 := ih₁ g hg
    have h2 := ih₂ (Function.extend f m.regs g) (ext_comp hf _ _)
    rw [ext_ext hf] at h2
    exact Stmt.Exec.seq h1 h2
  | @ite_neg a sn sz sp s s' ha _ ih =>
    intro g hg
    exact Stmt.Exec.ite_neg (by show g (f a) < 0; rw [show g (f a) = s.regs a from by rw [← hg]; rfl]; exact ha) (ih g hg)
  | @ite_zero a sn sz sp s s' ha _ ih =>
    intro g hg
    exact Stmt.Exec.ite_zero (by show g (f a) = 0; rw [show g (f a) = s.regs a from by rw [← hg]; rfl]; exact ha) (ih g hg)
  | @ite_pos a sn sz sp s s' ha _ ih =>
    intro g hg
    exact Stmt.Exec.ite_pos (by show 0 < g (f a); rw [show g (f a) = s.regs a from by rw [← hg]; rfl]; exact ha) (ih g hg)
  | @while_done a body s ha =>
    intro g hg
    have key : Function.extend f s.regs g = g := by rw [← hg, ext_self hf]
    rw [key]
    exact Stmt.Exec.while_done (by show g (f a) = 0; rw [show g (f a) = s.regs a from by rw [← hg]; rfl]; exact ha)
  | @while_step a body s m s' ha _ _ ih₁ ih₂ =>
    intro g hg
    have h1 := ih₁ g hg
    have h2 := ih₂ (Function.extend f m.regs g) (ext_comp hf _ _)
    rw [ext_ext hf] at h2
    exact Stmt.Exec.while_step (by show g (f a) ≠ 0; rw [show g (f a) = s.regs a from by rw [← hg]; rfl]; exact ha) h1 h2

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Sec -/

namespace Grunbaum2003
namespace RayAlg

/-! ## The one-dimensional secant search

`A i + B i * x` are finitely many affine functions; a *sample* at `x` is the value of their
maximum.  All `A i ≤ 1` and some `A i = 1` (the maximum at `0` is `1`). -/

section Sec
variable {ι : Type} (A B : ι → ℝ)

/-- `f` is the maximum of the affine functions at `x`. -/
def Samp (x f : ℝ) : Prop := (∀ i, A i + B i * x ≤ f) ∧ ∃ i, A i + B i * x = f

variable {A B}

/-- An index active at two points is active in between. -/
theorem Samp.between {xl xr y fl fr fy : ℝ} {i : ι} (hlr : xl < xr) (hly : xl ≤ y) (hyr : y ≤ xr)
    (hl : Samp A B xl fl) (hr : Samp A B xr fr) (hy : Samp A B y fy)
    (hil : A i + B i * xl = fl) (hir : A i + B i * xr = fr) : A i + B i * y = fy := by
  obtain ⟨j, hj⟩ := hy.2
  have h1 := hl.1 j
  have h2 := hr.1 j
  have h3 := hy.1 i
  have e1 : (xr - xl) * fy = (xr - y) * (A j + B j * xl) + (y - xl) * (A j + B j * xr) := by
    rw [← hj]; ring
  have e2 : (xr - xl) * (A i + B i * y) = (xr - y) * fl + (y - xl) * fr := by
    rw [← hil, ← hir]; ring
  have h4 : (xr - y) * (A j + B j * xl) ≤ (xr - y) * fl :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h5 : (y - xl) * (A j + B j * xr) ≤ (y - xl) * fr :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : (xr - xl) * fy ≤ (xr - xl) * (A i + B i * y) := by linarith
  have h7 : fy ≤ A i + B i * y := le_of_mul_le_mul_left h6 (by linarith)
  linarith

variable (h0 : (∀ i, A i ≤ 1) ∧ ∃ i, A i = 1)
include h0

/-- The lower line `1 + σ x` through the samples at `-1` and `0`. -/
theorem lam_le {fm x f : ℝ} (hm : Samp A B (-1) fm) (hx : 0 ≤ x) (h : Samp A B x f) :
    1 + (1 - fm) * x ≤ f := by
  obtain ⟨i, hi⟩ := h0.2
  have h1 := hm.1 i
  have h2 := h.1 i
  rw [hi] at h1 h2
  have : (1 - fm) * x ≤ B i * x := mul_le_mul_of_nonneg_right (by linarith) hx
  linarith

omit h0 in
/-- Chord inequality at `0 < xb < xa`, with the active index at `xb`. -/
theorem chord_ineq {xa xb fa fb : ℝ} {i : ι} (hb : 0 < xb)
    (ha : Samp A B xa fa) (hi : A i + B i * xb = fb) :
    (1 - A i) * (xa - xb) ≤ (fa - 1) * xb - (fb - 1) * xa := by
  have h1 := ha.1 i
  have h2 : (A i + B i * xa - 1) * xb ≤ (fa - 1) * xb :=
    mul_le_mul_of_nonneg_right (by linarith) hb.le
  rw [← hi]
  nlinarith

/-- One step of the secant search. -/
theorem secant_step {fm xa xb fa fb : ℝ} (hm : Samp A B (-1) fm) (hb : 0 < xb) (hab : xb < xa)
    (ha : Samp A B xa fa) (hsb : Samp A B xb fb)
    (hA : fb ≠ 1 + (1 - fm) * xb) (hB : (fa - 1) * xb ≠ (fb - 1) * xa) :
    xa - xb ≠ 0 ∧ (fa - fb) / (xa - xb) - (1 - fm) ≠ 0 ∧
    (let μ := (fa - fb) / (xa - xb)
     let xn := (1 - (fb - μ * xb)) / (μ - (1 - fm))
     0 < xn ∧ xn < xb ∧ (fa - fb) * (xn - xb) = (1 + (1 - fm) * xn - fb) * (xa - xb)) := by
  have hd : 0 < xa - xb := by linarith
  obtain ⟨i, hi⟩ := hsb.2
  have hch := chord_ineq hb ha hi
  have hAi := h0.1 i
  have hlt : (fb - 1) * xa < (fa - 1) * xb := by
    have : 0 ≤ (1 - A i) * (xa - xb) := mul_nonneg (by linarith) hd.le
    exact lt_of_le_of_ne (by linarith) (Ne.symm hB)
  have hlam := lam_le h0 hm hb.le hsb
  have hlam' : 1 + (1 - fm) * xb < fb := lt_of_le_of_ne hlam (Ne.symm hA)
  set μ := (fa - fb) / (xa - xb) with hμ
  have hμd : μ * (xa - xb) = fa - fb := by rw [hμ]; field_simp
  -- Λ0 < 1
  have hL : fb - μ * xb < 1 := by
    have : (fb - μ * xb) * (xa - xb) < 1 * (xa - xb) := by nlinarith
    exact lt_of_mul_lt_mul_right this hd.le
  have hμσ : 0 < μ - (1 - fm) := by
    have : 0 < (μ - (1 - fm)) * xb := by nlinarith
    exact pos_of_mul_pos_left this hb.le
  refine ⟨hd.ne', hμσ.ne', ?_⟩
  simp only
  set xn := (1 - (fb - μ * xb)) / (μ - (1 - fm)) with hxn
  have hxnd : xn * (μ - (1 - fm)) = 1 - (fb - μ * xb) := by rw [hxn]; field_simp
  refine ⟨div_pos (by linarith) hμσ, ?_, ?_⟩
  · have : xn * (μ - (1 - fm)) < xb * (μ - (1 - fm)) := by nlinarith
    exact lt_of_mul_lt_mul_right this hμσ.le
  · have : (fa - fb) * (xn - xb) = μ * (xa - xb) * (xn - xb) := by rw [hμd]
    rw [this]
    nlinarith

/-- When the search stops, the sample point lies on a line active at `0`. -/
theorem secant_stop {fm xa xb fa fb : ℝ} (hm : Samp A B (-1) fm) (hb : 0 < xb) (hab : xb < xa)
    (ha : Samp A B xa fa) (hsb : Samp A B xb fb)
    (hstop : fb = 1 + (1 - fm) * xb ∨ (fa - 1) * xb = (fb - 1) * xa) :
    ∃ i, A i = 1 ∧ A i + B i * xb = fb := by
  rcases hstop with hA | hB
  · obtain ⟨i, hi⟩ := h0.2
    refine ⟨i, hi, ?_⟩
    have h1 := hm.1 i
    have h2 := hsb.1 i
    rw [hi] at h1 h2 ⊢
    have h3 : B i * xb ≤ (1 - fm) * xb := by linarith
    have h4 : B i ≤ 1 - fm := le_of_mul_le_mul_right h3 hb
    have h5 : B i = 1 - fm := le_antisymm h4 (by linarith)
    rw [hA, h5]
  · obtain ⟨i, hi⟩ := hsb.2
    refine ⟨i, ?_, hi⟩
    have hch := chord_ineq hb ha hi
    have hAi := h0.1 i
    have : (1 - A i) * (xa - xb) ≤ 0 := by linarith
    have h1 : 0 ≤ 1 - A i := by linarith
    have h2 : 0 < xa - xb := by linarith
    nlinarith

end Sec

/-! ### Counting the samples -/

theorem exists_three_lt {s : Finset ℕ} (h : 2 < s.card) :
    ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · exact ⟨a, b, c, ha, hb, hc, h1, h2⟩
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · exact ⟨a, c, b, ha, hc, hb, h3, h2⟩
      · exact absurd h3 hac
      · exact ⟨c, a, b, hc, ha, hb, h3, h1⟩
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · exact ⟨b, a, c, hb, ha, hc, h1, h2⟩
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · exact ⟨b, c, a, hb, hc, ha, h3, h2⟩
      · exact absurd h3 hbc
      · exact ⟨c, b, a, hc, hb, ha, h3, h1⟩

/-- A run of the secant search with `N` samples `x 0 > x 1 > … > x (N-1)`. -/
structure SecRun {ι : Type} (A B : ι → ℝ) (U : Finset ι) (σ : ℝ) (N : ℕ) (x f : ℕ → ℝ) : Prop where
  samp : ∀ j, j < N → Samp A B (x j) (f j)
  act : ∀ j, j < N → ∀ i, A i + B i * x j = f j → i ∈ U
  anti : ∀ j, j + 1 < N → x (j + 1) < x j
  nonstop : ∀ j, 1 ≤ j → j + 1 < N → f j ≠ 1 + σ * x j
  cross : ∀ j, 1 ≤ j → j + 1 < N →
    (f (j - 1) - f j) * (x (j + 1) - x j) = (1 + σ * x (j + 1) - f j) * (x (j - 1) - x j)

theorem SecRun.anti_le {ι : Type} {A B : ι → ℝ} {U : Finset ι} {σ : ℝ} {N : ℕ} {x f : ℕ → ℝ}
    (h : SecRun A B U σ N x f) {j k : ℕ} (hjk : j ≤ k) (hk : k < N) : x k ≤ x j := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact le_trans (h.anti k hk).le (ih (by omega) (by omega))
    · have : j = k + 1 := by omega
      subst this; exact le_rfl

theorem SecRun.anti_lt {ι : Type} {A B : ι → ℝ} {U : Finset ι} {σ : ℝ} {N : ℕ} {x f : ℕ → ℝ}
    (h : SecRun A B U σ N x f) {j k : ℕ} (hjk : j < k) (hk : k < N) : x k < x j :=
  lt_of_lt_of_le (h.anti (k - 1) (by omega) |> fun e => by
    have : k - 1 + 1 = k := by omega
    rwa [this] at e) (h.anti_le (by omega) (by omega))

/-- No index is active at three non-final samples; hence `N ≤ 2 |U| + 1`. -/
theorem SecRun.length_le {ι : Type} [DecidableEq ι] {A B : ι → ℝ} {U : Finset ι} {σ : ℝ} {N : ℕ}
    {x f : ℕ → ℝ} (h : SecRun A B U σ N x f) : N ≤ 2 * U.card + 1 := by
  classical
  -- choose an active index for every non-final sample
  rcases Nat.lt_or_ge N 2 with hN | hN
  · omega
  obtain ⟨i0, _⟩ := (h.samp 0 (by omega)).2
  let ia : ℕ → ι := fun j => if hj : j < N then Classical.choose (h.samp j hj).2 else i0
  have hia : ∀ j (hj : j < N), A (ia j) + B (ia j) * x j = f j := by
    intro j hj
    simp only [ia, dif_pos hj]
    exact Classical.choose_spec (h.samp j hj).2
  let T := Finset.range (N - 1)
  have himg : T.image ia ⊆ U := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have hj' : j < N := by have := Finset.mem_range.1 hj; omega
    exact h.act j hj' _ (hia j hj')
  have hfib : ∀ i ∈ T.image ia, (T.filter fun j => ia j = i).card ≤ 2 := by
    intro i _
    by_contra hcon
    obtain ⟨a, b, c, ha, hb, hc, hab, hbc⟩ := exists_three_lt (by omega : 2 < (T.filter fun j => ia j = i).card)
    simp only [T, Finset.mem_filter, Finset.mem_range] at ha hb hc
    have haN : a < N := by omega
    have hbN : b < N := by omega
    have hcN : c < N := by omega
    have eA : A i + B i * x a = f a := ha.2 ▸ hia a haN
    have eC : A i + B i * x c = f c := hc.2 ▸ hia c hcN
    have hxca : x c < x a := h.anti_lt (by omega) hcN
    have act : ∀ j, a ≤ j → j ≤ c → A i + B i * x j = f j := by
      intro j haj hjc
      exact Samp.between hxca (h.anti_le hjc hcN) (h.anti_le haj (by omega))
        (h.samp c hcN) (h.samp a haN) (h.samp j (by omega)) eC eA
    have e1 := act (b - 1) (by omega) (by omega)
    have e2 := act b (by omega) (by omega)
    have e3 := act (b + 1) (by omega) (by omega)
    have hcr := h.cross b (by omega) (by omega)
    have hns := h.nonstop (b + 1) (by omega) (by omega)
    have hlt : x b < x (b - 1) := h.anti_lt (by omega) hbN
    apply hns
    rw [← e1, ← e2] at hcr
    have : (x (b - 1) - x b) * (B i * (x (b + 1) - x b) - (1 + σ * x (b + 1) - (A i + B i * x b))) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · rw [← e3]; linarith
  have hcard := Finset.card_le_mul_card_image T 2 hfib
  have hU := Finset.card_le_card himg
  have hT : T.card = N - 1 := by simp [T]
  omega

/-- Extending a run by one sample. -/
theorem SecRun.extend {ι : Type} {A B : ι → ℝ} {U : Finset ι} {σ : ℝ} {N : ℕ} {x f : ℕ → ℝ}
    (h : SecRun A B U σ N x f) (hN : 2 ≤ N) (xn fn : ℝ)
    (hs : Samp A B xn fn) (hact : ∀ i, A i + B i * xn = fn → i ∈ U) (hlt : xn < x (N - 1))
    (hns : f (N - 1) ≠ 1 + σ * x (N - 1))
    (hcr : (f (N - 2) - f (N - 1)) * (xn - x (N - 1)) =
      (1 + σ * xn - f (N - 1)) * (x (N - 2) - x (N - 1))) :
    SecRun A B U σ (N + 1) (Function.update x N xn) (Function.update f N fn) := by
  have upd_lt : ∀ {g : ℕ → ℝ} {v : ℝ} {j : ℕ}, j < N → Function.update g N v j = g j :=
    fun hj => Function.update_of_ne (by omega) _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjN : j = N
    · subst hjN; simpa using hs
    · rw [upd_lt (by omega), upd_lt (by omega)]; exact h.samp j (by omega)
  · intro j hj i hi
    by_cases hjN : j = N
    · subst hjN
      simp only [Function.update_self] at hi
      exact hact i hi
    · rw [upd_lt (by omega), upd_lt (by omega)] at hi
      exact h.act j (by omega) i hi
  · intro j hj
    by_cases hjN : j + 1 = N
    · have e : j = N - 1 := by omega
      rw [hjN, Function.update_self, upd_lt (by omega), e]; exact hlt
    · rw [upd_lt (by omega), upd_lt (by omega)]; exact h.anti j (by omega)
  · intro j h1 hj
    rw [upd_lt (by omega), upd_lt (by omega)]
    by_cases hjN : j + 1 = N
    · have e : j = N - 1 := by omega
      rw [e]; exact hns
    · exact h.nonstop j h1 (by omega)
  · intro j h1 hj
    by_cases hjN : j + 1 = N
    · have e : j = N - 1 := by omega
      have e' : j - 1 = N - 2 := by omega
      rw [hjN, Function.update_self, upd_lt (by omega), upd_lt (by omega), upd_lt (by omega),
        upd_lt (by omega), e', e]
      exact hcr
    · repeat rw [upd_lt (by omega)]
      exact h.cross j h1 (by omega)

/-- Known lines stay strictly below the lower line on `(0, 1/acc]`. -/
theorem known_excluded {δ γ acc x : ℝ} (hδ : 0 < δ) (hacc : (1 + γ ^ 2) / δ ≤ acc) (hx : 0 < x)
    (hxa : x ≤ 1 / acc) : γ * x < δ := by
  have hpos : 0 < (1 + γ ^ 2) / δ := div_pos (by positivity) hδ
  have hacc0 : 0 < acc := lt_of_lt_of_le hpos hacc
  have h1 : x * acc ≤ 1 := by
    rw [le_div_iff₀ hacc0] at hxa; exact hxa
  have h2 : 1 + γ ^ 2 ≤ acc * δ := by
    rw [div_le_iff₀ hδ] at hacc; exact hacc
  have h3 : x * (1 + γ ^ 2) ≤ δ := by nlinarith
  nlinarith [sq_nonneg (γ - 1)]

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Geo -/

namespace Grunbaum2003
namespace RayAlg

open scoped BigOperators Matrix Classical

/-! ## Polytope geometry, Cramer basic feasible solutions, and face-lattice closure -/

def dot {d : ℕ} (a x : Fin d → ℝ) : ℝ := ∑ l, a l * x l

@[simp] theorem dot_zero_right {d : ℕ} (a : Fin d → ℝ) : dot a 0 = 0 := by
  simp [dot]

@[simp] theorem dot_zero_left {d : ℕ} (x : Fin d → ℝ) : dot 0 x = 0 := by
  simp [dot]

theorem dot_add_right {d : ℕ} (a x y : Fin d → ℝ) : dot a (x + y) = dot a x + dot a y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_sub_right {d : ℕ} (a x y : Fin d → ℝ) : dot a (x - y) = dot a x - dot a y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_smul_right {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (x : Fin d → ℝ) :
    dot a (c • x) = c * dot a x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem dot_comm {d : ℕ} (a x : Fin d → ℝ) : dot a x = dot x a :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem dot_self_eq_zero {d : ℕ} {x : Fin d → ℝ} : dot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext l
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have hl := (Finset.sum_eq_zero_iff_of_nonneg hle).1 h l (Finset.mem_univ l)
    exact mul_self_eq_zero.1 hl
  · rintro rfl; simp

theorem dot_self_pos {d : ℕ} {x : Fin d → ℝ} (hx : x ≠ 0) : 0 < dot x x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun l _ => mul_self_nonneg (x l))
    (Ne.symm (mt dot_self_eq_zero.1 hx))

def vecOfLinear {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) : Fin d → ℝ :=
  fun l => f (Pi.single l 1)

theorem dot_vecOfLinear {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    dot (vecOfLinear f) x = f x := by
  have hx : x = ∑ l : Fin d, x l • Pi.single l (1 : ℝ) := by
    funext i
    simp [Pi.single_apply]
  conv_rhs => rw [hx, map_sum]
  simp only [dot, vecOfLinear, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

def vecOfCLM {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) : Fin d → ℝ :=
  vecOfLinear L.toLinearMap

theorem dot_vecOfCLM {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (x : Fin d → ℝ) :
    dot (vecOfCLM L) x = L x :=
  dot_vecOfLinear L.toLinearMap x

/-! ### Cramer basic feasible solutions and recession-free polyhedra -/

def IsCramerBFS {d M : ℕ} (α : Fin M → Fin d → ℝ) (β : Fin M → ℝ) (u : Fin d → ℝ) : Prop :=
  (∀ r, dot (α r) u ≤ β r) ∧
    ∃ idx : Fin d → Fin M, (Matrix.of fun i l => α (idx i) l).det ≠ 0 ∧
      ∀ i, dot (α (idx i)) u = β (idx i)

theorem cramer_sol_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (hdet : A.det ≠ 0) :
    let u : Fin d → ℝ := fun l => (A.updateCol l b).det / A.det
    ∀ i, dot (A i) u = b i := by
  intro u i
  have hu : u = A.det⁻¹ • A.cramer b := by
    funext l
    simp [u, Matrix.cramer_apply, div_eq_inv_mul]
  have hmv : (A *ᵥ u) i = b i := by
    rw [hu, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  simpa [Matrix.mulVec, dotProduct, dot] using hmv

theorem cramer_sol_is_bfs {d M : ℕ} (α : Fin M → Fin d → ℝ) (β : Fin M → ℝ)
    (idx : Fin d → Fin M) (hdet : (Matrix.of fun i l => α (idx i) l).det ≠ 0)
    (hfeas : ∀ r, dot (α r)
      (fun l => ((Matrix.of fun i l' => α (idx i) l').updateCol l (fun i => β (idx i))).det /
        (Matrix.of fun i l' => α (idx i) l').det) ≤ β r) :
    IsCramerBFS α β
      (fun l => ((Matrix.of fun i l' => α (idx i) l').updateCol l (fun i => β (idx i))).det /
        (Matrix.of fun i l' => α (idx i) l').det) := by
  refine ⟨hfeas, idx, hdet, ?_⟩
  intro i
  exact cramer_sol_eq (Matrix.of fun i' l' => α (idx i') l') (fun i' => β (idx i')) hdet i

theorem exists_nonzero_perp_of_span_ne_top {d : ℕ} {S : Set (Fin d → ℝ)}
    (h : Submodule.span ℝ S ≠ ⊤) :
    ∃ z : Fin d → ℝ, z ≠ 0 ∧ ∀ v ∈ S, dot v z = 0 := by
  have hlt : Submodule.span ℝ S < ⊤ := lt_top_iff_ne_top.2 h
  obtain ⟨f, hf0, hfbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨vecOfLinear f, ?_, ?_⟩
  · intro hz
    apply hf0
    apply DFunLike.ext
    intro x
    rw [← dot_vecOfLinear, hz, dot_zero_left, LinearMap.zero_apply]
  · intro v hv
    rw [dot_comm, dot_vecOfLinear]
    have hmem : f v ∈ (Submodule.span ℝ S).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span hv)
    rwa [hfbot, Submodule.mem_bot] at hmem

theorem exists_det_ne_zero_of_span_eq_top {d M : ℕ} (α : Fin M → Fin d → ℝ)
    (Aset : Finset (Fin M)) (hsp : Submodule.span ℝ (Set.image α Aset) = ⊤) :
    ∃ idx : Fin d → Fin M, (∀ i, idx i ∈ Aset) ∧
      (Matrix.of fun i l => α (idx i) l).det ≠ 0 := by
  let v : Aset → Fin d → ℝ := fun a => α a.val
  have hrange : Set.range v = Set.image α Aset := by
    ext x; simp [v]
  obtain ⟨κ, emb, _, hsp', hli⟩ := exists_linearIndependent' ℝ v
  rw [hrange, hsp] at hsp'
  have : Finite κ := hli.finite
  cases nonempty_fintype κ
  have hcard : Fintype.card κ = d := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp', finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (emb (e i)).val, fun i => (emb (e i)).property, ?_⟩
  have hli' : LinearIndependent ℝ (fun i : Fin d => α (emb (e i)).val) :=
    hli.comp e e.injective
  have hu : IsUnit (Matrix.of fun i l => α (emb (e i)).val l) :=
    (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of fun i l => α (emb (e i)).val l)).1 hli'
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu |>.ne_zero

theorem polyhedron_subset_convexHull_bfs {d M : ℕ} (α : Fin M → Fin d → ℝ) (β : Fin M → ℝ)
    (hrec : ∀ w, (∀ r, dot (α r) w ≤ 0) → w = 0) :
    { x : Fin d → ℝ | ∀ r, dot (α r) x ≤ β r } ⊆ convexHull ℝ { u | IsCramerBFS α β u } := by
  let act : (Fin d → ℝ) → Finset (Fin M) := fun x => Finset.univ.filter fun r => dot (α r) x = β r
  suffices ∀ (k : ℕ) (x : Fin d → ℝ), M - (act x).card = k →
      (∀ r, dot (α r) x ≤ β r) → x ∈ convexHull ℝ { u | IsCramerBFS α β u } by
    intro x hx
    exact this _ x rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hsp : Submodule.span ℝ (Set.image α (act x)) = ⊤
    · obtain ⟨idx, hidx, hdet⟩ := exists_det_ne_zero_of_span_eq_top α (act x) hsp
      apply subset_convexHull ℝ { u | IsCramerBFS α β u }
      refine ⟨hx, idx, hdet, fun i => ?_⟩
      exact (Finset.mem_filter.1 (hidx i)).2
    · obtain ⟨z, hz0, hperp⟩ := exists_nonzero_perp_of_span_ne_top hsp
      have hex_pos : ∀ w : Fin d → ℝ, w ≠ 0 → ∃ r, 0 < dot (α r) w := by
        intro w hw
        by_contra! hall
        exact hw (hrec w hall)
      have step_ray : ∀ w : Fin d → ℝ, w ≠ 0 → (∀ r ∈ act x, dot (α r) w = 0) →
          ∃ t : ℝ, 0 < t ∧ (∀ r, dot (α r) (x + t • w) ≤ β r) ∧
            (act x).card < (act (x + t • w)).card := by
        intro w hw hwp
        obtain ⟨r₀, hr₀⟩ := hex_pos w hw
        let Ppos := Finset.univ.filter fun r : Fin M => 0 < dot (α r) w
        have hPne : Ppos.Nonempty := ⟨r₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr₀⟩⟩
        let ratio : Fin M → ℝ := fun r => (β r - dot (α r) x) / dot (α r) w
        obtain ⟨r_min, hr_mem, hr_le⟩ := Ppos.exists_min_image ratio hPne
        have hr_pos : 0 < dot (α r_min) w := (Finset.mem_filter.1 hr_mem).2
        have hr_not_act : r_min ∉ act x := by
          intro hm
          linarith [hwp r_min hm]
        have hslack : dot (α r_min) x < β r_min := by
          refine lt_of_le_of_ne (hx r_min) fun heq => hr_not_act ?_
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, heq⟩
        let t := ratio r_min
        have ht : 0 < t := div_pos (by linarith) hr_pos
        refine ⟨t, ht, ?_, ?_⟩
        · intro r
          rw [dot_add_right, dot_smul_right]
          rcases lt_trichotomy (dot (α r) w) 0 with hneg | hzero | hpos
          · have : t * dot (α r) w < 0 := mul_neg_of_pos_of_neg ht hneg
            linarith [hx r]
          · rw [hzero, mul_zero, add_zero]; exact hx r
          · have hle := hr_le r (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos⟩)
            have : t * dot (α r) w ≤ β r - dot (α r) x := (le_div_iff₀ hpos).1 hle
            linarith
        · refine Finset.card_lt_card ⟨?_, ?_⟩
          · intro r hr
            have hra := (Finset.mem_filter.1 hr).2
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            rw [dot_add_right, dot_smul_right, hwp r hr, mul_zero, add_zero, hra]
          · intro hsub
            apply hr_not_act
            apply hsub
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            rw [dot_add_right, dot_smul_right]
            have : t * dot (α r_min) w = β r_min - dot (α r_min) x :=
              div_mul_cancel₀ _ hr_pos.ne'
            linarith
      have hzp : ∀ r ∈ act x, dot (α r) z = 0 := fun r hr =>
        hperp _ (Set.mem_image_of_mem α hr)
      have hnzp : ∀ r ∈ act x, dot (α r) (-z) = 0 := by
        intro r hr
        have : -z = (-1 : ℝ) • z := by simp
        rw [this, dot_smul_right, hzp r hr, mul_zero]
      obtain ⟨t₁, ht₁, hx₁, hc₁⟩ := step_ray z hz0 hzp
      obtain ⟨t₂, ht₂, hx₂, hc₂⟩ := step_ray (-z) (neg_ne_zero.2 hz0) hnzp
      have hle₁ : (act (x + t₁ • z)).card ≤ M := by
        simpa using Finset.card_le_univ (act (x + t₁ • z))
      have hle₂ : (act (x + t₂ • (-z))).card ≤ M := by
        simpa using Finset.card_le_univ (act (x + t₂ • (-z)))
      have hm₁ := ih (M - (act (x + t₁ • z)).card) (by omega) _ rfl hx₁
      have hm₂ := ih (M - (act (x + t₂ • (-z))).card) (by omega) _ rfl hx₂
      have hsum : 0 < t₁ + t₂ := by linarith
      have hcomb : (t₂ / (t₁ + t₂)) • (x + t₁ • z) + (t₁ / (t₁ + t₂)) • (x + t₂ • (-z)) = x := by
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        field_simp [hsum.ne']
        ring
      rw [← hcomb]
      exact convex_convexHull ℝ _ hm₁ hm₂
        (div_nonneg ht₂.le hsum.le) (div_nonneg ht₁.le hsum.le)
        (by field_simp [hsum.ne']; ring)

/-! ### Recession cone test via bounded box `[-1, 1]^d` -/

def recAlpha {d k : ℕ} (a : Fin k → Fin d → ℝ) (r : Fin (k + 2 * d)) : Fin d → ℝ :=
  if h1 : r.val < k then a ⟨r.val, h1⟩
  else if h2 : r.val < k + d then Pi.single ⟨r.val - k, by omega⟩ 1
  else -Pi.single ⟨r.val - (k + d), by omega⟩ 1

def recBeta (k d : ℕ) (r : Fin (k + 2 * d)) : ℝ :=
  if r.val < k then 0 else 1

theorem rec_feasible_nonpos {d k : ℕ} (a : Fin k → Fin d → ℝ) {u : Fin d → ℝ}
    (h : ∀ r, dot (recAlpha a r) u ≤ recBeta k d r) (j : Fin k) :
    dot (a j) u ≤ 0 := by
  have hr := h ⟨j.val, by omega⟩
  simpa [recAlpha, recBeta, j.isLt] using hr

theorem recession_bfs_zero_imp_cone_zero {d k : ℕ} (a : Fin k → Fin d → ℝ)
    (hzero : ∀ u, IsCramerBFS (recAlpha a) (recBeta k d) u → u = 0) :
    ∀ w, (∀ j : Fin k, dot (a j) w ≤ 0) → w = 0 := by
  have hrecT : ∀ w, (∀ r, dot (recAlpha a r) w ≤ 0) → w = 0 := by
    intro w hw
    funext l
    have h1 := hw ⟨k + l.val, by omega⟩
    have h2 := hw ⟨k + d + l.val, by omega⟩
    have e1 : dot (recAlpha a ⟨k + l.val, by omega⟩) w = w l := by
      have hn1 : ¬ (k + l.val < k) := by omega
      have hy2 : k + l.val < k + d := by omega
      simp [recAlpha, hn1, hy2, dot, Pi.single_apply]
    have e2 : dot (recAlpha a ⟨k + d + l.val, by omega⟩) w = -w l := by
      have hn1 : ¬ (k + d + l.val < k) := by omega
      have hn2 : ¬ (k + d + l.val < k + d) := by omega
      simp [recAlpha, hn1, hn2, dot, Pi.single_apply]
    rw [e1] at h1
    rw [e2] at h2
    simp only [Pi.zero_apply]
    linarith
  have hsub := polyhedron_subset_convexHull_bfs (recAlpha a) (recBeta k d) hrecT
  have hB : { u | IsCramerBFS (recAlpha a) (recBeta k d) u } ⊆ ({0} : Set (Fin d → ℝ)) :=
    fun u hu => Set.mem_singleton_iff.2 (hzero u hu)
  intro w hw
  by_contra hw0
  let μ : ℝ := 1 + ∑ l : Fin d, |w l|
  have hμ : 0 < μ := by
    have : 0 ≤ ∑ l : Fin d, |w l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  let v : Fin d → ℝ := μ⁻¹ • w
  have hv_mem : v ∈ { x | ∀ r, dot (recAlpha a r) x ≤ recBeta k d r } := by
    intro r
    dsimp only [recAlpha, recBeta, v]
    rw [dot_smul_right]
    split_ifs with h1 h2
    · exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hμ.le) (hw ⟨r.val, h1⟩)
    · have hl : |w ⟨r.val - k, by omega⟩| ≤ ∑ l : Fin d, |w l| :=
        Finset.single_le_sum (f := fun l : Fin d => |w l|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
      have : dot (Pi.single (⟨r.val - k, by omega⟩ : Fin d) 1) w = w ⟨r.val - k, by omega⟩ := by
        simp [dot, Pi.single_apply]
      rw [this, inv_mul_le_iff₀ hμ]
      linarith [le_abs_self (w ⟨r.val - k, by omega⟩)]
    · have hl : |w ⟨r.val - (k + d), by omega⟩| ≤ ∑ l : Fin d, |w l| :=
        Finset.single_le_sum (f := fun l : Fin d => |w l|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
      have : dot (-Pi.single (⟨r.val - (k + d), by omega⟩ : Fin d) 1) w =
          -w ⟨r.val - (k + d), by omega⟩ := by
        simp [dot, Pi.single_apply]
      rw [this, inv_mul_le_iff₀ hμ]
      linarith [neg_le_abs (w ⟨r.val - (k + d), by omega⟩)]
  have hv0 : v ∈ ({0} : Set (Fin d → ℝ)) := by
    have := convexHull_mono hB (hsub hv_mem)
    rwa [convexHull_singleton] at this
  have : μ⁻¹ • w = 0 := hv0
  exact hw0 ((smul_eq_zero.1 this).resolve_left (inv_ne_zero hμ.ne'))

/-! ### Oracle, frontier, gauge, and outer-polytope invariants -/

theorem halfspace_closed_convex {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) :
    IsClosed { x : Fin d → ℝ | ∀ i, L i x ≤ 1 } ∧ Convex ℝ { x : Fin d → ℝ | ∀ i, L i x ≤ 1 } := by
  have heq : { x : Fin d → ℝ | ∀ i, L i x ≤ 1 } = ⋂ i : Fin m, { x | L i x ≤ 1 } := by
    ext x; simp
  rw [heq]
  refine ⟨isClosed_iInter fun i => isClosed_le (L i).continuous continuous_const,
    convex_iInter fun i => convex_halfSpace_le (L i).toLinearMap.isLinear 1⟩

theorem interior_eq_strict {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 }) :
    interior P = { x | ∀ i, L i x < 1 } := by
  subst hP
  apply Set.Subset.antisymm
  · intro x hx i
    by_cases hLi : L i = 0
    · simp [hLi]
    · have hex : ∃ v, L i v ≠ 0 := by
        by_contra! hall
        exact hLi (ContinuousLinearMap.ext hall)
      obtain ⟨v, hv⟩ := hex
      let w : Fin d → ℝ := if 0 < L i v then v else -v
      have hw : 0 < L i w := by
        dsimp only [w]
        split_ifs with hp
        · exact hp
        · rw [map_neg]
          have hle0 : L i v ≤ 0 := not_lt.1 hp
          have hlt0 : L i v < 0 := lt_of_le_of_ne hle0 hv
          linarith
      have hcont : Continuous (fun t : ℝ => x + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hev : ∀ᶠ t : ℝ in nhds 0, x + t • w ∈ { z : Fin d → ℝ | ∀ j, L j z ≤ 1 } :=
        hcont.continuousAt.preimage_mem_nhds
          (by simpa using mem_interior_iff_mem_nhds.1 hx)
      have hev_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          x + t • w ∈ { z : Fin d → ℝ | ∀ j, L j z ≤ 1 } ∧ (0 : ℝ) < t :=
        (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      have : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
      obtain ⟨δ, hmem, hδ⟩ := hev_pos.exists
      have hle := hmem i
      rw [map_add, map_smul, smul_eq_mul] at hle
      have : 0 < δ * L i w := mul_pos hδ hw
      linarith
  · have hop : IsOpen { x : Fin d → ℝ | ∀ i, L i x < 1 } := by
      have heq : { x : Fin d → ℝ | ∀ i, L i x < 1 } = ⋂ i : Fin m, { x | L i x < 1 } := by
        ext x; simp
      rw [heq]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (L i).continuous continuous_const
    exact interior_maximal (fun x hx i => (hx i).le) hop

theorem frontier_iff_max_one {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 }) :
    ∀ p, p ∈ frontier P ↔ (∀ i, L i p ≤ 1) ∧ ∃ i, L i p = 1 := by
  have hcl := (halfspace_closed_convex L).1
  have hint := interior_eq_strict L hP
  subst hP
  intro p
  rw [frontier, hcl.closure_eq, hint, Set.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra! hall
    exact h2 fun i => lt_of_le_of_ne (h1 i) (hall i)
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, fun h2 => (h2 i).ne hi⟩

theorem frontier_ne_zero {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 }) {p : Fin d → ℝ}
    (hp : p ∈ frontier P) : p ≠ 0 := by
  obtain ⟨_, i, hi⟩ := (frontier_iff_max_one L hP p).1 hp
  rintro rfl
  simp at hi

theorem oracle_gauge {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    let y := oracle v
    0 < dot y v ∧
      (∀ i, L i v ≤ dot v v / dot y v) ∧
      (∃ i, L i v = dot v v / dot y v) ∧
      (∀ i, L i y = 1 ↔ L i v = dot v v / dot y v) := by
  intro y
  obtain ⟨hyf, t, ht, hyt⟩ := horacle v hv
  obtain ⟨hle, hex⟩ := (frontier_iff_max_one L hP y).1 hyf
  have hvv : 0 < dot v v := dot_self_pos hv
  have hyv : dot y v = t * dot v v := by
    rw [show y = t • v from hyt, dot_comm, dot_smul_right, dot_comm]
  have hpos : 0 < dot y v := by rw [hyv]; exact mul_pos ht hvv
  have hquo : dot v v / dot y v = 1 / t := by
    rw [hyv]
    field_simp [ht.ne', hvv.ne']
  have hLy : ∀ i, L i y = t * L i v := fun i => by
    rw [show y = t • v from hyt, map_smul, smul_eq_mul]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro i
    rw [hquo, le_div_iff₀ ht, mul_comm]
    linarith [hle i, hLy i]
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    rw [hquo, eq_div_iff ht.ne', mul_comm, ← hLy i, hi]
  · intro i
    rw [hquo, hLy i]
    constructor
    · intro h; rw [eq_div_iff ht.ne']; linarith
    · intro h; rw [h]; field_simp [ht.ne']

theorem oracle_samp_ray {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (c w : Fin d → ℝ) (s : ℝ) (hv : c + s • w ≠ 0) :
    let v := c + s • w
    let y := oracle v
    dot y v ≠ 0 ∧ Samp (fun i => L i c) (fun i => L i w) s (dot v v / dot y v) ∧
      (∀ i, L i y = 1 ↔ L i c + L i w * s = dot v v / dot y v) := by
  intro v y
  obtain ⟨hpos, hle, hex, hiff⟩ := oracle_gauge L hP horacle hv
  have hlin : ∀ i, L i v = L i c + L i w * s := fun i => by
    simp [v, map_add, map_smul, smul_eq_mul, mul_comm]
  refine ⟨hpos.ne', ⟨fun i => hlin i ▸ hle i, ?_⟩, fun i => hlin i ▸ hiff i⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hlin i ▸ hi⟩

theorem recession_trigger {d m k : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (a : Fin k → Fin d → ℝ) {u : Fin d → ℝ} (hu0 : u ≠ 0)
    (hnonpos : ∀ j : Fin k, dot (a j) u ≤ 0) :
    oracle u ∈ frontier P ∧ oracle u ≠ 0 ∧ ∀ j : Fin k, dot (a j) (oracle u) < 1 := by
  obtain ⟨hf, t, ht, htu⟩ := horacle u hu0
  refine ⟨hf, frontier_ne_zero L hP hf, fun j => ?_⟩
  rw [htu, dot_smul_right]
  have : t * dot (a j) u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (hnonpos j)
  linarith

theorem outer_bfs_dichotomy {d m k : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (hPpoly : IsDPolytope P) (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (a : Fin k → Fin d → ℝ) (ha : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x)
    {u : Fin d → ℝ} (hbfs : IsCramerBFS a (fun _ => 1) u) :
    u ≠ 0 ∧
      ((oracle u = u → u ∈ P.extremePoints ℝ ∧ IsExposed ℝ P {u}) ∧
       (oracle u ≠ u → oracle u ∈ frontier P ∧ oracle u ≠ 0 ∧
         ∀ j : Fin k, dot (a j) (oracle u) < 1)) := by
  obtain ⟨hfeas, idx, hdet, hact⟩ := hbfs
  have hu0 : u ≠ 0 := by
    rintro rfl
    have := hact ⟨0, by omega⟩
    simp at this
  refine ⟨hu0, ?_, ?_⟩
  · intro heq
    obtain ⟨hf, _⟩ := horacle u hu0
    have huP : u ∈ P := by
      rw [← heq, hP]
      exact ((frontier_iff_max_one L hP (oracle u)).1 hf).1
    have hext : u ∈ P.extremePoints ℝ := by
      refine ⟨huP, fun x hx y hy hseg => ?_⟩
      rw [openSegment_eq_image] at hseg
      obtain ⟨θ, ⟨hθ0, hθ1⟩, hcomb⟩ := hseg
      have hsubP : ∀ z ∈ P, ∀ j : Fin k, dot (a j) z ≤ 1 := by
        intro z hz j
        obtain ⟨i, hi⟩ := ha j
        rw [hi]
        rw [hP] at hz
        exact hz i
      let A := Matrix.of fun r l => a (idx r) l
      have hAx : A *ᵥ x = A *ᵥ u := by
        funext r
        simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
        change dot (a (idx r)) x = dot (a (idx r)) u
        rw [hact r]
        have h1 := hsubP x hx (idx r)
        have h2 := hsubP y hy (idx r)
        have h3 : (1 - θ) * dot (a (idx r)) x + θ * dot (a (idx r)) y = 1 := by
          have := congrArg (dot (a (idx r))) hcomb
          simpa [AffineMap.lineMap_apply_module, dot_add_right, dot_smul_right, hact r] using this
        have hpos1 : 0 < 1 - θ := by linarith
        nlinarith
      have hinj : Function.Injective A.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hdet.isUnit)
      exact hinj hAx
    have hexp_eq :=
      ((ray_oracle_outer_polytope_invariants_and_phased_trace_bound d hd).1
        hPpoly hzero L hP horacle).1.1
    refine ⟨hext, ?_⟩
    have : u ∈ { x : Fin d → ℝ | IsExposed ℝ P {x} } := hexp_eq ▸ hext
    exact this
  · intro hne
    obtain ⟨hf, t, ht, htu⟩ := horacle u hu0
    refine ⟨hf, frontier_ne_zero L hP hf, ?_⟩
    have ht_le : t ≤ 1 := by
      obtain ⟨i₀, hi₀⟩ := ha (idx ⟨0, by omega⟩)
      have hp_le : L i₀ (oracle u) ≤ 1 := ((frontier_iff_max_one L hP _).1 hf).1 i₀
      rw [htu, map_smul, smul_eq_mul, ← hi₀, hact ⟨0, by omega⟩, mul_one] at hp_le
      exact hp_le
    have ht_lt : t < 1 := by
      refine lt_of_le_of_ne ht_le ?_
      rintro rfl
      rw [one_smul] at htu
      exact hne htu
    intro j
    rw [htu, dot_smul_right]
    have h1 := hfeas j
    rcases le_or_gt 0 (dot (a j) u) with h0 | h0
    · nlinarith
    · have : t * dot (a j) u < 0 := mul_neg_of_pos_of_neg ht h0
      linarith

theorem outer_done {d m k : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)} (hPpoly : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (a : Fin k → Fin d → ℝ) (ha : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x)
    (hrec : ∀ w, (∀ j : Fin k, dot (a j) w ≤ 0) → w = 0)
    (Cset : Set (Fin d → ℝ)) (hCexp : Cset ⊆ { x | IsExposed ℝ P {x} })
    (hbfsC : ∀ u, IsCramerBFS a (fun _ => 1) u → u ∈ Cset) :
    { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } = P ∧
      Cset = { x | IsExposed ℝ P {x} } := by
  have hexp_eq :=
    ((ray_oracle_outer_polytope_invariants_and_phased_trace_bound d hd).1
      hPpoly hzero L hP horacle).1.1
  have hCext : Cset ⊆ P.extremePoints ℝ := hexp_eq.symm ▸ hCexp
  have hCP : Cset ⊆ P := fun x hx => (hCext hx).1
  have hPQ : P ⊆ { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } := by
    intro x hx j
    obtain ⟨i, hi⟩ := ha j
    rw [hi]
    rw [hP] at hx
    exact hx i
  have hQch : { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } ⊆ convexHull ℝ Cset :=
    (polyhedron_subset_convexHull_bfs a (fun _ => 1) hrec).trans
      (convexHull_mono fun u hu => hbfsC u hu)
  have hconvP : Convex ℝ P := hP ▸ (halfspace_closed_convex L).2
  have hQP : { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } ⊆ P :=
    hQch.trans (convexHull_min hCP hconvP)
  have hEq : { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } = P := Set.Subset.antisymm hQP hPQ
  refine ⟨hEq, Set.Subset.antisymm hCexp ?_⟩
  rw [← hexp_eq]
  have hPch : P = convexHull ℝ Cset :=
    Set.Subset.antisymm (hPQ.trans hQch) (convexHull_min hCP hconvP)
  intro x hx
  rw [hPch] at hx
  exact extremePoints_convexHull_subset hx

/-! ### Facet-finding stage invariant and Cramer normal -/

theorem initFrame_linearIndependent {d : ℕ} (hd : 0 < d) {p : Fin d → ℝ} {l₀ : Fin d}
    (hp : p l₀ ≠ 0) (W₀ : Fin d → Fin d → ℝ) (h0 : W₀ ⟨0, hd⟩ = p)
    (f : Fin (d - 1) → Fin d) (hf_inj : Function.Injective f) (hf_ne : ∀ r, f r ≠ l₀)
    (hrest : ∀ r : Fin (d - 1), W₀ ⟨r.val + 1, by omega⟩ = Pi.single (f r) 1) :
    LinearIndependent ℝ W₀ := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hl₀ : g ⟨0, hd⟩ = 0 := by
    have hcoord := congrFun hg l₀
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single ⟨0, hd⟩] at hcoord
    · rw [h0] at hcoord
      exact (mul_eq_zero.1 hcoord).resolve_right hp
    · intro t _ ht0
      have htpos : 0 < t.val := Nat.pos_of_ne_zero fun e => ht0 (Fin.ext e)
      let r : Fin (d - 1) := ⟨t.val - 1, by omega⟩
      have htr : t = ⟨r.val + 1, by omega⟩ := by ext; simp [r]; omega
      rw [htr, hrest r, Pi.single_eq_of_ne (Ne.symm (hf_ne r)), mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  intro t
  by_cases ht0 : t = ⟨0, hd⟩
  · rwa [ht0]
  · have htpos : 0 < t.val := Nat.pos_of_ne_zero fun e => ht0 (Fin.ext e)
    let r : Fin (d - 1) := ⟨t.val - 1, by omega⟩
    have htr : t = ⟨r.val + 1, by omega⟩ := by ext; simp [r]; omega
    have hcoord := congrFun hg (f r)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single t] at hcoord
    · rw [htr, hrest r, Pi.single_eq_same, mul_one] at hcoord
      rwa [htr]
    · intro s _ hst
      by_cases hs0 : s = ⟨0, hd⟩
      · rw [hs0, hl₀, zero_mul]
      · have hspos : 0 < s.val := Nat.pos_of_ne_zero fun e => hs0 (Fin.ext e)
        let r' : Fin (d - 1) := ⟨s.val - 1, by omega⟩
        have hsr : s = ⟨r'.val + 1, by omega⟩ := by ext; simp [r']; omega
        have hrr : r' ≠ r := by
          intro e
          apply hst
          ext
          have := congrArg Fin.val e
          dsimp [r', r] at this
          omega
        rw [hsr, hrest r', Pi.single_eq_of_ne (fun e => hrr (hf_inj e.symm)), mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

structure StageInv {d m k : ℕ} (P : Set (Fin d → ℝ)) (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (a : Fin k → Fin d → ℝ) (p : Fin d → ℝ) (W₀ : Fin d → Fin d → ℝ)
    (r : ℕ) (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) : Prop where
  hr : r < d
  hM0 : M ⟨0, by omega⟩ = p
  hli : LinearIndependent ℝ M
  hspan : Submodule.span ℝ (M '' { t : Fin d | t.val ≤ r }) =
    Submodule.span ℝ (W₀ '' { t : Fin d | t.val ≤ r })
  htail : ∀ t : Fin d, r < t.val → M t = W₀ t
  hMP : ∀ t : Fin d, t.val ≤ r → M t ∈ P
  hc_front : c ∈ frontier P
  hc_span : c ∈ Submodule.span ℝ (M '' { t : Fin d | t.val ≤ r })
  hcommon : ∀ i : Fin m, L i c = 1 → ∀ t : Fin d, t.val ≤ r → L i (M t) = 1
  hknown : ∀ j : Fin k, dot (a j) c < 1

theorem StageInv.init {d m k : ℕ} (hd : 0 < d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    (a : Fin k → Fin d → ℝ) (p : Fin d → ℝ) (hp : p ∈ frontier P)
    (hknown : ∀ j : Fin k, dot (a j) p < 1)
    (W₀ : Fin d → Fin d → ℝ) (hW0 : W₀ ⟨0, hd⟩ = p) (hli : LinearIndependent ℝ W₀) :
    StageInv P L a p W₀ 0 W₀ p := by
  have hpP : p ∈ P := by
    rw [hP]; exact ((frontier_iff_max_one L hP p).1 hp).1
  refine ⟨hd, hW0, hli, rfl, fun _ _ => rfl, ?_, hp, ?_, ?_, hknown⟩
  · intro t ht
    have ht0 : t = ⟨0, hd⟩ := Fin.ext (by simp; omega)
    rwa [ht0, hW0]
  · apply Submodule.subset_span
    exact ⟨⟨0, hd⟩, by simp, hW0⟩
  · intro i hi t ht
    have ht0 : t = ⟨0, hd⟩ := Fin.ext (by simp; omega)
    rwa [ht0, hW0]

theorem StageInv.w_not_mem_span {d m k : ℕ} {P : Set (Fin d → ℝ)}
    {L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ} {a : Fin k → Fin d → ℝ}
    {p : Fin d → ℝ} {W₀ : Fin d → Fin d → ℝ} {r : ℕ} {M : Fin d → Fin d → ℝ} {c : Fin d → ℝ}
    (h : StageInv P L a p W₀ r M c) (hr1 : r + 1 < d) :
    M ⟨r + 1, hr1⟩ ∉ Submodule.span ℝ (M '' { t : Fin d | t.val ≤ r }) :=
  h.hli.notMem_span_image (s := { t : Fin d | t.val ≤ r }) (by simp)

theorem StageInv.ray_ne_zero {d m k : ℕ} {P : Set (Fin d → ℝ)}
    {L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ} {a : Fin k → Fin d → ℝ}
    {p : Fin d → ℝ} {W₀ : Fin d → Fin d → ℝ} {r : ℕ} {M : Fin d → Fin d → ℝ} {c : Fin d → ℝ}
    (h : StageInv P L a p W₀ r M c) (hr1 : r + 1 < d) {s : ℝ} (hs : s ≠ 0) :
    c + s • M ⟨r + 1, hr1⟩ ≠ 0 := by
  intro heq
  apply h.w_not_mem_span hr1
  have : M ⟨r + 1, hr1⟩ = (-s⁻¹) • c := by
    funext l
    have hl := congrFun heq l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hl ⊢
    field_simp [hs]
    linarith
  rw [this]
  exact Submodule.smul_mem _ _ h.hc_span

theorem StageInv.step {d m k : ℕ} {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    (a : Fin k → Fin d → ℝ) (ha : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    {p : Fin d → ℝ} {W₀ : Fin d → Fin d → ℝ} {r : ℕ} {M : Fin d → Fin d → ℝ} {c : Fin d → ℝ}
    (h : StageInv P L a p W₀ r M c) (hr1 : r + 1 < d)
    {u : ℝ} (hu : 0 < u)
    (hcom : ∃ i : Fin m, L i c = 1 ∧ L i (oracle (c + u • M ⟨r + 1, hr1⟩)) = 1) :
    let idx₁ : Fin d := ⟨r + 1, hr1⟩
    let q := oracle (c + u • M idx₁)
    StageInv P L a p W₀ (r + 1) (Function.update M idx₁ q) ((1 / 2 : ℝ) • (c + q)) := by
  intro idx₁ q
  have hv0 : c + u • M idx₁ ≠ 0 := h.ray_ne_zero hr1 hu.ne'
  obtain ⟨hqf, τ, hτ, hqτ⟩ := horacle _ hv0
  have hqP : q ∈ P := by rw [hP]; exact ((frontier_iff_max_one L hP q).1 hqf).1
  let M' := Function.update M idx₁ q
  have hidx_val : idx₁.val = r + 1 := rfl
  have hM'le : ∀ t : Fin d, t.val ≤ r → M' t = M t := fun t ht =>
    Function.update_of_ne (fun e => by have := congrArg Fin.val e; omega) _ _
  have hM'gt : ∀ t : Fin d, r + 1 < t.val → M' t = W₀ t := fun t ht => by
    change Function.update M idx₁ q t = W₀ t
    rw [Function.update_of_ne (fun e => by have := congrArg Fin.val e; omega)]
    exact h.htail t (by omega)
  have hspan_new : Submodule.span ℝ (M' '' { t : Fin d | t.val ≤ r + 1 }) =
      Submodule.span ℝ (W₀ '' { t : Fin d | t.val ≤ r + 1 }) := by
    have himg1 : M' '' { t : Fin d | t.val ≤ r + 1 } = insert q (M '' { t : Fin d | t.val ≤ r }) := by
      ext x; constructor
      · rintro ⟨t, ht, rfl⟩
        by_cases htr : t.val ≤ r
        · right; exact ⟨t, htr, (hM'le t htr).symm⟩
        · left
          have hteq : t = idx₁ := Fin.ext (by change t.val ≤ r + 1 at ht; omega)
          simp [M', hteq]
      · rintro (rfl | ⟨t, ht, rfl⟩)
        · exact ⟨idx₁, by simp [hidx_val], by simp [M']⟩
        · change t.val ≤ r at ht
          exact ⟨t, by simp; omega, hM'le t ht⟩
    have himg2 : W₀ '' { t : Fin d | t.val ≤ r + 1 } =
        insert (M idx₁) (W₀ '' { t : Fin d | t.val ≤ r }) := by
      ext x; constructor
      · rintro ⟨t, ht, rfl⟩
        by_cases htr : t.val ≤ r
        · right; exact ⟨t, htr, rfl⟩
        · left
          have hteq : t = idx₁ := Fin.ext (by change t.val ≤ r + 1 at ht; omega)
          rw [hteq, h.htail idx₁ (by omega)]
      · rintro (rfl | ⟨t, ht, rfl⟩)
        · exact ⟨idx₁, by simp [hidx_val], (h.htail idx₁ (by omega)).symm⟩
        · change t.val ≤ r at ht
          exact ⟨t, by simp; omega, rfl⟩
    rw [himg1, himg2, Submodule.span_insert, Submodule.span_insert, ← h.hspan]
    apply le_antisymm
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      rw [Submodule.span_singleton_le_iff_mem]
      have hqeq : q = τ • c + (τ * u) • M idx₁ := by
        change oracle (c + u • M idx₁) = _
        rw [hqτ, smul_add, smul_smul]
      rw [hqeq]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_right h.hc_span))
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      rw [Submodule.span_singleton_le_iff_mem]
      have htu : τ * u ≠ 0 := mul_ne_zero hτ.ne' hu.ne'
      have hweq : M idx₁ = (τ * u)⁻¹ • q - (τ * u)⁻¹ • (τ • c) := by
        have hqeq : q = τ • c + (τ * u) • M idx₁ := by
          change oracle (c + u • M idx₁) = _
          rw [hqτ, smul_add, smul_smul]
        rw [hqeq, smul_add, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htu, one_smul]
      rw [hweq]
      exact sub_mem
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right h.hc_span)))
  have hspan_all : Submodule.span ℝ (Set.range M') = Submodule.span ℝ (Set.range M) := by
    have hsplit : ∀ F : Fin d → Fin d → ℝ,
        Set.range F = F '' { t : Fin d | t.val ≤ r + 1 } ∪ F '' { t : Fin d | r + 1 < t.val } := by
      intro F; ext x; constructor
      · rintro ⟨t, rfl⟩
        rcases le_or_gt t.val (r + 1) with hle | hgt
        · left; exact ⟨t, hle, rfl⟩
        · right; exact ⟨t, hgt, rfl⟩
      · rintro (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) <;> exact ⟨t, rfl⟩
    have htail_eq : M' '' { t : Fin d | r + 1 < t.val } = M '' { t : Fin d | r + 1 < t.val } := by
      ext x; constructor
      · rintro ⟨t, ht, rfl⟩
        change r + 1 < t.val at ht
        exact ⟨t, ht, (h.htail t (by omega)).trans (hM'gt t ht).symm⟩
      · rintro ⟨t, ht, rfl⟩
        change r + 1 < t.val at ht
        exact ⟨t, ht, (hM'gt t ht).trans (h.htail t (by omega)).symm⟩
    have hM_pref : Submodule.span ℝ (M '' { t : Fin d | t.val ≤ r + 1 }) =
        Submodule.span ℝ (W₀ '' { t : Fin d | t.val ≤ r + 1 }) := by
      have himgM : M '' { t : Fin d | t.val ≤ r + 1 } =
          insert (M idx₁) (M '' { t : Fin d | t.val ≤ r }) := by
        ext x; constructor
        · rintro ⟨t, ht, rfl⟩
          by_cases htr : t.val ≤ r
          · right; exact ⟨t, htr, rfl⟩
          · left; congr 1; exact Fin.ext (by change t.val ≤ r + 1 at ht; omega)
        · rintro (rfl | ⟨t, ht, rfl⟩)
          · exact ⟨idx₁, by simp [hidx_val], rfl⟩
          · change t.val ≤ r at ht
            exact ⟨t, by simp; omega, rfl⟩
      have himgW : W₀ '' { t : Fin d | t.val ≤ r + 1 } =
          insert (M idx₁) (W₀ '' { t : Fin d | t.val ≤ r }) := by
        ext x; constructor
        · rintro ⟨t, ht, rfl⟩
          by_cases htr : t.val ≤ r
          · right; exact ⟨t, htr, rfl⟩
          · left
            have hteq : t = idx₁ := Fin.ext (by change t.val ≤ r + 1 at ht; omega)
            rw [hteq, h.htail idx₁ (by omega)]
        · rintro (rfl | ⟨t, ht, rfl⟩)
          · exact ⟨idx₁, by simp [hidx_val], (h.htail idx₁ (by omega)).symm⟩
          · change t.val ≤ r at ht
            exact ⟨t, by simp; omega, rfl⟩
      rw [himgM, himgW, Submodule.span_insert, Submodule.span_insert, h.hspan]
    rw [hsplit M', hsplit M, Submodule.span_union, Submodule.span_union, hspan_new, hM_pref, htail_eq]
  have hli' : LinearIndependent ℝ M' := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan_all, ← Set.finrank,
      ← linearIndependent_iff_card_eq_finrank_span]
    exact h.hli
  have hc_le : ∀ i, L i c ≤ 1 := ((frontier_iff_max_one L hP c).1 h.hc_front).1
  have hq_le : ∀ i, L i q ≤ 1 := ((frontier_iff_max_one L hP q).1 hqf).1
  show StageInv P L a p W₀ (r + 1) M' ((1 / 2 : ℝ) • (c + q))
  refine ⟨hr1, ?_, hli', hspan_new, hM'gt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hM'le ⟨0, by omega⟩ (by simp), h.hM0]
  · intro t ht
    by_cases htr : t.val ≤ r
    · rw [hM'le t htr]; exact h.hMP t htr
    · have hteq : t = idx₁ := Fin.ext (by omega)
      simpa [M', hteq] using hqP
  · rw [frontier_iff_max_one L hP]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [map_smul, map_add, smul_eq_mul]
      linarith [hc_le i, hq_le i]
    · obtain ⟨i₀, hic, hiq⟩ := hcom
      change L i₀ q = 1 at hiq
      refine ⟨i₀, ?_⟩
      simp only [map_smul, map_add, smul_eq_mul, hic, hiq]
      norm_num
  · apply Submodule.smul_mem
    apply add_mem
    · have hsub : M '' { t : Fin d | t.val ≤ r } ⊆ M' '' { t : Fin d | t.val ≤ r + 1 } := by
        rintro _ ⟨t, ht, rfl⟩
        change t.val ≤ r at ht
        exact ⟨t, by simp; omega, hM'le t ht⟩
      exact Submodule.span_mono hsub h.hc_span
    · apply Submodule.subset_span
      exact ⟨idx₁, by simp [hidx_val], by simp [M']⟩
  · intro i hi t ht
    simp only [map_smul, map_add, smul_eq_mul] at hi
    have hic : L i c = 1 := by linarith [hc_le i, hq_le i]
    have hiq : L i q = 1 := by linarith [hc_le i, hq_le i]
    by_cases htr : t.val ≤ r
    · rw [hM'le t htr]; exact h.hcommon i hic t htr
    · have hteq : t = idx₁ := Fin.ext (by omega)
      simpa [M', hteq] using hiq
  · intro j
    obtain ⟨i, hi⟩ := ha j
    rw [dot_smul_right, dot_add_right]
    have hqj : dot (a j) q ≤ 1 := by rw [hi]; exact hq_le i
    linarith [h.hknown j]

theorem StageInv.finish {d m k : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {a : Fin k → Fin d → ℝ} {p : Fin d → ℝ} {W₀ : Fin d → Fin d → ℝ}
    {M : Fin d → Fin d → ℝ} {c : Fin d → ℝ}
    (h : StageInv P L a p W₀ (d - 1) M c) :
    let A := Matrix.of M
    A.det ≠ 0 ∧
      ∃ i_new : Fin m,
        (∀ x, dot (fun l => (A.updateCol l (fun _ => 1)).det / A.det) x = L i_new x) ∧
        L i_new p = 1 := by
  intro A
  have hu : IsUnit A := (Matrix.linearIndependent_rows_iff_isUnit (A := A)).1 h.hli
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hu).ne_zero
  obtain ⟨_, i_new, hic⟩ := (frontier_iff_max_one L hP c).1 h.hc_front
  have hall : ∀ t : Fin d, L i_new (M t) = 1 := fun t => h.hcommon i_new hic t (by omega)
  let a_new : Fin d → ℝ := fun l => (A.updateCol l (fun _ => 1)).det / A.det
  have hsol : A *ᵥ a_new = fun _ => 1 := by
    funext t
    simpa [Matrix.mulVec, dotProduct, dot, A, a_new] using cramer_sol_eq A (fun _ => 1) hdet t
  have hLsol : A *ᵥ vecOfCLM (L i_new) = fun _ => 1 := by
    funext t
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    change dot (M t) (vecOfCLM (L i_new)) = 1
    rw [dot_comm, dot_vecOfCLM, hall t]
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hu
  have heq : a_new = vecOfCLM (L i_new) := hinj (hsol.trans hLsol.symm)
  refine ⟨hdet, i_new, fun x => ?_, ?_⟩
  · change dot a_new x = L i_new x
    rw [heq, dot_vecOfCLM]
  · have := hall ⟨0, by omega⟩
    rwa [h.hM0] at this

/-! ### Face-lattice characterization from facet-intersection vertex sets -/

theorem exposed_of_facet_inter {d k : ℕ} {P : Set (Fin d → ℝ)}
    (a : Fin k → Fin d → ℝ) (hP : P = { x | ∀ j : Fin k, dot (a j) x ≤ 1 })
    (J : Finset (Fin k)) :
    IsExposed ℝ P { x ∈ P | ∀ j ∈ J, dot (a j) x = 1 } := by
  intro hne
  let l : (Fin d → ℝ) →L[ℝ] ℝ := ∑ j ∈ J, LinearMap.toContinuousLinearMap
    { toFun := fun x => dot (a j) x
      map_add' := dot_add_right (a j)
      map_smul' := fun c x => by simp [dot_smul_right] }
  have hl : ∀ x, l x = ∑ j ∈ J, dot (a j) x := by
    intro x
    simp [l]
  obtain ⟨x₀, hx₀P, hx₀J⟩ := hne
  have hlx₀ : l x₀ = (J.card : ℝ) := by
    rw [hl, Finset.sum_congr rfl fun j hj => hx₀J j hj]; simp
  refine ⟨l, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxP, hxJ⟩
    refine ⟨hxP, fun y hyP => ?_⟩
    have hlx : l x = (J.card : ℝ) := by
      rw [hl, Finset.sum_congr rfl fun j hj => hxJ j hj]; simp
    rw [hlx, hl]
    have hy_le : ∀ j ∈ J, dot (a j) y ≤ 1 := fun j _ => by rw [hP] at hyP; exact hyP j
    calc ∑ j ∈ J, dot (a j) y ≤ ∑ _j ∈ J, (1 : ℝ) := Finset.sum_le_sum hy_le
      _ = (J.card : ℝ) := by simp
  · rintro x ⟨hxP, hmax⟩
    refine ⟨hxP, ?_⟩
    have hx_le : ∀ j ∈ J, dot (a j) x ≤ 1 := fun j _ => by rw [hP] at hxP; exact hxP j
    have hge : (J.card : ℝ) ≤ ∑ j ∈ J, dot (a j) x := by
      have := hmax x₀ hx₀P
      rwa [hlx₀, hl] at this
    have hle : ∑ j ∈ J, dot (a j) x ≤ ∑ _j ∈ J, (1 : ℝ) := Finset.sum_le_sum hx_le
    have heq : ∑ j ∈ J, dot (a j) x = ∑ _j ∈ J, (1 : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hle ⊢
      linarith
    exact (Finset.sum_eq_sum_iff_of_le hx_le).1 heq

theorem nonempty_exposed_eq_facet_inter {d k : ℕ} {P : Set (Fin d → ℝ)}
    (a : Fin k → Fin d → ℝ) (hP : P = { x | ∀ j : Fin k, dot (a j) x ≤ 1 })
    (F : PolytopeFace P) (hne : F.val.Nonempty)
    (hVfin : { x : Fin d → ℝ | IsExposed ℝ P {x} }.Finite)
    (hFch : F.val = convexHull ℝ (F.val ∩ { x : Fin d → ℝ | IsExposed ℝ P {x} })) :
    ∃ J : Finset (Fin k), F.val = { x ∈ P | ∀ j ∈ J, dot (a j) x = 1 } := by
  obtain ⟨φ, hFφ⟩ := F.property hne
  let W : Finset (Fin d → ℝ) :=
    (hVfin.subset (Set.inter_subset_right (s := F.val))).toFinset
  have hWcoe : (W : Set (Fin d → ℝ)) = F.val ∩ { x : Fin d → ℝ | IsExposed ℝ P {x} } :=
    Set.Finite.coe_toFinset _
  have hWne : W.Nonempty := by
    rw [← Finset.coe_nonempty, hWcoe]
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hFch, hcon, convexHull_empty] at hne
    exact Set.not_nonempty_empty hne
  have hWF : ∀ w ∈ W, w ∈ F.val := fun w hw => ((Set.Finite.mem_toFinset _).1 hw).1
  have hconvP : Convex ℝ P := by
    have heq : { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } = ⋂ j : Fin k, { x | dot (a j) x ≤ 1 } := by
      ext x; simp
    rw [hP, heq]
    exact convex_iInter fun j => convex_halfSpace_le
      ({ toFun := fun x => dot (a j) x
         map_add' := dot_add_right (a j)
         map_smul' := fun c x => by simp [dot_smul_right] } : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear 1
  have hconvF : Convex ℝ F.val := hFch ▸ convex_convexHull ℝ _
  let cW : ℝ := (W.card : ℝ)⁻¹
  have hcW : 0 < cW := inv_pos.2 (Nat.cast_pos.2 hWne.card_pos)
  have hW0 : (W.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hWne.card_pos.ne'
  let b : Fin d → ℝ := ∑ w ∈ W, cW • w
  have hbF : b ∈ F.val := by
    apply hconvF.sum_mem
    · intro w _; exact hcW.le
    · simp [cW, mul_inv_cancel₀ hW0]
    · exact hWF
  have hbP : b ∈ P := F.property.subset hbF
  let J : Finset (Fin k) := Finset.univ.filter fun j => dot (a j) b = 1
  refine ⟨J, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxF
    refine ⟨F.property.subset hxF, fun j hj => ?_⟩
    have hjb : dot (a j) b = 1 := (Finset.mem_filter.1 hj).2
    have hw_le : ∀ w ∈ W, dot (a j) w ≤ 1 := fun w hw => by
      have hwP := F.property.subset (hWF w hw)
      rw [hP] at hwP; exact hwP j
    have hw_eq : ∀ w ∈ W, dot (a j) w = 1 := by
      have hsum : ∑ w ∈ W, cW * dot (a j) w = ∑ _w ∈ W, cW * 1 := by
        have hdb : dot (a j) b = ∑ w ∈ W, cW * dot (a j) w := by
          simp only [b, dot]
          trans ∑ l : Fin d, ∑ w ∈ W, a j l * (cW * w l)
          · refine Finset.sum_congr rfl fun l _ => ?_
            simp [Finset.sum_apply, Finset.mul_sum]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => by ring
        rw [← hdb, hjb]
        simp [cW, mul_inv_cancel₀ hW0]
      intro w hw
      have h1 := (Finset.sum_eq_sum_iff_of_le (fun u hu =>
        mul_le_mul_of_nonneg_left (hw_le u hu) hcW.le)).1 hsum w hw
      exact mul_left_cancel₀ hcW.ne' h1
    have hxch : x ∈ convexHull ℝ (W : Set (Fin d → ℝ)) := by rwa [hWcoe, ← hFch]
    have hsub : (W : Set (Fin d → ℝ)) ⊆ { z | dot (a j) z = 1 } :=
      fun w hw => hw_eq w (Finset.mem_coe.1 hw)
    have hconvH : Convex ℝ { z : Fin d → ℝ | dot (a j) z = 1 } :=
      convex_hyperplane ({ toFun := fun z => dot (a j) z
                           map_add' := dot_add_right (a j)
                           map_smul' := fun c z => by simp [dot_smul_right] } :
        (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear 1
    exact convexHull_min hsub hconvH hxch
  · rintro y ⟨hyP, hyJ⟩
    -- Step slightly past b away from y while staying inside P
    let denom : ℝ := 1 + ∑ j ∈ Finset.univ \ J, (1 + |dot (a j) (b - y)|) / (1 - dot (a j) b)
    have hslack : ∀ j ∈ Finset.univ \ J, 0 < 1 - dot (a j) b := by
      intro j hj
      have hjJ : j ∉ J := (Finset.mem_sdiff.1 hj).2
      have hle : dot (a j) b ≤ 1 := by rw [hP] at hbP; exact hbP j
      have hne' : dot (a j) b ≠ 1 := fun he => hjJ (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
      linarith [lt_of_le_of_ne hle hne']
    have hterm_nn : ∀ j ∈ Finset.univ \ J,
        0 ≤ (1 + |dot (a j) (b - y)|) / (1 - dot (a j) b) := fun j hj =>
      div_nonneg (by positivity) (hslack j hj).le
    have hden_pos : 0 < denom := by
      have : 0 ≤ ∑ j ∈ Finset.univ \ J, (1 + |dot (a j) (b - y)|) / (1 - dot (a j) b) :=
        Finset.sum_nonneg hterm_nn
      linarith
    let ε : ℝ := 1 / denom
    have hε : 0 < ε := div_pos one_pos hden_pos
    let z : Fin d → ℝ := b + ε • (b - y)
    have hzP : z ∈ P := by
      rw [hP]
      intro j
      dsimp only [z]
      rw [dot_add_right, dot_smul_right]
      by_cases hj : j ∈ J
      · have hjb : dot (a j) b = 1 := (Finset.mem_filter.1 hj).2
        rw [dot_sub_right, hjb, hyJ j hj, sub_self, mul_zero, add_zero]
      · have hjs : j ∈ Finset.univ \ J := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hj⟩
        have hle_den : (1 + |dot (a j) (b - y)|) / (1 - dot (a j) b) ≤ denom := by
          have := Finset.single_le_sum hterm_nn hjs
          linarith
        have h1 : ε * ((1 + |dot (a j) (b - y)|) / (1 - dot (a j) b)) ≤ 1 := by
          dsimp only [ε]
          rw [one_div, inv_mul_le_iff₀ hden_pos, mul_one]
          exact hle_den
        have h2 : ε * (1 + |dot (a j) (b - y)|) ≤ 1 - dot (a j) b := by
          rw [mul_div_assoc', div_le_iff₀ (hslack j hjs), one_mul] at h1
          exact h1
        have h3 : dot (a j) (b - y) ≤ |dot (a j) (b - y)| := le_abs_self _
        nlinarith
    have hb_max : ∀ u ∈ P, φ u ≤ φ b := by
      have hb' := hbF; rw [hFφ] at hb'; exact hb'.2
    have hφz := hb_max z hzP
    simp only [z, map_add, map_sub, map_smul, smul_eq_mul] at hφz
    have hφge : φ b ≤ φ y := by nlinarith
    rw [hFφ]
    refine ⟨hyP, fun u huP => le_trans (hb_max u huP) hφge⟩

theorem face_lattice_output_of_closure {d k V n : ℕ} {P : Set (Fin d → ℝ)}
    (hPpoly : IsDPolytope P) (a : Fin k → Fin d → ℝ)
    (hP : P = { x | ∀ j : Fin k, dot (a j) x ≤ 1 })
    (vVec : Fin V → Fin d → ℝ)
    (hv_range : Set.range vVec = { x | IsExposed ℝ P {x} })
    (faceBit : Fin n → Fin V → ℝ) (hf_inj : Function.Injective faceBit)
    (hf_zo : ∀ i r, faceBit i r = 0 ∨ faceBit i r = 1)
    (hf_range : Set.range faceBit =
      { fun _ : Fin V => (0 : ℝ) } ∪
        Set.range (fun J : Finset (Fin k) => fun r : Fin V =>
          if ∀ j ∈ J, dot (a j) (vVec r) = 1 then (1 : ℝ) else 0))
    (c : RayConfiguration)
    (hones : ∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1)
    (hzero_sep : c.tape (c.head + (n : ℤ)) = 0)
    (hbits : ∀ i j : Fin n,
      c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
        if (∑ r : Fin V, faceBit i r * (1 - faceBit j r)) = 0 then 1 else 0) :
    IsRayFaceLatticeOutput P c := by
  obtain ⟨hVfin, hFch⟩ := polytope_face_eq_convexHull_exposed_vertices d P hPpoly
  have henc := rayMachine_static_field_expr_and_face_lattice_encoding.2 hFch
  -- Map each PolytopeFace P to its indicator vector on Fin V
  let indOf : PolytopeFace P → (Fin V → ℝ) := fun F r =>
    if vVec r ∈ F.val then (1 : ℝ) else 0
  have hind_inj : Function.Injective indOf := by
    intro F₁ F₂ heq
    apply le_antisymm
    · rw [henc.1]
      intro x hx hx1
      obtain ⟨r, rfl⟩ := hv_range.symm.subset hx
      have hr := congrFun heq r
      simp only [indOf, if_pos hx1] at hr
      by_contra hx2
      simp [hx2] at hr
    · rw [henc.1]
      intro x hx hx2
      obtain ⟨r, rfl⟩ := hv_range.symm.subset hx
      have hr := congrFun heq r
      simp only [indOf, if_pos hx2] at hr
      by_contra hx1
      simp [hx1] at hr
  have hind_range : Set.range indOf = Set.range faceBit := by
    rw [hf_range]
    ext b; constructor
    · rintro ⟨F, rfl⟩
      by_cases hne : F.val.Nonempty
      · obtain ⟨J, hFJ⟩ := nonempty_exposed_eq_facet_inter a hP F hne hVfin (hFch F)
        right
        refine ⟨J, funext fun r => ?_⟩
        have hrP : vVec r ∈ P := by
          have hrE : IsExposed ℝ P {vVec r} := hv_range.subset ⟨r, rfl⟩
          exact hrE.subset (Set.mem_singleton _)
        simp [indOf, hFJ, hrP]
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        left
        ext r; simp [indOf, hne]
    · rintro (rfl | ⟨J, rfl⟩)
      · refine ⟨⟨∅, isExposed_empty⟩, funext fun r => ?_⟩
        simp [indOf]
      · refine ⟨⟨{ x ∈ P | ∀ j ∈ J, dot (a j) x = 1 }, exposed_of_facet_inter a hP J⟩,
          funext fun r => ?_⟩
        have hrP : vVec r ∈ P := by
          have hrE : IsExposed ℝ P {vVec r} := hv_range.subset ⟨r, rfl⟩
          exact hrE.subset (Set.mem_singleton _)
        simp [indOf, hrP]
  have hsub_to : ∀ i : Fin n, ∃ F : PolytopeFace P, indOf F = faceBit i := fun i =>
    hind_range.symm.subset ⟨i, rfl⟩
  let toFace : Fin n → PolytopeFace P := fun i => Classical.choose (hsub_to i)
  have htoFace : ∀ i, indOf (toFace i) = faceBit i := fun i => Classical.choose_spec (hsub_to i)
  have hbij : Function.Bijective toFace := by
    refine ⟨fun i j hij => hf_inj (by rw [← htoFace i, ← htoFace j, hij]), fun F => ?_⟩
    obtain ⟨i, hi⟩ := hind_range.subset ⟨F, rfl⟩
    exact ⟨i, hind_inj (by rw [htoFace i, hi])⟩
  let e : Fin n ≃ PolytopeFace P := Equiv.ofBijective toFace hbij
  have he : ∀ i r, faceBit i r = if vVec r ∈ (e i).val then 1 else 0 := fun i r =>
    (congrFun (htoFace i) r).symm
  refine henc.2.2 e c hones hzero_sep fun i j => ?_
  rw [hbits i j]
  have hiff : (∑ r : Fin V, faceBit i r * (1 - faceBit j r)) = 0 ↔
      (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) := by
    have hnn : ∀ r ∈ (Finset.univ : Finset (Fin V)), 0 ≤ faceBit i r * (1 - faceBit j r) := by
      intro r _
      rcases hf_zo i r with hi | hi <;> rcases hf_zo j r with hj | hj <;> simp [hi, hj]
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
    constructor
    · intro hall x hx hxi
      obtain ⟨r, rfl⟩ := hv_range.symm.subset hx
      have hr := hall r (Finset.mem_univ r)
      rw [he i r, he j r, if_pos hxi] at hr
      by_contra hxj
      simp [hxj] at hr
    · intro hall r _
      rw [he i r, he j r]
      by_cases hxi : vVec r ∈ (e i).val
      · have hxj : vVec r ∈ (e j).val := hall (vVec r) (hv_range.subset ⟨r, rfl⟩) hxi
        simp [hxi, hxj]
      · simp [hxi]
  by_cases h0 : (∑ r : Fin V, faceBit i r * (1 - faceBit j r)) = 0
  · rw [if_pos h0, if_pos (hiff.1 h0)]
  · have hn0 : ¬ (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) :=
      fun h => h0 (hiff.2 h)
    rw [if_neg h0, if_neg hn0]

theorem query_budget_le (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    f₀ + ∑ s ∈ Finset.range m, (1 + (d - 1) * (2 * (m - s) + 2)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m := by
  have hrep := (repaired_ray_query_budget_bound d m f₀ hd hm).2
  have hsum : ∑ s ∈ Finset.range m, (1 + (d - 1) * (2 * (m - s) + 2)) ≤
      ∑ s ∈ Finset.range m, (1 + (d - 1) * (2 * (m - s) + 3)) :=
    Finset.sum_le_sum fun s _ => by
      have : 2 * (m - s) + 2 ≤ 2 * (m - s) + 3 := by omega
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (d - 1) this) 1
  omega

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Bfs -/

namespace Grunbaum2003
namespace RayAlg

open scoped BigOperators Matrix Classical

/-! ## General RAM loop combinators and Cramer BFS enumeration -/

def PExpr.dot {α : Type} {d : ℕ} (u v : Fin d → PExpr α) : PExpr α :=
  PExpr.sumFin d fun l => u l * v l

@[simp] theorem PExpr.eval_dot {α : Type} (g : α → ℝ) {d : ℕ} (u v : Fin d → PExpr α) :
    (PExpr.dot u v).eval g = RayAlg.dot (fun l => (u l).eval g) (fun l => (v l).eval g) := by
  simp [PExpr.dot, RayAlg.dot]

theorem Stmt.Exec.assign_eval {α : Type} [DecidableEq α] {d : ℕ}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} {qr : Fin d → α}
    (dst : α) (e : PExpr α) (s : RS α) (v : ℝ) (hv : e.eval s.regs = v) :
    Stmt.Exec oracle qr (Stmt.assign dst e) s ⟨Function.update s.regs dst v, s.mem, s.queries⟩ :=
  hv ▸ Stmt.Exec.assign dst e s

theorem Stmt.Exec.vset_eval {α : Type} [DecidableEq α] {d n : ℕ}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} {qr : Fin d → α}
    {X : Fin n → α} (hX : Function.Injective X) (e : Fin n → PExpr α)
    (s : RS α) (v : Fin n → ℝ) (hv : ∀ i, (e i).eval s.regs = v i) :
    Stmt.Exec oracle qr (Stmt.vset X e) s ⟨Function.extend X v s.regs, s.mem, s.queries⟩ := by
  have h : (fun i => (e i).eval s.regs) = v := funext hv
  exact h ▸ Stmt.Exec.vset hX e s

/-- Count-controlled loop `for cnt = 0, 1, ..., N - 1` where `s.regs boundReg = (N : ℝ)`. -/
def Stmt.forNat {α : Type} (cntReg boundReg condReg : α) (body : Stmt α) : Stmt α :=
  .seq (.par [(cntReg, PExpr.const 0), (condReg, PExpr.reg boundReg)])
    (.while condReg
      (.seq body
        (.par [(cntReg, PExpr.reg cntReg + PExpr.const 1),
               (condReg, PExpr.reg boundReg - (PExpr.reg cntReg + PExpr.const 1))])))

section ForNat
variable {α : Type} [DecidableEq α] {d : ℕ}
  {oracle : (Fin d → ℝ) → Fin d → ℝ} {qr : Fin d → α}

theorem Stmt.Exec.forNat_loop {cntReg boundReg condReg : α}
    (hcb : cntReg ≠ boundReg) (hcc : cntReg ≠ condReg) (hbc : boundReg ≠ condReg)
    {body : Stmt α} {N : ℕ} (Inv : ℕ → RS α → Prop)
    (hframe : ∀ c (s : RS α) v₁ v₂, Inv c s →
      Inv c ⟨Function.update (Function.update s.regs cntReg v₁) condReg v₂, s.mem, s.queries⟩)
    (hstep : ∀ c, c < N → ∀ s,
      s.regs cntReg = (c : ℝ) → s.regs boundReg = (N : ℝ) →
      s.regs condReg = (N : ℝ) - (c : ℝ) → Inv c s →
      ∃ m, Stmt.Exec oracle qr body s m ∧
        m.regs cntReg = (c : ℝ) ∧ m.regs boundReg = (N : ℝ) ∧ Inv (c + 1) m) :
    ∀ (rem c : ℕ) (s : RS α), N - c = rem → c ≤ N →
      s.regs cntReg = (c : ℝ) → s.regs boundReg = (N : ℝ) →
      s.regs condReg = (N : ℝ) - (c : ℝ) → Inv c s →
      ∃ s', Stmt.Exec oracle qr
        (.while condReg
          (.seq body
            (.par [(cntReg, PExpr.reg cntReg + PExpr.const 1),
                   (condReg, PExpr.reg boundReg - (PExpr.reg cntReg + PExpr.const 1))]))) s s' ∧
        s'.regs cntReg = (N : ℝ) ∧ s'.regs boundReg = (N : ℝ) ∧
        s'.regs condReg = 0 ∧ Inv N s' := by
  intro rem
  induction rem with
  | zero =>
    intro c s hrem hc hcnt hbnd hcond hI
    have hcN : c = N := by omega
    subst hcN
    have hzero : s.regs condReg = 0 := by rw [hcond, sub_self]
    exact ⟨s, Stmt.Exec.while_done hzero, hcnt, hbnd, hzero, hI⟩
  | succ rem ih =>
    intro c s hrem hc hcnt hbnd hcond hI
    have hlt : c < N := by omega
    have hcond_ne : s.regs condReg ≠ 0 := by
      rw [hcond]
      have : (c : ℝ) < (N : ℝ) := by exact_mod_cast hlt
      linarith
    obtain ⟨m, hm, hmcnt, hmbnd, hmI⟩ := hstep c hlt s hcnt hbnd hcond hI
    have e2 := Stmt.Exec.par (oracle := oracle) (qr := qr)
      [(cntReg, PExpr.reg cntReg + PExpr.const 1),
       (condReg, PExpr.reg boundReg - (PExpr.reg cntReg + PExpr.const 1))] m
    let m' : RS α :=
      ⟨parUpd m.regs [(cntReg, PExpr.reg cntReg + PExpr.const 1),
        (condReg, PExpr.reg boundReg - (PExpr.reg cntReg + PExpr.const 1))] m.regs,
       m.mem, m.queries⟩
    have hm'cnt : m'.regs cntReg = ((c + 1 : ℕ) : ℝ) := by
      simp only [m', parUpd, PExpr.eval_add, PExpr.eval_reg, PExpr.eval_const]
      rw [Function.update_of_ne hcc, Function.update_self, hmcnt]
      push_cast; ring
    have hm'bnd : m'.regs boundReg = (N : ℝ) := by
      simp only [m', parUpd]
      rw [Function.update_of_ne hbc, Function.update_of_ne hcb.symm, hmbnd]
    have hm'cond : m'.regs condReg = (N : ℝ) - ((c + 1 : ℕ) : ℝ) := by
      simp only [m', parUpd, PExpr.eval_sub, PExpr.eval_add, PExpr.eval_reg, PExpr.eval_const]
      rw [Function.update_self, hmbnd, hmcnt]
      push_cast; ring
    have hm'I : Inv (c + 1) m' := by
      simpa only [m', parUpd] using hframe (c + 1) m _ _ hmI
    obtain ⟨s', hs', h1, h2, h3, h4⟩ :=
      ih (c + 1) m' (by omega) (by omega) hm'cnt hm'bnd hm'cond hm'I
    exact ⟨s', Stmt.Exec.while_step hcond_ne (Stmt.Exec.seq hm e2) hs', h1, h2, h3, h4⟩

theorem Stmt.Exec.forNat {cntReg boundReg condReg : α}
    (hcb : cntReg ≠ boundReg) (hcc : cntReg ≠ condReg) (hbc : boundReg ≠ condReg)
    {body : Stmt α} {N : ℕ} (Inv : ℕ → RS α → Prop)
    (hframe : ∀ c (s : RS α) v₁ v₂, Inv c s →
      Inv c ⟨Function.update (Function.update s.regs cntReg v₁) condReg v₂, s.mem, s.queries⟩)
    (hstep : ∀ c, c < N → ∀ s,
      s.regs cntReg = (c : ℝ) → s.regs boundReg = (N : ℝ) →
      s.regs condReg = (N : ℝ) - (c : ℝ) → Inv c s →
      ∃ m, Stmt.Exec oracle qr body s m ∧
        m.regs cntReg = (c : ℝ) ∧ m.regs boundReg = (N : ℝ) ∧ Inv (c + 1) m)
    (s : RS α) (hbound : s.regs boundReg = (N : ℝ)) (h0 : Inv 0 s) :
    ∃ s', Stmt.Exec oracle qr (Stmt.forNat cntReg boundReg condReg body) s s' ∧
      s'.regs cntReg = (N : ℝ) ∧ s'.regs boundReg = (N : ℝ) ∧
      s'.regs condReg = 0 ∧ Inv N s' := by
  have e0 := Stmt.Exec.par (oracle := oracle) (qr := qr)
    [(cntReg, PExpr.const 0), (condReg, PExpr.reg boundReg)] s
  let s₀ : RS α :=
    ⟨parUpd s.regs [(cntReg, PExpr.const 0), (condReg, PExpr.reg boundReg)] s.regs,
     s.mem, s.queries⟩
  have hs₀cnt : s₀.regs cntReg = ((0 : ℕ) : ℝ) := by
    simp only [s₀, parUpd, PExpr.eval_const, PExpr.eval_reg]
    rw [Function.update_of_ne hcc, Function.update_self]; simp
  have hs₀bnd : s₀.regs boundReg = (N : ℝ) := by
    simp only [s₀, parUpd]
    rw [Function.update_of_ne hbc, Function.update_of_ne hcb.symm, hbound]
  have hs₀cond : s₀.regs condReg = (N : ℝ) - ((0 : ℕ) : ℝ) := by
    simp only [s₀, parUpd, PExpr.eval_reg]
    rw [Function.update_self, hbound]; simp
  have hs₀I : Inv 0 s₀ := by
    simpa only [s₀, parUpd] using hframe 0 s _ _ h0
  obtain ⟨s', hs', h1, h2, h3, h4⟩ :=
    Stmt.Exec.forNat_loop hcb hcc hbc Inv hframe hstep N 0 s₀
      (by omega) (by omega) hs₀cnt hs₀bnd hs₀cond hs₀I
  exact ⟨s', Stmt.Exec.seq e0 hs', h1, h2, h3, h4⟩

end ForNat

/-! ### Base-`M` tuple encoding for `Fin d → Fin M` -/

def partEnc {d M : ℕ} (idx : Fin d → Fin M) : ℕ → ℕ
  | 0 => 0
  | r + 1 => partEnc idx r + (if hr : r < d then (idx ⟨r, hr⟩).val else 0) * M ^ r

def encTuple {d M : ℕ} (idx : Fin d → Fin M) : ℕ := partEnc idx d

theorem partEnc_lt {d M : ℕ} (hM : 0 < M) (idx : Fin d → Fin M) :
    ∀ r, partEnc idx r < M ^ r
  | 0 => by simp [partEnc]
  | r + 1 => by
      have ih := partEnc_lt hM idx r
      have hd_lt : (if hr : r < d then (idx ⟨r, hr⟩).val else 0) < M := by
        split_ifs with hr
        · exact (idx ⟨r, hr⟩).isLt
        · exact hM
      have h1 : ((if hr : r < d then (idx ⟨r, hr⟩).val else 0) + 1) * M ^ r ≤ M * M ^ r :=
        Nat.mul_le_mul_right _ hd_lt
      calc partEnc idx (r + 1)
          = partEnc idx r + (if hr : r < d then (idx ⟨r, hr⟩).val else 0) * M ^ r := rfl
        _ < M ^ r + (if hr : r < d then (idx ⟨r, hr⟩).val else 0) * M ^ r :=
            Nat.add_lt_add_right ih _
        _ = ((if hr : r < d then (idx ⟨r, hr⟩).val else 0) + 1) * M ^ r := by ring
        _ ≤ M * M ^ r := h1
        _ = M ^ (r + 1) := by rw [pow_succ']

theorem partEnc_inj {d M : ℕ} (hM : 0 < M) {idx₁ idx₂ : Fin d → Fin M} :
    ∀ r, r ≤ d → partEnc idx₁ r = partEnc idx₂ r → ∀ l : Fin d, l.val < r → idx₁ l = idx₂ l
  | 0, _, _, l, hl => by omega
  | r + 1, hr, heq, l, hl => by
      have hr' : r < d := by omega
      simp only [partEnc, dif_pos hr'] at heq
      have hp₁ := partEnc_lt hM idx₁ r
      have hp₂ := partEnc_lt hM idx₂ r
      have ha_eq : (idx₁ ⟨r, hr'⟩).val = (idx₂ ⟨r, hr'⟩).val := by
        rcases lt_trichotomy (idx₁ ⟨r, hr'⟩).val (idx₂ ⟨r, hr'⟩).val with hlt | he | hgt
        · exfalso
          have hle : ((idx₁ ⟨r, hr'⟩).val + 1) * M ^ r ≤ (idx₂ ⟨r, hr'⟩).val * M ^ r :=
            Nat.mul_le_mul_right _ hlt
          have : partEnc idx₁ r + (idx₁ ⟨r, hr'⟩).val * M ^ r <
              partEnc idx₂ r + (idx₂ ⟨r, hr'⟩).val * M ^ r := by
            calc partEnc idx₁ r + (idx₁ ⟨r, hr'⟩).val * M ^ r
                < M ^ r + (idx₁ ⟨r, hr'⟩).val * M ^ r := Nat.add_lt_add_right hp₁ _
              _ = ((idx₁ ⟨r, hr'⟩).val + 1) * M ^ r := by ring
              _ ≤ (idx₂ ⟨r, hr'⟩).val * M ^ r := hle
              _ ≤ partEnc idx₂ r + (idx₂ ⟨r, hr'⟩).val * M ^ r := Nat.le_add_left _ _
          omega
        · exact he
        · exfalso
          have hle : ((idx₂ ⟨r, hr'⟩).val + 1) * M ^ r ≤ (idx₁ ⟨r, hr'⟩).val * M ^ r :=
            Nat.mul_le_mul_right _ hgt
          have : partEnc idx₂ r + (idx₂ ⟨r, hr'⟩).val * M ^ r <
              partEnc idx₁ r + (idx₁ ⟨r, hr'⟩).val * M ^ r := by
            calc partEnc idx₂ r + (idx₂ ⟨r, hr'⟩).val * M ^ r
                < M ^ r + (idx₂ ⟨r, hr'⟩).val * M ^ r := Nat.add_lt_add_right hp₂ _
              _ = ((idx₂ ⟨r, hr'⟩).val + 1) * M ^ r := by ring
              _ ≤ (idx₁ ⟨r, hr'⟩).val * M ^ r := hle
              _ ≤ partEnc idx₁ r + (idx₁ ⟨r, hr'⟩).val * M ^ r := Nat.le_add_left _ _
          omega
      have hp_eq : partEnc idx₁ r = partEnc idx₂ r := by
        rw [ha_eq] at heq
        exact Nat.add_right_cancel heq
      by_cases hlr : l.val < r
      · exact partEnc_inj hM r (by omega) hp_eq l hlr
      · have hle : l = ⟨r, hr'⟩ := Fin.ext (by dsimp; omega)
        rw [hle]
        exact Fin.ext ha_eq

theorem encTuple_lt {d M : ℕ} (hM : 0 < M) (idx : Fin d → Fin M) : encTuple idx < M ^ d :=
  partEnc_lt hM idx d

theorem encTuple_inj {d M : ℕ} (hM : 0 < M) :
    Function.Injective (encTuple (d := d) (M := M)) :=
  fun _ _ heq => funext fun l => partEnc_inj hM d le_rfl heq l l.isLt

theorem partEnc_zero {d M : ℕ} (hM : 0 < M) :
    ∀ r, partEnc (fun _ : Fin d => (⟨0, hM⟩ : Fin M)) r = 0
  | 0 => rfl
  | r + 1 => by simp [partEnc, partEnc_zero hM r]

theorem encTuple_zero {d M : ℕ} (hM : 0 < M) :
    encTuple (fun _ : Fin d => (⟨0, hM⟩ : Fin M)) = 0 :=
  partEnc_zero hM d

/-! ### Register file and generic Cramer BFS search -/

namespace Bfs

abbrev CramerReg (d : ℕ) := Fin 18 ⊕ (Fin 7 × Fin d) ⊕ (Fin d × Fin d)

abbrev rFound   {d : ℕ} : CramerReg d := Sum.inl 0
abbrev rK       {d : ℕ} : CramerReg d := Sum.inl 1
abbrev rV       {d : ℕ} : CramerReg d := Sum.inl 2
abbrev rM       {d : ℕ} : CramerReg d := Sum.inl 3
abbrev rTupAct  {d : ℕ} : CramerReg d := Sum.inl 4
abbrev rCarry   {d : ℕ} : CramerReg d := Sum.inl 5
abbrev rConIdx  {d : ℕ} : CramerReg d := Sum.inl 6
abbrev rConB    {d : ℕ} : CramerReg d := Sum.inl 7
abbrev rDet     {d : ℕ} : CramerReg d := Sum.inl 8
abbrev rNum     {d : ℕ} : CramerReg d := Sum.inl 9
abbrev rFeasOk  {d : ℕ} : CramerReg d := Sum.inl 10
abbrev rCnt1    {d : ℕ} : CramerReg d := Sum.inl 11
abbrev rCond1   {d : ℕ} : CramerReg d := Sum.inl 12
abbrev rExtraOk {d : ℕ} : CramerReg d := Sum.inl 13
abbrev rCnt2    {d : ℕ} : CramerReg d := Sum.inl 14
abbrev rCond2   {d : ℕ} : CramerReg d := Sum.inl 15
abbrev rIx      {d : ℕ} : CramerReg d := Sum.inl 16
abbrev rTmp     {d : ℕ} : CramerReg d := Sum.inl 17

abbrev rQr     {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (0, l))
abbrev rU      {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (1, l))
abbrev rTup    {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (2, l))
abbrev rVecB   {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (3, l))
abbrev rConA   {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (4, l))
abbrev rVecTmp {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (5, l))
abbrev rCand   {d : ℕ} (l : Fin d) : CramerReg d := Sum.inr (Sum.inl (6, l))

abbrev rMat {d : ℕ} (i l : Fin d) : CramerReg d := Sum.inr (Sum.inr (i, l))

theorem rQr_injective (d : ℕ) : Function.Injective (rQr (d := d)) := by
  intro i j h; simpa using h

theorem rU_injective (d : ℕ) : Function.Injective (rU (d := d)) := by
  intro i j h; simpa using h

theorem rTup_injective (d : ℕ) : Function.Injective (rTup (d := d)) := by
  intro i j h; simpa using h

theorem rConA_injective (d : ℕ) : Function.Injective (rConA (d := d)) := by
  intro i j h; simpa using h

theorem rVecTmp_injective (d : ℕ) : Function.Injective (rVecTmp (d := d)) := by
  intro i j h; simpa using h

theorem rMat_row_injective (d : ℕ) (i : Fin d) : Function.Injective (rMat i) := by
  intro l₁ l₂ h; simpa using h

/-- Advance the `d`-tuple `rTup` in base `rM`, setting `rTupAct := 1 - rCarry`. -/
def stepTuple (d : ℕ) : Stmt (CramerReg d) :=
  .seq (Stmt.assign rCarry (PExpr.const 1))
    (.seq
      (Stmt.seqFin d fun l =>
        .ite rCarry .skip .skip
          (.seq
            (.par [(rTup l, PExpr.reg (rTup l) + PExpr.const 1),
                   (rTmp, (PExpr.reg (rTup l) + PExpr.const 1) - PExpr.reg rM)])
            (.ite rTmp
              (Stmt.assign rCarry (PExpr.const 0))
              (Stmt.assign (rTup l) (PExpr.const 0))
              .skip)))
      (Stmt.assign rTupAct (PExpr.const 1 - PExpr.reg rCarry)))

theorem stepTuple_spec {d M : ℕ} (hM : 0 < M)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (idx : Fin d → Fin M) (s : RS (CramerReg d))
    (hMreg : s.regs rM = (M : ℝ))
    (htup : ∀ l : Fin d, s.regs (rTup l) = ((idx l).val : ℝ)) :
    ∃ s', Stmt.Exec oracle rQr (stepTuple d) s s' ∧
      s'.mem = s.mem ∧ s'.queries = s.queries ∧
      (∀ reg, reg ≠ rCarry → reg ≠ rTmp → reg ≠ rTupAct → (∀ l, reg ≠ rTup l) →
        s'.regs reg = s.regs reg) ∧
      ((encTuple idx + 1 < M ^ d ∧ s'.regs rTupAct = 1 ∧
          ∃ idx' : Fin d → Fin M,
            encTuple idx' = encTuple idx + 1 ∧
            ∀ l : Fin d, s'.regs (rTup l) = ((idx' l).val : ℝ)) ∨
       (encTuple idx + 1 = M ^ d ∧ s'.regs rTupAct = 0)) := by
  have e0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rCarry (PExpr.const 1) s 1 (by simp)
  let s₀ : RS (CramerReg d) :=
    ⟨Function.update s.regs rCarry 1, s.mem, s.queries⟩
  -- Run seqFin d maintaining partial odometer invariant
  let Inv : ℕ → RS (CramerReg d) → Prop := fun r st =>
    st.mem = s.mem ∧ st.queries = s.queries ∧
    (∀ reg, reg ≠ rCarry → reg ≠ rTmp → reg ≠ rTupAct → (∀ l, reg ≠ rTup l) →
      st.regs reg = s.regs reg) ∧
    (∀ l : Fin d, r ≤ l.val → st.regs (rTup l) = ((idx l).val : ℝ)) ∧
    ∃ (idx' : Fin d → Fin M) (c : ℕ),
      (c = 0 ∨ c = 1) ∧
      st.regs rCarry = (c : ℝ) ∧
      (∀ l : Fin d, l.val < r → st.regs (rTup l) = ((idx' l).val : ℝ)) ∧
      partEnc idx' r + c * M ^ r = partEnc idx r + 1
  have h0 : Inv 0 s₀ := by
    refine ⟨rfl, rfl, ?_, ?_, idx, 1, Or.inr rfl, ?_, fun _ hl => by omega, by simp [partEnc]⟩
    · intro reg hc _ _ _
      exact Function.update_of_ne hc _ _
    · intro l _
      simp [s₀, htup l]
    · simp [s₀]
  obtain ⟨s₁, eseq, hmem₁, hq₁, hpres₁, _, idx', c, hc01, hcarry₁, htup₁, henc₁⟩ :=
    Stmt.Exec.seqFin_inv (oracle := oracle) (qr := rQr)
      (fun l : Fin d =>
        Stmt.ite rCarry .skip .skip
          (.seq
            (.par [(rTup l, PExpr.reg (rTup l) + PExpr.const 1),
                   (rTmp, (PExpr.reg (rTup l) + PExpr.const 1) - PExpr.reg rM)])
            (.ite rTmp
              (Stmt.assign rCarry (PExpr.const 0))
              (Stmt.assign (rTup l) (PExpr.const 0))
              .skip)))
      Inv
      (by
        intro l st ⟨hm, hq, hpr, hhi, idx_p, c, hc, hcar, hlo, heq_p⟩
        have hM_st : st.regs rM = (M : ℝ) := by
          rw [hpr rM (by simp) (by simp) (by simp) (fun _ => by simp), hMreg]
        have htl : st.regs (rTup l) = ((idx l).val : ℝ) := hhi l le_rfl
        rcases hc with rfl | rfl
        · -- carry = 0: ite_zero -> skip
          have hcz : st.regs rCarry = 0 := by simpa using hcar
          refine ⟨st, Stmt.Exec.ite_zero hcz (Stmt.Exec.skip st), hm, hq, hpr,
            fun l' hl' => hhi l' (by omega),
            Function.update idx_p l (idx l), 0, Or.inl rfl, hcar, ?_, ?_⟩
          · intro l' hl'
            by_cases hll : l' = l
            · subst hll; simpa using htl
            · have hlt' : l'.val < l.val := by
                have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                omega
              rw [Function.update_of_ne hll]
              exact hlo l' hlt'
          · have hp_same : partEnc (Function.update idx_p l (idx l)) l.val = partEnc idx_p l.val := by
              clear hcz hcar
              suffices ∀ r, r ≤ l.val →
                  partEnc (Function.update idx_p l (idx l)) r = partEnc idx_p r from
                this l.val le_rfl
              intro r hr
              induction r with
              | zero => rfl
              | succ r ihr =>
                have hrlt : r < d := by have := l.isLt; omega
                have hne_l : (⟨r, hrlt⟩ : Fin d) ≠ l := fun e => by
                  have := congrArg Fin.val e; dsimp at this; omega
                simp [partEnc, dif_pos hrlt, ihr (by omega), Function.update_of_ne hne_l]
            simp only [partEnc, dif_pos l.isLt, Fin.eta, hp_same, Function.update_self, zero_mul, add_zero] at heq_p ⊢
            omega
        · -- carry = 1: ite_pos
          have hcp : 0 < st.regs rCarry := by rw [hcar]; norm_num
          have ep1 := Stmt.Exec.par (oracle := oracle) (qr := rQr)
            [(rTup l, PExpr.reg (rTup l) + PExpr.const 1),
             (rTmp, (PExpr.reg (rTup l) + PExpr.const 1) - PExpr.reg rM)] st
          let st1 : RS (CramerReg d) :=
            ⟨parUpd st.regs [(rTup l, PExpr.reg (rTup l) + PExpr.const 1),
              (rTmp, (PExpr.reg (rTup l) + PExpr.const 1) - PExpr.reg rM)] st.regs,
             st.mem, st.queries⟩
          have htmp1 : st1.regs rTmp = ((idx l).val : ℝ) + 1 - (M : ℝ) := by
            simp [st1, parUpd, htl, hM_st]
          have htup1_l : st1.regs (rTup l) = (((idx l).val + 1 : ℕ) : ℝ) := by
            have hne : rTup l ≠ rTmp := by simp
            simp only [st1, parUpd, PExpr.eval_add, PExpr.eval_reg, PExpr.eval_const]
            rw [Function.update_of_ne hne, Function.update_self, htl]
            push_cast; ring
          rcases Nat.lt_or_ge ((idx l).val + 1) M with hltM | hgeM
          · -- (idx l).val + 1 < M: rTmp < 0, carry := 0
            have hneg : st1.regs rTmp < 0 := by
              rw [htmp1]
              have : (((idx l).val + 1 : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hltM
              push_cast at this; linarith
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rCarry (PExpr.const 0) st1 0 (by simp)
            let st2 : RS (CramerReg d) := ⟨Function.update st1.regs rCarry 0, st1.mem, st1.queries⟩
            let d_new : Fin M := ⟨(idx l).val + 1, hltM⟩
            have hp_same : partEnc (Function.update idx_p l d_new) l.val = partEnc idx_p l.val := by
              suffices ∀ r, r ≤ l.val →
                  partEnc (Function.update idx_p l d_new) r = partEnc idx_p r from
                this l.val le_rfl
              intro r hr
              induction r with
              | zero => rfl
              | succ r ihr =>
                have hrlt : r < d := by have := l.isLt; omega
                have hne_l : (⟨r, hrlt⟩ : Fin d) ≠ l := fun e => by
                  have := congrArg Fin.val e; dsimp at this; omega
                simp [partEnc, dif_pos hrlt, ihr (by omega), Function.update_of_ne hne_l]
            refine ⟨st2, Stmt.Exec.ite_pos hcp (Stmt.Exec.seq ep1 (Stmt.Exec.ite_neg hneg ea)),
              hm, hq, ?_, ?_, Function.update idx_p l d_new, 0, Or.inl rfl, ?_, ?_, ?_⟩
            · intro reg hc ht ha htu
              simp only [st2, st1, parUpd]
              rw [Function.update_of_ne hc, Function.update_of_ne ht, Function.update_of_ne (htu l)]
              exact hpr reg hc ht ha htu
            · intro l' hl'
              have hne_ll : rTup l' ≠ rTup l := fun e => by
                have := rTup_injective d e; subst this; omega
              simp only [st2, st1, parUpd]
              rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
                Function.update_of_ne hne_ll]
              exact hhi l' (by omega)
            · simp [st2]
            · intro l' hl'
              by_cases hll : l' = l
              · subst hll
                simp only [st2, d_new]
                rw [Function.update_self, Function.update_of_ne (by simp : rTup l' ≠ rCarry)]
                exact htup1_l
              · have hlt' : l'.val < l.val := by
                  have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                  omega
                have hne_ll : rTup l' ≠ rTup l := fun e => hll (rTup_injective d e)
                simp only [st2, st1, parUpd]
                rw [Function.update_of_ne hll, Function.update_of_ne (by simp),
                  Function.update_of_ne (by simp), Function.update_of_ne hne_ll]
                exact hlo l' hlt'
            · simp only [partEnc, dif_pos l.isLt, Fin.eta, hp_same, Function.update_self, d_new,
                zero_mul, add_zero]
              simp only [one_mul] at heq_p
              have : ((idx l).val + 1) * M ^ l.val = M ^ l.val + (idx l).val * M ^ l.val := by ring
              omega
          · -- (idx l).val + 1 = M: rTmp = 0, rTup l := 0, carry stays 1
            have heqM : (idx l).val + 1 = M := by have := (idx l).isLt; omega
            have hzero : st1.regs rTmp = 0 := by
              rw [htmp1]
              have : (((idx l).val + 1 : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast heqM
              push_cast at this; linarith
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) (rTup l) (PExpr.const 0) st1 0 (by simp)
            let st2 : RS (CramerReg d) :=
              ⟨Function.update st1.regs (rTup l) 0, st1.mem, st1.queries⟩
            let d_new : Fin M := ⟨0, hM⟩
            have hp_same : partEnc (Function.update idx_p l d_new) l.val = partEnc idx_p l.val := by
              suffices ∀ r, r ≤ l.val →
                  partEnc (Function.update idx_p l d_new) r = partEnc idx_p r from
                this l.val le_rfl
              intro r hr
              induction r with
              | zero => rfl
              | succ r ihr =>
                have hrlt : r < d := by have := l.isLt; omega
                have hne_l : (⟨r, hrlt⟩ : Fin d) ≠ l := fun e => by
                  have := congrArg Fin.val e; dsimp at this; omega
                simp [partEnc, dif_pos hrlt, ihr (by omega), Function.update_of_ne hne_l]
            refine ⟨st2, Stmt.Exec.ite_pos hcp (Stmt.Exec.seq ep1 (Stmt.Exec.ite_zero hzero ea)),
              hm, hq, ?_, ?_, Function.update idx_p l d_new, 1, Or.inr rfl, ?_, ?_, ?_⟩
            · intro reg hc ht ha htu
              simp only [st2, st1, parUpd]
              rw [Function.update_of_ne (htu l), Function.update_of_ne ht,
                Function.update_of_ne (htu l)]
              exact hpr reg hc ht ha htu
            · intro l' hl'
              have hne_ll : rTup l' ≠ rTup l := fun e => by
                have := rTup_injective d e; subst this; omega
              simp only [st2, st1, parUpd]
              rw [Function.update_of_ne hne_ll, Function.update_of_ne (by simp),
                Function.update_of_ne hne_ll]
              exact hhi l' (by omega)
            · simp only [st2, st1, parUpd]
              rw [Function.update_of_ne (by simp : rCarry ≠ rTup l),
                Function.update_of_ne (by simp : rCarry ≠ rTmp),
                Function.update_of_ne (by simp : rCarry ≠ rTup l), hcar]
            · intro l' hl'
              by_cases hll : l' = l
              · subst hll
                simp [st2, d_new]
              · have hlt' : l'.val < l.val := by
                  have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                  omega
                have hne_ll : rTup l' ≠ rTup l := fun e => hll (rTup_injective d e)
                simp only [st2, st1, parUpd]
                rw [Function.update_of_ne hll, Function.update_of_ne hne_ll,
                  Function.update_of_ne (by simp), Function.update_of_ne hne_ll]
                exact hlo l' hlt'
            · simp only [partEnc, dif_pos l.isLt, Fin.eta, hp_same, Function.update_self, d_new,
                zero_mul, add_zero, one_mul]
              simp only [one_mul] at heq_p
              have hpow : M ^ (l.val + 1) = M * M ^ l.val := pow_succ' M l.val
              have hmul : M * M ^ l.val = M ^ l.val + (idx l).val * M ^ l.val := by
                calc M * M ^ l.val = ((idx l).val + 1) * M ^ l.val := by rw [heqM]
                  _ = M ^ l.val + (idx l).val * M ^ l.val := by ring
              omega)
      s₀ h0
  -- Final assignment rTupAct := 1 - rCarry
  have e_end := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rTupAct
    (PExpr.const 1 - PExpr.reg rCarry) s₁ (1 - s₁.regs rCarry) (by simp)
  let s' : RS (CramerReg d) :=
    ⟨Function.update s₁.regs rTupAct (1 - s₁.regs rCarry), s₁.mem, s₁.queries⟩
  refine ⟨s', Stmt.Exec.seq e0 (Stmt.Exec.seq eseq e_end), hmem₁, hq₁, ?_, ?_⟩
  · intro reg hc ht ha htu
    simp only [s']
    rw [Function.update_of_ne ha]
    exact hpres₁ reg hc ht ha htu
  · change encTuple idx' + c * M ^ d = encTuple idx + 1 at henc₁
    have hlt' : encTuple idx' < M ^ d := encTuple_lt hM idx'
    have hlt0 : encTuple idx < M ^ d := encTuple_lt hM idx
    rcases hc01 with rfl | rfl
    · left
      simp only [zero_mul, add_zero] at henc₁
      refine ⟨by omega, ?_, idx', henc₁, ?_⟩
      · simp [s', hcarry₁]
      · intro l
        simp only [s']
        rw [Function.update_of_ne (by simp : rTup l ≠ rTupAct)]
        exact htup₁ l l.isLt
    · right
      simp only [one_mul] at henc₁
      have : encTuple idx' = 0 ∧ encTuple idx + 1 = M ^ d := by omega
      refine ⟨this.2, ?_⟩
      simp [s', hcarry₁]

/-- Generic Cramer BFS search parameterized by `loadCon` and `checkExtra`. -/
noncomputable def cramerSearch (d : ℕ) (loadCon checkExtra : Stmt (CramerReg d)) :
    Stmt (CramerReg d) :=
  let loadMatrix : Stmt (CramerReg d) :=
    Stmt.seqFin d fun i =>
      .seq (Stmt.assign rConIdx (PExpr.reg (rTup i)))
        (.seq loadCon
          (.seq (Stmt.vset (rMat i) fun l => PExpr.reg (rConA l))
            (Stmt.assign (rVecB i) (PExpr.reg rConB))))
  let solveCand : Stmt (CramerReg d) :=
    Stmt.seqFin d fun l =>
      .seq
        (Stmt.assign rNum
          (PExpr.det fun i l' => if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')))
        (.div (rCand l) rNum rDet)
  let checkFeas : Stmt (CramerReg d) :=
    .seq (Stmt.assign rFeasOk (PExpr.const 1))
      (Stmt.forNat rCnt1 rM rCond1
        (.seq (Stmt.assign rConIdx (PExpr.reg rCnt1))
          (.seq loadCon
            (.seq
              (Stmt.assign rTmp
                (PExpr.dot (fun l => PExpr.reg (rConA l)) (fun l => PExpr.reg (rCand l)) -
                  PExpr.reg rConB))
              (.ite rTmp .skip .skip (Stmt.assign rFeasOk (PExpr.const 0)))))))
  let solveAndCheck : Stmt (CramerReg d) :=
    .seq solveCand
      (.seq checkFeas
        (.seq checkExtra
          (.seq (Stmt.assign rTmp (PExpr.reg rFeasOk * PExpr.reg rExtraOk))
            (.ite rTmp .skip .skip
              (.seq (Stmt.vset rU fun l => PExpr.reg (rCand l))
                (Stmt.assign rFound (PExpr.const 1)))))))
  let body : Stmt (CramerReg d) :=
    .seq loadMatrix
      (.seq (Stmt.assign rDet (PExpr.det fun i l => PExpr.reg (rMat i l)))
        (.seq (Stmt.assign rTmp (PExpr.reg rDet * PExpr.reg rDet))
          (.seq (.ite rTmp .skip .skip solveAndCheck)
            (stepTuple d))))
  .seq (Stmt.assign rFound (PExpr.const 0))
    (.ite rM .skip .skip
      (.seq
        (.seq (Stmt.vset rTup fun _ => PExpr.const 0)
          (Stmt.assign rTupAct (PExpr.const 1)))
        (.while rTupAct body)))

theorem cramerSearch_spec {d k V M : ℕ} (hd : 0 < d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (mem₀ : ℕ → ℝ) (α : Fin M → Fin d → ℝ) (β : Fin M → ℝ)
    (P_extra : (Fin d → ℝ) → Prop)
    (loadCon checkExtra : Stmt (CramerReg d))
    (hload : ∀ (r : Fin M) (s : RS (CramerReg d)),
      s.mem = mem₀ → s.regs rK = (k : ℝ) → s.regs rV = (V : ℝ) →
      s.regs rConIdx = (r.val : ℝ) →
      ∃ s', Stmt.Exec oracle rQr loadCon s s' ∧
        s'.mem = s.mem ∧ s'.queries = s.queries ∧
        (∀ l : Fin d, s'.regs (rConA l) = α r l) ∧
        s'.regs rConB = β r ∧
        (∀ reg, (∀ l, reg ≠ rConA l) → reg ≠ rConB → reg ≠ rIx → reg ≠ rTmp →
          s'.regs reg = s.regs reg))
    (hextra : ∀ (s : RS (CramerReg d)),
      s.mem = mem₀ → s.regs rK = (k : ℝ) → s.regs rV = (V : ℝ) →
      ∃ s', Stmt.Exec oracle rQr checkExtra s s' ∧
        s'.mem = s.mem ∧ s'.queries = s.queries ∧
        ((s'.regs rExtraOk = 1 ∧ P_extra (fun l => s.regs (rCand l))) ∨
         (s'.regs rExtraOk = 0 ∧ ¬ P_extra (fun l => s.regs (rCand l)))) ∧
        (∀ reg, reg ≠ rExtraOk → reg ≠ rCnt2 → reg ≠ rCond2 → reg ≠ rIx → reg ≠ rTmp →
          (∀ l, reg ≠ rVecTmp l) → s'.regs reg = s.regs reg))
    (s : RS (CramerReg d))
    (hmem : s.mem = mem₀) (hK : s.regs rK = (k : ℝ)) (hV : s.regs rV = (V : ℝ))
    (hM : s.regs rM = (M : ℝ)) :
    ∃ s', Stmt.Exec oracle rQr (cramerSearch d loadCon checkExtra) s s' ∧
      s'.mem = s.mem ∧ s'.queries = s.queries ∧
      s'.regs rK = (k : ℝ) ∧ s'.regs rV = (V : ℝ) ∧
      ((s'.regs rFound = 1 ∧
          IsCramerBFS α β (fun l => s'.regs (rU l)) ∧
          P_extra (fun l => s'.regs (rU l))) ∨
       (s'.regs rFound = 0 ∧
          ∀ u, IsCramerBFS α β u → ¬ P_extra u)) := by
  have ef0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rFound (PExpr.const 0) s 0 (by simp)
  let s₀ : RS (CramerReg d) := ⟨Function.update s.regs rFound 0, s.mem, s.queries⟩
  have hs₀M : s₀.regs rM = (M : ℝ) := by simp [s₀, hM]
  have hs₀K : s₀.regs rK = (k : ℝ) := by simp [s₀, hK]
  have hs₀V : s₀.regs rV = (V : ℝ) := by simp [s₀, hV]
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · -- M = 0: ite_zero
    have hz : s₀.regs rM = 0 := by simpa using hs₀M
    refine ⟨s₀, Stmt.Exec.seq ef0 (Stmt.Exec.ite_zero hz (Stmt.Exec.skip s₀)),
      rfl, rfl, hs₀K, hs₀V, Or.inr ⟨by simp [s₀], ?_⟩⟩
    intro u ⟨_, idx, _⟩
    exact Fin.elim0 (idx ⟨0, hd⟩)
  · -- 0 < M: ite_pos
    have hpM : 0 < s₀.regs rM := by
      rw [hs₀M]; exact_mod_cast hMpos
    have ev0 := Stmt.Exec.vset_eval (oracle := oracle) (qr := rQr) (rTup_injective d)
      (fun _ => PExpr.const 0) s₀ (fun _ => 0) (fun _ => by simp)
    let s₁ : RS (CramerReg d) :=
      ⟨Function.extend rTup (fun _ => (0 : ℝ)) s₀.regs, s₀.mem, s₀.queries⟩
    have ea0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rTupAct (PExpr.const 1) s₁ 1 (by simp)
    let s₂ : RS (CramerReg d) :=
      ⟨Function.update s₁.regs rTupAct 1, s₁.mem, s₁.queries⟩
    -- Define validity of a tuple
    let solOf : (Fin d → Fin M) → Fin d → ℝ := fun idx l =>
      (((Matrix.of fun i l' => α (idx i) l').updateCol l (fun i => β (idx i))).det) /
        (Matrix.of fun i l' => α (idx i) l').det
    let ValidTuple : (Fin d → Fin M) → Prop := fun idx =>
      (Matrix.of fun i l => α (idx i) l).det ≠ 0 ∧
        (∀ r : Fin M, dot (α r) (solOf idx) ≤ β r) ∧ P_extra (solOf idx)
    let LoopInv : RS (CramerReg d) → Prop := fun st =>
      st.mem = mem₀ ∧ st.queries = s.queries ∧
      st.regs rK = (k : ℝ) ∧ st.regs rV = (V : ℝ) ∧ st.regs rM = (M : ℝ) ∧
      ∃ cur : ℕ, cur ≤ M ^ d ∧
        ((cur < M ^ d ∧ st.regs rTupAct = 1 ∧
            ∃ idx : Fin d → Fin M, encTuple idx = cur ∧
              ∀ l : Fin d, st.regs (rTup l) = ((idx l).val : ℝ)) ∨
         (cur = M ^ d ∧ st.regs rTupAct = 0)) ∧
        ((st.regs rFound = 1 ∧
            IsCramerBFS α β (fun l => st.regs (rU l)) ∧
            P_extra (fun l => st.regs (rU l))) ∨
         (st.regs rFound = 0 ∧
            ∀ idx₀ : Fin d → Fin M, encTuple idx₀ < cur → ¬ ValidTuple idx₀))
    let μ : RS (CramerReg d) → ℕ := fun st =>
      if h : st.regs rTupAct = 1 ∧
          ∃ idx : Fin d → Fin M, ∀ l : Fin d, st.regs (rTup l) = ((idx l).val : ℝ)
      then M ^ d - encTuple (Classical.choose h.2)
      else 0
    have hInv2 : LoopInv s₂ := by
      have hnot_tup : ∀ reg, (∀ l, reg ≠ rTup l) → s₁.regs reg = s₀.regs reg := by
        intro reg hne
        dsimp only [s₁]
        exact Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact hne l he.symm)
      refine ⟨hmem, rfl, ?_, ?_, ?_, 0, Nat.zero_le _, Or.inl ⟨pow_pos hMpos d, ?_, ?_⟩,
        Or.inr ⟨?_, fun _ hlt => by omega⟩⟩
      · simp [s₂, hnot_tup rK (fun _ => by simp), hs₀K]
      · simp [s₂, hnot_tup rV (fun _ => by simp), hs₀V]
      · simp [s₂, hnot_tup rM (fun _ => by simp), hs₀M]
      · simp [s₂]
      · refine ⟨fun _ => ⟨0, hMpos⟩, encTuple_zero hMpos, fun l => ?_⟩
        simp only [s₂, Function.update_of_ne (by simp : rTup l ≠ rTupAct), s₁]
        rw [(rTup_injective d).extend_apply]; simp
      · simp [s₂, hnot_tup rFound (fun _ => by simp), s₀]
    -- Prove while loop via Stmt.Exec.while_inv
    obtain ⟨s_end, ewhile, hEndInv, hEndZero⟩ :=
      Stmt.Exec.while_inv (oracle := oracle) (qr := rQr) LoopInv μ
        (by
          intro st hI hact_ne
          obtain ⟨hst_mem, hst_q, hst_K, hst_V, hst_M, cur, _, hcur_state, hfound_state⟩ := hI
          rcases hcur_state with ⟨hcur_lt, hst_act, idx, hidx_enc, hst_tup⟩ | ⟨_, hst_act0⟩
          swap
          · exact absurd hst_act0 hact_ne
          have hμ_st : μ st = M ^ d - cur := by
            have hex : st.regs rTupAct = 1 ∧
                ∃ idx : Fin d → Fin M, ∀ l, st.regs (rTup l) = ((idx l).val : ℝ) :=
              ⟨hst_act, idx, hst_tup⟩
            simp only [μ, dif_pos hex]
            have hch := Classical.choose_spec hex.2
            have heq_idx : Classical.choose hex.2 = idx := by
              funext l
              have hl := (hch l).symm.trans (hst_tup l)
              exact Fin.ext (Nat.cast_injective hl)
            rw [heq_idx, hidx_enc]
          -- Step A: loadMatrix
          obtain ⟨stA, eA, hA_mem, hA_q, hA_mat, hA_b, hA_pres⟩ :
              ∃ stA, Stmt.Exec oracle rQr
                (Stmt.seqFin d fun i =>
                  .seq (Stmt.assign rConIdx (PExpr.reg (rTup i)))
                    (.seq loadCon
                      (.seq (Stmt.vset (rMat i) fun l => PExpr.reg (rConA l))
                        (Stmt.assign (rVecB i) (PExpr.reg rConB))))) st stA ∧
                stA.mem = mem₀ ∧ stA.queries = s.queries ∧
                (∀ i l : Fin d, stA.regs (rMat i l) = α (idx i) l) ∧
                (∀ i : Fin d, stA.regs (rVecB i) = β (idx i)) ∧
                (∀ reg, reg ≠ rConIdx → (∀ l, reg ≠ rConA l) → reg ≠ rConB →
                  reg ≠ rIx → reg ≠ rTmp → (∀ i l, reg ≠ rMat i l) → (∀ i, reg ≠ rVecB i) →
                  stA.regs reg = st.regs reg) := by
            obtain ⟨stA, eA, h1, h2, h3, h4, h5⟩ :=
              Stmt.Exec.seqFin_inv (oracle := oracle) (qr := rQr)
                (fun i =>
                  .seq (Stmt.assign rConIdx (PExpr.reg (rTup i)))
                    (.seq loadCon
                      (.seq (Stmt.vset (rMat i) fun l => PExpr.reg (rConA l))
                        (Stmt.assign (rVecB i) (PExpr.reg rConB)))))
                (fun r st1 =>
                  st1.mem = mem₀ ∧ st1.queries = s.queries ∧
                  (∀ i : Fin d, i.val < r → ∀ l : Fin d, st1.regs (rMat i l) = α (idx i) l) ∧
                  (∀ i : Fin d, i.val < r → st1.regs (rVecB i) = β (idx i)) ∧
                  (∀ reg, reg ≠ rConIdx → (∀ l, reg ≠ rConA l) → reg ≠ rConB →
                    reg ≠ rIx → reg ≠ rTmp → (∀ i l, reg ≠ rMat i l) → (∀ i, reg ≠ rVecB i) →
                    st1.regs reg = st.regs reg))
                (by
                  intro i st1 ⟨hm1, hq1, hmat1, hb1, hpr1⟩
                  have htup_i : st1.regs (rTup i) = ((idx i).val : ℝ) := by
                    rw [hpr1 (rTup i) (by simp) (fun _ => by simp) (by simp)
                      (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp)]
                    exact hst_tup i
                  have ea1 := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rConIdx
                    (PExpr.reg (rTup i)) st1
                  let st2 : RS (CramerReg d) :=
                    ⟨Function.update st1.regs rConIdx (st1.regs (rTup i)), st1.mem, st1.queries⟩
                  have hK2 : st2.regs rK = (k : ℝ) := by
                    simp only [st2, Function.update_of_ne (by simp : rK ≠ rConIdx)]
                    rw [hpr1 rK (by simp) (fun _ => by simp) (by simp) (by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_K]
                  have hV2 : st2.regs rV = (V : ℝ) := by
                    simp only [st2, Function.update_of_ne (by simp : rV ≠ rConIdx)]
                    rw [hpr1 rV (by simp) (fun _ => by simp) (by simp) (by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_V]
                  obtain ⟨st3, elc, hm3, hq3, hca3, hcb3, hpr3⟩ :=
                    hload (idx i) st2 hm1 hK2 hV2 (by simp [st2, htup_i])
                  have ev3 := Stmt.Exec.vset (oracle := oracle) (qr := rQr) (rMat_row_injective d i)
                    (fun l => PExpr.reg (rConA l)) st3
                  let st4 : RS (CramerReg d) :=
                    ⟨Function.extend (rMat i) (fun l => st3.regs (rConA l)) st3.regs,
                     st3.mem, st3.queries⟩
                  have eb4 := Stmt.Exec.assign (oracle := oracle) (qr := rQr) (rVecB i)
                    (PExpr.reg rConB) st4
                  let st5 : RS (CramerReg d) :=
                    ⟨Function.update st4.regs (rVecB i) (st4.regs rConB), st4.mem, st4.queries⟩
                  refine ⟨st5, Stmt.Exec.seq ea1 (Stmt.Exec.seq elc (Stmt.Exec.seq ev3 eb4)),
                    hm3.trans hm1, hq3.trans hq1, ?_, ?_, ?_⟩
                  · intro j hj l
                    by_cases hji : j = i
                    · subst hji
                      simp only [st5, Function.update_of_ne (by simp : rMat j l ≠ rVecB j), st4]
                      rw [(rMat_row_injective d j).extend_apply, hca3 l]
                    · have hjlt : j.val < i.val := by
                        have : j.val ≠ i.val := fun e => hji (Fin.ext e)
                        omega
                      simp only [st5, Function.update_of_ne (by simp : rMat j l ≠ rVecB i), st4]
                      rw [Function.extend_apply' _ _ _ (by
                        rintro ⟨l', he⟩; simp at he; exact hji he.1.symm)]
                      rw [hpr3 (rMat j l) (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp only [st2, Function.update_of_ne (by simp : rMat j l ≠ rConIdx)]
                      exact hmat1 j hjlt l
                  · intro j hj
                    by_cases hji : j = i
                    · subst hji
                      simp only [st5, Function.update_self, st4]
                      rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hcb3]
                    · have hjlt : j.val < i.val := by
                        have : j.val ≠ i.val := fun e => hji (Fin.ext e)
                        omega
                      have hneb : rVecB j ≠ rVecB i := fun e => by simp at e; exact hji e
                      simp only [st5, Function.update_of_ne hneb, st4]
                      rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
                      rw [hpr3 (rVecB j) (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp only [st2, Function.update_of_ne (by simp : rVecB j ≠ rConIdx)]
                      exact hb1 j hjlt
                  · intro reg hci hca hcb hix htm hm_ne hvb_ne
                    simp only [st5, Function.update_of_ne (hvb_ne i), st4]
                    rw [Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact hm_ne i l he.symm)]
                    rw [hpr3 reg hca hcb hix htm]
                    simp only [st2, Function.update_of_ne hci]
                    exact hpr1 reg hci hca hcb hix htm hm_ne hvb_ne)
                st ⟨hst_mem, hst_q, fun _ h => by omega, fun _ h => by omega,
                  fun _ _ _ _ _ _ _ _ => rfl⟩
            exact ⟨stA, eA, h1, h2, fun i l => h3 i i.isLt l, fun i => h4 i i.isLt, h5⟩
          -- Step B: compute det and rDet * rDet
          let A_mat := Matrix.of fun i l => α (idx i) l
          have edet := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rDet
            (PExpr.det fun i l => PExpr.reg (rMat i l)) stA
          let stB : RS (CramerReg d) :=
            ⟨Function.update stA.regs rDet ((PExpr.det fun i l => PExpr.reg (rMat i l)).eval stA.regs),
             stA.mem, stA.queries⟩
          have hB_det : stB.regs rDet = A_mat.det := by
            simp only [stB, Function.update_self, PExpr.eval_det, PExpr.eval_reg, A_mat]
            congr 1; ext i l; exact hA_mat i l
          have edet2 := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
            (PExpr.reg rDet * PExpr.reg rDet) stB
          let stC : RS (CramerReg d) :=
            ⟨Function.update stB.regs rTmp (stB.regs rDet * stB.regs rDet), stB.mem, stB.queries⟩
          have hC_pres : ∀ reg, reg ≠ rDet → reg ≠ rConIdx → (∀ l, reg ≠ rConA l) →
              reg ≠ rConB → reg ≠ rIx → reg ≠ rTmp → (∀ i l, reg ≠ rMat i l) →
              (∀ i, reg ≠ rVecB i) → stC.regs reg = st.regs reg := by
            intro reg hd1 hci hca hcb hix htm hm_ne hvb_ne
            simp only [stC, Function.update_of_ne htm, stB, Function.update_of_ne hd1]
            exact hA_pres reg hci hca hcb hix htm hm_ne hvb_ne
          -- Step C: branch on rTmp = A_mat.det * A_mat.det
          obtain ⟨stD, eD, hD_mem, hD_q, hD_K, hD_V, hD_M, hD_tup, hD_found⟩ :
              ∃ stD, Stmt.Exec oracle rQr
                (.ite rTmp .skip .skip
                  (.seq
                    (Stmt.seqFin d fun l =>
                      .seq
                        (Stmt.assign rNum
                          (PExpr.det fun i l' =>
                            if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')))
                        (.div (rCand l) rNum rDet))
                    (.seq
                      (.seq (Stmt.assign rFeasOk (PExpr.const 1))
                        (Stmt.forNat rCnt1 rM rCond1
                          (.seq (Stmt.assign rConIdx (PExpr.reg rCnt1))
                            (.seq loadCon
                              (.seq
                                (Stmt.assign rTmp
                                  (PExpr.dot (fun l => PExpr.reg (rConA l))
                                    (fun l => PExpr.reg (rCand l)) - PExpr.reg rConB))
                                (.ite rTmp .skip .skip (Stmt.assign rFeasOk (PExpr.const 0))))))))
                      (.seq checkExtra
                        (.seq (Stmt.assign rTmp (PExpr.reg rFeasOk * PExpr.reg rExtraOk))
                          (.ite rTmp .skip .skip
                            (.seq (Stmt.vset rU fun l => PExpr.reg (rCand l))
                              (Stmt.assign rFound (PExpr.const 1))))))))) stC stD ∧
                stD.mem = mem₀ ∧ stD.queries = s.queries ∧
                stD.regs rK = (k : ℝ) ∧ stD.regs rV = (V : ℝ) ∧ stD.regs rM = (M : ℝ) ∧
                (∀ l : Fin d, stD.regs (rTup l) = ((idx l).val : ℝ)) ∧
                ((stD.regs rFound = 1 ∧
                    IsCramerBFS α β (fun l => stD.regs (rU l)) ∧
                    P_extra (fun l => stD.regs (rU l))) ∨
                 (stD.regs rFound = 0 ∧
                    ∀ idx₀ : Fin d → Fin M, encTuple idx₀ < cur + 1 → ¬ ValidTuple idx₀)) := by
            by_cases hdet0 : A_mat.det = 0
            · -- det = 0 -> ite_zero -> skip
              have htmp0 : stC.regs rTmp = 0 := by simp [stC, hB_det, hdet0]
              refine ⟨stC, Stmt.Exec.ite_zero htmp0 (Stmt.Exec.skip stC), hA_mem, hA_q,
                ?_, ?_, ?_, ?_, ?_⟩
              · rw [hC_pres rK (by simp) (by simp) (fun _ => by simp) (by simp)
                  (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_K]
              · rw [hC_pres rV (by simp) (by simp) (fun _ => by simp) (by simp)
                  (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_V]
              · rw [hC_pres rM (by simp) (by simp) (fun _ => by simp) (by simp)
                  (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_M]
              · intro l
                rw [hC_pres (rTup l) (by simp) (by simp) (fun _ => by simp) (by simp)
                  (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_tup l]
              · have hfC : stC.regs rFound = st.regs rFound :=
                  hC_pres rFound (by simp) (by simp) (fun _ => by simp) (by simp)
                    (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp)
                have huC : (fun l => stC.regs (rU l)) = (fun l => st.regs (rU l)) := by
                  funext l
                  exact hC_pres (rU l) (by simp) (by simp) (fun _ => by simp) (by simp)
                    (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp)
                rcases hfound_state with ⟨hf1, hbfs, hex⟩ | ⟨hf0, hnone⟩
                · left; rw [hfC, huC]; exact ⟨hf1, hbfs, hex⟩
                · right
                  refine ⟨hfC.trans hf0, fun idx₀ hlt => ?_⟩
                  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hlt) with hlt' | heq'
                  · exact hnone idx₀ hlt'
                  · have hsame : idx₀ = idx := encTuple_inj hMpos (heq'.trans hidx_enc.symm)
                    subst hsame
                    intro hv
                    exact hv.1 hdet0
            · -- det ≠ 0 -> ite_pos -> solveCand, checkFeas, checkExtra, commit
              have htmp_pos : 0 < stC.regs rTmp := by
                simp only [stC, Function.update_self, hB_det]
                exact mul_self_pos.2 hdet0
              -- 1. solveCand
              obtain ⟨stS, eS, hS_mem, hS_q, hS_cand, hS_pres⟩ :
                  ∃ stS, Stmt.Exec oracle rQr
                    (Stmt.seqFin d fun l =>
                      .seq
                        (Stmt.assign rNum
                          (PExpr.det fun i l' =>
                            if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')))
                        (.div (rCand l) rNum rDet)) stC stS ∧
                    stS.mem = mem₀ ∧ stS.queries = s.queries ∧
                    (∀ l : Fin d, stS.regs (rCand l) = solOf idx l) ∧
                    (∀ reg, reg ≠ rNum → (∀ l, reg ≠ rCand l) → stS.regs reg = stC.regs reg) := by
                obtain ⟨stS, eS, h1, h2, h3, h4⟩ :=
                  Stmt.Exec.seqFin_inv (oracle := oracle) (qr := rQr)
                    (fun l =>
                      .seq
                        (Stmt.assign rNum
                          (PExpr.det fun i l' =>
                            if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')))
                        (.div (rCand l) rNum rDet))
                    (fun r st1 =>
                      st1.mem = mem₀ ∧ st1.queries = s.queries ∧
                      (∀ l : Fin d, l.val < r → st1.regs (rCand l) = solOf idx l) ∧
                      (∀ reg, reg ≠ rNum → (∀ l, reg ≠ rCand l) → st1.regs reg = stC.regs reg))
                    (by
                      intro l st1 ⟨hm1, hq1, hcand1, hpr1⟩
                      have en := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rNum
                        (PExpr.det fun i l' =>
                          if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')) st1
                      let st2 : RS (CramerReg d) :=
                        ⟨Function.update st1.regs rNum
                          ((PExpr.det fun i l' =>
                            if l' = l then PExpr.reg (rVecB i) else PExpr.reg (rMat i l')).eval st1.regs),
                         st1.mem, st1.queries⟩
                      have hdet2 : st2.regs rDet = A_mat.det := by
                        simp only [st2, Function.update_of_ne (by simp : rDet ≠ rNum)]
                        rw [hpr1 rDet (by simp) (fun _ => by simp)]
                        simp [stC, hB_det]
                      have hnum2 : st2.regs rNum =
                          (A_mat.updateCol l (fun i => β (idx i))).det := by
                        simp only [st2, Function.update_self, PExpr.eval_det]
                        congr 1; ext i l'
                        by_cases hll : l' = l
                        · subst hll
                          simp only [Matrix.of_apply, ite_true, PExpr.eval_reg, Matrix.updateCol_self]
                          rw [hpr1 (rVecB i) (by simp) (fun _ => by simp)]
                          simp [stC, stB, hA_b i]
                        · simp only [Matrix.of_apply, if_neg hll, PExpr.eval_reg, Matrix.updateCol_ne hll]
                          rw [hpr1 (rMat i l') (by simp) (fun _ => by simp)]
                          simp [stC, stB, A_mat, hA_mat i l']
                      have ediv := Stmt.Exec.div (oracle := oracle) (qr := rQr) (rCand l) rNum rDet
                        st2 (by rw [hdet2]; exact hdet0)
                      let st3 : RS (CramerReg d) :=
                        ⟨Function.update st2.regs (rCand l) (st2.regs rNum / st2.regs rDet),
                         st2.mem, st2.queries⟩
                      refine ⟨st3, Stmt.Exec.seq en ediv, hm1, hq1, ?_, ?_⟩
                      · intro l' hl'
                        by_cases hll : l' = l
                        · subst hll
                          simp [st3, hnum2, hdet2, solOf, A_mat]
                        · have hlt' : l'.val < l.val := by
                            have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                            omega
                          have hnec : rCand l' ≠ rCand l := fun e => by simp at e; exact hll e
                          simp only [st3, Function.update_of_ne hnec, st2,
                            Function.update_of_ne (by simp : rCand l' ≠ rNum)]
                          exact hcand1 l' hlt'
                      · intro reg hnu hca
                        simp only [st3, Function.update_of_ne (hca l), st2,
                          Function.update_of_ne hnu]
                        exact hpr1 reg hnu hca)
                    stC ⟨hA_mem, hA_q, fun _ h => by omega, fun _ _ _ => rfl⟩
                exact ⟨stS, eS, h1, h2, fun l => h3 l l.isLt, h4⟩
              -- 2. checkFeas
              have ef_init := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rFeasOk
                (PExpr.const 1) stS 1 (by simp)
              let stF0 : RS (CramerReg d) :=
                ⟨Function.update stS.regs rFeasOk 1, stS.mem, stS.queries⟩
              have hF0_M : stF0.regs rM = (M : ℝ) := by
                simp only [stF0, Function.update_of_ne (by simp : rM ≠ rFeasOk)]
                rw [hS_pres rM (by simp) (fun _ => by simp),
                  hC_pres rM (by simp) (by simp) (fun _ => by simp) (by simp)
                    (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_M]
              obtain ⟨stF, eF_loop, _, _, _, hF_inv⟩ :=
                Stmt.Exec.forNat (oracle := oracle) (qr := rQr)
                  (cntReg := rCnt1) (boundReg := rM) (condReg := rCond1)
                  (body := .seq (Stmt.assign rConIdx (PExpr.reg rCnt1))
                    (.seq loadCon
                      (.seq
                        (Stmt.assign rTmp
                          (PExpr.dot (fun l => PExpr.reg (rConA l)) (fun l => PExpr.reg (rCand l)) -
                            PExpr.reg rConB))
                        (.ite rTmp .skip .skip (Stmt.assign rFeasOk (PExpr.const 0))))))
                  (by simp) (by simp) (by simp)
                  (fun c st1 =>
                    st1.mem = mem₀ ∧ st1.queries = s.queries ∧
                    (∀ l : Fin d, st1.regs (rCand l) = solOf idx l) ∧
                    ((st1.regs rFeasOk = 1 ∧ ∀ r : Fin M, r.val < c → dot (α r) (solOf idx) ≤ β r) ∨
                     (st1.regs rFeasOk = 0 ∧ ¬ ∀ r : Fin M, r.val < c → dot (α r) (solOf idx) ≤ β r)) ∧
                    (∀ reg, reg ≠ rFeasOk → reg ≠ rCnt1 → reg ≠ rCond1 → reg ≠ rConIdx →
                      (∀ l, reg ≠ rConA l) → reg ≠ rConB → reg ≠ rIx → reg ≠ rTmp →
                      st1.regs reg = stS.regs reg))
                  (by
                    intro c st1 v₁ v₂ ⟨hm1, hq1, hca1, hfe1, hpr1⟩
                    refine ⟨hm1, hq1, ?_, ?_, ?_⟩
                    · intro l
                      simp only [Function.update_of_ne (by simp : rCand l ≠ rCond1),
                        Function.update_of_ne (by simp : rCand l ≠ rCnt1)]
                      exact hca1 l
                    · simp only [Function.update_of_ne (by simp : rFeasOk ≠ rCond1),
                        Function.update_of_ne (by simp : rFeasOk ≠ rCnt1)]
                      exact hfe1
                    · intro reg h1 h2 h3 h4 h5 h6 h7 h8
                      simp only [Function.update_of_ne h3, Function.update_of_ne h2]
                      exact hpr1 reg h1 h2 h3 h4 h5 h6 h7 h8)
                  (by
                    intro c hc st1 hcnt1 hbnd1 _ ⟨hm1, hq1, hca1, hfe1, hpr1⟩
                    have eci := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rConIdx
                      (PExpr.reg rCnt1) st1
                    let st2 : RS (CramerReg d) :=
                      ⟨Function.update st1.regs rConIdx (st1.regs rCnt1), st1.mem, st1.queries⟩
                    have hK2 : st2.regs rK = (k : ℝ) := by
                      simp only [st2, Function.update_of_ne (by simp : rK ≠ rConIdx)]
                      rw [hpr1 rK (by simp) (by simp) (by simp) (by simp)
                        (fun _ => by simp) (by simp) (by simp) (by simp),
                        hS_pres rK (by simp) (fun _ => by simp),
                        hC_pres rK (by simp) (by simp) (fun _ => by simp) (by simp)
                          (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_K]
                    have hV2 : st2.regs rV = (V : ℝ) := by
                      simp only [st2, Function.update_of_ne (by simp : rV ≠ rConIdx)]
                      rw [hpr1 rV (by simp) (by simp) (by simp) (by simp)
                        (fun _ => by simp) (by simp) (by simp) (by simp),
                        hS_pres rV (by simp) (fun _ => by simp),
                        hC_pres rV (by simp) (by simp) (fun _ => by simp) (by simp)
                          (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_V]
                    obtain ⟨st3, elc, hm3, hq3, hconA3, hconB3, hpr3⟩ :=
                      hload ⟨c, hc⟩ st2 hm1 hK2 hV2 (by simp [st2, hcnt1])
                    have hcand3 : ∀ l : Fin d, st3.regs (rCand l) = solOf idx l := by
                      intro l
                      rw [hpr3 (rCand l) (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp [st2, hca1 l]
                    have etm := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
                      (PExpr.dot (fun l => PExpr.reg (rConA l)) (fun l => PExpr.reg (rCand l)) -
                        PExpr.reg rConB) st3
                    let st4 : RS (CramerReg d) :=
                      ⟨Function.update st3.regs rTmp
                        ((PExpr.dot (fun l => PExpr.reg (rConA l)) (fun l => PExpr.reg (rCand l)) -
                          PExpr.reg rConB).eval st3.regs),
                       st3.mem, st3.queries⟩
                    have htmp4 : st4.regs rTmp = dot (α ⟨c, hc⟩) (solOf idx) - β ⟨c, hc⟩ := by
                      simp only [st4, Function.update_self, PExpr.eval_sub, PExpr.eval_dot,
                        PExpr.eval_reg, hconB3]
                      congr 1; congr 1
                      · funext l; exact hconA3 l
                      · funext l; exact hcand3 l
                    have hcnt4 : st4.regs rCnt1 = (c : ℝ) := by
                      simp only [st4, Function.update_of_ne (by simp : rCnt1 ≠ rTmp)]
                      rw [hpr3 rCnt1 (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp [st2, hcnt1]
                    have hbnd4 : st4.regs rM = (M : ℝ) := by
                      simp only [st4, Function.update_of_ne (by simp : rM ≠ rTmp)]
                      rw [hpr3 rM (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp [st2, hbnd1]
                    have hfe4 : st4.regs rFeasOk = st1.regs rFeasOk := by
                      simp only [st4, Function.update_of_ne (by simp : rFeasOk ≠ rTmp)]
                      rw [hpr3 rFeasOk (fun _ => by simp) (by simp) (by simp) (by simp)]
                      simp [st2]
                    rcases lt_trichotomy (st4.regs rTmp) 0 with hneg | hzero | hpos
                    · refine ⟨st4,
                        Stmt.Exec.seq eci (Stmt.Exec.seq elc (Stmt.Exec.seq etm
                          (Stmt.Exec.ite_neg hneg (Stmt.Exec.skip st4)))),
                        hcnt4, hbnd4, hm3.trans hm1, hq3.trans hq1, ?_, ?_, ?_⟩
                      · intro l
                        simp [st4, hcand3 l]
                      · rw [hfe4]
                        rcases hfe1 with ⟨hf1, hall⟩ | ⟨hf0, hnot⟩
                        · left
                          refine ⟨hf1, fun r hr => ?_⟩
                          by_cases hrc : r.val < c
                          · exact hall r hrc
                          · have hre : r = ⟨c, hc⟩ := Fin.ext (by dsimp; omega)
                            rw [hre]; linarith [htmp4]
                        · right
                          exact ⟨hf0, fun hall => hnot fun r hr => hall r (by omega)⟩
                      · intro reg h1 h2 h3 h4 h5 h6 h7 h8
                        simp only [st4, Function.update_of_ne h8]
                        rw [hpr3 reg h5 h6 h7 h8]
                        simp only [st2, Function.update_of_ne h4]
                        exact hpr1 reg h1 h2 h3 h4 h5 h6 h7 h8
                    · refine ⟨st4,
                        Stmt.Exec.seq eci (Stmt.Exec.seq elc (Stmt.Exec.seq etm
                          (Stmt.Exec.ite_zero hzero (Stmt.Exec.skip st4)))),
                        hcnt4, hbnd4, hm3.trans hm1, hq3.trans hq1, ?_, ?_, ?_⟩
                      · intro l
                        simp [st4, hcand3 l]
                      · rw [hfe4]
                        rcases hfe1 with ⟨hf1, hall⟩ | ⟨hf0, hnot⟩
                        · left
                          refine ⟨hf1, fun r hr => ?_⟩
                          by_cases hrc : r.val < c
                          · exact hall r hrc
                          · have hre : r = ⟨c, hc⟩ := Fin.ext (by dsimp; omega)
                            rw [hre]; linarith [htmp4]
                        · right
                          exact ⟨hf0, fun hall => hnot fun r hr => hall r (by omega)⟩
                      · intro reg h1 h2 h3 h4 h5 h6 h7 h8
                        simp only [st4, Function.update_of_ne h8]
                        rw [hpr3 reg h5 h6 h7 h8]
                        simp only [st2, Function.update_of_ne h4]
                        exact hpr1 reg h1 h2 h3 h4 h5 h6 h7 h8
                    · have ebad := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rFeasOk
                        (PExpr.const 0) st4 0 (by simp)
                      let st5 : RS (CramerReg d) :=
                        ⟨Function.update st4.regs rFeasOk 0, st4.mem, st4.queries⟩
                      refine ⟨st5,
                        Stmt.Exec.seq eci (Stmt.Exec.seq elc (Stmt.Exec.seq etm
                          (Stmt.Exec.ite_pos hpos ebad))),
                        by simp [st5, hcnt4],
                        by simp [st5, hbnd4],
                        hm3.trans hm1, hq3.trans hq1, ?_, ?_, ?_⟩
                      · intro l
                        simp [st5, st4, hcand3 l]
                      · right
                        refine ⟨by simp [st5], fun hall => ?_⟩
                        have := hall ⟨c, hc⟩ (by dsimp; omega)
                        linarith [htmp4]
                      · intro reg h1 h2 h3 h4 h5 h6 h7 h8
                        simp only [st5, Function.update_of_ne h1, st4, Function.update_of_ne h8]
                        rw [hpr3 reg h5 h6 h7 h8]
                        simp only [st2, Function.update_of_ne h4]
                        exact hpr1 reg h1 h2 h3 h4 h5 h6 h7 h8)
                  stF0 hF0_M
                  ⟨hS_mem, hS_q,
                    fun l => by
                      simp [stF0, hS_cand l],
                    Or.inl ⟨by simp [stF0], fun _ h => by omega⟩,
                    fun reg h1 _ _ _ _ _ _ _ => by simp [stF0, Function.update_of_ne h1]⟩
              obtain ⟨hF_mem, hF_q, hF_cand, hF_feas, hF_pres⟩ := hF_inv
              -- 3. checkExtra
              have hF_K : stF.regs rK = (k : ℝ) := by
                rw [hF_pres rK (by simp) (by simp) (by simp) (by simp)
                  (fun _ => by simp) (by simp) (by simp) (by simp),
                  hS_pres rK (by simp) (fun _ => by simp),
                  hC_pres rK (by simp) (by simp) (fun _ => by simp) (by simp)
                    (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_K]
              have hF_V : stF.regs rV = (V : ℝ) := by
                rw [hF_pres rV (by simp) (by simp) (by simp) (by simp)
                  (fun _ => by simp) (by simp) (by simp) (by simp),
                  hS_pres rV (by simp) (fun _ => by simp),
                  hC_pres rV (by simp) (by simp) (fun _ => by simp) (by simp)
                    (by simp) (by simp) (fun _ _ => by simp) (fun _ => by simp), hst_V]
              obtain ⟨stE, eE, hE_mem, hE_q, hE_ext, hE_pres⟩ :=
                hextra stF hF_mem hF_K hF_V
              have hcand_eq : (fun l => stF.regs (rCand l)) = solOf idx := funext hF_cand
              rw [hcand_eq] at hE_ext
              -- 4. Commit if rFeasOk * rExtraOk > 0
              have emul := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
                (PExpr.reg rFeasOk * PExpr.reg rExtraOk) stE
              let stM : RS (CramerReg d) :=
                ⟨Function.update stE.regs rTmp (stE.regs rFeasOk * stE.regs rExtraOk),
                 stE.mem, stE.queries⟩
              have hE_feas_reg : stE.regs rFeasOk = stF.regs rFeasOk :=
                hE_pres rFeasOk (by simp) (by simp) (by simp) (by simp) (by simp)
                  (fun _ => by simp)
              have hM_pres_st : ∀ reg, reg ≠ rFeasOk → reg ≠ rCnt1 → reg ≠ rCond1 →
                  reg ≠ rConIdx → (∀ l, reg ≠ rConA l) → reg ≠ rConB →
                  reg ≠ rExtraOk → reg ≠ rCnt2 → reg ≠ rCond2 → reg ≠ rIx → reg ≠ rTmp →
                  reg ≠ rNum → (∀ l, reg ≠ rCand l) → (∀ l, reg ≠ rVecTmp l) →
                  reg ≠ rDet → (∀ i l, reg ≠ rMat i l) → (∀ i, reg ≠ rVecB i) →
                  stM.regs reg = st.regs reg := by
                intro reg h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
                simp only [stM, Function.update_of_ne h11]
                rw [hE_pres reg h7 h8 h9 h10 h11 h14,
                  hF_pres reg h1 h2 h3 h4 h5 h6 h10 h11,
                  hS_pres reg h12 h13,
                  hC_pres reg h15 h4 h5 h6 h10 h11 h16 h17]
              -- Case split on (hF_feas, hE_ext)
              rcases hF_feas with ⟨hfe1, hfeas_all⟩ | ⟨hfe0, hfeas_not⟩
              · rcases hE_ext with ⟨hex1, hex_ok⟩ | ⟨hex0, hex_not⟩
                · -- Both 1: commit!
                  have htmp1 : 0 < stM.regs rTmp := by
                    simp [stM, hE_feas_reg, hfe1, hex1]
                  have evU := Stmt.Exec.vset (oracle := oracle) (qr := rQr) (rU_injective d)
                    (fun l => PExpr.reg (rCand l)) stM
                  let stU : RS (CramerReg d) :=
                    ⟨Function.extend rU (fun l => stM.regs (rCand l)) stM.regs,
                     stM.mem, stM.queries⟩
                  have ef1 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rFound
                    (PExpr.const 1) stU 1 (by simp)
                  let stD : RS (CramerReg d) :=
                    ⟨Function.update stU.regs rFound 1, stU.mem, stU.queries⟩
                  have hD_u : (fun l => stD.regs (rU l)) = solOf idx := by
                    funext l
                    simp only [stD, Function.update_of_ne (by simp : rU l ≠ rFound), stU]
                    rw [(rU_injective d).extend_apply]
                    simp only [stM, Function.update_of_ne (by simp : rCand l ≠ rTmp)]
                    rw [hE_pres (rCand l) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (fun _ => by simp), hF_cand l]
                  have hbfs_ok : IsCramerBFS α β (solOf idx) :=
                    cramer_sol_is_bfs α β idx hdet0 (fun r => hfeas_all r r.isLt)
                  refine ⟨stD,
                    Stmt.Exec.ite_pos htmp_pos
                      (Stmt.Exec.seq eS (Stmt.Exec.seq (Stmt.Exec.seq ef_init eF_loop)
                        (Stmt.Exec.seq eE (Stmt.Exec.seq emul
                          (Stmt.Exec.ite_pos htmp1 (Stmt.Exec.seq evU ef1)))))),
                    hE_mem.trans hF_mem, hE_q.trans hF_q, ?_, ?_, ?_, ?_,
                    Or.inl ⟨by simp [stD], hD_u ▸ hbfs_ok, hD_u ▸ hex_ok⟩⟩
                  · simp only [stD, Function.update_of_ne (by simp : rK ≠ rFound), stU]
                    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
                    exact (hM_pres_st rK (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_K
                  · simp only [stD, Function.update_of_ne (by simp : rV ≠ rFound), stU]
                    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
                    exact (hM_pres_st rV (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_V
                  · simp only [stD, Function.update_of_ne (by simp : rM ≠ rFound), stU]
                    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
                    exact (hM_pres_st rM (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_M
                  · intro l
                    simp only [stD, Function.update_of_ne (by simp : rTup l ≠ rFound), stU]
                    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
                    exact (hM_pres_st (rTup l) (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans (hst_tup l)
                · -- feas = 1, extra = 0: rTmp = 0 -> skip
                  have htmp0 : stM.regs rTmp = 0 := by simp [stM, hE_feas_reg, hfe1, hex0]
                  refine ⟨stM,
                    Stmt.Exec.ite_pos htmp_pos
                      (Stmt.Exec.seq eS (Stmt.Exec.seq (Stmt.Exec.seq ef_init eF_loop)
                        (Stmt.Exec.seq eE (Stmt.Exec.seq emul
                          (Stmt.Exec.ite_zero htmp0 (Stmt.Exec.skip stM)))))),
                    hE_mem.trans hF_mem, hE_q.trans hF_q, ?_, ?_, ?_, ?_, ?_⟩
                  · exact (hM_pres_st rK (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_K
                  · exact (hM_pres_st rV (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_V
                  · exact (hM_pres_st rM (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_M
                  · intro l
                    exact (hM_pres_st (rTup l) (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans (hst_tup l)
                  · have hfM : stM.regs rFound = st.regs rFound :=
                      hM_pres_st rFound (by simp) (by simp) (by simp) (by simp)
                        (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                        (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                        (by simp) (fun _ _ => by simp) (fun _ => by simp)
                    have huM : (fun l => stM.regs (rU l)) = (fun l => st.regs (rU l)) := by
                      funext l
                      exact hM_pres_st (rU l) (by simp) (by simp) (by simp) (by simp)
                        (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                        (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                        (by simp) (fun _ _ => by simp) (fun _ => by simp)
                    rcases hfound_state with ⟨hf1, hbfs, hex⟩ | ⟨hf0, hnone⟩
                    · left; rw [hfM, huM]; exact ⟨hf1, hbfs, hex⟩
                    · right
                      refine ⟨hfM.trans hf0, fun idx₀ hlt => ?_⟩
                      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hlt) with hlt' | heq'
                      · exact hnone idx₀ hlt'
                      · have hsame : idx₀ = idx := encTuple_inj hMpos (heq'.trans hidx_enc.symm)
                        subst hsame
                        exact fun hv => hex_not hv.2.2
              · -- feas = 0: rTmp = 0 -> skip
                have htmp0 : stM.regs rTmp = 0 := by simp [stM, hE_feas_reg, hfe0]
                refine ⟨stM,
                  Stmt.Exec.ite_pos htmp_pos
                    (Stmt.Exec.seq eS (Stmt.Exec.seq (Stmt.Exec.seq ef_init eF_loop)
                      (Stmt.Exec.seq eE (Stmt.Exec.seq emul
                        (Stmt.Exec.ite_zero htmp0 (Stmt.Exec.skip stM)))))),
                  hE_mem.trans hF_mem, hE_q.trans hF_q, ?_, ?_, ?_, ?_, ?_⟩
                · exact (hM_pres_st rK (by simp) (by simp) (by simp) (by simp)
                    (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                    (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                    (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_K
                · exact (hM_pres_st rV (by simp) (by simp) (by simp) (by simp)
                    (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                    (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                    (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_V
                · exact (hM_pres_st rM (by simp) (by simp) (by simp) (by simp)
                    (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                    (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                    (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans hst_M
                · intro l
                  exact (hM_pres_st (rTup l) (by simp) (by simp) (by simp) (by simp)
                    (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                    (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                    (by simp) (fun _ _ => by simp) (fun _ => by simp)).trans (hst_tup l)
                · have hfM : stM.regs rFound = st.regs rFound :=
                    hM_pres_st rFound (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)
                  have huM : (fun l => stM.regs (rU l)) = (fun l => st.regs (rU l)) := by
                    funext l
                    exact hM_pres_st (rU l) (by simp) (by simp) (by simp) (by simp)
                      (fun _ => by simp) (by simp) (by simp) (by simp) (by simp)
                      (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
                      (by simp) (fun _ _ => by simp) (fun _ => by simp)
                  rcases hfound_state with ⟨hf1, hbfs, hex⟩ | ⟨hf0, hnone⟩
                  · left; rw [hfM, huM]; exact ⟨hf1, hbfs, hex⟩
                  · right
                    refine ⟨hfM.trans hf0, fun idx₀ hlt => ?_⟩
                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hlt) with hlt' | heq'
                    · exact hnone idx₀ hlt'
                    · have hsame : idx₀ = idx := encTuple_inj hMpos (heq'.trans hidx_enc.symm)
                      subst hsame
                      exact fun hv => hfeas_not fun r _ => hv.2.1 r
          -- Step D: stepTuple
          obtain ⟨stN, eN, hN_mem, hN_q, hN_pres, hN_next⟩ :=
            stepTuple_spec (oracle := oracle) hMpos idx stD hD_M hD_tup
          have hN_K : stN.regs rK = (k : ℝ) :=
            (hN_pres rK (by simp) (by simp) (by simp) (fun _ => by simp)).trans hD_K
          have hN_V : stN.regs rV = (V : ℝ) :=
            (hN_pres rV (by simp) (by simp) (by simp) (fun _ => by simp)).trans hD_V
          have hN_M : stN.regs rM = (M : ℝ) :=
            (hN_pres rM (by simp) (by simp) (by simp) (fun _ => by simp)).trans hD_M
          have hN_found_reg : stN.regs rFound = stD.regs rFound :=
            hN_pres rFound (by simp) (by simp) (by simp) (fun _ => by simp)
          have hN_u : (fun l => stN.regs (rU l)) = (fun l => stD.regs (rU l)) := by
            funext l
            exact hN_pres (rU l) (by simp) (by simp) (by simp) (fun _ => by simp)
          refine ⟨stN,
            Stmt.Exec.seq eA (Stmt.Exec.seq edet (Stmt.Exec.seq edet2 (Stmt.Exec.seq eD eN))),
            ⟨hN_mem.trans hD_mem, hN_q.trans hD_q, hN_K, hN_V, hN_M, cur + 1, by omega, ?_, ?_⟩,
            ?_⟩
          · rw [hidx_enc] at hN_next
            exact hN_next
          · rw [hN_found_reg, hN_u]
            exact hD_found
          · rw [hμ_st]
            rw [hidx_enc] at hN_next
            rcases hN_next with ⟨hlt1, hact1, idx', hidx'_enc, htup'⟩ | ⟨_, hact0⟩
            · have hex' : stN.regs rTupAct = 1 ∧
                  ∃ idx'' : Fin d → Fin M, ∀ l, stN.regs (rTup l) = ((idx'' l).val : ℝ) :=
                ⟨hact1, idx', htup'⟩
              simp only [μ, dif_pos hex']
              have hch' := Classical.choose_spec hex'.2
              have heq' : Classical.choose hex'.2 = idx' := by
                funext l
                have hl := (hch' l).symm.trans (htup' l)
                exact Fin.ext (Nat.cast_injective hl)
              rw [heq', hidx'_enc]
              omega
            · have hnot : ¬ (stN.regs rTupAct = 1 ∧
                  ∃ idx'' : Fin d → Fin M, ∀ l, stN.regs (rTup l) = ((idx'' l).val : ℝ)) := by
                rintro ⟨h1, _⟩; linarith
              simp only [μ, dif_neg hnot]
              omega)
        s₂ hInv2
    -- Extract postcondition at loop exit (rTupAct = 0 -> cur = M ^ d)
    obtain ⟨hend_mem, hend_q, hend_K, hend_V, _, cur_f, _, hcur_f, hfound_f⟩ := hEndInv
    have hcur_eq : cur_f = M ^ d := by
      rcases hcur_f with ⟨_, h1, _⟩ | ⟨he, _⟩
      · linarith [hEndZero]
      · exact he
    subst hcur_eq
    refine ⟨s_end,
      Stmt.Exec.seq ef0
        (Stmt.Exec.ite_pos hpM (Stmt.Exec.seq (Stmt.Exec.seq ev0 ea0) ewhile)),
      hend_mem.trans hmem.symm, hend_q, hend_K, hend_V, ?_⟩
    rcases hfound_f with ⟨hf1, hbfs, hex⟩ | ⟨hf0, hnone⟩
    · exact Or.inl ⟨hf1, hbfs, hex⟩
    · refine Or.inr ⟨hf0, fun u ⟨hfeas, idx₀, hdet, hact⟩ hpu => ?_⟩
      apply hnone idx₀ (encTuple_lt hMpos idx₀)
      -- Show u = solOf idx₀ by uniqueness of nonsingular linear system solution
      let A₀ := Matrix.of fun i l => α (idx₀ i) l
      have hu_sol : A₀ *ᵥ u = fun i => β (idx₀ i) := by
        funext i
        simpa [Matrix.mulVec, dotProduct, dot, A₀] using hact i
      have hc_sol : A₀ *ᵥ solOf idx₀ = fun i => β (idx₀ i) := by
        funext i
        simpa [Matrix.mulVec, dotProduct, dot, A₀, solOf] using
          cramer_sol_eq A₀ (fun i => β (idx₀ i)) hdet i
      have hinj : Function.Injective A₀.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A₀).2 hdet.isUnit)
      have hueq : u = solOf idx₀ := hinj (hu_sol.trans hc_sol.symm)
      subst hueq
      exact ⟨hdet, hfeas, hpu⟩

/-! ### Instantiation 1: `recSearch` (recession cone in `[-1, 1]^d`) -/

def recLoadCon (d : ℕ) : Stmt (CramerReg d) :=
  .seq (Stmt.assign rTmp (PExpr.reg rConIdx - PExpr.reg rK + PExpr.const (1 / 2)))
    (.ite rTmp
      -- r < k: load known facet j = rConIdx from (2*j)*d + l, rhs = 0
      (.seq
        (Stmt.loadFam rConA rIx fun l =>
          (PExpr.const 2 * PExpr.reg rConIdx) * PExpr.nat d + PExpr.nat l.val)
        (Stmt.assign rConB (PExpr.const 0)))
      .skip
      -- r ≥ k: check r < k + d vs r ≥ k + d
      (.seq
        (Stmt.assign rTmp (PExpr.reg rConIdx - (PExpr.reg rK + PExpr.nat d) + PExpr.const (1 / 2)))
        (.ite rTmp
          -- k ≤ r < k + d: +e_{r - k} ≤ 1
          (.seq
            (Stmt.seqFin d fun l =>
              .seq (Stmt.assign rTmp ((PExpr.reg rConIdx - PExpr.reg rK) - PExpr.nat l.val))
                (.ite rTmp
                  (Stmt.assign (rConA l) (PExpr.const 0))
                  (Stmt.assign (rConA l) (PExpr.const 1))
                  (Stmt.assign (rConA l) (PExpr.const 0))))
            (Stmt.assign rConB (PExpr.const 1)))
          .skip
          -- k + d ≤ r < k + 2*d: -e_{r - (k + d)} ≤ 1
          (.seq
            (Stmt.seqFin d fun l =>
              .seq
                (Stmt.assign rTmp
                  ((PExpr.reg rConIdx - (PExpr.reg rK + PExpr.nat d)) - PExpr.nat l.val))
                (.ite rTmp
                  (Stmt.assign (rConA l) (PExpr.const 0))
                  (Stmt.assign (rConA l) (PExpr.const (-1)))
                  (Stmt.assign (rConA l) (PExpr.const 0))))
            (Stmt.assign rConB (PExpr.const 1))))))

def recCheckExtra (d : ℕ) : Stmt (CramerReg d) :=
  .seq
    (Stmt.assign rTmp
      (PExpr.dot (fun l => PExpr.reg (rCand l)) (fun l => PExpr.reg (rCand l))))
    (.ite rTmp
      (Stmt.assign rExtraOk (PExpr.const 0))
      (Stmt.assign rExtraOk (PExpr.const 0))
      (Stmt.assign rExtraOk (PExpr.const 1)))

noncomputable def recSearch (d : ℕ) : Stmt (CramerReg d) :=
  .seq (Stmt.assign rM (PExpr.reg rK + PExpr.nat (2 * d)))
    (cramerSearch d (recLoadCon d) (recCheckExtra d))

theorem setBasisVec_spec {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (off : PExpr (CramerReg d)) (sgn : ℚ) (idxVal : ℕ) (_hidx : idxVal < d)
    (s : RS (CramerReg d))
    (hoff : ∀ regs' : CramerReg d → ℝ,
      (∀ reg, (∀ l, reg ≠ rConA l) → reg ≠ rTmp → regs' reg = s.regs reg) →
      off.eval regs' = (idxVal : ℝ)) :
    ∃ s', Stmt.Exec oracle rQr
      (Stmt.seqFin d fun l =>
        .seq (Stmt.assign rTmp (off - PExpr.nat l.val))
          (.ite rTmp
            (Stmt.assign (rConA l) (PExpr.const 0))
            (Stmt.assign (rConA l) (PExpr.const sgn))
            (Stmt.assign (rConA l) (PExpr.const 0)))) s s' ∧
      s'.mem = s.mem ∧ s'.queries = s.queries ∧
      (∀ l : Fin d, s'.regs (rConA l) = if l.val = idxVal then (sgn : ℝ) else 0) ∧
      (∀ reg, (∀ l, reg ≠ rConA l) → reg ≠ rTmp → s'.regs reg = s.regs reg) := by
  obtain ⟨s', es', h1, h2, h3, h4⟩ :=
    Stmt.Exec.seqFin_inv (oracle := oracle) (qr := rQr)
      (fun l =>
        .seq (Stmt.assign rTmp (off - PExpr.nat l.val))
          (.ite rTmp
            (Stmt.assign (rConA l) (PExpr.const 0))
            (Stmt.assign (rConA l) (PExpr.const sgn))
            (Stmt.assign (rConA l) (PExpr.const 0))))
      (fun r st =>
        st.mem = s.mem ∧ st.queries = s.queries ∧
        (∀ l : Fin d, l.val < r → st.regs (rConA l) = if l.val = idxVal then (sgn : ℝ) else 0) ∧
        (∀ reg, (∀ l, reg ≠ rConA l) → reg ≠ rTmp → st.regs reg = s.regs reg))
      (by
        intro l st ⟨hm, hq, hlo, hpr⟩
        have hev : off.eval st.regs = (idxVal : ℝ) := hoff st.regs hpr
        have et := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rTmp (off - PExpr.nat l.val) st
          (off.eval st.regs - (l.val : ℝ)) (by simp)
        let st1 : RS (CramerReg d) :=
          ⟨Function.update st.regs rTmp (off.eval st.regs - (l.val : ℝ)), st.mem, st.queries⟩
        have htmp1 : st1.regs rTmp = (idxVal : ℝ) - (l.val : ℝ) := by simp [st1, hev]
        rcases lt_trichotomy idxVal l.val with hlt | heq | hgt
        · have hneg : st1.regs rTmp < 0 := by
            rw [htmp1]
            have : (idxVal : ℝ) < (l.val : ℝ) := by exact_mod_cast hlt
            linarith
          have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) (rConA l) (PExpr.const 0) st1 0 (by simp)
          let st2 : RS (CramerReg d) := ⟨Function.update st1.regs (rConA l) 0, st1.mem, st1.queries⟩
          refine ⟨st2, Stmt.Exec.seq et (Stmt.Exec.ite_neg hneg ea), hm, hq, ?_, ?_⟩
          · intro l' hl'
            by_cases hll : l' = l
            · subst hll
              have hne_i : l'.val ≠ idxVal := by omega
              simp [st2, hne_i]
            · have hlt' : l'.val < l.val := by
                have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                omega
              have hnec : rConA l' ≠ rConA l := fun e => hll (rConA_injective d e)
              simp only [st2, Function.update_of_ne hnec, st1,
                Function.update_of_ne (by simp : rConA l' ≠ rTmp)]
              exact hlo l' hlt'
          · intro reg hca htm
            simp only [st2, Function.update_of_ne (hca l), st1, Function.update_of_ne htm]
            exact hpr reg hca htm
        · have hzero : st1.regs rTmp = 0 := by rw [htmp1, heq, sub_self]
          have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) (rConA l) (PExpr.const sgn) st1 (sgn : ℝ) (by simp)
          let st2 : RS (CramerReg d) :=
            ⟨Function.update st1.regs (rConA l) (sgn : ℝ), st1.mem, st1.queries⟩
          refine ⟨st2, Stmt.Exec.seq et (Stmt.Exec.ite_zero hzero ea), hm, hq, ?_, ?_⟩
          · intro l' hl'
            by_cases hll : l' = l
            · subst hll; simp [st2, heq]
            · have hlt' : l'.val < l.val := by
                have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                omega
              have hnec : rConA l' ≠ rConA l := fun e => hll (rConA_injective d e)
              simp only [st2, Function.update_of_ne hnec, st1,
                Function.update_of_ne (by simp : rConA l' ≠ rTmp)]
              exact hlo l' hlt'
          · intro reg hca htm
            simp only [st2, Function.update_of_ne (hca l), st1, Function.update_of_ne htm]
            exact hpr reg hca htm
        · have hpos : 0 < st1.regs rTmp := by
            rw [htmp1]
            have : (l.val : ℝ) < (idxVal : ℝ) := by exact_mod_cast hgt
            linarith
          have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) (rConA l) (PExpr.const 0) st1 0 (by simp)
          let st2 : RS (CramerReg d) := ⟨Function.update st1.regs (rConA l) 0, st1.mem, st1.queries⟩
          refine ⟨st2, Stmt.Exec.seq et (Stmt.Exec.ite_pos hpos ea), hm, hq, ?_, ?_⟩
          · intro l' hl'
            by_cases hll : l' = l
            · subst hll
              have hne_i : l'.val ≠ idxVal := by omega
              simp [st2, hne_i]
            · have hlt' : l'.val < l.val := by
                have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
                omega
              have hnec : rConA l' ≠ rConA l := fun e => hll (rConA_injective d e)
              simp only [st2, Function.update_of_ne hnec, st1,
                Function.update_of_ne (by simp : rConA l' ≠ rTmp)]
              exact hlo l' hlt'
          · intro reg hca htm
            simp only [st2, Function.update_of_ne (hca l), st1, Function.update_of_ne htm]
            exact hpr reg hca htm)
      s ⟨rfl, rfl, fun _ h => by omega, fun _ _ _ => rfl⟩
  exact ⟨s', es', h1, h2, fun l => h3 l l.isLt, h4⟩

theorem recSearch_spec {d k V : ℕ} (hd : 0 < d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (s : RS (CramerReg d))
    (hmem : s.mem = mem₀) (hK : s.regs rK = (k : ℝ)) (hV : s.regs rV = (V : ℝ)) :
    ∃ s', Stmt.Exec oracle rQr (recSearch d) s s' ∧
      s'.mem = s.mem ∧ s'.queries = s.queries ∧
      s'.regs rK = (k : ℝ) ∧ s'.regs rV = (V : ℝ) ∧
      ((s'.regs rFound = 1 ∧
          IsCramerBFS (recAlpha a) (recBeta k d) (fun l => s'.regs (rU l)) ∧
          (fun l => s'.regs (rU l)) ≠ 0) ∨
       (s'.regs rFound = 0 ∧
          ∀ u, IsCramerBFS (recAlpha a) (recBeta k d) u → u = 0)) := by
  have em := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rM
    (PExpr.reg rK + PExpr.nat (2 * d)) s
  let s₁ : RS (CramerReg d) :=
    ⟨Function.update s.regs rM ((k : ℝ) + ((2 * d : ℕ) : ℝ)), s.mem, s.queries⟩
  have em' : Stmt.Exec oracle rQr (Stmt.assign rM (PExpr.reg rK + PExpr.nat (2 * d))) s s₁ := by
    simpa [s₁, hK] using em
  have hM1 : s₁.regs rM = ((k + 2 * d : ℕ) : ℝ) := by simp [s₁]
  have hK1 : s₁.regs rK = (k : ℝ) := by simp [s₁, hK]
  have hV1 : s₁.regs rV = (V : ℝ) := by simp [s₁, hV]
  obtain ⟨s', es', hm', hq', hK', hV', hres⟩ :=
    cramerSearch_spec (d := d) (k := k) (V := V) (M := k + 2 * d) hd (oracle := oracle)
      mem₀ (recAlpha a) (recBeta k d) (fun u => u ≠ 0)
      (recLoadCon d) (recCheckExtra d)
      (by
        intro r st hstm hstk _ hstci
        have et1 := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
          (PExpr.reg rConIdx - PExpr.reg rK + PExpr.const (1 / 2)) st
        let st1 : RS (CramerReg d) :=
          ⟨Function.update st.regs rTmp ((r.val : ℝ) - (k : ℝ) + 1 / 2), st.mem, st.queries⟩
        have et1' : Stmt.Exec oracle rQr
            (Stmt.assign rTmp (PExpr.reg rConIdx - PExpr.reg rK + PExpr.const (1 / 2))) st st1 := by
          simpa [st1, hstci, hstk] using et1
        by_cases hrk : r.val < k
        · -- r < k: ite_neg
          have hneg1 : st1.regs rTmp < 0 := by
            simp only [st1, Function.update_self]
            have : ((r.val + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
            push_cast at this; linarith
          obtain ⟨st2, eload, hca2, hpr2, hm2, hq2⟩ :=
            Stmt.Exec.loadFam (oracle := oracle) (qr := rQr) (ix := rIx) (rConA_injective d)
              (fun _ => by simp)
              (fun l => (PExpr.const 2 * PExpr.reg rConIdx) * PExpr.nat d + PExpr.nat l.val)
              st1 (fun l => (2 * r.val) * d + l.val)
              (by
                intro l regs' hreg
                have hci : regs' rConIdx = (r.val : ℝ) := by
                  rw [hreg rConIdx (by simp) (fun _ => by simp)]
                  simp [st1, hstci]
                simp [hci])
          have eb2 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rConB (PExpr.const 0) st2 0 (by simp)
          let st3 : RS (CramerReg d) := ⟨Function.update st2.regs rConB 0, st2.mem, st2.queries⟩
          refine ⟨st3, Stmt.Exec.seq et1' (Stmt.Exec.ite_neg hneg1 (Stmt.Exec.seq eload eb2)),
            hm2, hq2, ?_, ?_, ?_⟩
          · intro l
            simp only [st3, Function.update_of_ne (by simp : rConA l ≠ rConB), hca2 l]
            change st.mem _ = _
            rw [hstm, ha_mem ⟨r.val, hrk⟩ l]
            simp [recAlpha, hrk]
          · simp [st3, recBeta, hrk]
          · intro reg hca hcb hix htm
            simp only [st3, Function.update_of_ne hcb]
            rw [hpr2 reg hix hca]
            simp [st1, Function.update_of_ne htm]
        · -- r ≥ k: ite_pos
          have hpos1 : 0 < st1.regs rTmp := by
            simp only [st1, Function.update_self]
            have : (k : ℝ) ≤ (r.val : ℝ) := by exact_mod_cast Nat.le_of_not_lt hrk
            linarith
          have et2 := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
            (PExpr.reg rConIdx - (PExpr.reg rK + PExpr.nat d) + PExpr.const (1 / 2)) st1
          let st2 : RS (CramerReg d) :=
            ⟨Function.update st1.regs rTmp ((r.val : ℝ) - ((k : ℝ) + (d : ℝ)) + 1 / 2),
             st1.mem, st1.queries⟩
          have et2' : Stmt.Exec oracle rQr
              (Stmt.assign rTmp
                (PExpr.reg rConIdx - (PExpr.reg rK + PExpr.nat d) + PExpr.const (1 / 2)))
              st1 st2 := by
            have hci1 : st1.regs rConIdx = (r.val : ℝ) := by simp [st1, hstci]
            have hk1' : st1.regs rK = (k : ℝ) := by simp [st1, hstk]
            simpa [st2, hci1, hk1'] using et2
          by_cases hrkd : r.val < k + d
          · -- k ≤ r < k + d: +e_{r - k}
            have hneg2 : st2.regs rTmp < 0 := by
              simp only [st2, Function.update_self]
              have : ((r.val + 1 : ℕ) : ℝ) ≤ ((k + d : ℕ) : ℝ) := by exact_mod_cast hrkd
              push_cast at this; linarith
            obtain ⟨st3, ebas, hm3, hq3, hca3, hpr3⟩ :=
              setBasisVec_spec (oracle := oracle)
                (PExpr.reg rConIdx - PExpr.reg rK) 1 (r.val - k) (by omega) st2
                (by
                  intro regs' hreg
                  have hci : regs' rConIdx = (r.val : ℝ) := by
                    rw [hreg rConIdx (fun _ => by simp) (by simp)]
                    simp [st2, st1, hstci]
                  have hk' : regs' rK = (k : ℝ) := by
                    rw [hreg rK (fun _ => by simp) (by simp)]
                    simp [st2, st1, hstk]
                  have hle : k ≤ r.val := by omega
                  simp [hci, hk', Nat.cast_sub hle])
            have eb3 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rConB (PExpr.const 1) st3 1 (by simp)
            let st4 : RS (CramerReg d) := ⟨Function.update st3.regs rConB 1, st3.mem, st3.queries⟩
            refine ⟨st4,
              Stmt.Exec.seq et1' (Stmt.Exec.ite_pos hpos1
                (Stmt.Exec.seq et2' (Stmt.Exec.ite_neg hneg2 (Stmt.Exec.seq ebas eb3)))),
              hm3, hq3, ?_, ?_, ?_⟩
            · intro l
              simp only [st4, Function.update_of_ne (by simp : rConA l ≠ rConB), hca3 l]
              simp only [recAlpha, dif_neg hrk, dif_pos hrkd, Pi.single_apply]
              by_cases hl : l = ⟨r.val - k, by omega⟩
              · subst hl; simp
              · have hlv : l.val ≠ r.val - k := fun e => hl (Fin.ext e)
                simp [hl, hlv]
            · simp [st4, recBeta, hrk]
            · intro reg hca hcb _ htm
              simp only [st4, Function.update_of_ne hcb]
              rw [hpr3 reg hca htm]
              simp [st2, st1, Function.update_of_ne htm]
          · -- k + d ≤ r < k + 2*d: -e_{r - (k + d)}
            have hpos2 : 0 < st2.regs rTmp := by
              simp only [st2, Function.update_self]
              have : ((k + d : ℕ) : ℝ) ≤ (r.val : ℝ) := by exact_mod_cast Nat.le_of_not_lt hrkd
              push_cast at this; linarith
            obtain ⟨st3, ebas, hm3, hq3, hca3, hpr3⟩ :=
              setBasisVec_spec (oracle := oracle)
                (PExpr.reg rConIdx - (PExpr.reg rK + PExpr.nat d)) (-1)
                (r.val - (k + d)) (by omega) st2
                (by
                  intro regs' hreg
                  have hci : regs' rConIdx = (r.val : ℝ) := by
                    rw [hreg rConIdx (fun _ => by simp) (by simp)]
                    simp [st2, st1, hstci]
                  have hk' : regs' rK = (k : ℝ) := by
                    rw [hreg rK (fun _ => by simp) (by simp)]
                    simp [st2, st1, hstk]
                  have hle : k + d ≤ r.val := by omega
                  simp [hci, hk', Nat.cast_sub hle, Nat.cast_add])
            have eb3 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rConB (PExpr.const 1) st3 1 (by simp)
            let st4 : RS (CramerReg d) := ⟨Function.update st3.regs rConB 1, st3.mem, st3.queries⟩
            refine ⟨st4,
              Stmt.Exec.seq et1' (Stmt.Exec.ite_pos hpos1
                (Stmt.Exec.seq et2' (Stmt.Exec.ite_pos hpos2 (Stmt.Exec.seq ebas eb3)))),
              hm3, hq3, ?_, ?_, ?_⟩
            · intro l
              simp only [st4, Function.update_of_ne (by simp : rConA l ≠ rConB), hca3 l]
              simp only [recAlpha, dif_neg hrk, dif_neg hrkd, Pi.neg_apply, Pi.single_apply]
              by_cases hl : l = ⟨r.val - (k + d), by omega⟩
              · subst hl; simp
              · have hlv : l.val ≠ r.val - (k + d) := fun e => hl (Fin.ext e)
                simp [hl, hlv]
            · simp [st4, recBeta, hrk]
            · intro reg hca hcb _ htm
              simp only [st4, Function.update_of_ne hcb]
              rw [hpr3 reg hca htm]
              simp [st2, st1, Function.update_of_ne htm])
      (by
        intro st _ _ _
        have et := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
          (PExpr.dot (fun l => PExpr.reg (rCand l)) (fun l => PExpr.reg (rCand l))) st
        let u := fun l => st.regs (rCand l)
        let st1 : RS (CramerReg d) := ⟨Function.update st.regs rTmp (dot u u), st.mem, st.queries⟩
        have et' : Stmt.Exec oracle rQr
            (Stmt.assign rTmp
              (PExpr.dot (fun l => PExpr.reg (rCand l)) (fun l => PExpr.reg (rCand l))))
            st st1 := by
          simpa [st1, u] using et
        by_cases hu0 : u = 0
        · have hz : st1.regs rTmp = 0 := by simp [st1, hu0]
          have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rExtraOk (PExpr.const 0) st1 0 (by simp)
          let st2 : RS (CramerReg d) := ⟨Function.update st1.regs rExtraOk 0, st1.mem, st1.queries⟩
          refine ⟨st2, Stmt.Exec.seq et' (Stmt.Exec.ite_zero hz ea), rfl, rfl,
            Or.inr ⟨by simp [st2], not_not.2 hu0⟩, ?_⟩
          intro reg hex _ _ _ htm _
          simp [st2, st1, Function.update_of_ne hex, Function.update_of_ne htm]
        · have hp : 0 < st1.regs rTmp := by simp [st1]; exact dot_self_pos hu0
          have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rExtraOk (PExpr.const 1) st1 1 (by simp)
          let st2 : RS (CramerReg d) := ⟨Function.update st1.regs rExtraOk 1, st1.mem, st1.queries⟩
          refine ⟨st2, Stmt.Exec.seq et' (Stmt.Exec.ite_pos hp ea), rfl, rfl,
            Or.inl ⟨by simp [st2], hu0⟩, ?_⟩
          intro reg hex _ _ _ htm _
          simp [st2, st1, Function.update_of_ne hex, Function.update_of_ne htm])
      s₁ hmem hK1 hV1 hM1
  refine ⟨s', Stmt.Exec.seq em' es', hm', hq', hK', hV', ?_⟩
  rcases hres with h1 | ⟨hf0, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf0, fun u hu => not_not.1 (h2 u hu)⟩

/-! ### Instantiation 2: `outerSearch` (outer polytope `a_j · x ≤ 1`, avoiding `C[0..V-1]`) -/

def outerLoadCon (d : ℕ) : Stmt (CramerReg d) :=
  .seq
    (Stmt.loadFam rConA rIx fun l =>
      (PExpr.const 2 * PExpr.reg rConIdx) * PExpr.nat d + PExpr.nat l.val)
    (Stmt.assign rConB (PExpr.const 1))

def outerCheckExtra (d : ℕ) : Stmt (CramerReg d) :=
  .seq (Stmt.assign rExtraOk (PExpr.const 1))
    (Stmt.forNat rCnt2 rV rCond2
      (.seq
        (Stmt.loadFam rVecTmp rIx fun l =>
          (PExpr.const 2 * PExpr.reg rCnt2 + PExpr.const 1) * PExpr.nat d + PExpr.nat l.val)
        (.seq
          (Stmt.assign rTmp
            (PExpr.dot (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))
              (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))))
          (.ite rTmp .skip (Stmt.assign rExtraOk (PExpr.const 0)) .skip))))

noncomputable def outerSearch (d : ℕ) : Stmt (CramerReg d) :=
  .seq (Stmt.assign rM (PExpr.reg rK))
    (cramerSearch d (outerLoadCon d) (outerCheckExtra d))

theorem outerSearch_spec {d k V : ℕ} (hd : 0 < d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (hv_mem : ∀ (c : Fin V) (l : Fin d), mem₀ ((2 * c.val + 1) * d + l.val) = vVec c l)
    (s : RS (CramerReg d))
    (hmem : s.mem = mem₀) (hK : s.regs rK = (k : ℝ)) (hV : s.regs rV = (V : ℝ)) :
    ∃ s', Stmt.Exec oracle rQr (outerSearch d) s s' ∧
      s'.mem = s.mem ∧ s'.queries = s.queries ∧
      s'.regs rK = (k : ℝ) ∧ s'.regs rV = (V : ℝ) ∧
      ((s'.regs rFound = 1 ∧
          IsCramerBFS a (fun _ => 1) (fun l => s'.regs (rU l)) ∧
          ∀ c : Fin V, (fun l => s'.regs (rU l)) ≠ vVec c) ∨
       (s'.regs rFound = 0 ∧
          ∀ u, IsCramerBFS a (fun _ => 1) u → ∃ c : Fin V, u = vVec c)) := by
  have em := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rM (PExpr.reg rK) s
  let s₁ : RS (CramerReg d) := ⟨Function.update s.regs rM (k : ℝ), s.mem, s.queries⟩
  have em' : Stmt.Exec oracle rQr (Stmt.assign rM (PExpr.reg rK)) s s₁ := by
    simpa [s₁, hK] using em
  have hM1 : s₁.regs rM = (k : ℝ) := by simp [s₁]
  have hK1 : s₁.regs rK = (k : ℝ) := by simp [s₁, hK]
  have hV1 : s₁.regs rV = (V : ℝ) := by simp [s₁, hV]
  obtain ⟨s', es', hm', hq', hK', hV', hres⟩ :=
    cramerSearch_spec (d := d) (k := k) (V := V) (M := k) hd (oracle := oracle)
      mem₀ a (fun _ => 1) (fun u => ∀ c : Fin V, u ≠ vVec c)
      (outerLoadCon d) (outerCheckExtra d)
      (by
        intro r st hstm _ _ hstci
        obtain ⟨st1, eload, hca1, hpr1, hm1, hq1⟩ :=
          Stmt.Exec.loadFam (oracle := oracle) (qr := rQr) (ix := rIx) (rConA_injective d)
            (fun _ => by simp)
            (fun l => (PExpr.const 2 * PExpr.reg rConIdx) * PExpr.nat d + PExpr.nat l.val)
            st (fun l => (2 * r.val) * d + l.val)
            (by
              intro l regs' hreg
              have hci : regs' rConIdx = (r.val : ℝ) :=
                (hreg rConIdx (by simp) (fun _ => by simp)).trans hstci
              simp [hci])
        have eb1 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rConB (PExpr.const 1) st1 1 (by simp)
        let st2 : RS (CramerReg d) := ⟨Function.update st1.regs rConB 1, st1.mem, st1.queries⟩
        refine ⟨st2, Stmt.Exec.seq eload eb1, hm1, hq1, ?_, by simp [st2], ?_⟩
        · intro l
          simp only [st2, Function.update_of_ne (by simp : rConA l ≠ rConB), hca1 l]
          rw [hstm, ha_mem r l]
        · intro reg hca hcb hix _
          simp only [st2, Function.update_of_ne hcb]
          exact hpr1 reg hix hca)
      (by
        intro st hstm _ hstv
        let u := fun l => st.regs (rCand l)
        have e0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rExtraOk (PExpr.const 1) st 1 (by simp)
        let st0 : RS (CramerReg d) := ⟨Function.update st.regs rExtraOk 1, st.mem, st.queries⟩
        have hV0 : st0.regs rV = (V : ℝ) := by simp [st0, hstv]
        obtain ⟨stF, eF, _, _, _, hF_inv⟩ :=
          Stmt.Exec.forNat (oracle := oracle) (qr := rQr)
            (cntReg := rCnt2) (boundReg := rV) (condReg := rCond2)
            (body := .seq
              (Stmt.loadFam rVecTmp rIx fun l =>
                (PExpr.const 2 * PExpr.reg rCnt2 + PExpr.const 1) * PExpr.nat d + PExpr.nat l.val)
              (.seq
                (Stmt.assign rTmp
                  (PExpr.dot (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))
                    (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))))
                (.ite rTmp .skip (Stmt.assign rExtraOk (PExpr.const 0)) .skip)))
            (by simp) (by simp) (by simp)
            (fun c st1 =>
              st1.mem = mem₀ ∧ st1.queries = st.queries ∧
              (∀ l : Fin d, st1.regs (rCand l) = u l) ∧
              ((st1.regs rExtraOk = 1 ∧ ∀ j : Fin V, j.val < c → u ≠ vVec j) ∨
               (st1.regs rExtraOk = 0 ∧ ¬ ∀ j : Fin V, j.val < c → u ≠ vVec j)) ∧
              (∀ reg, reg ≠ rExtraOk → reg ≠ rCnt2 → reg ≠ rCond2 → reg ≠ rIx → reg ≠ rTmp →
                (∀ l, reg ≠ rVecTmp l) → st1.regs reg = st.regs reg))
            (by
              intro c st1 v₁ v₂ ⟨hm1, hq1, hca1, hex1, hpr1⟩
              refine ⟨hm1, hq1, ?_, ?_, ?_⟩
              · intro l
                simp only [Function.update_of_ne (by simp : rCand l ≠ rCond2),
                  Function.update_of_ne (by simp : rCand l ≠ rCnt2)]
                exact hca1 l
              · simp only [Function.update_of_ne (by simp : rExtraOk ≠ rCond2),
                  Function.update_of_ne (by simp : rExtraOk ≠ rCnt2)]
                exact hex1
              · intro reg h1 h2 h3 h4 h5 h6
                simp only [Function.update_of_ne h3, Function.update_of_ne h2]
                exact hpr1 reg h1 h2 h3 h4 h5 h6)
            (by
              intro c hc st1 hcnt1 hbnd1 _ ⟨hm1, hq1, hca1, hex1, hpr1⟩
              obtain ⟨st2, eload, hv2, hpr2, hm2, hq2⟩ :=
                Stmt.Exec.loadFam (oracle := oracle) (qr := rQr) (ix := rIx) (rVecTmp_injective d)
                  (fun _ => by simp)
                  (fun l =>
                    (PExpr.const 2 * PExpr.reg rCnt2 + PExpr.const 1) * PExpr.nat d +
                      PExpr.nat l.val)
                  st1 (fun l => (2 * c + 1) * d + l.val)
                  (by
                    intro l regs' hreg
                    have hc' : regs' rCnt2 = (c : ℝ) :=
                      (hreg rCnt2 (by simp) (fun _ => by simp)).trans hcnt1
                    simp [hc'])
              have hcand2 : ∀ l : Fin d, st2.regs (rCand l) = u l := fun l =>
                (hpr2 (rCand l) (by simp) (fun _ => by simp)).trans (hca1 l)
              have hv2' : ∀ l : Fin d, st2.regs (rVecTmp l) = vVec ⟨c, hc⟩ l := fun l => by
                rw [hv2 l, hm1, hv_mem ⟨c, hc⟩ l]
              have etm := Stmt.Exec.assign (oracle := oracle) (qr := rQr) rTmp
                (PExpr.dot (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))
                  (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))) st2
              let st3 : RS (CramerReg d) :=
                ⟨Function.update st2.regs rTmp (dot (u - vVec ⟨c, hc⟩) (u - vVec ⟨c, hc⟩)),
                 st2.mem, st2.queries⟩
              have etm' : Stmt.Exec oracle rQr
                  (Stmt.assign rTmp
                    (PExpr.dot (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))
                      (fun l => PExpr.reg (rCand l) - PExpr.reg (rVecTmp l))))
                  st2 st3 := by
                have heq_sub : (fun l => st2.regs (rCand l) - st2.regs (rVecTmp l)) =
                    u - vVec ⟨c, hc⟩ := by
                  funext l; simp [hcand2 l, hv2' l]
                simpa [st3, heq_sub] using etm
              have hcnt3 : st3.regs rCnt2 = (c : ℝ) := by
                simp only [st3, Function.update_of_ne (by simp : rCnt2 ≠ rTmp)]
                exact (hpr2 rCnt2 (by simp) (fun _ => by simp)).trans hcnt1
              have hbnd3 : st3.regs rV = (V : ℝ) := by
                simp only [st3, Function.update_of_ne (by simp : rV ≠ rTmp)]
                exact (hpr2 rV (by simp) (fun _ => by simp)).trans hbnd1
              by_cases hueq : u = vVec ⟨c, hc⟩
              · have hzero : st3.regs rTmp = 0 := by simp [st3, hueq]
                have ebad := Stmt.Exec.assign_eval (oracle := oracle) (qr := rQr) rExtraOk
                  (PExpr.const 0) st3 0 (by simp)
                let st4 : RS (CramerReg d) :=
                  ⟨Function.update st3.regs rExtraOk 0, st3.mem, st3.queries⟩
                refine ⟨st4,
                  Stmt.Exec.seq eload (Stmt.Exec.seq etm' (Stmt.Exec.ite_zero hzero ebad)),
                  by simp [st4, hcnt3],
                  by simp [st4, hbnd3],
                  hm2.trans hm1, hq2.trans hq1, ?_, ?_, ?_⟩
                · intro l
                  simp [st4, st3, hcand2 l]
                · right
                  exact ⟨by simp [st4], fun hall => hall ⟨c, hc⟩ (by dsimp; omega) hueq⟩
                · intro reg h1 h2 h3 h4 h5 h6
                  simp only [st4, Function.update_of_ne h1, st3, Function.update_of_ne h5]
                  rw [hpr2 reg h4 h6]
                  exact hpr1 reg h1 h2 h3 h4 h5 h6
              · have hpos : 0 < st3.regs rTmp := by
                  simp only [st3, Function.update_self]
                  exact dot_self_pos (sub_ne_zero.2 hueq)
                refine ⟨st3,
                  Stmt.Exec.seq eload (Stmt.Exec.seq etm'
                    (Stmt.Exec.ite_pos hpos (Stmt.Exec.skip st3))),
                  hcnt3, hbnd3, hm2.trans hm1, hq2.trans hq1, ?_, ?_, ?_⟩
                · intro l
                  simp [st3, hcand2 l]
                · have hex3 : st3.regs rExtraOk = st1.regs rExtraOk := by
                    simp only [st3, Function.update_of_ne (by simp : rExtraOk ≠ rTmp)]
                    exact hpr2 rExtraOk (by simp) (fun _ => by simp)
                  rw [hex3]
                  rcases hex1 with ⟨he1, hall⟩ | ⟨he0, hnot⟩
                  · left
                    refine ⟨he1, fun j hj => ?_⟩
                    by_cases hjc : j.val < c
                    · exact hall j hjc
                    · have hje : j = ⟨c, hc⟩ := Fin.ext (by dsimp; omega)
                      rwa [hje]
                  · right
                    exact ⟨he0, fun hall => hnot fun j hj => hall j (by omega)⟩
                · intro reg h1 h2 h3 h4 h5 h6
                  simp only [st3, Function.update_of_ne h5]
                  rw [hpr2 reg h4 h6]
                  exact hpr1 reg h1 h2 h3 h4 h5 h6)
            st0 hV0
            ⟨hstm, rfl,
              fun l => by simp [st0, u],
              Or.inl ⟨by simp [st0], fun _ h => by omega⟩,
              fun reg h1 _ _ _ _ _ => by simp [st0, Function.update_of_ne h1]⟩
        obtain ⟨hFm, hFq, _, hFext, hFpr⟩ := hF_inv
        refine ⟨stF, Stmt.Exec.seq e0 eF, hFm.trans hstm.symm, hFq, ?_, hFpr⟩
        rcases hFext with ⟨he1, hall⟩ | ⟨he0, hnot⟩
        · exact Or.inl ⟨he1, fun j => hall j j.isLt⟩
        · exact Or.inr ⟨he0, fun hall => hnot fun j _ => hall j⟩)
      s₁ hmem hK1 hV1 hM1
  refine ⟨s', Stmt.Exec.seq em' es', hm', hq', hK', hV', ?_⟩
  rcases hres with h1 | ⟨hf0, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hf0, fun u hu => ?_⟩
    by_contra! hall
    exact h2 u hu hall

end Bfs

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Facet -/

namespace Grunbaum2003
namespace RayAlg

open scoped BigOperators Matrix Classical

/-! ## Facet-finding subroutine (`facetFind`) via `(d - 1)` secant stages -/

namespace Facet

abbrev FacetReg (d : ℕ) := Fin 21 ⊕ (Fin 7 × Fin d) ⊕ (Fin d × Fin d)

abbrev fK       {d : ℕ} : FacetReg d := Sum.inl 0
abbrev fSkip    {d : ℕ} : FacetReg d := Sum.inl 1
abbrev fTmp     {d : ℕ} : FacetReg d := Sum.inl 2
abbrev fIx      {d : ℕ} : FacetReg d := Sum.inl 3
abbrev fNum     {d : ℕ} : FacetReg d := Sum.inl 4
abbrev fDen     {d : ℕ} : FacetReg d := Sum.inl 5
abbrev fFm      {d : ℕ} : FacetReg d := Sum.inl 6
abbrev fSig     {d : ℕ} : FacetReg d := Sum.inl 7
abbrev fAcc     {d : ℕ} : FacetReg d := Sum.inl 8
abbrev fTerm    {d : ℕ} : FacetReg d := Sum.inl 9
abbrev fCnt     {d : ℕ} : FacetReg d := Sum.inl 10
abbrev fCond    {d : ℕ} : FacetReg d := Sum.inl 11
abbrev fXa      {d : ℕ} : FacetReg d := Sum.inl 12
abbrev fFa      {d : ℕ} : FacetReg d := Sum.inl 13
abbrev fXb      {d : ℕ} : FacetReg d := Sum.inl 14
abbrev fFb      {d : ℕ} : FacetReg d := Sum.inl 15
abbrev fMu      {d : ℕ} : FacetReg d := Sum.inl 16
abbrev fXn      {d : ℕ} : FacetReg d := Sum.inl 17
abbrev fFn      {d : ℕ} : FacetReg d := Sum.inl 18
abbrev fSecCond {d : ℕ} : FacetReg d := Sum.inl 19
abbrev fDet     {d : ℕ} : FacetReg d := Sum.inl 20

abbrev fQr  {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (0, l))
abbrev fP   {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (1, l))
abbrev fOut {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (2, l))
abbrev fC   {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (3, l))
abbrev fV   {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (4, l))
abbrev fQb  {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (5, l))
abbrev fAj  {d : ℕ} (l : Fin d) : FacetReg d := Sum.inr (Sum.inl (6, l))

abbrev fMat {d : ℕ} (i l : Fin d) : FacetReg d := Sum.inr (Sum.inr (i, l))

theorem fQr_injective (d : ℕ) : Function.Injective (fQr (d := d)) := by
  intro i j h; simpa using h

theorem fC_injective (d : ℕ) : Function.Injective (fC (d := d)) := by
  intro i j h; simpa using h

theorem fV_injective (d : ℕ) : Function.Injective (fV (d := d)) := by
  intro i j h; simpa using h

theorem fQb_injective (d : ℕ) : Function.Injective (fQb (d := d)) := by
  intro i j h; simpa using h

theorem fAj_injective (d : ℕ) : Function.Injective (fAj (d := d)) := by
  intro i j h; simpa using h

theorem fOut_injective (d : ℕ) : Function.Injective (fOut (d := d)) := by
  intro i j h; simpa using h

theorem fMat_row_injective (d : ℕ) (i : Fin d) : Function.Injective (fMat i) := by
  intro l₁ l₂ h; simpa using h

/-- Sample the oracle along ray `c + sExpr • M wRow`, storing the gauge value in `fDst`
and (if `saveQb = true`) the frontier point in `fQb`. -/
def sampleRay (d : ℕ) (sExpr : PExpr (FacetReg d)) (wRow : Fin d)
    (fDst : FacetReg d) (saveQb : Bool) : Stmt (FacetReg d) :=
  .seq (Stmt.vset fV fun l => PExpr.reg (fC l) + sExpr * PExpr.reg (fMat wRow l))
    (.seq (Stmt.vset fQr fun l => PExpr.reg (fV l))
      (.seq .query
        (.seq (if saveQb then Stmt.vset fQb fun l => PExpr.reg (fQr l) else .skip)
          (.seq
            (.par [(fNum, PExpr.dot (fun l => PExpr.reg (fV l)) (fun l => PExpr.reg (fV l))),
                   (fDen, PExpr.dot (fun l => PExpr.reg (fQr l)) (fun l => PExpr.reg (fV l)))])
            (.div fDst fNum fDen)))))

theorem sampleRay_spec {d m : ℕ} {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (sExpr : PExpr (FacetReg d)) (wRow : Fin d) (fDst : FacetReg d) (saveQb : Bool)
    (_hdst_num : fDst ≠ fNum) (_hdst_den : fDst ≠ fDen)
    (hdst_qb : ∀ l, fDst ≠ fQb l)
    (st : RS (FacetReg d)) (sVal : ℝ) (hsExpr : sExpr.eval st.regs = sVal)
    (hv : (fun l => st.regs (fC l)) + sVal • (fun l => st.regs (fMat wRow l)) ≠ 0) :
    let c := fun l => st.regs (fC l)
    let w := fun l => st.regs (fMat wRow l)
    let v := c + sVal • w
    let y := oracle v
    let fVal := dot v v / dot y v
    ∃ st', Stmt.Exec oracle fQr (sampleRay d sExpr wRow fDst saveQb) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries + 1 ∧
      st'.regs fDst = fVal ∧
      Samp (fun i => L i c) (fun i => L i w) sVal fVal ∧
      (∀ i, L i y = 1 ↔ L i c + L i w * sVal = fVal) ∧
      (saveQb = true → ∀ l, st'.regs (fQb l) = y l) ∧
      (saveQb = false → ∀ l, st'.regs (fQb l) = st.regs (fQb l)) ∧
      (∀ reg, reg ≠ fDst → reg ≠ fNum → reg ≠ fDen →
        (∀ l, reg ≠ fV l) → (∀ l, reg ≠ fQr l) → (∀ l, reg ≠ fQb l) →
        st'.regs reg = st.regs reg) := by
  intro c w v y fVal
  have ev := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fV_injective d)
    (fun l => PExpr.reg (fC l) + sExpr * PExpr.reg (fMat wRow l)) st
  let st1 : RS (FacetReg d) :=
    ⟨Function.extend fV
      (fun l => (PExpr.reg (fC l) + sExpr * PExpr.reg (fMat wRow l)).eval st.regs) st.regs,
     st.mem, st.queries⟩
  have hv1 : ∀ l, st1.regs (fV l) = v l := by
    intro l
    simp only [st1]
    rw [(fV_injective d).extend_apply]
    simp [hsExpr, v, c, w]
  have eqr := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fQr_injective d)
    (fun l => PExpr.reg (fV l)) st1
  let st2 : RS (FacetReg d) :=
    ⟨Function.extend fQr (fun l => st1.regs (fV l)) st1.regs, st1.mem, st1.queries⟩
  have hqr2 : (fun l => st2.regs (fQr l)) = v := by
    funext l
    simp only [st2]
    rw [(fQr_injective d).extend_apply, hv1 l]
  have equery := Stmt.Exec.query (oracle := oracle) (qr := fQr) st2 (by rw [hqr2]; exact hv)
  let st3 : RS (FacetReg d) :=
    ⟨Function.extend fQr (oracle (fun l => st2.regs (fQr l))) st2.regs, st2.mem, st2.queries + 1⟩
  have hqr3 : ∀ l, st3.regs (fQr l) = y l := by
    intro l
    simp only [st3]
    rw [(fQr_injective d).extend_apply, hqr2]
  have hv3 : ∀ l, st3.regs (fV l) = v l := by
    intro l
    simp only [st3]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
    simp only [st2]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hv1 l]
  obtain ⟨st4, esave, hm4, hq4, hqr4, hv4, hqb4_t, hqb4_f, hpr4⟩ :
      ∃ st4, Stmt.Exec oracle fQr
        (if saveQb then Stmt.vset fQb fun l => PExpr.reg (fQr l) else .skip) st3 st4 ∧
        st4.mem = st.mem ∧ st4.queries = st.queries + 1 ∧
        (∀ l, st4.regs (fQr l) = y l) ∧ (∀ l, st4.regs (fV l) = v l) ∧
        (saveQb = true → ∀ l, st4.regs (fQb l) = y l) ∧
        (saveQb = false → ∀ l, st4.regs (fQb l) = st.regs (fQb l)) ∧
        (∀ reg, (∀ l, reg ≠ fV l) → (∀ l, reg ≠ fQr l) → (∀ l, reg ≠ fQb l) →
          st4.regs reg = st.regs reg) := by
    cases saveQb with
    | false =>
      refine ⟨st3, Stmt.Exec.skip st3, rfl, rfl, hqr3, hv3, fun h => Bool.noConfusion h, ?_, ?_⟩
      · intro _ l
        simp only [st3, st2, st1]
        rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
          Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
          Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
      · intro reg h1 h2 _
        simp only [st3, st2, st1]
        rw [Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h2 l he.symm),
          Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h2 l he.symm),
          Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h1 l he.symm)]
    | true =>
      have esv := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fQb_injective d)
        (fun l => PExpr.reg (fQr l)) st3
      let st4 : RS (FacetReg d) :=
        ⟨Function.extend fQb (fun l => st3.regs (fQr l)) st3.regs, st3.mem, st3.queries⟩
      refine ⟨st4, esv, rfl, rfl, ?_, ?_, ?_, fun h => Bool.noConfusion h, ?_⟩
      · intro l
        simp only [st4]
        rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hqr3 l]
      · intro l
        simp only [st4]
        rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hv3 l]
      · intro _ l
        simp only [st4]
        rw [(fQb_injective d).extend_apply, hqr3 l]
      · intro reg h1 h2 h3
        simp only [st4, st3, st2, st1]
        rw [Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h3 l he.symm),
          Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h2 l he.symm),
          Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h2 l he.symm),
          Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; exact h1 l he.symm)]
  have epar := Stmt.Exec.par (oracle := oracle) (qr := fQr)
    [(fNum, PExpr.dot (fun l => PExpr.reg (fV l)) (fun l => PExpr.reg (fV l))),
     (fDen, PExpr.dot (fun l => PExpr.reg (fQr l)) (fun l => PExpr.reg (fV l)))] st4
  let st5 : RS (FacetReg d) :=
    ⟨parUpd st4.regs
      [(fNum, PExpr.dot (fun l => PExpr.reg (fV l)) (fun l => PExpr.reg (fV l))),
       (fDen, PExpr.dot (fun l => PExpr.reg (fQr l)) (fun l => PExpr.reg (fV l)))] st4.regs,
     st4.mem, st4.queries⟩
  have hnum5 : st5.regs fNum = dot v v := by
    simp only [st5, parUpd, PExpr.eval_dot, PExpr.eval_reg]
    rw [Function.update_of_ne (by simp : fNum ≠ fDen), Function.update_self]
    congr 1 <;> funext l <;> exact hv4 l
  have hden5 : st5.regs fDen = dot y v := by
    simp only [st5, parUpd, PExpr.eval_dot, PExpr.eval_reg, Function.update_self]
    congr 1
    · funext l; exact hqr4 l
    · funext l; exact hv4 l
  obtain ⟨hden_ne, hsamp, hiff⟩ := oracle_samp_ray L hP horacle c w sVal hv
  have ediv := Stmt.Exec.div (oracle := oracle) (qr := fQr) fDst fNum fDen st5
    (by rw [hden5]; exact hden_ne)
  let st6 : RS (FacetReg d) :=
    ⟨Function.update st5.regs fDst (st5.regs fNum / st5.regs fDen), st5.mem, st5.queries⟩
  refine ⟨st6,
    Stmt.Exec.seq ev (Stmt.Exec.seq eqr (Stmt.Exec.seq equery
      (Stmt.Exec.seq esave (Stmt.Exec.seq epar ediv)))),
    hm4, hq4, ?_, hsamp, hiff, ?_, ?_, ?_⟩
  · simp [st6, hnum5, hden5, fVal]
  · intro hsb l
    simp only [st6, Function.update_of_ne (hdst_qb l).symm, st5, parUpd,
      Function.update_of_ne (by simp : fQb l ≠ fDen),
      Function.update_of_ne (by simp : fQb l ≠ fNum)]
    exact hqb4_t hsb l
  · intro hsb l
    simp only [st6, Function.update_of_ne (hdst_qb l).symm, st5, parUpd,
      Function.update_of_ne (by simp : fQb l ≠ fDen),
      Function.update_of_ne (by simp : fQb l ≠ fNum)]
    exact hqb4_f hsb l
  · intro reg h1 h2 h3 h4 h5 h6
    simp only [st6, Function.update_of_ne h1, st5, parUpd,
      Function.update_of_ne h3, Function.update_of_ne h2]
    exact hpr4 reg h4 h5 h6

/-- Initialize `fMat` with row 0 = `p` and rows `1 .. d - 1` = standard basis skipping first
nonzero coordinate of `p`, and set `fC := p`. -/
def initBasis (d : ℕ) (hd0 : 0 < d) : Stmt (FacetReg d) :=
  .seq (Stmt.vset (fMat ⟨0, hd0⟩) fun l => PExpr.reg (fP l))
    (.seq (Stmt.vset fC fun l => PExpr.reg (fP l))
      (.seq (Stmt.assign fSkip (PExpr.const 0))
        (Stmt.seqFin (d - 1) fun r =>
          let r0 : Fin d := ⟨r.val, by omega⟩
          let r1 : Fin d := ⟨r.val + 1, by omega⟩
          .ite fSkip .skip
            -- fSkip = 0: check p r0 * p r0
            (.seq (Stmt.assign fTmp (PExpr.reg (fP r0) * PExpr.reg (fP r0)))
              (.ite fTmp .skip
                -- p r0 = 0: row r1 := e_{r0}, fSkip stays 0
                (Stmt.vset (fMat r1) fun l => if l = r0 then PExpr.const 1 else PExpr.const 0)
                -- p r0 ≠ 0: fSkip := 1, row r1 := e_{r1}
                (.seq (Stmt.assign fSkip (PExpr.const 1))
                  (Stmt.vset (fMat r1) fun l => if l = r1 then PExpr.const 1 else PExpr.const 0))))
            -- fSkip > 0: row r1 := e_{r1}
            (Stmt.vset (fMat r1) fun l => if l = r1 then PExpr.const 1 else PExpr.const 0))))

theorem initBasis_spec {d : ℕ} (hd : 2 ≤ d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (st : RS (FacetReg d))
    (hp0 : (fun l => st.regs (fP l)) ≠ 0) :
    let hd0 : 0 < d := by omega
    let p := fun l => st.regs (fP l)
    ∃ (st' : RS (FacetReg d)) (W₀ : Fin d → Fin d → ℝ),
      Stmt.Exec oracle fQr (initBasis d hd0) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      W₀ ⟨0, hd0⟩ = p ∧
      LinearIndependent ℝ W₀ ∧
      (∀ i l : Fin d, st'.regs (fMat i l) = W₀ i l) ∧
      (∀ l : Fin d, st'.regs (fC l) = p l) ∧
      (∀ l : Fin d, st'.regs (fP l) = p l) ∧
      st'.regs fK = st.regs fK := by
  intro hd0 p
  -- Find the minimum index l₀ with p l₀ ≠ 0
  have hex : ∃ n : ℕ, ∃ hn : n < d, p ⟨n, hn⟩ ≠ 0 := by
    by_contra! hall
    apply hp0
    funext l
    exact hall l.val l.isLt
  let n₀ := Nat.find hex
  obtain ⟨hn₀, hpn₀⟩ := Nat.find_spec hex
  have hlt_zero : ∀ m, m < n₀ → ∀ hm : m < d, p ⟨m, hm⟩ = 0 := by
    intro m hm hmd
    by_contra hne
    exact Nat.find_min hex hm ⟨hmd, hne⟩
  let l₀ : Fin d := ⟨n₀, hn₀⟩
  let f : Fin (d - 1) → Fin d := fun r =>
    if r.val < n₀ then ⟨r.val, by omega⟩ else ⟨r.val + 1, by omega⟩
  have hf_inj : Function.Injective f := by
    intro r₁ r₂ h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    split_ifs at hv with h1 h2 <;> simp at hv <;> exact Fin.ext (by omega)
  have hf_ne : ∀ r, f r ≠ l₀ := by
    intro r h
    have hv := congrArg Fin.val h
    dsimp [f, l₀] at hv
    split_ifs at hv <;> simp at hv <;> omega
  let W₀ : Fin d → Fin d → ℝ := fun i =>
    if hi : i.val = 0 then p else Pi.single (f ⟨i.val - 1, by omega⟩) 1
  have hW0 : W₀ ⟨0, hd0⟩ = p := by simp [W₀]
  have hWrest : ∀ r : Fin (d - 1), W₀ ⟨r.val + 1, by omega⟩ = Pi.single (f r) 1 := by
    intro r
    simp [W₀]
  have hli : LinearIndependent ℝ W₀ :=
    initFrame_linearIndependent hd0 hpn₀ W₀ hW0 f hf_inj hf_ne hWrest
  -- Execute row 0, fC, fSkip
  have em0 := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fMat_row_injective d ⟨0, hd0⟩)
    (fun l => PExpr.reg (fP l)) st
  let st1 : RS (FacetReg d) :=
    ⟨Function.extend (fMat ⟨0, hd0⟩) (fun l => st.regs (fP l)) st.regs, st.mem, st.queries⟩
  have ec0 := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fC_injective d)
    (fun l => PExpr.reg (fP l)) st1
  let st2 : RS (FacetReg d) :=
    ⟨Function.extend fC (fun l => st1.regs (fP l)) st1.regs, st1.mem, st1.queries⟩
  have esk0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := fQr) fSkip (PExpr.const 0) st2 0 (by simp)
  let st3 : RS (FacetReg d) := ⟨Function.update st2.regs fSkip 0, st2.mem, st2.queries⟩
  have hp3 : ∀ l, st3.regs (fP l) = p l := by
    intro l
    simp only [st3, Function.update_of_ne (by simp : fP l ≠ fSkip), st2, st1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
  have hc3 : ∀ l, st3.regs (fC l) = p l := by
    intro l
    simp only [st3, Function.update_of_ne (by simp : fC l ≠ fSkip), st2]
    rw [(fC_injective d).extend_apply]
    simp only [st1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
  have hm0_3 : ∀ l, st3.regs (fMat ⟨0, hd0⟩ l) = p l := by
    intro l
    simp only [st3, Function.update_of_ne (by simp : fMat ⟨0, hd0⟩ l ≠ fSkip), st2]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
    simp only [st1]
    rw [(fMat_row_injective d ⟨0, hd0⟩).extend_apply]
  have hk3 : st3.regs fK = st.regs fK := by
    simp only [st3, Function.update_of_ne (by simp : fK ≠ fSkip), st2, st1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
  -- Run seqFin (d - 1)
  obtain ⟨st', eseq, hm', hq', _, hmat', hp', hc', hk'⟩ :=
    Stmt.Exec.seqFin_inv (oracle := oracle) (qr := fQr)
      (fun r : Fin (d - 1) =>
        let r0 : Fin d := ⟨r.val, by omega⟩
        let r1 : Fin d := ⟨r.val + 1, by omega⟩
        Stmt.ite fSkip .skip
          (.seq (Stmt.assign fTmp (PExpr.reg (fP r0) * PExpr.reg (fP r0)))
            (.ite fTmp .skip
              (Stmt.vset (fMat r1) fun l => if l = r0 then PExpr.const 1 else PExpr.const 0)
              (.seq (Stmt.assign fSkip (PExpr.const 1))
                (Stmt.vset (fMat r1) fun l => if l = r1 then PExpr.const 1 else PExpr.const 0))))
          (Stmt.vset (fMat r1) fun l => if l = r1 then PExpr.const 1 else PExpr.const 0))
      (fun c_r st_r =>
        st_r.mem = st.mem ∧ st_r.queries = st.queries ∧
        st_r.regs fSkip = (if c_r ≤ n₀ then 0 else 1) ∧
        (∀ i : Fin d, i.val ≤ c_r → ∀ l : Fin d, st_r.regs (fMat i l) = W₀ i l) ∧
        (∀ l : Fin d, st_r.regs (fP l) = p l) ∧
        (∀ l : Fin d, st_r.regs (fC l) = p l) ∧
        st_r.regs fK = st.regs fK)
      (by
        intro r st_r ⟨hm_r, hq_r, hsk_r, hmat_r, hp_r, hc_r, hk_r⟩
        let r0 : Fin d := ⟨r.val, by omega⟩
        let r1 : Fin d := ⟨r.val + 1, by omega⟩
        by_cases hrn : r.val ≤ n₀
        · have hsk0 : st_r.regs fSkip = 0 := by simp [hsk_r, hrn]
          have et := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fTmp
            (PExpr.reg (fP r0) * PExpr.reg (fP r0)) st_r
          let st_t : RS (FacetReg d) :=
            ⟨Function.update st_r.regs fTmp (p r0 * p r0), st_r.mem, st_r.queries⟩
          have et' : Stmt.Exec oracle fQr
              (Stmt.assign fTmp (PExpr.reg (fP r0) * PExpr.reg (fP r0))) st_r st_t := by
            simpa [st_t, hp_r r0] using et
          rcases Nat.lt_or_eq_of_le hrn with hr_lt | hr_eq
          · -- r.val < n₀: p r0 = 0
            have hpr0 : p r0 = 0 := hlt_zero r.val hr_lt (by omega)
            have htmp0 : st_t.regs fTmp = 0 := by simp [st_t, hpr0]
            have ev := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fMat_row_injective d r1)
              (fun l => if l = r0 then PExpr.const 1 else PExpr.const 0) st_t
            let st_n : RS (FacetReg d) :=
              ⟨Function.extend (fMat r1)
                (fun l => (if l = r0 then (PExpr.const 1 : PExpr (FacetReg d))
                           else PExpr.const 0).eval st_t.regs) st_t.regs,
               st_t.mem, st_t.queries⟩
            refine ⟨st_n,
              Stmt.Exec.ite_zero hsk0 (Stmt.Exec.seq et' (Stmt.Exec.ite_zero htmp0 ev)),
              hm_r, hq_r, ?_, ?_, ?_, ?_, ?_⟩
            · have hle1 : r.val + 1 ≤ n₀ := hr_lt
              simp only [if_pos hle1, st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_t, hsk0]
            · intro i hi l
              by_cases hir : i = r1
              · subst hir
                simp only [st_n]
                rw [(fMat_row_injective d r1).extend_apply, hWrest r]
                simp only [f, if_pos hr_lt, Pi.single_apply]
                by_cases hlr : l = r0 <;> simp [hlr, r0]
              · have hilt : i.val ≤ r.val := by
                  have : i.val ≠ r.val + 1 := fun e => hir (Fin.ext e)
                  omega
                simp only [st_n]
                rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he; exact hir he.1.symm)]
                simp [st_t, hmat_r i hilt l]
            · intro l
              simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_t, hp_r l]
            · intro l
              simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_t, hc_r l]
            · simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_t, hk_r]
          · -- r.val = n₀: p r0 ≠ 0
            have hpr0 : p r0 ≠ 0 := by
              have hr0_eq : r0 = l₀ := Fin.ext hr_eq
              rwa [hr0_eq]
            have htmp_pos : 0 < st_t.regs fTmp := by
              simp only [st_t, Function.update_self]
              exact mul_self_pos.2 hpr0
            have esk1 := Stmt.Exec.assign_eval (oracle := oracle) (qr := fQr) fSkip (PExpr.const 1) st_t 1 (by simp)
            let st_s : RS (FacetReg d) :=
              ⟨Function.update st_t.regs fSkip 1, st_t.mem, st_t.queries⟩
            have ev := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fMat_row_injective d r1)
              (fun l => if l = r1 then PExpr.const 1 else PExpr.const 0) st_s
            let st_n : RS (FacetReg d) :=
              ⟨Function.extend (fMat r1)
                (fun l => (if l = r1 then (PExpr.const 1 : PExpr (FacetReg d))
                           else PExpr.const 0).eval st_s.regs) st_s.regs,
               st_s.mem, st_s.queries⟩
            refine ⟨st_n,
              Stmt.Exec.ite_zero hsk0
                (Stmt.Exec.seq et' (Stmt.Exec.ite_pos htmp_pos (Stmt.Exec.seq esk1 ev))),
              hm_r, hq_r, ?_, ?_, ?_, ?_, ?_⟩
            · have hnle : ¬ (r.val + 1 ≤ n₀) := by omega
              simp only [if_neg hnle, st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_s]
            · intro i hi l
              by_cases hir : i = r1
              · subst hir
                simp only [st_n]
                rw [(fMat_row_injective d r1).extend_apply, hWrest r]
                have hnlt : ¬ (r.val < n₀) := by omega
                simp only [f, if_neg hnlt, Pi.single_apply]
                by_cases hlr : l = r1 <;> simp [hlr, r1]
              · have hilt : i.val ≤ r.val := by
                  have : i.val ≠ r.val + 1 := fun e => hir (Fin.ext e)
                  omega
                simp only [st_n]
                rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he; exact hir he.1.symm)]
                simp [st_s, st_t, hmat_r i hilt l]
            · intro l
              simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_s, st_t, hp_r l]
            · intro l
              simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_s, st_t, hc_r l]
            · simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
              simp [st_s, st_t, hk_r]
        · -- r.val > n₀: fSkip = 1 -> ite_pos
          have hsk_pos : 0 < st_r.regs fSkip := by simp [hsk_r, hrn]
          have ev := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fMat_row_injective d r1)
            (fun l => if l = r1 then PExpr.const 1 else PExpr.const 0) st_r
          let st_n : RS (FacetReg d) :=
            ⟨Function.extend (fMat r1)
              (fun l => (if l = r1 then (PExpr.const 1 : PExpr (FacetReg d))
                         else PExpr.const 0).eval st_r.regs) st_r.regs,
             st_r.mem, st_r.queries⟩
          refine ⟨st_n, Stmt.Exec.ite_pos hsk_pos ev, hm_r, hq_r, ?_, ?_, ?_, ?_, ?_⟩
          · have hnle : ¬ (r.val + 1 ≤ n₀) := by omega
            simp only [if_neg hnle, st_n]
            rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
            simp [hsk_r, hrn]
          · intro i hi l
            by_cases hir : i = r1
            · subst hir
              simp only [st_n]
              rw [(fMat_row_injective d r1).extend_apply, hWrest r]
              have hnlt : ¬ (r.val < n₀) := by omega
              simp only [f, if_neg hnlt, Pi.single_apply]
              by_cases hlr : l = r1 <;> simp [hlr, r1]
            · have hilt : i.val ≤ r.val := by
                have : i.val ≠ r.val + 1 := fun e => hir (Fin.ext e)
                omega
              simp only [st_n]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he; exact hir he.1.symm)]
              exact hmat_r i hilt l
          · intro l
            simp only [st_n]
            rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hp_r l]
          · intro l
            simp only [st_n]
            rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hc_r l]
          · simp only [st_n]
            rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hk_r])
      st3 ⟨rfl, rfl, by simp [st3],
        fun i hi l => by
          have hi0 : i = ⟨0, hd0⟩ := Fin.ext (by dsimp; omega)
          rw [hi0, hm0_3 l, hW0],
        hp3, hc3, hk3⟩
  refine ⟨st', W₀,
    Stmt.Exec.seq em0 (Stmt.Exec.seq ec0 (Stmt.Exec.seq esk0 eseq)),
    hm', hq', hW0, hli, fun i l => hmat' i (by omega) l, hc', hp', hk'⟩

/-- Secant stop condition expression `(fb - (1 + σ * xb)) * ((fa - 1) * xb - (fb - 1) * xa)`. -/
def secCondExpr {d : ℕ} : PExpr (FacetReg d) :=
  (PExpr.reg fFb - (PExpr.const 1 + PExpr.reg fSig * PExpr.reg fXb)) *
    ((PExpr.reg fFa - PExpr.const 1) * PExpr.reg fXb -
      (PExpr.reg fFb - PExpr.const 1) * PExpr.reg fXa)

/-- One stage `r` (`0 ≤ r < d - 1`) of `facetFind`, finding a point on a common facet with `c`
in `span(rows 0..r, w)` and updating row `r + 1` and `c`. -/
def facetStage (d : ℕ) (idx₁ : Fin d) : Stmt (FacetReg d) :=
  let computeAcc : Stmt (FacetReg d) :=
    .seq (Stmt.assign fAcc (PExpr.const 1))
      (Stmt.forNat fCnt fK fCond
        (.seq
          (Stmt.loadFam fAj fIx fun l =>
            (PExpr.const 2 * PExpr.reg fCnt) * PExpr.nat d + PExpr.nat l.val)
          (.seq
            (.par
              [(fNum, PExpr.const 1 +
                  (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                    PExpr.reg fSig) *
                  (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                    PExpr.reg fSig)),
               (fDen, PExpr.const 1 -
                  PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fC l)))])
            (.seq (.div fTerm fNum fDen)
              (Stmt.assign fAcc (PExpr.reg fAcc + PExpr.reg fTerm))))))
  let secBody : Stmt (FacetReg d) :=
    .seq
      (.par [(fNum, PExpr.reg fFa - PExpr.reg fFb),
             (fDen, PExpr.reg fXa - PExpr.reg fXb)])
      (.seq (.div fMu fNum fDen)
        (.seq
          (.par [(fNum, PExpr.const 1 - (PExpr.reg fFb - PExpr.reg fMu * PExpr.reg fXb)),
                 (fDen, PExpr.reg fMu - PExpr.reg fSig)])
          (.seq (.div fXn fNum fDen)
            (.seq (sampleRay d (PExpr.reg fXn) idx₁ fFn true)
              (.seq
                (.par [(fXa, PExpr.reg fXb),
                       (fFa, PExpr.reg fFb),
                       (fXb, PExpr.reg fXn),
                       (fFb, PExpr.reg fFn)])
                (Stmt.assign fSecCond secCondExpr))))))
  .seq (sampleRay d (PExpr.const (-1)) idx₁ fFm false)
    (.seq (Stmt.assign fSig (PExpr.const 1 - PExpr.reg fFm))
      (.seq computeAcc
        (.seq (Stmt.assign fNum (PExpr.const 1))
          (.seq (.div fXa fNum fAcc)
            (.seq (Stmt.assign fXb (PExpr.const (1 / 2) * PExpr.reg fXa))
              (.seq (sampleRay d (PExpr.reg fXa) idx₁ fFa false)
                (.seq (sampleRay d (PExpr.reg fXb) idx₁ fFb true)
                  (.seq (Stmt.assign fSecCond secCondExpr)
                    (.seq (.while fSecCond secBody)
                      (.seq (Stmt.vset (fMat idx₁) fun l => PExpr.reg (fQb l))
                        (Stmt.vset fC fun l =>
                          PExpr.const (1 / 2) * (PExpr.reg (fC l) + PExpr.reg (fQb l)))))))))))))

theorem facetStage_spec {d m k r : ℕ} (hr1 : r + 1 < d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ)
    (emb : Fin k → Fin m) (hemb_inj : Function.Injective emb)
    (ha_emb : ∀ (j : Fin k) (x : Fin d → ℝ), dot (a j) x = L (emb j) x)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    {p : Fin d → ℝ} {W₀ : Fin d → Fin d → ℝ} {M : Fin d → Fin d → ℝ} {c : Fin d → ℝ}
    (hInv : StageInv P L a p W₀ r M c)
    (st : RS (FacetReg d))
    (hmem : st.mem = mem₀) (hK : st.regs fK = (k : ℝ))
    (hMat : ∀ i l : Fin d, st.regs (fMat i l) = M i l)
    (hC : ∀ l : Fin d, st.regs (fC l) = c l)
    (hP_reg : ∀ l : Fin d, st.regs (fP l) = p l) :
    let idx₁ : Fin d := ⟨r + 1, hr1⟩
    ∃ st' M' c',
      Stmt.Exec oracle fQr (facetStage d idx₁) st st' ∧
      st'.mem = mem₀ ∧
      st'.queries ≤ st.queries + (2 * (m - k) + 2) ∧
      st'.regs fK = (k : ℝ) ∧
      (∀ l : Fin d, st'.regs (fP l) = p l) ∧
      (∀ i l : Fin d, st'.regs (fMat i l) = M' i l) ∧
      (∀ l : Fin d, st'.regs (fC l) = c' l) ∧
      StageInv P L a p W₀ (r + 1) M' c' := by
  intro idx₁
  let w := M idx₁
  let A_fn : Fin m → ℝ := fun i => L i c
  let B_fn : Fin m → ℝ := fun i => L i w
  have h0_AB : (∀ i, A_fn i ≤ 1) ∧ ∃ i, A_fn i = 1 :=
    (frontier_iff_max_one L hP c).1 hInv.hc_front
  have hc_eq : (fun l => st.regs (fC l)) = c := funext hC
  have hw_eq : (fun l => st.regs (fMat idx₁ l)) = w := funext (hMat idx₁)
  -- 1. Sample at s = -1
  have hv_m : (fun l => st.regs (fC l)) + (-1 : ℝ) • (fun l => st.regs (fMat idx₁ l)) ≠ 0 := by
    rw [hc_eq, hw_eq]
    exact hInv.ray_ne_zero hr1 (by norm_num)
  obtain ⟨st1, es1, hm1, hq1, hfm1, hmsamp, _, _, _, hpr1⟩ :=
    sampleRay_spec L hP horacle (PExpr.const (-1)) idx₁ fFm false
      (by simp) (by simp) (fun _ => by simp) st (-1) (by simp) hv_m
  rw [hc_eq, hw_eq] at hfm1 hmsamp
  let fm := st1.regs fFm
  have hmsamp' : Samp A_fn B_fn (-1) fm := by rw [← hfm1] at hmsamp; exact hmsamp
  -- 2. Set fSig := 1 - fm
  have esig := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fSig
    (PExpr.const 1 - PExpr.reg fFm) st1
  let σ := 1 - fm
  let st2 : RS (FacetReg d) := ⟨Function.update st1.regs fSig σ, st1.mem, st1.queries⟩
  have esig' : Stmt.Exec oracle fQr (Stmt.assign fSig (PExpr.const 1 - PExpr.reg fFm)) st1 st2 := by
    simpa [st2, σ, fm] using esig
  -- 3. Compute acc via forNat
  have eacc0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := fQr) fAcc (PExpr.const 1) st2 1 (by simp)
  let st3 : RS (FacetReg d) := ⟨Function.update st2.regs fAcc 1, st2.mem, st2.queries⟩
  have hK3 : st3.regs fK = (k : ℝ) := by
    simp only [st3, st2, Function.update_of_ne (by simp : fK ≠ fAcc),
      Function.update_of_ne (by simp : fK ≠ fSig)]
    exact (hpr1 fK (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans hK
  obtain ⟨st4, eacc_loop, _, _, _, hAccInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := fQr)
      (cntReg := fCnt) (boundReg := fK) (condReg := fCond)
      (by simp) (by simp) (by simp)
      (fun cj st_a =>
        st_a.mem = mem₀ ∧ st_a.queries = st.queries + 1 ∧
        1 ≤ st_a.regs fAcc ∧
        (∀ j : Fin k, j.val < cj →
          (1 + (dot (a j) w - σ) ^ 2) / (1 - dot (a j) c) ≤ st_a.regs fAcc) ∧
        (∀ reg, reg ≠ fAcc → reg ≠ fCnt → reg ≠ fCond → reg ≠ fIx →
          reg ≠ fNum → reg ≠ fDen → reg ≠ fTerm → (∀ l, reg ≠ fAj l) →
          st_a.regs reg = st3.regs reg))
      (by
        intro cj st_a v₁ v₂ ⟨hma, hqa, h1a, hba, hpra⟩
        refine ⟨hma, hqa, ?_, ?_, ?_⟩
        · simp only [Function.update_of_ne (by simp : fAcc ≠ fCond),
            Function.update_of_ne (by simp : fAcc ≠ fCnt)]
          exact h1a
        · intro j hj
          simp only [Function.update_of_ne (by simp : fAcc ≠ fCond),
            Function.update_of_ne (by simp : fAcc ≠ fCnt)]
          exact hba j hj
        · intro reg r1 r2 r3 r4 r5 r6 r7 r8
          simp only [Function.update_of_ne r3, Function.update_of_ne r2]
          exact hpra reg r1 r2 r3 r4 r5 r6 r7 r8)
      (by
        intro cj hcj st_a hcnt_a hbnd_a _ ⟨hma, hqa, h1a, hba, hpra⟩
        let j₀ : Fin k := ⟨cj, hcj⟩
        obtain ⟨st_l, eload, haj_l, hpr_l, hm_l, hq_l⟩ :=
          Stmt.Exec.loadFam (oracle := oracle) (qr := fQr) (ix := fIx) (fAj_injective d)
            (fun _ => by simp)
            (fun l => (PExpr.const 2 * PExpr.reg fCnt) * PExpr.nat d + PExpr.nat l.val)
            st_a (fun l => (2 * cj) * d + l.val)
            (by
              intro l regs' hreg
              have hc' : regs' fCnt = (cj : ℝ) :=
                (hreg fCnt (by simp) (fun _ => by simp)).trans hcnt_a
              simp [hc'])
        have haj_eq : (fun l => st_l.regs (fAj l)) = a j₀ := by
          funext l; rw [haj_l l, hma, ha_mem j₀ l]
        have hw_l : (fun l => st_l.regs (fMat idx₁ l)) = w := by
          funext l
          rw [hpr_l (fMat idx₁ l) (by simp) (fun _ => by simp),
            hpra (fMat idx₁ l) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (fun _ => by simp)]
          simp only [st3, st2, Function.update_of_ne (by simp : fMat idx₁ l ≠ fAcc),
            Function.update_of_ne (by simp : fMat idx₁ l ≠ fSig)]
          exact (hpr1 (fMat idx₁ l) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans (hMat idx₁ l)
        have hc_l : (fun l => st_l.regs (fC l)) = c := by
          funext l
          rw [hpr_l (fC l) (by simp) (fun _ => by simp),
            hpra (fC l) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (fun _ => by simp)]
          simp only [st3, st2, Function.update_of_ne (by simp : fC l ≠ fAcc),
            Function.update_of_ne (by simp : fC l ≠ fSig)]
          exact (hpr1 (fC l) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans (hC l)
        have hsig_l : st_l.regs fSig = σ := by
          rw [hpr_l fSig (by simp) (fun _ => by simp),
            hpra fSig (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp) (fun _ => by simp)]
          simp [st3, st2]
        have ep := Stmt.Exec.par (oracle := oracle) (qr := fQr)
          [(fNum, PExpr.const 1 +
              (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                PExpr.reg fSig) *
              (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                PExpr.reg fSig)),
           (fDen, PExpr.const 1 -
              PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fC l)))] st_l
        let st_p : RS (FacetReg d) :=
          ⟨parUpd st_l.regs
            [(fNum, PExpr.const 1 +
                (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                  PExpr.reg fSig) *
                (PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fMat idx₁ l)) -
                  PExpr.reg fSig)),
             (fDen, PExpr.const 1 -
                PExpr.dot (fun l => PExpr.reg (fAj l)) (fun l => PExpr.reg (fC l)))] st_l.regs,
           st_l.mem, st_l.queries⟩
        have hnum_p : st_p.regs fNum = 1 + (dot (a j₀) w - σ) ^ 2 := by
          simp only [st_p, parUpd, PExpr.eval_add, PExpr.eval_const, PExpr.eval_mul,
            PExpr.eval_sub, PExpr.eval_dot, PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fNum ≠ fDen), Function.update_self,
            haj_eq, hw_l, hsig_l]
          ring
        have hden_p : st_p.regs fDen = 1 - dot (a j₀) c := by
          simp only [st_p, parUpd, PExpr.eval_sub, PExpr.eval_const, PExpr.eval_dot,
            PExpr.eval_reg, Function.update_self, haj_eq, hc_l]
          norm_num
        have hδ_pos : 0 < 1 - dot (a j₀) c := by linarith [hInv.hknown j₀]
        have ediv := Stmt.Exec.div (oracle := oracle) (qr := fQr) fTerm fNum fDen st_p
          (by rw [hden_p]; exact hδ_pos.ne')
        let termVal := (1 + (dot (a j₀) w - σ) ^ 2) / (1 - dot (a j₀) c)
        let st_d : RS (FacetReg d) :=
          ⟨Function.update st_p.regs fTerm (st_p.regs fNum / st_p.regs fDen),
           st_p.mem, st_p.queries⟩
        have hterm_nn : 0 ≤ termVal := div_nonneg (by positivity) hδ_pos.le
        have hacc_d : st_d.regs fAcc = st_a.regs fAcc := by
          simp only [st_d, st_p, parUpd, Function.update_of_ne (by simp : fAcc ≠ fTerm),
            Function.update_of_ne (by simp : fAcc ≠ fDen),
            Function.update_of_ne (by simp : fAcc ≠ fNum)]
          exact hpr_l fAcc (by simp) (fun _ => by simp)
        have eadd := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fAcc
          (PExpr.reg fAcc + PExpr.reg fTerm) st_d
        let st_n : RS (FacetReg d) :=
          ⟨Function.update st_d.regs fAcc (st_d.regs fAcc + st_d.regs fTerm),
           st_d.mem, st_d.queries⟩
        have hacc_n : st_n.regs fAcc = st_a.regs fAcc + termVal := by
          rw [show st_n.regs fAcc = st_d.regs fAcc + st_d.regs fTerm from by simp [st_n], hacc_d]
          simp [st_d, hnum_p, hden_p, termVal]
        refine ⟨st_n,
          Stmt.Exec.seq eload (Stmt.Exec.seq ep (Stmt.Exec.seq ediv eadd)),
          ?_, ?_, hm_l.trans hma, hq_l.trans hqa, ?_, ?_, ?_⟩
        · simp only [st_n, st_d, st_p, parUpd,
            Function.update_of_ne (by simp : fCnt ≠ fAcc),
            Function.update_of_ne (by simp : fCnt ≠ fTerm),
            Function.update_of_ne (by simp : fCnt ≠ fDen),
            Function.update_of_ne (by simp : fCnt ≠ fNum)]
          exact (hpr_l fCnt (by simp) (fun _ => by simp)).trans hcnt_a
        · simp only [st_n, st_d, st_p, parUpd,
            Function.update_of_ne (by simp : fK ≠ fAcc),
            Function.update_of_ne (by simp : fK ≠ fTerm),
            Function.update_of_ne (by simp : fK ≠ fDen),
            Function.update_of_ne (by simp : fK ≠ fNum)]
          exact (hpr_l fK (by simp) (fun _ => by simp)).trans hbnd_a
        · rw [hacc_n]; linarith
        · intro j hj
          rw [hacc_n]
          by_cases hjc : j.val < cj
          · linarith [hba j hjc]
          · have hje : j = j₀ := Fin.ext (by dsimp [j₀]; omega)
            rw [hje]
            linarith
        · intro reg r1 r2 r3 r4 r5 r6 r7 r8
          simp only [st_n, st_d, st_p, parUpd,
            Function.update_of_ne r1, Function.update_of_ne r7,
            Function.update_of_ne r6, Function.update_of_ne r5]
          rw [hpr_l reg r4 r8]
          exact hpra reg r1 r2 r3 r4 r5 r6 r7 r8)
      st3 hK3
      ⟨hm1.trans hmem, hq1, by simp [st3], fun _ h => by omega, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨hm4, hq4, hacc_ge1, hacc_bnd, hpr4⟩ := hAccInv
  let acc := st4.regs fAcc
  have hacc_pos : 0 < acc := by linarith
  -- Unknown-facet set U and exclusion lemma on (0, 1 / acc]
  let U : Finset (Fin m) := Finset.univ \ Finset.univ.image emb
  have hU_card : U.card = m - k := by
    have himg : (Finset.univ.image emb).card = k := by
      rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_fin]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, himg]
  have hact_of_le : ∀ x f, 0 < x → x ≤ 1 / acc → Samp A_fn B_fn x f →
      ∀ i, A_fn i + B_fn i * x = f → i ∈ U := by
    intro x f hx hxa hs i hi
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro himg
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 himg
    have hAj : A_fn (emb j) = dot (a j) c := (ha_emb j c).symm
    have hBj : B_fn (emb j) = dot (a j) w := (ha_emb j w).symm
    have hδ : 0 < 1 - dot (a j) c := by linarith [hInv.hknown j]
    have hlt := known_excluded hδ (hacc_bnd j j.isLt) hx hxa
    have hlam := lam_le h0_AB hmsamp' hx.le hs
    rw [hAj, hBj] at hi
    dsimp [σ] at hlt
    linarith
  -- 4. Set xa := 1 / acc, xb := xa / 2, sample at xa and xb
  have enum1 := Stmt.Exec.assign_eval (oracle := oracle) (qr := fQr) fNum (PExpr.const 1) st4 1 (by simp)
  let st5 : RS (FacetReg d) := ⟨Function.update st4.regs fNum 1, st4.mem, st4.queries⟩
  have hacc5 : st5.regs fAcc = acc := by simp [st5, acc]
  have exa := Stmt.Exec.div (oracle := oracle) (qr := fQr) fXa fNum fAcc st5
    (by rw [hacc5]; exact hacc_pos.ne')
  let xa₀ := 1 / acc
  have hxa₀_pos : 0 < xa₀ := div_pos one_pos hacc_pos
  let st6 : RS (FacetReg d) :=
    ⟨Function.update st5.regs fXa (st5.regs fNum / st5.regs fAcc), st5.mem, st5.queries⟩
  have hxa6 : st6.regs fXa = xa₀ := by simp [st6, st5, xa₀, acc]
  have exb := Stmt.Exec.assign_eval (oracle := oracle) (qr := fQr) fXb
    (PExpr.const (1 / 2) * PExpr.reg fXa) st6 ((1 / 2 : ℝ) * st6.regs fXa) (by simp)
  let xb₀ := (1 / 2 : ℝ) * xa₀
  have hxb₀_pos : 0 < xb₀ := by dsimp only [xb₀]; linarith
  have hxb₀_lt : xb₀ < xa₀ := by dsimp only [xb₀]; linarith
  let st7 : RS (FacetReg d) :=
    ⟨Function.update st6.regs fXb ((1 / 2 : ℝ) * st6.regs fXa), st6.mem, st6.queries⟩
  have hxb7 : st7.regs fXb = xb₀ := by simp [st7, hxa6, xb₀]
  have hxa7 : st7.regs fXa = xa₀ := by simp [st7, hxa6]
  -- Helper: core registers unchanged from st to st7
  have hpr7_core : ∀ reg, reg ≠ fFm → reg ≠ fSig → reg ≠ fAcc → reg ≠ fCnt → reg ≠ fCond →
      reg ≠ fIx → reg ≠ fNum → reg ≠ fDen → reg ≠ fTerm → reg ≠ fXa → reg ≠ fXb →
      (∀ l, reg ≠ fAj l) → (∀ l, reg ≠ fV l) → (∀ l, reg ≠ fQr l) → (∀ l, reg ≠ fQb l) →
      st7.regs reg = st.regs reg := by
    intro reg r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    simp only [st7, st6, st5, Function.update_of_ne r11, Function.update_of_ne r10,
      Function.update_of_ne r7]
    rw [hpr4 reg r3 r4 r5 r6 r7 r8 r9 r12]
    simp only [st3, st2, Function.update_of_ne r3, Function.update_of_ne r2]
    exact hpr1 reg r1 r7 r8 r13 r14 r15
  have hc7 : (fun l => st7.regs (fC l)) = c := by
    funext l
    rw [hpr7_core (fC l) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hC l]
  have hw7 : (fun l => st7.regs (fMat idx₁ l)) = w := by
    funext l
    rw [hpr7_core (fMat idx₁ l) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
      hMat idx₁ l]
  -- Sample at xa₀
  have hv_xa : (fun l => st7.regs (fC l)) + xa₀ • (fun l => st7.regs (fMat idx₁ l)) ≠ 0 := by
    rw [hc7, hw7]; exact hInv.ray_ne_zero hr1 hxa₀_pos.ne'
  obtain ⟨st8, esa, hm8, hq8, hfa8, hasamp, _, _, _, hpr8⟩ :=
    sampleRay_spec L hP horacle (PExpr.reg fXa) idx₁ fFa false
      (by simp) (by simp) (fun _ => by simp) st7 xa₀ (by simp [hxa7]) hv_xa
  rw [hc7, hw7] at hfa8 hasamp
  let fa₀ := st8.regs fFa
  have hasamp' : Samp A_fn B_fn xa₀ fa₀ := by rw [← hfa8] at hasamp; exact hasamp
  -- Sample at xb₀
  have hc8 : (fun l => st8.regs (fC l)) = c := by
    funext l
    rw [hpr8 (fC l) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)]
    exact congrFun hc7 l
  have hw8 : (fun l => st8.regs (fMat idx₁ l)) = w := by
    funext l
    rw [hpr8 (fMat idx₁ l) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)]
    exact congrFun hw7 l
  have hxb8 : st8.regs fXb = xb₀ :=
    (hpr8 fXb (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans hxb7
  have hv_xb : (fun l => st8.regs (fC l)) + xb₀ • (fun l => st8.regs (fMat idx₁ l)) ≠ 0 := by
    rw [hc8, hw8]; exact hInv.ray_ne_zero hr1 hxb₀_pos.ne'
  obtain ⟨st9, esb, hm9, hq9, hfb9, hbsamp, _, hqb9_t, _, hpr9⟩ :=
    sampleRay_spec L hP horacle (PExpr.reg fXb) idx₁ fFb true
      (by simp) (by simp) (fun _ => by simp) st8 xb₀ (by simp [hxb8]) hv_xb
  rw [hc8, hw8] at hfb9 hbsamp
  let fb₀ := st9.regs fFb
  have hbsamp' : Samp A_fn B_fn xb₀ fb₀ := by rw [← hfb9] at hbsamp; exact hbsamp
  have hqb9 : ∀ l, st9.regs (fQb l) = oracle (c + xb₀ • w) l := by
    intro l
    have h := hqb9_t rfl l
    rwa [hc8, hw8] at h
  -- Initial secCond assignment
  have esec0 := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fSecCond secCondExpr st9
  let st10 : RS (FacetReg d) :=
    ⟨Function.update st9.regs fSecCond (secCondExpr.eval st9.regs), st9.mem, st9.queries⟩
  -- Build initial SecRun of length 2
  let x_init : ℕ → ℝ := Function.update (Function.update (fun _ => 0) 0 xa₀) 1 xb₀
  let f_init : ℕ → ℝ := Function.update (Function.update (fun _ => 0) 0 fa₀) 1 fb₀
  have hrun_init : SecRun A_fn B_fn U σ 2 x_init f_init := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simpa [x_init, f_init] using hasamp'
      · simpa [x_init, f_init] using hbsamp'
    · intro j hj i hi
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp only [x_init, f_init, Function.update_of_ne (by omega : 0 ≠ 1),
          Function.update_self] at hi
        exact hact_of_le xa₀ fa₀ hxa₀_pos le_rfl hasamp' i hi
      · simp only [x_init, f_init, Function.update_self] at hi
        exact hact_of_le xb₀ fb₀ hxb₀_pos (by linarith) hbsamp' i hi
    · intro j hj
      have : j = 0 := by omega
      subst this
      simpa [x_init] using hxb₀_lt
    · intro j h1 hj; omega
    · intro j h1 hj; omega
  -- Secant while loop invariant and variant
  let q_bound := st.queries + 1 + (2 * U.card + 1)
  let SecInv : RS (FacetReg d) → Prop := fun st_s =>
    st_s.mem = mem₀ ∧
    st_s.regs fK = (k : ℝ) ∧
    st_s.regs fSig = σ ∧
    (∀ l : Fin d, st_s.regs (fP l) = p l) ∧
    (∀ i l : Fin d, st_s.regs (fMat i l) = M i l) ∧
    (∀ l : Fin d, st_s.regs (fC l) = c l) ∧
    ∃ (N : ℕ) (x_seq f_seq : ℕ → ℝ),
      2 ≤ N ∧
      st_s.queries = st.queries + 1 + N ∧
      SecRun A_fn B_fn U σ N x_seq f_seq ∧
      x_seq 0 = xa₀ ∧
      st_s.regs fXa = x_seq (N - 2) ∧ st_s.regs fFa = f_seq (N - 2) ∧
      st_s.regs fXb = x_seq (N - 1) ∧ st_s.regs fFb = f_seq (N - 1) ∧
      0 < st_s.regs fXb ∧
      (∀ l : Fin d, st_s.regs (fQb l) = oracle (c + (st_s.regs fXb) • w) l) ∧
      st_s.regs fSecCond =
        (st_s.regs fFb - (1 + σ * st_s.regs fXb)) *
          ((st_s.regs fFa - 1) * st_s.regs fXb - (st_s.regs fFb - 1) * st_s.regs fXa)
  let μ_sec : RS (FacetReg d) → ℕ := fun st_s => q_bound - st_s.queries
  -- Verify SecInv st10
  have hpr9_from7 : ∀ reg, reg ≠ fFa → reg ≠ fFb → reg ≠ fNum → reg ≠ fDen →
      (∀ l, reg ≠ fV l) → (∀ l, reg ≠ fQr l) → (∀ l, reg ≠ fQb l) →
      st9.regs reg = st7.regs reg := by
    intro reg r1 r2 r3 r4 r5 r6 r7
    rw [hpr9 reg r2 r3 r4 r5 r6 r7, hpr8 reg r1 r3 r4 r5 r6 r7]
  have hsig9 : st9.regs fSig = σ := by
    rw [hpr9_from7 fSig (by simp) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)]
    simp only [st7, st6, st5, Function.update_of_ne (by simp : fSig ≠ fXb),
      Function.update_of_ne (by simp : fSig ≠ fXa),
      Function.update_of_ne (by simp : fSig ≠ fNum)]
    rw [hpr4 fSig (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (fun _ => by simp)]
    simp [st3, st2]
  have hxa9 : st9.regs fXa = xa₀ :=
    (hpr9_from7 fXa (by simp) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans hxa7
  have hxb9 : st9.regs fXb = xb₀ :=
    (hpr9_from7 fXb (by simp) (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)).trans hxb7
  have hfa9 : st9.regs fFa = fa₀ :=
    hpr9 fFa (by simp) (by simp) (by simp)
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
  have hSecInv10 : SecInv st10 := by
    refine ⟨hm9.trans (hm8.trans hm4), ?_, ?_, ?_, ?_, ?_,
      2, x_init, f_init, le_rfl, ?_, hrun_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [st10, Function.update_of_ne (by simp : fK ≠ fSecCond)]
      rw [hpr9_from7 fK (by simp) (by simp) (by simp) (by simp)
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hpr7_core fK (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hK]
    · simp [st10, hsig9]
    · intro l
      simp only [st10, Function.update_of_ne (by simp : fP l ≠ fSecCond)]
      rw [hpr9_from7 (fP l) (by simp) (by simp) (by simp) (by simp)
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hpr7_core (fP l) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hP_reg l]
    · intro i l
      simp only [st10, Function.update_of_ne (by simp : fMat i l ≠ fSecCond)]
      rw [hpr9_from7 (fMat i l) (by simp) (by simp) (by simp) (by simp)
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hpr7_core (fMat i l) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hMat i l]
    · intro l
      simp only [st10, Function.update_of_ne (by simp : fC l ≠ fSecCond)]
      rw [hpr9_from7 (fC l) (by simp) (by simp) (by simp) (by simp)
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hpr7_core (fC l) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
        hC l]
    · change st9.queries = st.queries + 1 + 2
      rw [hq9, hq8]; change st4.queries + 1 + 1 = _; rw [hq4]
    · simp [x_init]
    · simp [st10, hxa9, x_init]
    · simp [st10, hfa9, f_init]
    · simp [st10, hxb9, x_init]
    · simp [st10, fb₀, f_init]
    · simp [st10, hxb9, hxb₀_pos]
    · intro l
      simp only [st10, Function.update_of_ne (by simp : fQb l ≠ fSecCond),
        Function.update_of_ne (by simp : fXb ≠ fSecCond), hxb9]
      exact hqb9 l
    · simp [st10, secCondExpr, hsig9]
  -- 5. Run secant while loop
  obtain ⟨st_e, ewhile, hEndInv, hEndZero⟩ :=
    Stmt.Exec.while_inv (oracle := oracle) (qr := fQr) SecInv μ_sec
      (by
        intro st_s hIs hcond_ne
        obtain ⟨hms, hKs, hsigs, hPs, hMats, hCs,
          N, x_seq, f_seq, hN2, hqs, hrun, hx0, hxa_s, hfa_s, hxb_s, hfb_s,
          hxb_pos, hqb_s, hcond_eq⟩ := hIs
        let xa := st_s.regs fXa
        let fa := st_s.regs fFa
        let xb := st_s.regs fXb
        let fb := st_s.regs fFb
        rw [hcond_eq] at hcond_ne
        have hA : fb ≠ 1 + (1 - fm) * xb := sub_ne_zero.1 (mul_ne_zero_iff.1 hcond_ne).1
        have hB : (fa - 1) * xb ≠ (fb - 1) * xa := sub_ne_zero.1 (mul_ne_zero_iff.1 hcond_ne).2
        have hab : xb < xa := by
          change st_s.regs fXb < st_s.regs fXa
          rw [hxb_s, hxa_s]
          have hlt := hrun.anti (N - 2) (by omega)
          have he : N - 2 + 1 = N - 1 := by omega
          rwa [he] at hlt
        have hsa : Samp A_fn B_fn xa fa := by
          change Samp A_fn B_fn (st_s.regs fXa) (st_s.regs fFa)
          rw [hxa_s, hfa_s]
          exact hrun.samp (N - 2) (by omega)
        have hsb : Samp A_fn B_fn xb fb := by
          change Samp A_fn B_fn (st_s.regs fXb) (st_s.regs fFb)
          rw [hxb_s, hfb_s]
          exact hrun.samp (N - 1) (by omega)
        obtain ⟨hd_ne, hμσ_ne, hxn_pos, hxn_lt, hcross⟩ :=
          secant_step h0_AB hmsamp' hxb_pos hab hsa hsb hA hB
        let μ_s := (fa - fb) / (xa - xb)
        let xn := (1 - (fb - μ_s * xb)) / (μ_s - σ)
        -- Execute μ_s and xn
        have ep1 := Stmt.Exec.par (oracle := oracle) (qr := fQr)
          [(fNum, PExpr.reg fFa - PExpr.reg fFb),
           (fDen, PExpr.reg fXa - PExpr.reg fXb)] st_s
        let st_s1 : RS (FacetReg d) :=
          ⟨parUpd st_s.regs
            [(fNum, PExpr.reg fFa - PExpr.reg fFb),
             (fDen, PExpr.reg fXa - PExpr.reg fXb)] st_s.regs,
           st_s.mem, st_s.queries⟩
        have hden_s1 : st_s1.regs fDen = xa - xb := by simp [st_s1, parUpd, xa, xb]
        have hnum_s1 : st_s1.regs fNum = fa - fb := by
          simp only [st_s1, parUpd, PExpr.eval_sub, PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fNum ≠ fDen), Function.update_self]
        have ediv1 := Stmt.Exec.div (oracle := oracle) (qr := fQr) fMu fNum fDen st_s1
          (by rw [hden_s1]; exact hd_ne)
        let st_s2 : RS (FacetReg d) :=
          ⟨Function.update st_s1.regs fMu (st_s1.regs fNum / st_s1.regs fDen),
           st_s1.mem, st_s1.queries⟩
        have hmu_s2 : st_s2.regs fMu = μ_s := by simp [st_s2, hnum_s1, hden_s1, μ_s]
        have ep2 := Stmt.Exec.par (oracle := oracle) (qr := fQr)
          [(fNum, PExpr.const 1 - (PExpr.reg fFb - PExpr.reg fMu * PExpr.reg fXb)),
           (fDen, PExpr.reg fMu - PExpr.reg fSig)] st_s2
        let st_s3 : RS (FacetReg d) :=
          ⟨parUpd st_s2.regs
            [(fNum, PExpr.const 1 - (PExpr.reg fFb - PExpr.reg fMu * PExpr.reg fXb)),
             (fDen, PExpr.reg fMu - PExpr.reg fSig)] st_s2.regs,
           st_s2.mem, st_s2.queries⟩
        have hfb_s2 : st_s2.regs fFb = fb := by
          simp [st_s2, st_s1, parUpd, fb]
        have hxb_s2 : st_s2.regs fXb = xb := by
          simp [st_s2, st_s1, parUpd, xb]
        have hsig_s2 : st_s2.regs fSig = σ := by
          simp [st_s2, st_s1, parUpd, hsigs]
        have hnum_s3 : st_s3.regs fNum = 1 - (fb - μ_s * xb) := by
          simp only [st_s3, parUpd, PExpr.eval_sub, PExpr.eval_const, PExpr.eval_mul,
            PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fNum ≠ fDen), Function.update_self,
            hfb_s2, hmu_s2, hxb_s2]
          norm_num
        have hden_s3 : st_s3.regs fDen = μ_s - σ := by
          simp [st_s3, parUpd, hmu_s2, hsig_s2]
        have ediv2 := Stmt.Exec.div (oracle := oracle) (qr := fQr) fXn fNum fDen st_s3
          (by rw [hden_s3]; exact hμσ_ne)
        let st_s4 : RS (FacetReg d) :=
          ⟨Function.update st_s3.regs fXn (st_s3.regs fNum / st_s3.regs fDen),
           st_s3.mem, st_s3.queries⟩
        have hxn_s4 : st_s4.regs fXn = xn := by simp [st_s4, hnum_s3, hden_s3, xn]
        have hpr_s4 : ∀ reg, reg ≠ fNum → reg ≠ fDen → reg ≠ fMu → reg ≠ fXn →
            st_s4.regs reg = st_s.regs reg := by
          intro reg r1 r2 r3 r4
          simp [st_s4, st_s3, st_s2, st_s1, parUpd,
            Function.update_of_ne r4, Function.update_of_ne r3,
            Function.update_of_ne r2, Function.update_of_ne r1]
        have hc_s4 : (fun l => st_s4.regs (fC l)) = c := by
          funext l
          rw [hpr_s4 (fC l) (by simp) (by simp) (by simp) (by simp), hCs l]
        have hw_s4 : (fun l => st_s4.regs (fMat idx₁ l)) = w := by
          funext l
          rw [hpr_s4 (fMat idx₁ l) (by simp) (by simp) (by simp) (by simp), hMats idx₁ l]
        have hv_xn : (fun l => st_s4.regs (fC l)) + xn • (fun l => st_s4.regs (fMat idx₁ l)) ≠ 0 := by
          rw [hc_s4, hw_s4]; exact hInv.ray_ne_zero hr1 hxn_pos.ne'
        -- Sample at xn
        obtain ⟨st_s5, esn, hm_s5, hq_s5, hfn_s5, hnsamp, _, hqb_s5_t, _, hpr_s5⟩ :=
          sampleRay_spec L hP horacle (PExpr.reg fXn) idx₁ fFn true
            (by simp) (by simp) (fun _ => by simp) st_s4 xn (by simp [hxn_s4]) hv_xn
        rw [hc_s4, hw_s4] at hfn_s5 hnsamp
        let fn := st_s5.regs fFn
        have hnsamp' : Samp A_fn B_fn xn fn := by rw [← hfn_s5] at hnsamp; exact hnsamp
        -- Shift (xa, fa, xb, fb) and recompute secCond
        have eshift := Stmt.Exec.par (oracle := oracle) (qr := fQr)
          [(fXa, PExpr.reg fXb),
           (fFa, PExpr.reg fFb),
           (fXb, PExpr.reg fXn),
           (fFb, PExpr.reg fFn)] st_s5
        let st_s6 : RS (FacetReg d) :=
          ⟨parUpd st_s5.regs
            [(fXa, PExpr.reg fXb),
             (fFa, PExpr.reg fFb),
             (fXb, PExpr.reg fXn),
             (fFb, PExpr.reg fFn)] st_s5.regs,
           st_s5.mem, st_s5.queries⟩
        have econd := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fSecCond secCondExpr st_s6
        let st_s7 : RS (FacetReg d) :=
          ⟨Function.update st_s6.regs fSecCond (secCondExpr.eval st_s6.regs),
           st_s6.mem, st_s6.queries⟩
        -- Extend SecRun to N + 1
        have hxb_le_x0 : xb ≤ xa₀ := by
          change st_s.regs fXb ≤ xa₀
          rw [hxb_s, ← hx0]
          exact hrun.anti_le (Nat.zero_le _) (by omega)
        have hxn_le : xn ≤ 1 / acc := le_trans hxn_lt.le hxb_le_x0
        have hrun_next : SecRun A_fn B_fn U σ (N + 1)
            (Function.update x_seq N xn) (Function.update f_seq N fn) := by
          refine hrun.extend hN2 xn fn hnsamp' (hact_of_le xn fn hxn_pos hxn_le hnsamp') ?_ ?_ ?_
          · rw [← hxb_s]; exact hxn_lt
          · rw [← hfb_s, ← hxb_s]; exact hA
          · rw [← hfa_s, ← hfb_s, ← hxa_s, ← hxb_s]; exact hcross
        have hN1_le : N + 1 ≤ 2 * U.card + 1 := hrun_next.length_le
        -- Register values in st_s6 / st_s7
        have hxb_s5 : st_s5.regs fXb = xb := by
          rw [hpr_s5 fXb (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
            hpr_s4 fXb (by simp) (by simp) (by simp) (by simp)]
        have hfb_s5 : st_s5.regs fFb = fb := by
          rw [hpr_s5 fFb (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
            hpr_s4 fFb (by simp) (by simp) (by simp) (by simp)]
        have hxn_s5 : st_s5.regs fXn = xn := by
          rw [hpr_s5 fXn (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hxn_s4]
        have hxa_s6 : st_s6.regs fXa = xb := by
          simp only [st_s6, parUpd, PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fXa ≠ fFb),
            Function.update_of_ne (by simp : fXa ≠ fXb),
            Function.update_of_ne (by simp : fXa ≠ fFa),
            Function.update_self, hxb_s5]
        have hfa_s6 : st_s6.regs fFa = fb := by
          simp only [st_s6, parUpd, PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fFa ≠ fFb),
            Function.update_of_ne (by simp : fFa ≠ fXb),
            Function.update_self, hfb_s5]
        have hxb_s6 : st_s6.regs fXb = xn := by
          simp only [st_s6, parUpd, PExpr.eval_reg]
          rw [Function.update_of_ne (by simp : fXb ≠ fFb),
            Function.update_self, hxn_s5]
        have hfb_s6 : st_s6.regs fFb = fn := by
          simp [st_s6, parUpd, fn]
        have hpr_s7 : ∀ reg, reg ≠ fSecCond → reg ≠ fXa → reg ≠ fFa → reg ≠ fXb → reg ≠ fFb →
            reg ≠ fFn → reg ≠ fNum → reg ≠ fDen → reg ≠ fMu → reg ≠ fXn →
            (∀ l, reg ≠ fV l) → (∀ l, reg ≠ fQr l) → (∀ l, reg ≠ fQb l) →
            st_s7.regs reg = st_s.regs reg := by
          intro reg c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
          simp only [st_s7, st_s6, parUpd, Function.update_of_ne c0,
            Function.update_of_ne c4, Function.update_of_ne c3,
            Function.update_of_ne c2, Function.update_of_ne c1]
          rw [hpr_s5 reg c5 c6 c7 c10 c11 c12, hpr_s4 reg c6 c7 c8 c9]
        have hsig_s6 : st_s6.regs fSig = σ := by
          simp only [st_s6, parUpd,
            Function.update_of_ne (by simp : fSig ≠ fFb),
            Function.update_of_ne (by simp : fSig ≠ fXb),
            Function.update_of_ne (by simp : fSig ≠ fFa),
            Function.update_of_ne (by simp : fSig ≠ fXa)]
          rw [hpr_s5 fSig (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp),
            hpr_s4 fSig (by simp) (by simp) (by simp) (by simp), hsigs]
        refine ⟨st_s7,
          Stmt.Exec.seq ep1 (Stmt.Exec.seq ediv1 (Stmt.Exec.seq ep2
            (Stmt.Exec.seq ediv2 (Stmt.Exec.seq esn (Stmt.Exec.seq eshift econd))))),
          ⟨hm_s5.trans hms, ?_, ?_, ?_, ?_, ?_,
            N + 1, Function.update x_seq N xn, Function.update f_seq N fn,
            by omega, ?_, hrun_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          ?_⟩
        · rw [hpr_s7 fK (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hKs]
        · rw [hpr_s7 fSig (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hsigs]
        · intro l
          rw [hpr_s7 (fP l) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hPs l]
        · intro i l
          rw [hpr_s7 (fMat i l) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hMats i l]
        · intro l
          rw [hpr_s7 (fC l) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp) (fun _ => by simp) (fun _ => by simp), hCs l]
        · change st_s5.queries = st.queries + 1 + (N + 1)
          rw [hq_s5]; change st_s.queries + 1 = _; rw [hqs]; omega
        · rw [Function.update_of_ne (by omega : 0 ≠ N), hx0]
        · simp only [st_s7, Function.update_of_ne (by simp : fXa ≠ fSecCond), hxa_s6]
          have he : N + 1 - 2 = N - 1 := by omega
          rw [he, Function.update_of_ne (by omega : N - 1 ≠ N), ← hxb_s]
        · simp only [st_s7, Function.update_of_ne (by simp : fFa ≠ fSecCond), hfa_s6]
          have he : N + 1 - 2 = N - 1 := by omega
          rw [he, Function.update_of_ne (by omega : N - 1 ≠ N), ← hfb_s]
        · simp [st_s7, hxb_s6]
        · simp [st_s7, hfb_s6]
        · simp only [st_s7, Function.update_of_ne (by simp : fXb ≠ fSecCond), hxb_s6]
          exact hxn_pos
        · intro l
          have hxb7 : st_s7.regs fXb = xn := by simp [st_s7, hxb_s6]
          rw [hxb7]
          simp only [st_s7, Function.update_of_ne (by simp : fQb l ≠ fSecCond), st_s6, parUpd,
            Function.update_of_ne (by simp : fQb l ≠ fFb),
            Function.update_of_ne (by simp : fQb l ≠ fXb),
            Function.update_of_ne (by simp : fQb l ≠ fFa),
            Function.update_of_ne (by simp : fQb l ≠ fXa)]
          have h := hqb_s5_t rfl l
          rwa [hc_s4, hw_s4] at h
        · simp [st_s7, secCondExpr, hsig_s6]
        · dsimp only [μ_sec, q_bound]
          change _ - st_s5.queries < _ - st_s.queries
          rw [hq_s5]; change _ - (st_s.queries + 1) < _
          rw [hqs]
          omega)
      st10 hSecInv10
  -- 6. Secant stopped: apply secant_stop and StageInv.step
  obtain ⟨hm_e, hK_e, _, hP_e, hMat_e, hC_e,
    N_e, x_e, f_e, hN2_e, hq_e, hrun_e, _, hxa_e, hfa_e, hxb_e, hfb_e,
    hxb_pos_e, hqb_e, hcond_eq_e⟩ := hEndInv
  have hstop : st_e.regs fFb = 1 + (1 - fm) * st_e.regs fXb ∨
      (st_e.regs fFa - 1) * st_e.regs fXb = (st_e.regs fFb - 1) * st_e.regs fXa := by
    rw [hcond_eq_e] at hEndZero
    rcases mul_eq_zero.1 hEndZero with h1 | h2
    · left; linarith
    · right; linarith
  have hab_e : st_e.regs fXb < st_e.regs fXa := by
    rw [hxb_e, hxa_e]
    have hlt := hrun_e.anti (N_e - 2) (by omega)
    have he : N_e - 2 + 1 = N_e - 1 := by omega
    rwa [he] at hlt
  have hsa_e : Samp A_fn B_fn (st_e.regs fXa) (st_e.regs fFa) := by
    rw [hxa_e, hfa_e]; exact hrun_e.samp (N_e - 2) (by omega)
  have hsb_e : Samp A_fn B_fn (st_e.regs fXb) (st_e.regs fFb) := by
    rw [hxb_e, hfb_e]; exact hrun_e.samp (N_e - 1) (by omega)
  obtain ⟨i_com, hi_c, hi_xb⟩ := secant_stop h0_AB hmsamp' hxb_pos_e hab_e hsa_e hsb_e hstop
  -- Relate fFb to oracle (c + xb • w)
  have hv_e : c + (st_e.regs fXb) • w ≠ 0 := hInv.ray_ne_zero hr1 hxb_pos_e.ne'
  obtain ⟨_, hsamp_ray_e, hiff_ray_e⟩ := oracle_samp_ray L hP horacle c w (st_e.regs fXb) hv_e
  have hfb_eq_gauge : st_e.regs fFb =
      dot (c + (st_e.regs fXb) • w) (c + (st_e.regs fXb) • w) /
        dot (oracle (c + (st_e.regs fXb) • w)) (c + (st_e.regs fXb) • w) := by
    obtain ⟨j1, hj1⟩ := hsb_e.2
    obtain ⟨j2, hj2⟩ := hsamp_ray_e.2
    have hle1 := hsamp_ray_e.1 j1
    have hle2 := hsb_e.1 j2
    dsimp [A_fn, B_fn] at hj1 hle2
    linarith
  have hi_q : L i_com (oracle (c + (st_e.regs fXb) • w)) = 1 :=
    (hiff_ray_e i_com).2 (by dsimp [A_fn, B_fn] at hi_xb; linarith [hfb_eq_gauge])
  have ha_ex : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x :=
    fun j => ⟨emb j, ha_emb j⟩
  have hInv_next := StageInv.step L hP a ha_ex horacle hInv hr1 hxb_pos_e ⟨i_com, hi_c, hi_q⟩
  -- Execute final updates to fMat idx₁ and fC
  have eupM := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fMat_row_injective d idx₁)
    (fun l => PExpr.reg (fQb l)) st_e
  let st_f1 : RS (FacetReg d) :=
    ⟨Function.extend (fMat idx₁) (fun l => st_e.regs (fQb l)) st_e.regs, st_e.mem, st_e.queries⟩
  have eupC := Stmt.Exec.vset (oracle := oracle) (qr := fQr) (fC_injective d)
    (fun l => PExpr.const (1 / 2) * (PExpr.reg (fC l) + PExpr.reg (fQb l))) st_f1
  let st_f2 : RS (FacetReg d) :=
    ⟨Function.extend fC
      (fun l => (PExpr.const (1 / 2) * (PExpr.reg (fC l) + PExpr.reg (fQb l))).eval st_f1.regs)
      st_f1.regs,
     st_f1.mem, st_f1.queries⟩
  let q_pt := oracle (c + (st_e.regs fXb) • w)
  have hN_le : N_e ≤ 2 * (m - k) + 1 := hU_card ▸ hrun_e.length_le
  refine ⟨st_f2, Function.update M idx₁ q_pt, (1 / 2 : ℝ) • (c + q_pt),
    Stmt.Exec.seq es1 (Stmt.Exec.seq esig' (Stmt.Exec.seq (Stmt.Exec.seq eacc0 eacc_loop)
      (Stmt.Exec.seq enum1 (Stmt.Exec.seq exa (Stmt.Exec.seq exb
        (Stmt.Exec.seq esa (Stmt.Exec.seq esb (Stmt.Exec.seq esec0
          (Stmt.Exec.seq ewhile (Stmt.Exec.seq eupM eupC)))))))))),
    hm_e, ?_, ?_, ?_, ?_, ?_, hInv_next⟩
  · change st_e.queries ≤ _
    rw [hq_e]; omega
  · simp only [st_f2, st_f1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hK_e]
  · intro l
    simp only [st_f2, st_f1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he), hP_e l]
  · intro i l
    simp only [st_f2]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
    by_cases hi : i = idx₁
    · subst hi
      simp only [st_f1, Function.update_self]
      rw [(fMat_row_injective d idx₁).extend_apply, hqb_e l]
    · simp only [st_f1, Function.update_of_ne hi]
      rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he; exact hi he.1.symm), hMat_e i l]
  · intro l
    simp only [st_f2]
    rw [(fC_injective d).extend_apply]
    simp only [PExpr.eval_mul, PExpr.eval_const, PExpr.eval_add, PExpr.eval_reg, st_f1]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he),
      hC_e l, hqb_e l]
    simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul, q_pt]

/-- Complete `facetFind` subroutine: given frontier point `p` in `fP` (`p ≠ 0`, `a j · p < 1`)
and `k` in `fK`, outputs a new facet normal `a_new` in `fOut` with `L i_new p = 1` using at most
`(d - 1) * (2 * (m - k) + 2)` queries and zero memory writes. -/
noncomputable def facetFind (d : ℕ) (hd : 2 ≤ d) : Stmt (FacetReg d) :=
  let hd0 : 0 < d := by omega
  let solveNormal : Stmt (FacetReg d) :=
    .seq (Stmt.assign fDet (PExpr.det fun i l => PExpr.reg (fMat i l)))
      (Stmt.seqFin d fun l =>
        .seq
          (Stmt.assign fNum
            (PExpr.det fun i l' => if l' = l then PExpr.const 1 else PExpr.reg (fMat i l')))
          (.div (fOut l) fNum fDet))
  .seq (initBasis d hd0)
    (.seq (Stmt.seqFin (d - 1) fun r => facetStage d ⟨r.val + 1, by omega⟩)
      solveNormal)

theorem facetFind_spec {d m k : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ)
    (emb : Fin k → Fin m) (hemb_inj : Function.Injective emb)
    (ha_emb : ∀ (j : Fin k) (x : Fin d → ℝ), dot (a j) x = L (emb j) x)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (st : RS (FacetReg d))
    (hmem : st.mem = mem₀) (hK : st.regs fK = (k : ℝ))
    (hp_front : (fun l => st.regs (fP l)) ∈ frontier P)
    (hp_known : ∀ j : Fin k, dot (a j) (fun l => st.regs (fP l)) < 1) :
    ∃ st', Stmt.Exec oracle fQr (facetFind d hd) st st' ∧
      st'.mem = st.mem ∧
      st'.queries ≤ st.queries + (d - 1) * (2 * (m - k) + 2) ∧
      st'.regs fK = (k : ℝ) ∧
      ∃ i_new : Fin m,
        (∀ j : Fin k, i_new ≠ emb j) ∧
        (∀ x, dot (fun l => st'.regs (fOut l)) x = L i_new x) ∧
        L i_new (fun l => st.regs (fP l)) = 1 := by
  let hd0 : 0 < d := by omega
  let p := fun l => st.regs (fP l)
  have hp0 : p ≠ 0 := frontier_ne_zero L hP hp_front
  -- 1. initBasis
  obtain ⟨st0, W₀, einit, hm0, hq0, hW0, hli0, hMat0, hC0, hP0, hK0⟩ :=
    initBasis_spec hd (oracle := oracle) st hp0
  have hStage0 : StageInv P L a p W₀ 0 W₀ p :=
    StageInv.init hd0 L hP a p hp_front hp_known W₀ hW0 hli0
  -- 2. Run (d - 1) stages
  obtain ⟨stS, estages, hmS, hqS, hKS, _, M_fin, c_fin, hMatS, hCS, hStageFin⟩ :=
    Stmt.Exec.seqFin_inv (oracle := oracle) (qr := fQr)
      (fun r : Fin (d - 1) => facetStage d ⟨r.val + 1, by omega⟩)
      (fun r_cnt st_r =>
        st_r.mem = mem₀ ∧
        st_r.queries ≤ st.queries + r_cnt * (2 * (m - k) + 2) ∧
        st_r.regs fK = (k : ℝ) ∧
        (∀ l : Fin d, st_r.regs (fP l) = p l) ∧
        ∃ M_r c_r,
          (∀ i l : Fin d, st_r.regs (fMat i l) = M_r i l) ∧
          (∀ l : Fin d, st_r.regs (fC l) = c_r l) ∧
          StageInv P L a p W₀ r_cnt M_r c_r)
      (by
        intro r st_r ⟨hm_r, hq_r, hK_r, hP_r, M_r, c_r, hMat_r, hC_r, hInv_r⟩
        obtain ⟨st_n, M_n, c_n, estg, hm_n, hq_n, hK_n, hP_n, hMat_n, hC_n, hInv_n⟩ :=
          facetStage_spec (by omega) L hP horacle mem₀ a emb hemb_inj ha_emb ha_mem
            hInv_r st_r hm_r hK_r hMat_r hC_r hP_r
        refine ⟨st_n, estg, hm_n, ?_, hK_n, hP_n, M_n, c_n, hMat_n, hC_n, hInv_n⟩
        have : (r.val + 1) * (2 * (m - k) + 2) =
            r.val * (2 * (m - k) + 2) + (2 * (m - k) + 2) := Nat.succ_mul _ _
        omega)
      st0 ⟨hm0.trans hmem, by rw [hq0]; simp, hK0.trans hK, hP0, W₀, p, hMat0, hC0, hStage0⟩
  -- 3. Final Cramer solve
  obtain ⟨hdet_fin, i_new, ha_new_eq, hip1⟩ := StageInv.finish hd L hP hStageFin
  let A_fin := Matrix.of M_fin
  have edet := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fDet
    (PExpr.det fun i l => PExpr.reg (fMat i l)) stS
  let stD : RS (FacetReg d) :=
    ⟨Function.update stS.regs fDet ((PExpr.det fun i l => PExpr.reg (fMat i l)).eval stS.regs),
     stS.mem, stS.queries⟩
  have hdetD : stD.regs fDet = A_fin.det := by
    simp only [stD, Function.update_self, PExpr.eval_det, PExpr.eval_reg, A_fin]
    congr 1; ext i l; exact hMatS i l
  obtain ⟨stF, esolve, hmF, hqF, houtF, hprF⟩ :=
    Stmt.Exec.seqFin_inv (oracle := oracle) (qr := fQr)
      (fun l : Fin d =>
        .seq
          (Stmt.assign fNum
            (PExpr.det fun i l' => if l' = l then PExpr.const 1 else PExpr.reg (fMat i l')))
          (.div (fOut l) fNum fDet))
      (fun c_l st_l =>
        st_l.mem = mem₀ ∧ st_l.queries = stS.queries ∧
        (∀ l : Fin d, l.val < c_l →
          st_l.regs (fOut l) = (A_fin.updateCol l (fun _ => 1)).det / A_fin.det) ∧
        (∀ reg, reg ≠ fNum → (∀ l, reg ≠ fOut l) → st_l.regs reg = stD.regs reg))
      (by
        intro l st_l ⟨hm_l, hq_l, hout_l, hpr_l⟩
        have en := Stmt.Exec.assign (oracle := oracle) (qr := fQr) fNum
          (PExpr.det fun i l' => if l' = l then PExpr.const 1 else PExpr.reg (fMat i l')) st_l
        let st_n1 : RS (FacetReg d) :=
          ⟨Function.update st_l.regs fNum
            ((PExpr.det fun i l' =>
              if l' = l then PExpr.const 1 else PExpr.reg (fMat i l')).eval st_l.regs),
           st_l.mem, st_l.queries⟩
        have hdet_n1 : st_n1.regs fDet = A_fin.det := by
          simp only [st_n1, Function.update_of_ne (by simp : fDet ≠ fNum)]
          rw [hpr_l fDet (by simp) (fun _ => by simp), hdetD]
        have hnum_n1 : st_n1.regs fNum = (A_fin.updateCol l (fun _ => 1)).det := by
          simp only [st_n1, Function.update_self, PExpr.eval_det]
          congr 1; ext i l'
          by_cases hll : l' = l
          · subst hll
            simp [Matrix.of_apply, Matrix.updateCol_self]
          · simp only [Matrix.of_apply, if_neg hll, PExpr.eval_reg, Matrix.updateCol_ne hll]
            rw [hpr_l (fMat i l') (by simp) (fun _ => by simp)]
            simp [stD, A_fin, hMatS i l']
        have ediv := Stmt.Exec.div (oracle := oracle) (qr := fQr) (fOut l) fNum fDet st_n1
          (by rw [hdet_n1]; exact hdet_fin)
        let st_n2 : RS (FacetReg d) :=
          ⟨Function.update st_n1.regs (fOut l) (st_n1.regs fNum / st_n1.regs fDet),
           st_n1.mem, st_n1.queries⟩
        refine ⟨st_n2, Stmt.Exec.seq en ediv, hm_l, hq_l, ?_, ?_⟩
        · intro l' hl'
          by_cases hll : l' = l
          · subst hll
            simp [st_n2, hnum_n1, hdet_n1]
          · have hlt' : l'.val < l.val := by
              have : l'.val ≠ l.val := fun e => hll (Fin.ext e)
              omega
            have hneo : fOut l' ≠ fOut l := fun e => hll (fOut_injective d e)
            simp only [st_n2, st_n1, Function.update_of_ne hneo,
              Function.update_of_ne (by simp : fOut l' ≠ fNum)]
            exact hout_l l' hlt'
        · intro reg r1 r2
          simp only [st_n2, st_n1, Function.update_of_ne (r2 l), Function.update_of_ne r1]
          exact hpr_l reg r1 r2)
      stD ⟨hmS, rfl, fun _ h => by omega, fun _ _ _ => rfl⟩
  have hKF : stF.regs fK = (k : ℝ) := by
    rw [hprF fK (by simp) (fun _ => by simp)]
    simp [stD, hKS]
  have hout_eq : (fun l => stF.regs (fOut l)) =
      fun l => (A_fin.updateCol l (fun _ => 1)).det / A_fin.det :=
    funext fun l => houtF l l.isLt
  refine ⟨stF, Stmt.Exec.seq einit (Stmt.Exec.seq estages (Stmt.Exec.seq edet esolve)),
    hmF.trans hmem.symm, hqF ▸ hqS, hKF, i_new, ?_, ?_, hip1⟩
  · intro j heq
    have := ha_emb j p
    rw [← heq, hip1] at this
    linarith [hp_known j]
  · intro x
    rw [hout_eq]
    exact ha_new_eq x

end Facet

end RayAlg
end Grunbaum2003

/-! ### Module: Ray.Lattice -/

namespace Grunbaum2003
open scoped BigOperators Matrix Classical
namespace RayAlg

/-! ## Top-level discovery loop, face-lattice closure, and main reconstruction theorem -/

namespace Lattice

/-- Extract `n : ℕ` from `(n : ℝ)` for loop variants. -/
noncomputable def natOfReal (x : ℝ) : ℕ :=
  if h : ∃ n : ℕ, x = (n : ℝ) then Classical.choose h else 0

@[simp] theorem natOfReal_cast (n : ℕ) : natOfReal (n : ℝ) = n := by
  have h : ∃ m : ℕ, (n : ℝ) = (m : ℝ) := ⟨n, rfl⟩
  simp only [natOfReal, dif_pos h]
  exact Nat.cast_injective (Classical.choose_spec h).symm

/-- Append one element to a `Fin n`-indexed family. -/
def snocVec {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) : Fin (n + 1) → α :=
  fun j => if h : j.val < n then f ⟨j.val, h⟩ else x

@[simp] theorem snocVec_lt {n : ℕ} {α : Type*} (f : Fin n → α) (x : α)
    (j : Fin (n + 1)) (h : j.val < n) :
    snocVec f x j = f ⟨j.val, h⟩ := by
  simp [snocVec, h]

@[simp] theorem snocVec_castSucc {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) (j : Fin n) :
    snocVec f x ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = f j := by
  simp [snocVec, j.isLt]

@[simp] theorem snocVec_last {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) :
    snocVec f x ⟨n, Nat.lt_succ_self n⟩ = x := by
  simp [snocVec]

theorem snocVec_injective {n : ℕ} {α : Type*} {f : Fin n → α} {x : α}
    (hf : Function.Injective f) (hx : ∀ j : Fin n, x ≠ f j) :
    Function.Injective (snocVec f x) := by
  intro i j hij
  dsimp [snocVec] at hij
  split_ifs at hij with hi hj hj
  · have h := hf hij
    exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; exact this)
  · exact False.elim (hx ⟨i.val, hi⟩ hij.symm)
  · exact False.elim (hx ⟨j.val, hj⟩ hij)
  · exact Fin.ext (by omega)

theorem snocVec_range {n : ℕ} {α : Type*} (f : Fin n → α) (x : α) :
    Set.range (snocVec f x) = insert x (Set.range f) := by
  ext y; constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j.val < n
    · exact Or.inr ⟨⟨j.val, hj⟩, (snocVec_lt f x j hj).symm⟩
    · have hje : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega)
      rw [hje, snocVec_last]
      exact Or.inl rfl
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, snocVec_last f y⟩
    · exact ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, snocVec_castSucc f x j⟩

theorem mul_add_inj {W i₁ i₂ r₁ r₂ : ℕ} (hr₁ : r₁ < W) (hr₂ : r₂ < W)
    (h : i₁ * W + r₁ = i₂ * W + r₂) : i₁ = i₂ ∧ r₁ = r₂ := by
  have hi : i₁ = i₂ := by nlinarith
  subst hi
  exact ⟨rfl, by omega⟩

/-! ### Top-level register file and subroutine embeddings -/

abbrev MainCore (d : ℕ) := Fin 24 ⊕ (Fin 4 × Fin d)

abbrev MainReg (d : ℕ) :=
  Fin d ⊕ MainCore d ⊕ Bfs.CramerReg d ⊕ Facet.FacetReg d

abbrev mainQr {d : ℕ} (l : Fin d) : MainReg d := Sum.inl l
abbrev mCore  {d : ℕ} (c : MainCore d) : MainReg d := Sum.inr (Sum.inl c)

abbrev mK        {d : ℕ} : MainReg d := mCore (Sum.inl 0)
abbrev mV        {d : ℕ} : MainReg d := mCore (Sum.inl 1)
abbrev mActive   {d : ℕ} : MainReg d := mCore (Sum.inl 2)
abbrev mOut      {d : ℕ} : MainReg d := mCore (Sum.inl 3)
abbrev mIx       {d : ℕ} : MainReg d := mCore (Sum.inl 4)
abbrev mTmp      {d : ℕ} : MainReg d := mCore (Sum.inl 5)
abbrev mIncBase  {d : ℕ} : MainReg d := mCore (Sum.inl 6)
abbrev mFaceBase {d : ℕ} : MainReg d := mCore (Sum.inl 7)
abbrev mCurN     {d : ℕ} : MainReg d := mCore (Sum.inl 8)
abbrev mOldN     {d : ℕ} : MainReg d := mCore (Sum.inl 9)
abbrev mCnt1     {d : ℕ} : MainReg d := mCore (Sum.inl 10)
abbrev mCond1    {d : ℕ} : MainReg d := mCore (Sum.inl 11)
abbrev mCnt2     {d : ℕ} : MainReg d := mCore (Sum.inl 12)
abbrev mCond2    {d : ℕ} : MainReg d := mCore (Sum.inl 13)
abbrev mCnt3     {d : ℕ} : MainReg d := mCore (Sum.inl 14)
abbrev mCond3    {d : ℕ} : MainReg d := mCore (Sum.inl 15)
abbrev mCnt4     {d : ℕ} : MainReg d := mCore (Sum.inl 16)
abbrev mCond4    {d : ℕ} : MainReg d := mCore (Sum.inl 17)
abbrev mIsNew    {d : ℕ} : MainReg d := mCore (Sum.inl 18)
abbrev mAcc      {d : ℕ} : MainReg d := mCore (Sum.inl 19)
abbrev mValA     {d : ℕ} : MainReg d := mCore (Sum.inl 20)
abbrev mValB     {d : ℕ} : MainReg d := mCore (Sum.inl 21)
abbrev mAddr     {d : ℕ} : MainReg d := mCore (Sum.inl 22)
abbrev mScratch  {d : ℕ} : MainReg d := mCore (Sum.inl 23)

abbrev mU    {d : ℕ} (l : Fin d) : MainReg d := mCore (Sum.inr (0, l))
abbrev mP    {d : ℕ} (l : Fin d) : MainReg d := mCore (Sum.inr (1, l))
abbrev mVecA {d : ℕ} (l : Fin d) : MainReg d := mCore (Sum.inr (2, l))
abbrev mVecB {d : ℕ} (l : Fin d) : MainReg d := mCore (Sum.inr (3, l))

theorem mainQr_injective (d : ℕ) : Function.Injective (mainQr (d := d)) := by
  intro i j h; simpa using h

theorem mU_injective (d : ℕ) : Function.Injective (mU (d := d)) := by
  intro i j h; simpa using h

theorem mP_injective (d : ℕ) : Function.Injective (mP (d := d)) := by
  intro i j h; simpa using h

theorem mVecA_injective (d : ℕ) : Function.Injective (mVecA (d := d)) := by
  intro i j h; simpa using h

theorem mVecB_injective (d : ℕ) : Function.Injective (mVecB (d := d)) := by
  intro i j h; simpa using h

def embBfs {d : ℕ} (x : Bfs.CramerReg d) : MainReg d :=
  match x with
  | Sum.inr (Sum.inl (j, l)) =>
    if j = 0 then Sum.inl l else Sum.inr (Sum.inr (Sum.inl (Sum.inr (Sum.inl (j, l)))))
  | y => Sum.inr (Sum.inr (Sum.inl y))

def embFacet {d : ℕ} (x : Facet.FacetReg d) : MainReg d :=
  match x with
  | Sum.inr (Sum.inl (j, l)) =>
    if j = 0 then Sum.inl l else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, l)))))
  | y => Sum.inr (Sum.inr (Sum.inr y))

theorem embBfs_injective (d : ℕ) : Function.Injective (embBfs (d := d)) := by
  intro x₁ x₂ h
  rcases x₁ with a₁ | (⟨j₁, l₁⟩ | b₁) <;> rcases x₂ with a₂ | (⟨j₂, l₂⟩ | b₂) <;>
    dsimp [embBfs] at h <;> (try split_ifs at h) <;> simp_all

theorem embFacet_injective (d : ℕ) : Function.Injective (embFacet (d := d)) := by
  intro x₁ x₂ h
  rcases x₁ with a₁ | (⟨j₁, l₁⟩ | b₁) <;> rcases x₂ with a₂ | (⟨j₂, l₂⟩ | b₂) <;>
    dsimp [embFacet] at h <;> (try split_ifs at h) <;> simp_all

theorem embBfs_qr (d : ℕ) : embBfs ∘ (Bfs.rQr (d := d)) = mainQr := by
  funext l; rfl

theorem embFacet_qr (d : ℕ) : embFacet ∘ (Facet.fQr (d := d)) = mainQr := by
  funext l; rfl

theorem embBfs_ne_mCore {d : ℕ} (x : Bfs.CramerReg d) (c : MainCore d) :
    embBfs x ≠ mCore c := by
  rcases x with a | (⟨j, l⟩ | b) <;> dsimp [embBfs, mCore] <;> (try split_ifs) <;> simp

theorem embFacet_ne_mCore {d : ℕ} (x : Facet.FacetReg d) (c : MainCore d) :
    embFacet x ≠ mCore c := by
  rcases x with a | (⟨j, l⟩ | b) <;> dsimp [embFacet, mCore] <;> (try split_ifs) <;> simp

/-! ### Subroutine wrappers into `MainReg d` -/

noncomputable def callRecSearch (d : ℕ) : Stmt (MainReg d) :=
  .seq (.par [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)])
    (.seq ((Bfs.recSearch d).map embBfs)
      (.seq (Stmt.assign mTmp (PExpr.reg (embBfs Bfs.rFound)))
        (Stmt.vset mU fun l => PExpr.reg (embBfs (Bfs.rU l)))))

theorem callRecSearch_spec {d k V : ℕ} (hd : 0 < d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (st : RS (MainReg d))
    (hmem : st.mem = mem₀) (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (callRecSearch d) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      (∀ c : MainCore d, c ≠ Sum.inl 5 → (∀ l, c ≠ Sum.inr (0, l)) →
        st'.regs (mCore c) = st.regs (mCore c)) ∧
      ((st'.regs mTmp = 1 ∧
          IsCramerBFS (recAlpha a) (recBeta k d) (fun l => st'.regs (mU l)) ∧
          (fun l => st'.regs (mU l)) ≠ 0) ∨
       (st'.regs mTmp = 0 ∧
          ∀ u, IsCramerBFS (recAlpha a) (recBeta k d) u → u = 0)) := by
  have ep := Stmt.Exec.par (oracle := oracle) (qr := mainQr)
    [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)] st
  let st₁ : RS (MainReg d) :=
    ⟨parUpd st.regs [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)] st.regs,
     st.mem, st.queries⟩
  have hpr1 : ∀ c : MainCore d, st₁.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₁, parUpd, Function.update_of_ne (embBfs_ne_mCore Bfs.rV c).symm,
      Function.update_of_ne (embBfs_ne_mCore Bfs.rK c).symm]
  let s₀ : RS (Bfs.CramerReg d) := ⟨st₁.regs ∘ embBfs, st.mem, st.queries⟩
  have hs0_k : s₀.regs Bfs.rK = (k : ℝ) := by
    change st₁.regs (embBfs Bfs.rK) = (k : ℝ)
    simp only [st₁, parUpd, PExpr.eval_reg]
    have hne : embBfs (d := d) Bfs.rK ≠ embBfs Bfs.rV :=
      fun e => by have := embBfs_injective d e; simp at this
    rw [Function.update_of_ne hne, Function.update_self, hK]
  have hs0_v : s₀.regs Bfs.rV = (V : ℝ) := by
    change st₁.regs (embBfs Bfs.rV) = (V : ℝ)
    simp [st₁, parUpd, hV]
  obtain ⟨s', es', hsm, hsq, _, _, hres⟩ :=
    Bfs.recSearch_spec hd (oracle := oracle) mem₀ a ha_mem s₀ hmem hs0_k hs0_v
  have emap := Stmt.Exec.map (embBfs_injective d) (Bfs.rQr_injective d) es' st₁.regs rfl
  rw [embBfs_qr d] at emap
  let st₂ : RS (MainReg d) := ⟨Function.extend embBfs s'.regs st₁.regs, s'.mem, s'.queries⟩
  have hpr2 : ∀ c : MainCore d, st₂.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₂]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; exact embBfs_ne_mCore x c hx), hpr1 c]
  have hfnd2 : st₂.regs (embBfs Bfs.rFound) = s'.regs Bfs.rFound := by
    simp only [st₂]; exact (embBfs_injective d).extend_apply _ _ _
  have hu2 : ∀ l : Fin d, st₂.regs (embBfs (Bfs.rU l)) = s'.regs (Bfs.rU l) := by
    intro l; simp only [st₂]; exact (embBfs_injective d).extend_apply _ _ _
  have etmp := Stmt.Exec.assign (oracle := oracle) (qr := mainQr) mTmp
    (PExpr.reg (embBfs Bfs.rFound)) st₂
  let st₃ : RS (MainReg d) :=
    ⟨Function.update st₂.regs mTmp (st₂.regs (embBfs Bfs.rFound)), st₂.mem, st₂.queries⟩
  have eu := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mU_injective d)
    (fun l => PExpr.reg (embBfs (Bfs.rU l))) st₃
  let st₄ : RS (MainReg d) :=
    ⟨Function.extend mU (fun l => st₃.regs (embBfs (Bfs.rU l))) st₃.regs, st₃.mem, st₃.queries⟩
  have htmp4 : st₄.regs mTmp = s'.regs Bfs.rFound := by
    simp only [st₄]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
    simp [st₃, hfnd2]
  have hu4 : (fun l => st₄.regs (mU l)) = fun l => s'.regs (Bfs.rU l) := by
    funext l
    simp only [st₄]
    rw [(mU_injective d).extend_apply]
    simp only [st₃, Function.update_of_ne (embBfs_ne_mCore (Bfs.rU l) (Sum.inl 5)), hu2 l]
  refine ⟨st₄, Stmt.Exec.seq ep (Stmt.Exec.seq emap (Stmt.Exec.seq etmp eu)),
    hsm, hsq, ?_, ?_⟩
  · intro c hc1 hc2
    simp only [st₄]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; simp at he; exact hc2 l he.symm)]
    have hne : mCore c ≠ mTmp := fun e => hc1 (by simpa using e)
    simp only [st₃, Function.update_of_ne hne, hpr2 c]
  · rw [htmp4, hu4]
    exact hres

noncomputable def callOuterSearch (d : ℕ) : Stmt (MainReg d) :=
  .seq (.par [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)])
    (.seq ((Bfs.outerSearch d).map embBfs)
      (.seq (Stmt.assign mTmp (PExpr.reg (embBfs Bfs.rFound)))
        (Stmt.vset mU fun l => PExpr.reg (embBfs (Bfs.rU l)))))

theorem callOuterSearch_spec {d k V : ℕ} (hd : 0 < d)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (hv_mem : ∀ (c : Fin V) (l : Fin d), mem₀ ((2 * c.val + 1) * d + l.val) = vVec c l)
    (st : RS (MainReg d))
    (hmem : st.mem = mem₀) (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (callOuterSearch d) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      (∀ c : MainCore d, c ≠ Sum.inl 5 → (∀ l, c ≠ Sum.inr (0, l)) →
        st'.regs (mCore c) = st.regs (mCore c)) ∧
      ((st'.regs mTmp = 1 ∧
          IsCramerBFS a (fun _ => 1) (fun l => st'.regs (mU l)) ∧
          ∀ c : Fin V, (fun l => st'.regs (mU l)) ≠ vVec c) ∨
       (st'.regs mTmp = 0 ∧
          ∀ u, IsCramerBFS a (fun _ => 1) u → ∃ c : Fin V, u = vVec c)) := by
  have ep := Stmt.Exec.par (oracle := oracle) (qr := mainQr)
    [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)] st
  let st₁ : RS (MainReg d) :=
    ⟨parUpd st.regs [(embBfs Bfs.rK, PExpr.reg mK), (embBfs Bfs.rV, PExpr.reg mV)] st.regs,
     st.mem, st.queries⟩
  have hpr1 : ∀ c : MainCore d, st₁.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₁, parUpd, Function.update_of_ne (embBfs_ne_mCore Bfs.rV c).symm,
      Function.update_of_ne (embBfs_ne_mCore Bfs.rK c).symm]
  let s₀ : RS (Bfs.CramerReg d) := ⟨st₁.regs ∘ embBfs, st.mem, st.queries⟩
  have hs0_k : s₀.regs Bfs.rK = (k : ℝ) := by
    change st₁.regs (embBfs Bfs.rK) = (k : ℝ)
    simp only [st₁, parUpd, PExpr.eval_reg]
    have hne : embBfs (d := d) Bfs.rK ≠ embBfs Bfs.rV :=
      fun e => by have := embBfs_injective d e; simp at this
    rw [Function.update_of_ne hne, Function.update_self, hK]
  have hs0_v : s₀.regs Bfs.rV = (V : ℝ) := by
    change st₁.regs (embBfs Bfs.rV) = (V : ℝ)
    simp [st₁, parUpd, hV]
  obtain ⟨s', es', hsm, hsq, _, _, hres⟩ :=
    Bfs.outerSearch_spec hd (oracle := oracle) mem₀ a vVec ha_mem hv_mem s₀ hmem hs0_k hs0_v
  have emap := Stmt.Exec.map (embBfs_injective d) (Bfs.rQr_injective d) es' st₁.regs rfl
  rw [embBfs_qr d] at emap
  let st₂ : RS (MainReg d) := ⟨Function.extend embBfs s'.regs st₁.regs, s'.mem, s'.queries⟩
  have hpr2 : ∀ c : MainCore d, st₂.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₂]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; exact embBfs_ne_mCore x c hx), hpr1 c]
  have hfnd2 : st₂.regs (embBfs Bfs.rFound) = s'.regs Bfs.rFound := by
    simp only [st₂]; exact (embBfs_injective d).extend_apply _ _ _
  have hu2 : ∀ l : Fin d, st₂.regs (embBfs (Bfs.rU l)) = s'.regs (Bfs.rU l) := by
    intro l; simp only [st₂]; exact (embBfs_injective d).extend_apply _ _ _
  have etmp := Stmt.Exec.assign (oracle := oracle) (qr := mainQr) mTmp
    (PExpr.reg (embBfs Bfs.rFound)) st₂
  let st₃ : RS (MainReg d) :=
    ⟨Function.update st₂.regs mTmp (st₂.regs (embBfs Bfs.rFound)), st₂.mem, st₂.queries⟩
  have eu := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mU_injective d)
    (fun l => PExpr.reg (embBfs (Bfs.rU l))) st₃
  let st₄ : RS (MainReg d) :=
    ⟨Function.extend mU (fun l => st₃.regs (embBfs (Bfs.rU l))) st₃.regs, st₃.mem, st₃.queries⟩
  have htmp4 : st₄.regs mTmp = s'.regs Bfs.rFound := by
    simp only [st₄]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, he⟩; simp at he)]
    simp [st₃, hfnd2]
  have hu4 : (fun l => st₄.regs (mU l)) = fun l => s'.regs (Bfs.rU l) := by
    funext l
    simp only [st₄]
    rw [(mU_injective d).extend_apply]
    simp only [st₃, Function.update_of_ne (embBfs_ne_mCore (Bfs.rU l) (Sum.inl 5)), hu2 l]
  refine ⟨st₄, Stmt.Exec.seq ep (Stmt.Exec.seq emap (Stmt.Exec.seq etmp eu)),
    hsm, hsq, ?_, ?_⟩
  · intro c hc1 hc2
    simp only [st₄]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨l, he⟩; simp at he; exact hc2 l he.symm)]
    have hne : mCore c ≠ mTmp := fun e => hc1 (by simpa using e)
    simp only [st₃, Function.update_of_ne hne, hpr2 c]
  · rw [htmp4, hu4]
    exact hres

noncomputable def callFacetFind (d : ℕ) (hd : 2 ≤ d) : Stmt (MainReg d) :=
  .seq (Stmt.assign (embFacet Facet.fK) (PExpr.reg mK))
    (.seq (Stmt.vset (fun l => embFacet (Facet.fP l)) fun l => PExpr.reg (mP l))
      (.seq ((Facet.facetFind d hd).map embFacet)
        (Stmt.vset mVecA fun l => PExpr.reg (embFacet (Facet.fOut l)))))

theorem callFacetFind_spec {d m k : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (mem₀ : ℕ → ℝ) (a : Fin k → Fin d → ℝ)
    (emb : Fin k → Fin m) (hemb_inj : Function.Injective emb)
    (ha_emb : ∀ (j : Fin k) (x : Fin d → ℝ), dot (a j) x = L (emb j) x)
    (ha_mem : ∀ (j : Fin k) (l : Fin d), mem₀ ((2 * j.val) * d + l.val) = a j l)
    (st : RS (MainReg d))
    (hmem : st.mem = mem₀) (hK : st.regs mK = (k : ℝ))
    (hp_front : (fun l => st.regs (mP l)) ∈ frontier P)
    (hp_known : ∀ j : Fin k, dot (a j) (fun l => st.regs (mP l)) < 1) :
    ∃ st', Stmt.Exec oracle mainQr (callFacetFind d hd) st st' ∧
      st'.mem = st.mem ∧
      st'.queries ≤ st.queries + (d - 1) * (2 * (m - k) + 2) ∧
      (∀ c : MainCore d, (∀ l, c ≠ Sum.inr (2, l)) → st'.regs (mCore c) = st.regs (mCore c)) ∧
      ∃ i_new : Fin m,
        (∀ j : Fin k, i_new ≠ emb j) ∧
        (∀ x, dot (fun l => st'.regs (mVecA l)) x = L i_new x) := by
  have ek := Stmt.Exec.assign (oracle := oracle) (qr := mainQr) (embFacet Facet.fK)
    (PExpr.reg mK) st
  let st₁ : RS (MainReg d) :=
    ⟨Function.update st.regs (embFacet Facet.fK) (st.regs mK), st.mem, st.queries⟩
  have hfp_inj : Function.Injective (fun l : Fin d => embFacet (Facet.fP l)) :=
    (embFacet_injective d).comp (fun _ _ h => by simpa using h)
  have ep := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) hfp_inj
    (fun l => PExpr.reg (mP l)) st₁
  let st₂ : RS (MainReg d) :=
    ⟨Function.extend (fun l => embFacet (Facet.fP l)) (fun l => st₁.regs (mP l)) st₁.regs,
     st₁.mem, st₁.queries⟩
  have hpr2 : ∀ c : MainCore d, st₂.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₂]
    rw [Function.extend_apply' _ _ _
      (by rintro ⟨l, hl⟩; exact embFacet_ne_mCore (Facet.fP l) c hl)]
    simp only [st₁, Function.update_of_ne (embFacet_ne_mCore Facet.fK c).symm]
  let s₀ : RS (Facet.FacetReg d) := ⟨st₂.regs ∘ embFacet, st.mem, st.queries⟩
  have hs0_k : s₀.regs Facet.fK = (k : ℝ) := by
    change st₂.regs (embFacet Facet.fK) = (k : ℝ)
    simp only [st₂]
    rw [Function.extend_apply' _ _ _ (by
      rintro ⟨l, hl⟩
      have := embFacet_injective d hl
      simp at this)]
    simp [st₁, hK]
  have hs0_p : (fun l => s₀.regs (Facet.fP l)) = fun l => st.regs (mP l) := by
    funext l
    change st₂.regs (embFacet (Facet.fP l)) = st.regs (mP l)
    simp only [st₂]
    rw [hfp_inj.extend_apply]
    simp only [st₁, Function.update_of_ne (embFacet_ne_mCore Facet.fK (Sum.inr (1, l))).symm]
  obtain ⟨s', es', hsm, hsq, _, i_new, hinew, hdot, _⟩ :=
    Facet.facetFind_spec hd L hP horacle mem₀ a emb hemb_inj ha_emb ha_mem s₀ hmem hs0_k
      (by rw [hs0_p]; exact hp_front) (by rw [hs0_p]; exact hp_known)
  have emap := Stmt.Exec.map (embFacet_injective d) (Facet.fQr_injective d) es' st₂.regs rfl
  rw [embFacet_qr d] at emap
  let st₃ : RS (MainReg d) := ⟨Function.extend embFacet s'.regs st₂.regs, s'.mem, s'.queries⟩
  have hpr3 : ∀ c : MainCore d, st₃.regs (mCore c) = st.regs (mCore c) := by
    intro c
    simp only [st₃]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; exact embFacet_ne_mCore x c hx), hpr2 c]
  have hout3 : ∀ l : Fin d, st₃.regs (embFacet (Facet.fOut l)) = s'.regs (Facet.fOut l) := by
    intro l; simp only [st₃]; exact (embFacet_injective d).extend_apply _ _ _
  have ev := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mVecA_injective d)
    (fun l => PExpr.reg (embFacet (Facet.fOut l))) st₃
  let st₄ : RS (MainReg d) :=
    ⟨Function.extend mVecA (fun l => st₃.regs (embFacet (Facet.fOut l))) st₃.regs,
     st₃.mem, st₃.queries⟩
  have hout4 : (fun l => st₄.regs (mVecA l)) = fun l => s'.regs (Facet.fOut l) := by
    funext l
    simp only [st₄]
    rw [(mVecA_injective d).extend_apply, hout3 l]
  refine ⟨st₄, Stmt.Exec.seq ek (Stmt.Exec.seq ep (Stmt.Exec.seq emap ev)),
    hsm, hsq, ?_, i_new, hinew, ?_⟩
  · intro c hc
    simp only [st₄]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨l, hl⟩; simp at hl; exact hc l hl.symm), hpr3 c]
  · rw [hout4]; exact hdot

/-! ### Discovering and storing one new facet -/

noncomputable def discoverAndStoreFacet (d : ℕ) (hd : 2 ≤ d) : Stmt (MainReg d) :=
  .seq (callFacetFind d hd)
    (.seq
      (Stmt.storeFam mVecA mIx fun l =>
        (PExpr.const 2 * PExpr.reg mK) * PExpr.nat d + PExpr.nat l.val)
      (Stmt.assign mK (PExpr.reg mK + PExpr.const 1)))

theorem discoverAndStoreFacet_spec {d m k V : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (emb : Fin k → Fin m) (hemb_inj : Function.Injective emb)
    (ha_emb : ∀ (j : Fin k) (x : Fin d → ℝ), dot (a j) x = L (emb j) x)
    (st : RS (MainReg d))
    (ha_mem : ∀ (j : Fin k) (l : Fin d), st.mem ((2 * j.val) * d + l.val) = a j l)
    (hv_mem : ∀ (c : Fin V) (l : Fin d), st.mem ((2 * c.val + 1) * d + l.val) = vVec c l)
    (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ)) (hAct : st.regs mActive = 1)
    (hp_front : (fun l => st.regs (mP l)) ∈ frontier P)
    (hp_known : ∀ j : Fin k, dot (a j) (fun l => st.regs (mP l)) < 1) :
    ∃ (st' : RS (MainReg d)) (a' : Fin (k + 1) → Fin d → ℝ) (emb' : Fin (k + 1) → Fin m),
      Stmt.Exec oracle mainQr (discoverAndStoreFacet d hd) st st' ∧
      Function.Injective emb' ∧
      k + 1 ≤ m ∧
      (∀ (j : Fin (k + 1)) (x : Fin d → ℝ), dot (a' j) x = L (emb' j) x) ∧
      (∀ (j : Fin (k + 1)) (l : Fin d), st'.mem ((2 * j.val) * d + l.val) = a' j l) ∧
      (∀ (c : Fin V) (l : Fin d), st'.mem ((2 * c.val + 1) * d + l.val) = vVec c l) ∧
      st'.regs mK = ((k + 1 : ℕ) : ℝ) ∧
      st'.regs mV = (V : ℝ) ∧
      st'.regs mActive = 1 ∧
      st'.queries ≤ st.queries + (d - 1) * (2 * (m - k) + 2) := by
  obtain ⟨st₁, eff, hm1, hq1, hpr1, i_new, hinew, hdot⟩ :=
    callFacetFind_spec hd L hP horacle st.mem a emb hemb_inj ha_emb ha_mem st rfl hK
      hp_front hp_known
  have hK1 : st₁.regs mK = (k : ℝ) := (hpr1 (Sum.inl 0) (fun _ => by simp)).trans hK
  have hV1 : st₁.regs mV = (V : ℝ) := (hpr1 (Sum.inl 1) (fun _ => by simp)).trans hV
  have hAct1 : st₁.regs mActive = 1 := (hpr1 (Sum.inl 2) (fun _ => by simp)).trans hAct
  obtain ⟨st₂, estore, hmem_new, hmem_other, hreg2, hq2⟩ :=
    Stmt.Exec.storeFam (oracle := oracle) (qr := mainQr) (ix := mIx) mVecA
      (fun _ => by simp)
      (fun l => (PExpr.const 2 * PExpr.reg mK) * PExpr.nat d + PExpr.nat l.val)
      st₁ (fun l => (2 * k) * d + l.val)
      (fun l₁ l₂ h => Fin.ext (by dsimp at h; omega))
      (by
        intro l regs' hreg
        have hk' : regs' mK = (k : ℝ) := (hreg mK (by simp)).trans hK1
        simp [hk'])
  have ek_inc := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mK
    (PExpr.reg mK + PExpr.const 1) st₂ ((k + 1 : ℕ) : ℝ)
    (by
      have hk2 : st₂.regs mK = (k : ℝ) := (hreg2 mK (by simp)).trans hK1
      simp [hk2])
  let st₃ : RS (MainReg d) := ⟨Function.update st₂.regs mK ((k + 1 : ℕ) : ℝ), st₂.mem, st₂.queries⟩
  let a_new : Fin d → ℝ := fun l => st₁.regs (mVecA l)
  let a' := snocVec a a_new
  let emb' := snocVec emb i_new
  have hemb'_inj : Function.Injective emb' := snocVec_injective hemb_inj hinew
  have hk1_le : k + 1 ≤ m := by simpa using Fintype.card_le_of_injective emb' hemb'_inj
  refine ⟨st₃, a', emb',
    Stmt.Exec.seq eff (Stmt.Exec.seq estore ek_inc),
    hemb'_inj, hk1_le, ?_, ?_, ?_,
    by simp [st₃],
    by simp only [st₃, Function.update_of_ne (by simp : mV ≠ mK)]; exact (hreg2 mV (by simp)).trans hV1,
    by simp only [st₃, Function.update_of_ne (by simp : mActive ≠ mK)]; exact (hreg2 mActive (by simp)).trans hAct1,
    by rw [hq2]; exact hq1⟩
  · intro j x
    dsimp only [a', emb']
    by_cases hj : j.val < k
    · rw [snocVec_lt _ _ j hj, snocVec_lt _ _ j hj]
      exact ha_emb ⟨j.val, hj⟩ x
    · have hje : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
      rw [hje, snocVec_last, snocVec_last]
      exact hdot x
  · intro j l
    change st₂.mem _ = _
    dsimp only [a']
    by_cases hj : j.val < k
    · rw [snocVec_lt _ _ j hj, hmem_other _ (fun l' => by have := l.isLt; have := l'.isLt; nlinarith),
        hm1, ha_mem ⟨j.val, hj⟩ l]
    · have hje : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
      rw [hje, snocVec_last]
      exact hmem_new l
  · intro c l
    change st₂.mem _ = _
    rw [hmem_other _ (fun l' heq => by have := (mul_add_inj l.isLt l'.isLt heq).1; omega), hm1, hv_mem c l]

/-! ### Main discovery loop -/

noncomputable def discoveryBody (d : ℕ) (hd : 2 ≤ d) : Stmt (MainReg d) :=
  .seq (callRecSearch d)
    (.ite mTmp .skip
      -- mTmp = 0: recession cone is {0}; run outerSearch
      (.seq (callOuterSearch d)
        (.ite mTmp .skip
          -- mTmp = 0: outer polytope = P and vertices complete!
          (Stmt.assign mActive (PExpr.const 0))
          -- mTmp > 0: query candidate vertex u
          (.seq (Stmt.vset mainQr fun l => PExpr.reg (mU l))
            (.seq .query
              (.seq (Stmt.vset mP fun l => PExpr.reg (mainQr l))
                (.seq
                  (Stmt.assign mTmp
                    (PExpr.dot (fun l => PExpr.reg (mP l) - PExpr.reg (mU l))
                      (fun l => PExpr.reg (mP l) - PExpr.reg (mU l))))
                  (.ite mTmp .skip
                    -- p = u: certify vertex u at slot V
                    (.seq
                      (Stmt.storeFam mU mIx fun l =>
                        (PExpr.const 2 * PExpr.reg mV + PExpr.const 1) * PExpr.nat d +
                          PExpr.nat l.val)
                      (Stmt.assign mV (PExpr.reg mV + PExpr.const 1)))
                    -- p ≠ u: discover and store new facet from p
                    (discoverAndStoreFacet d hd))))))))
      -- mTmp > 0: query recession ray u and discover new facet
      (.seq (Stmt.vset mainQr fun l => PExpr.reg (mU l))
        (.seq .query
          (.seq (Stmt.vset mP fun l => PExpr.reg (mainQr l))
            (discoverAndStoreFacet d hd)))))

noncomputable def discoveryLoop (d : ℕ) (hd : 2 ≤ d) : Stmt (MainReg d) :=
  .seq
    (.par [(mK, PExpr.const 0), (mV, PExpr.const 0), (mActive, PExpr.const 1)])
    (.while mActive (discoveryBody d hd))

theorem discoveryLoop_spec {d m : ℕ} (hd : 2 ≤ d) {P : Set (Fin d → ℝ)}
    (hPpoly : IsDPolytope P) (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP : P = { x | ∀ i, L i x ≤ 1 })
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (st₀ : RS (MainReg d)) (hq₀ : st₀.queries = 0) :
    ∃ (st' : RS (MainReg d)) (k V : ℕ)
      (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ),
      Stmt.Exec oracle mainQr (discoveryLoop d hd) st₀ st' ∧
      k ≤ m ∧ 0 < V ∧ V ≤ faceCount P 0 ∧
      Function.Injective vVec ∧
      { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } = P ∧
      Set.range vVec = { x : Fin d → ℝ | IsExposed ℝ P {x} } ∧
      (∀ (j : Fin k) (l : Fin d), st'.mem ((2 * j.val) * d + l.val) = a j l) ∧
      (∀ (c : Fin V) (l : Fin d), st'.mem ((2 * c.val + 1) * d + l.val) = vVec c l) ∧
      st'.regs mK = (k : ℝ) ∧ st'.regs mV = (V : ℝ) ∧
      st'.queries ≤ V + ∑ s ∈ Finset.range k, (1 + (d - 1) * (2 * (m - s) + 2)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨hVfin, _⟩ := polytope_face_eq_convexHull_exposed_vertices d P hPpoly
  have hinv0 :=
    ((ray_oracle_outer_polytope_invariants_and_phased_trace_bound d hd).1
      hPpoly hzero L hP horacle).1
  have hf0_card : faceCount P 0 = hVfin.toFinset.card := by
    rw [hinv0.2, hinv0.1, Set.ncard_eq_toFinset_card _ hVfin]
  have hv_le_of_inj : ∀ {V' : ℕ} (v' : Fin V' → Fin d → ℝ),
      Function.Injective v' → (∀ c, IsExposed ℝ P {v' c}) → V' ≤ faceCount P 0 := by
    intro V' v' hinj hexp
    rw [hf0_card]
    have hsub : Finset.univ.image v' ⊆ hVfin.toFinset := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
      exact hVfin.mem_toFinset.2 (hexp c)
    have hcard : (Finset.univ.image v').card = V' := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    rw [← hcard]
    exact Finset.card_le_card hsub
  -- Initial par assignment
  have einit := Stmt.Exec.par (oracle := oracle) (qr := mainQr)
    [(mK, PExpr.const 0), (mV, PExpr.const 0), (mActive, PExpr.const 1)] st₀
  let st_init : RS (MainReg d) :=
    ⟨parUpd st₀.regs [(mK, PExpr.const 0), (mV, PExpr.const 0), (mActive, PExpr.const 1)] st₀.regs,
     st₀.mem, st₀.queries⟩
  let Inv : RS (MainReg d) → Prop := fun st =>
    ∃ (k V : ℕ) (a : Fin k → Fin d → ℝ) (emb : Fin k → Fin m) (vVec : Fin V → Fin d → ℝ),
      Function.Injective emb ∧
      k ≤ m ∧
      Function.Injective vVec ∧
      (∀ c : Fin V, IsExposed ℝ P {vVec c}) ∧
      V ≤ faceCount P 0 ∧
      (∀ (j : Fin k) (x : Fin d → ℝ), dot (a j) x = L (emb j) x) ∧
      (∀ (j : Fin k) (l : Fin d), st.mem ((2 * j.val) * d + l.val) = a j l) ∧
      (∀ (c : Fin V) (l : Fin d), st.mem ((2 * c.val + 1) * d + l.val) = vVec c l) ∧
      st.regs mK = (k : ℝ) ∧
      st.regs mV = (V : ℝ) ∧
      st.queries ≤ V + ∑ s ∈ Finset.range k, (1 + (d - 1) * (2 * (m - s) + 2)) ∧
      (st.regs mActive = 1 ∨
        (st.regs mActive = 0 ∧ 0 < V ∧
          { x : Fin d → ℝ | ∀ j : Fin k, dot (a j) x ≤ 1 } = P ∧
          Set.range vVec = { x : Fin d → ℝ | IsExposed ℝ P {x} }))
  let μ : RS (MainReg d) → ℕ := fun st =>
    (m - natOfReal (st.regs mK)) + (faceCount P 0 - natOfReal (st.regs mV)) +
      if st.regs mActive = 0 then 0 else 1
  have hInv_init : Inv st_init := by
    refine ⟨0, 0, Fin.elim0, Fin.elim0, Fin.elim0,
      fun i => Fin.elim0 i, Nat.zero_le _, fun i => Fin.elim0 i,
      fun c => Fin.elim0 c, Nat.zero_le _,
      fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun c => Fin.elim0 c,
      ?_, ?_, ?_, Or.inl ?_⟩
    · simp only [st_init, parUpd, PExpr.eval_const]
      rw [Function.update_of_ne (by simp : mK ≠ mActive),
        Function.update_of_ne (by simp : mK ≠ mV), Function.update_self]
      norm_num
    · simp only [st_init, parUpd, PExpr.eval_const]
      rw [Function.update_of_ne (by simp : mV ≠ mActive), Function.update_self]
      norm_num
    · change st₀.queries ≤ _
      simp [hq₀]
    · simp [st_init, parUpd]
  obtain ⟨st_end, ewhile, hInv_end, hAct_zero⟩ :=
    Stmt.Exec.while_inv (oracle := oracle) (qr := mainQr) (body := discoveryBody d hd) Inv μ
      (by
        intro st hIs hAct_ne
        obtain ⟨k, V, a, emb, vVec, hemb_inj, hk_le, hv_inj, hv_exp, hV_le,
          ha_emb, ha_mem, hv_mem, hK, hV, hq, hAct_or⟩ := hIs
        have hAct1 : st.regs mActive = 1 := by
          rcases hAct_or with h1 | ⟨h0, _⟩
          · exact h1
          · exact False.elim (hAct_ne h0)
        have hμ_st : μ st = (m - k) + (faceCount P 0 - V) + 1 := by
          simp [μ, hK, hV, hAct1]
        -- Step 1: callRecSearch
        obtain ⟨st₁, erec, hm1, hq1, hpr1, hrec_res⟩ :=
          callRecSearch_spec (oracle := oracle) hd0 st.mem a ha_mem st rfl hK hV
        have hK1 : st₁.regs mK = (k : ℝ) :=
          (hpr1 (Sum.inl 0) (by simp) (fun _ => by simp)).trans hK
        have hV1 : st₁.regs mV = (V : ℝ) :=
          (hpr1 (Sum.inl 1) (by simp) (fun _ => by simp)).trans hV
        have hAct_st1 : st₁.regs mActive = 1 :=
          (hpr1 (Sum.inl 2) (by simp) (fun _ => by simp)).trans hAct1
        rcases hrec_res with ⟨htmp1, hbfs_rec, hu_ne0⟩ | ⟨htmp0, hrec_all0⟩
        · -- Branch 1: nonzero recession BFS u
          have htpos : 0 < st₁.regs mTmp := by linarith
          let u := fun l => st₁.regs (mU l)
          have hnonpos : ∀ j : Fin k, dot (a j) u ≤ 0 :=
            rec_feasible_nonpos a hbfs_rec.1
          obtain ⟨hp_front, _, hp_known⟩ :=
            recession_trigger L hP horacle a hu_ne0 hnonpos
          have eqr := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mainQr_injective d)
            (fun l => PExpr.reg (mU l)) st₁
          let st₂ : RS (MainReg d) :=
            ⟨Function.extend mainQr u st₁.regs, st₁.mem, st₁.queries⟩
          have hqr2 : (fun l => st₂.regs (mainQr l)) = u := by
            funext l; simp only [st₂]; exact (mainQr_injective d).extend_apply _ _ _
          have equery := Stmt.Exec.query (oracle := oracle) (qr := mainQr) st₂
            (by rw [hqr2]; exact hu_ne0)
          let st₃ : RS (MainReg d) :=
            ⟨Function.extend mainQr (oracle (fun l => st₂.regs (mainQr l))) st₂.regs,
             st₂.mem, st₂.queries + 1⟩
          have ep := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mP_injective d)
            (fun l => PExpr.reg (mainQr l)) st₃
          let st₄ : RS (MainReg d) :=
            ⟨Function.extend mP (fun l => st₃.regs (mainQr l)) st₃.regs, st₃.mem, st₃.queries⟩
          have hp4 : (fun l => st₄.regs (mP l)) = oracle u := by
            funext l
            simp only [st₄]
            rw [(mP_injective d).extend_apply]
            simp only [st₃]
            rw [(mainQr_injective d).extend_apply, hqr2]
          have hpr4 : ∀ c : MainCore d, (∀ l, c ≠ Sum.inr (1, l)) →
              st₄.regs (mCore c) = st₁.regs (mCore c) := by
            intro c hc
            simp only [st₄, st₃, st₂]
            rw [Function.extend_apply' _ _ _ (by rintro ⟨l, hl⟩; simp at hl; exact hc l hl.symm),
              Function.extend_apply' _ _ _ (by rintro ⟨_, hl⟩; simp at hl),
              Function.extend_apply' _ _ _ (by rintro ⟨_, hl⟩; simp at hl)]
          have hK4 : st₄.regs mK = (k : ℝ) := (hpr4 (Sum.inl 0) (fun _ => by simp)).trans hK1
          have hV4 : st₄.regs mV = (V : ℝ) := (hpr4 (Sum.inl 1) (fun _ => by simp)).trans hV1
          have hAct4 : st₄.regs mActive = 1 := (hpr4 (Sum.inl 2) (fun _ => by simp)).trans hAct_st1
          obtain ⟨st₅, a', emb', edisc, hemb'_inj, hk1_le, ha'_emb, ha'_mem, hv'_mem,
            hK5, hV5, hAct5, hq5⟩ :=
            discoverAndStoreFacet_spec hd L hP horacle a vVec emb hemb_inj ha_emb st₄
              (by intro j l; change st₁.mem _ = _; rw [hm1]; exact ha_mem j l)
              (by intro c l; change st₁.mem _ = _; rw [hm1]; exact hv_mem c l)
              hK4 hV4 hAct4 (by rw [hp4]; exact hp_front) (by rw [hp4]; exact hp_known)
          refine ⟨st₅,
            Stmt.Exec.seq erec (Stmt.Exec.ite_pos htpos
              (Stmt.Exec.seq eqr (Stmt.Exec.seq equery (Stmt.Exec.seq ep edisc)))),
            ⟨k + 1, V, a', emb', vVec, hemb'_inj, hk1_le, hv_inj, hv_exp, hV_le,
              ha'_emb, ha'_mem, hv'_mem, hK5, hV5, ?_, Or.inl hAct5⟩,
            ?_⟩
          · rw [Finset.sum_range_succ]
            have hq4 : st₄.queries = st.queries + 1 := by change st₁.queries + 1 = _; rw [hq1]
            omega
          · rw [hμ_st]
            simp only [μ, hK5, hV5, hAct5, natOfReal_cast, one_ne_zero, ↓reduceIte]
            omega
        · -- Branch 2: recession cone is {0}; run callOuterSearch
          have hrec_cone0 : ∀ w, (∀ j : Fin k, dot (a j) w ≤ 0) → w = 0 :=
            recession_bfs_zero_imp_cone_zero a hrec_all0
          obtain ⟨st₂, eout, hm2, hq2, hpr2, hout_res⟩ :=
            callOuterSearch_spec (oracle := oracle) hd0 st₁.mem a vVec
              (by intro j l; rw [hm1]; exact ha_mem j l)
              (by intro c l; rw [hm1]; exact hv_mem c l)
              st₁ rfl hK1 hV1
          have hK2 : st₂.regs mK = (k : ℝ) :=
            (hpr2 (Sum.inl 0) (by simp) (fun _ => by simp)).trans hK1
          have hV2 : st₂.regs mV = (V : ℝ) :=
            (hpr2 (Sum.inl 1) (by simp) (fun _ => by simp)).trans hV1
          have hAct2 : st₂.regs mActive = 1 :=
            (hpr2 (Sum.inl 2) (by simp) (fun _ => by simp)).trans hAct_st1
          rcases hout_res with ⟨hout1, hbfs_out, hu_new⟩ | ⟨hout0, hbfs_covered⟩
          · -- Branch 2a: outer BFS u not in vVec
            have hopos : 0 < st₂.regs mTmp := by linarith
            let u := fun l => st₂.regs (mU l)
            have ha_ex : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x :=
              fun j => ⟨emb j, ha_emb j⟩
            obtain ⟨hu_ne0, hu_eq_imp, hu_ne_imp⟩ :=
              outer_bfs_dichotomy hd hPpoly hzero L hP horacle a ha_ex hbfs_out
            have eqr := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mainQr_injective d)
              (fun l => PExpr.reg (mU l)) st₂
            let st₃ : RS (MainReg d) :=
              ⟨Function.extend mainQr u st₂.regs, st₂.mem, st₂.queries⟩
            have hqr3 : (fun l => st₃.regs (mainQr l)) = u := by
              funext l; simp only [st₃]; exact (mainQr_injective d).extend_apply _ _ _
            have equery := Stmt.Exec.query (oracle := oracle) (qr := mainQr) st₃
              (by rw [hqr3]; exact hu_ne0)
            let st₄ : RS (MainReg d) :=
              ⟨Function.extend mainQr (oracle (fun l => st₃.regs (mainQr l))) st₃.regs,
               st₃.mem, st₃.queries + 1⟩
            have ep := Stmt.Exec.vset (oracle := oracle) (qr := mainQr) (mP_injective d)
              (fun l => PExpr.reg (mainQr l)) st₄
            let st₅ : RS (MainReg d) :=
              ⟨Function.extend mP (fun l => st₄.regs (mainQr l)) st₄.regs, st₄.mem, st₄.queries⟩
            have hp5 : (fun l => st₅.regs (mP l)) = oracle u := by
              funext l
              simp only [st₅]
              rw [(mP_injective d).extend_apply]
              simp only [st₄]
              rw [(mainQr_injective d).extend_apply, hqr3]
            have hpr5 : ∀ c : MainCore d, (∀ l, c ≠ Sum.inr (1, l)) →
                st₅.regs (mCore c) = st₂.regs (mCore c) := by
              intro c hc
              simp only [st₅, st₄, st₃]
              rw [Function.extend_apply' _ _ _ (by rintro ⟨l, hl⟩; simp at hl; exact hc l hl.symm),
                Function.extend_apply' _ _ _ (by rintro ⟨_, hl⟩; simp at hl),
                Function.extend_apply' _ _ _ (by rintro ⟨_, hl⟩; simp at hl)]
            have hu5 : (fun l => st₅.regs (mU l)) = u := by
              funext l; exact hpr5 (Sum.inr (0, l)) (fun _ => by simp)
            have ediff := Stmt.Exec.assign (oracle := oracle) (qr := mainQr) mTmp
              (PExpr.dot (fun l => PExpr.reg (mP l) - PExpr.reg (mU l))
                (fun l => PExpr.reg (mP l) - PExpr.reg (mU l))) st₅
            let st₆ : RS (MainReg d) :=
              ⟨Function.update st₅.regs mTmp (dot (oracle u - u) (oracle u - u)),
               st₅.mem, st₅.queries⟩
            have ediff' : Stmt.Exec oracle mainQr
                (Stmt.assign mTmp
                  (PExpr.dot (fun l => PExpr.reg (mP l) - PExpr.reg (mU l))
                    (fun l => PExpr.reg (mP l) - PExpr.reg (mU l)))) st₅ st₆ := by
              have hsub_eq : (fun l => st₅.regs (mP l) - st₅.regs (mU l)) = oracle u - u := by
                funext l; simp [congrFun hp5 l, congrFun hu5 l]
              simpa [st₆, hsub_eq] using ediff
            have hK6 : st₆.regs mK = (k : ℝ) := by
              simp only [st₆, Function.update_of_ne (by simp : mK ≠ mTmp)]
              exact (hpr5 (Sum.inl 0) (fun _ => by simp)).trans hK2
            have hV6 : st₆.regs mV = (V : ℝ) := by
              simp only [st₆, Function.update_of_ne (by simp : mV ≠ mTmp)]
              exact (hpr5 (Sum.inl 1) (fun _ => by simp)).trans hV2
            have hAct6 : st₆.regs mActive = 1 := by
              simp only [st₆, Function.update_of_ne (by simp : mActive ≠ mTmp)]
              exact (hpr5 (Sum.inl 2) (fun _ => by simp)).trans hAct2
            by_cases heq_ou : oracle u = u
            · -- Subbranch: oracle u = u -> certify vertex u
              have hdiff0 : st₆.regs mTmp = 0 := by simp [st₆, heq_ou]
              have hu_exp : IsExposed ℝ P {u} := (hu_eq_imp heq_ou).2
              have hu6 : ∀ l : Fin d, st₆.regs (mU l) = u l := by
                intro l
                simp only [st₆, Function.update_of_ne (by simp : mU l ≠ mTmp)]
                exact congrFun hu5 l
              obtain ⟨st₇, estore, hmem_v, hmem_other, hreg7, hq7⟩ :=
                Stmt.Exec.storeFam (oracle := oracle) (qr := mainQr) (ix := mIx) mU
                  (fun _ => by simp)
                  (fun l =>
                    (PExpr.const 2 * PExpr.reg mV + PExpr.const 1) * PExpr.nat d +
                      PExpr.nat l.val)
                  st₆ (fun l => (2 * V + 1) * d + l.val)
                  (fun l₁ l₂ h => Fin.ext (by dsimp at h; omega))
                  (by
                    intro l regs' hreg
                    have hv' : regs' mV = (V : ℝ) := (hreg mV (by simp)).trans hV6
                    simp [hv'])
              have ev_inc := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mV
                (PExpr.reg mV + PExpr.const 1) st₇ ((V + 1 : ℕ) : ℝ)
                (by
                  have hv7 : st₇.regs mV = (V : ℝ) := (hreg7 mV (by simp)).trans hV6
                  simp [hv7])
              let st₈ : RS (MainReg d) :=
                ⟨Function.update st₇.regs mV ((V + 1 : ℕ) : ℝ), st₇.mem, st₇.queries⟩
              let vVec' := snocVec vVec u
              have hv'_inj : Function.Injective vVec' := snocVec_injective hv_inj hu_new
              have hv'_exp : ∀ c : Fin (V + 1), IsExposed ℝ P {vVec' c} := by
                intro c
                dsimp only [vVec']
                by_cases hc : c.val < V
                · rw [snocVec_lt _ _ c hc]; exact hv_exp ⟨c.val, hc⟩
                · have hce : c = ⟨V, Nat.lt_succ_self V⟩ := Fin.ext (by dsimp; omega)
                  rw [hce, snocVec_last]; exact hu_exp
              have hV1_le : V + 1 ≤ faceCount P 0 := hv_le_of_inj vVec' hv'_inj hv'_exp
              have hK8 : st₈.regs mK = (k : ℝ) := by
                simp only [st₈, Function.update_of_ne (by simp : mK ≠ mV)]
                exact (hreg7 mK (by simp)).trans hK6
              have hV8 : st₈.regs mV = ((V + 1 : ℕ) : ℝ) := by simp [st₈]
              have hAct8 : st₈.regs mActive = 1 := by
                simp only [st₈, Function.update_of_ne (by simp : mActive ≠ mV)]
                exact (hreg7 mActive (by simp)).trans hAct6
              refine ⟨st₈,
                Stmt.Exec.seq erec (Stmt.Exec.ite_zero htmp0
                  (Stmt.Exec.seq eout (Stmt.Exec.ite_pos hopos
                    (Stmt.Exec.seq eqr (Stmt.Exec.seq equery
                      (Stmt.Exec.seq ep (Stmt.Exec.seq ediff'
                        (Stmt.Exec.ite_zero hdiff0 (Stmt.Exec.seq estore ev_inc))))))))),
                ⟨k, V + 1, a, emb, vVec', hemb_inj, hk_le, hv'_inj, hv'_exp, hV1_le,
                  ha_emb, ?_, ?_, hK8, hV8, ?_, Or.inl hAct8⟩,
                ?_⟩
              · intro j l
                change st₇.mem _ = _
                rw [hmem_other _ (fun l' heq => by have := (mul_add_inj l.isLt l'.isLt heq).1; omega)]
                change st₂.mem _ = _
                rw [hm2, hm1, ha_mem j l]
              · intro c l
                change st₇.mem _ = _
                dsimp only [vVec']
                by_cases hc : c.val < V
                · rw [snocVec_lt _ _ c hc,
                    hmem_other _ (fun l' => by have := l.isLt; have := l'.isLt; nlinarith)]
                  change st₂.mem _ = _
                  rw [hm2, hm1, hv_mem ⟨c.val, hc⟩ l]
                · have hce : c = ⟨V, Nat.lt_succ_self V⟩ := Fin.ext (by dsimp; omega)
                  rw [hce, snocVec_last, hmem_v l, hu6 l]
              · change st₇.queries ≤ _
                rw [hq7]; change st₂.queries + 1 ≤ _; rw [hq2, hq1]; omega
              · rw [hμ_st]
                simp only [μ, hK8, hV8, hAct8, natOfReal_cast, one_ne_zero, ↓reduceIte]
                omega
            · -- Subbranch: oracle u ≠ u -> discover and store new facet
              have hdiff_pos : 0 < st₆.regs mTmp := by
                simp only [st₆, Function.update_self]
                exact dot_self_pos (sub_ne_zero.2 heq_ou)
              obtain ⟨hp_front, _, hp_known⟩ := hu_ne_imp heq_ou
              have hp6 : (fun l => st₆.regs (mP l)) = oracle u := by
                funext l
                simp only [st₆, Function.update_of_ne (by simp : mP l ≠ mTmp)]
                exact congrFun hp5 l
              obtain ⟨st₇, a', emb', edisc, hemb'_inj, hk1_le, ha'_emb, ha'_mem, hv'_mem,
                hK7, hV7, hAct7, hq7⟩ :=
                discoverAndStoreFacet_spec hd L hP horacle a vVec emb hemb_inj ha_emb st₆
                  (by intro j l; change st₂.mem _ = _; rw [hm2, hm1]; exact ha_mem j l)
                  (by intro c l; change st₂.mem _ = _; rw [hm2, hm1]; exact hv_mem c l)
                  hK6 hV6 hAct6 (by rw [hp6]; exact hp_front) (by rw [hp6]; exact hp_known)
              refine ⟨st₇,
                Stmt.Exec.seq erec (Stmt.Exec.ite_zero htmp0
                  (Stmt.Exec.seq eout (Stmt.Exec.ite_pos hopos
                    (Stmt.Exec.seq eqr (Stmt.Exec.seq equery
                      (Stmt.Exec.seq ep (Stmt.Exec.seq ediff'
                        (Stmt.Exec.ite_pos hdiff_pos edisc)))))))),
                ⟨k + 1, V, a', emb', vVec, hemb'_inj, hk1_le, hv_inj, hv_exp, hV_le,
                  ha'_emb, ha'_mem, hv'_mem, hK7, hV7, ?_, Or.inl hAct7⟩,
                ?_⟩
              · rw [Finset.sum_range_succ]
                have hq6 : st₆.queries = st.queries + 1 := by
                  change st₂.queries + 1 = _; rw [hq2, hq1]
                omega
              · rw [hμ_st]
                simp only [μ, hK7, hV7, hAct7, natOfReal_cast, one_ne_zero, ↓reduceIte]
                omega
          · -- Branch 2b: outerSearch returned 0 -> done!
            have ha_ex : ∀ j : Fin k, ∃ i : Fin m, ∀ x, dot (a j) x = L i x :=
              fun j => ⟨emb j, ha_emb j⟩
            obtain ⟨hQP_eq, hV_range⟩ :=
              outer_done hd hPpoly hzero L hP horacle a ha_ex hrec_cone0
                (Set.range vVec)
                (by rintro _ ⟨c, rfl⟩; exact hv_exp c)
                (fun u hu => by obtain ⟨c, hc⟩ := hbfs_covered u hu; exact ⟨c, hc.symm⟩)
            have hV_pos : 0 < V := by
              by_contra hV0
              have hVeq : V = 0 := by omega
              subst hVeq
              have h0P : (0 : Fin d → ℝ) ∈ P := interior_subset hzero
              rw [← hQP_eq] at h0P
              have hsub := polyhedron_subset_convexHull_bfs a (fun _ => 1) hrec_cone0 h0P
              have hemp : { u | IsCramerBFS a (fun _ => 1) u } = ∅ := by
                ext u; constructor
                · intro hu; obtain ⟨c, _⟩ := hbfs_covered u hu; exact Fin.elim0 c
                · intro h; exact False.elim h
              rw [hemp, convexHull_empty] at hsub
              exact hsub
            have edone := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mActive
              (PExpr.const 0) st₂ 0 (by simp)
            let st₃ : RS (MainReg d) := ⟨Function.update st₂.regs mActive 0, st₂.mem, st₂.queries⟩
            have hK3 : st₃.regs mK = (k : ℝ) := by simp [st₃, hK2]
            have hV3 : st₃.regs mV = (V : ℝ) := by simp [st₃, hV2]
            have hAct3 : st₃.regs mActive = 0 := by simp [st₃]
            refine ⟨st₃,
              Stmt.Exec.seq erec (Stmt.Exec.ite_zero htmp0
                (Stmt.Exec.seq eout (Stmt.Exec.ite_zero hout0 edone))),
              ⟨k, V, a, emb, vVec, hemb_inj, hk_le, hv_inj, hv_exp, hV_le, ha_emb,
                by intro j l; change st₂.mem _ = _; rw [hm2, hm1, ha_mem j l],
                by intro c l; change st₂.mem _ = _; rw [hm2, hm1, hv_mem c l],
                hK3, hV3,
                by change st₂.queries ≤ _; rw [hq2, hq1]; exact hq,
                Or.inr ⟨hAct3, hV_pos, hQP_eq, hV_range⟩⟩,
              ?_⟩
            rw [hμ_st]
            simp [μ, hK3, hV3, hAct3])
      st_init hInv_init
  obtain ⟨k, V, a, _, vVec, _, hk_le, hv_inj, _, hV_le, _, ha_mem, hv_mem, hK, hV, hq, hAct_or⟩ :=
    hInv_end
  rcases hAct_or with h1 | ⟨_, hV_pos, hQP_eq, hV_range⟩
  · exfalso; linarith
  · exact ⟨st_end, k, V, a, vVec, Stmt.Exec.seq einit ewhile,
      hk_le, hV_pos, hV_le, hv_inj, hQP_eq, hV_range, ha_mem, hv_mem, hK, hV, hq⟩

/-! ### Post-loop Phase 1: Incidence table at `incBase` -/

def buildIncRow (d : ℕ) : Stmt (MainReg d) :=
  Stmt.forNat mCnt2 mV mCond2
    (.seq
      (Stmt.loadFam mVecB mIx fun l =>
        (PExpr.const 2 * PExpr.reg mCnt2 + PExpr.const 1) * PExpr.nat d + PExpr.nat l.val)
      (.seq
        (Stmt.assign mTmp
          (PExpr.dot (fun l => PExpr.reg (mVecA l)) (fun l => PExpr.reg (mVecB l)) -
            PExpr.const 1))
        (.seq
          (.ite mTmp
            (Stmt.assign mValA (PExpr.const 0))
            (Stmt.assign mValA (PExpr.const 1))
            (Stmt.assign mValA (PExpr.const 0)))
          (.seq
            (Stmt.assign mAddr
              (PExpr.reg mIncBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt2))
            (.store mAddr mValA)))))

theorem buildIncRow_spec {d V : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (aj : Fin d → ℝ) (vVec : Fin V → Fin d → ℝ) (incBase cj : ℕ)
    (hinc_gt : ∀ (c : Fin V) (l : Fin d), (2 * c.val + 1) * d + l.val < incBase)
    (st : RS (MainReg d))
    (hv_mem : ∀ (c : Fin V) (l : Fin d), st.mem ((2 * c.val + 1) * d + l.val) = vVec c l)
    (haj_reg : ∀ l : Fin d, st.regs (mVecA l) = aj l)
    (hV : st.regs mV = (V : ℝ))
    (hInc : st.regs mIncBase = (incBase : ℝ))
    (hcj : st.regs mCnt1 = (cj : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (buildIncRow d) st st' ∧
      st'.queries = st.queries ∧
      (∀ r : Fin V, st'.mem (incBase + cj * V + r.val) =
        if dot aj (vVec r) = 1 then 1 else 0) ∧
      (∀ addr, (addr < incBase + cj * V ∨ incBase + (cj + 1) * V ≤ addr) →
        st'.mem addr = st.mem addr) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 12 → c ≠ Sum.inl 13 → c ≠ Sum.inl 4 →
        c ≠ Sum.inl 5 → c ≠ Sum.inl 20 → c ≠ Sum.inl 22 → (∀ l, c ≠ Sum.inr (3, l)) →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  obtain ⟨st', exec, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt2) (boundReg := mV) (condReg := mCond2)
      (by simp) (by simp) (by simp)
      (fun cr st1 =>
        st1.queries = st.queries ∧
        (∀ r : Fin V, r.val < cr → st1.mem (incBase + cj * V + r.val) =
          if dot aj (vVec r) = 1 then 1 else 0) ∧
        (∀ addr, (addr < incBase + cj * V ∨ incBase + cj * V + cr ≤ addr) →
          st1.mem addr = st.mem addr) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 12 → c ≠ Sum.inl 13 → c ≠ Sum.inl 4 →
          c ≠ Sum.inl 5 → c ≠ Sum.inl 20 → c ≠ Sum.inl 22 → (∀ l, c ≠ Sum.inr (3, l)) →
          st1.regs (mCore c) = st.regs (mCore c)))
      (by
        intro cr st1 v₁ v₂ ⟨hq1, hlo, hoth, hpr⟩
        refine ⟨hq1, hlo, hoth, ?_⟩
        intro c r1 r2 r3 r4 r5 r6 r7
        have hne1 : mCore c ≠ mCond2 := fun e => r2 (by simpa using e)
        have hne2 : mCore c ≠ mCnt2 := fun e => r1 (by simpa using e)
        simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hpr c r1 r2 r3 r4 r5 r6 r7)
      (by
        intro cr hcr st1 hcnt1 hbnd1 _ ⟨hq1, hlo, hoth, hpr⟩
        let r₀ : Fin V := ⟨cr, hcr⟩
        obtain ⟨st2, eload, hvb2, hpr2, hm2, hq2⟩ :=
          Stmt.Exec.loadFam (oracle := oracle) (qr := mainQr) (ix := mIx) (mVecB_injective d)
            (fun _ => by simp)
            (fun l => (PExpr.const 2 * PExpr.reg mCnt2 + PExpr.const 1) * PExpr.nat d + PExpr.nat l.val)
            st1 (fun l => (2 * cr + 1) * d + l.val)
            (by
              intro l regs' hreg
              have hc' : regs' mCnt2 = (cr : ℝ) :=
                (hreg mCnt2 (by simp) (fun _ => by simp)).trans hcnt1
              simp [hc'])
        have haj2 : (fun l => st2.regs (mVecA l)) = aj := by
          funext l
          rw [hpr2 (mVecA l) (by simp) (fun _ => by simp)]
          exact (hpr (Sum.inr (2, l)) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (fun _ => by simp)).trans (haj_reg l)
        have hvb2' : (fun l => st2.regs (mVecB l)) = vVec r₀ := by
          funext l
          rw [hvb2 l, hoth _ (Or.inl (Nat.lt_of_lt_of_le (hinc_gt r₀ l) (by omega))), hv_mem r₀ l]
        have etmp := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mTmp
          (PExpr.dot (fun l => PExpr.reg (mVecA l)) (fun l => PExpr.reg (mVecB l)) - PExpr.const 1)
          st2 (dot aj (vVec r₀) - 1) (by simp [haj2, hvb2'])
        let st3 : RS (MainReg d) :=
          ⟨Function.update st2.regs mTmp (dot aj (vVec r₀) - 1), st2.mem, st2.queries⟩
        let bitVal : ℝ := if dot aj (vVec r₀) = 1 then 1 else 0
        have ebit : ∃ st4, Stmt.Exec oracle mainQr
            (.ite mTmp (Stmt.assign mValA (PExpr.const 0))
              (Stmt.assign mValA (PExpr.const 1)) (Stmt.assign mValA (PExpr.const 0))) st3 st4 ∧
            st4.mem = st3.mem ∧ st4.queries = st3.queries ∧
            st4.regs mValA = bitVal ∧
            (∀ r, r ≠ mValA → st4.regs r = st3.regs r) := by
          rcases lt_trichotomy (dot aj (vVec r₀) - 1) 0 with hlt | heq | hgt
          · have hne1 : dot aj (vVec r₀) ≠ 1 := by linarith
            have hn : st3.regs mTmp < 0 := by simp [st3, hlt]
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mValA (PExpr.const 0) st3 0 (by simp)
            exact ⟨_, Stmt.Exec.ite_neg hn ea, rfl, rfl, by simp [bitVal, hne1],
              fun r hr => by simp [Function.update_of_ne hr]⟩
          · have heq1 : dot aj (vVec r₀) = 1 := by linarith
            have hz : st3.regs mTmp = 0 := by simp [st3, heq]
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mValA (PExpr.const 1) st3 1 (by simp)
            exact ⟨_, Stmt.Exec.ite_zero hz ea, rfl, rfl, by simp [bitVal, heq1],
              fun r hr => by simp [Function.update_of_ne hr]⟩
          · have hne1 : dot aj (vVec r₀) ≠ 1 := by linarith
            have hp : 0 < st3.regs mTmp := by simp [st3, hgt]
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mValA (PExpr.const 0) st3 0 (by simp)
            exact ⟨_, Stmt.Exec.ite_pos hp ea, rfl, rfl, by simp [bitVal, hne1],
              fun r hr => by simp [Function.update_of_ne hr]⟩
        obtain ⟨st4, eite, hm4, hq4, hval4, hpr4⟩ := ebit
        have hinc4 : st4.regs mIncBase = (incBase : ℝ) := by
          rw [hpr4 mIncBase (by simp)]
          simp only [st3, Function.update_of_ne (by simp : mIncBase ≠ mTmp)]
          rw [hpr2 mIncBase (by simp) (fun _ => by simp)]
          exact (hpr (Sum.inl 6) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (fun _ => by simp)).trans hInc
        have hcj4 : st4.regs mCnt1 = (cj : ℝ) := by
          rw [hpr4 mCnt1 (by simp)]
          simp only [st3, Function.update_of_ne (by simp : mCnt1 ≠ mTmp)]
          rw [hpr2 mCnt1 (by simp) (fun _ => by simp)]
          exact (hpr (Sum.inl 10) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (fun _ => by simp)).trans hcj
        have hv4 : st4.regs mV = (V : ℝ) := by
          rw [hpr4 mV (by simp)]
          simp only [st3, Function.update_of_ne (by simp : mV ≠ mTmp)]
          exact (hpr2 mV (by simp) (fun _ => by simp)).trans hbnd1
        have hcr4 : st4.regs mCnt2 = (cr : ℝ) := by
          rw [hpr4 mCnt2 (by simp)]
          simp only [st3, Function.update_of_ne (by simp : mCnt2 ≠ mTmp)]
          exact (hpr2 mCnt2 (by simp) (fun _ => by simp)).trans hcnt1
        let targetAddr := incBase + cj * V + cr
        have eaddr := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAddr
          (PExpr.reg mIncBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt2) st4
          (targetAddr : ℝ) (by simp [hinc4, hcj4, hv4, hcr4, targetAddr])
        let st5 : RS (MainReg d) :=
          ⟨Function.update st4.regs mAddr (targetAddr : ℝ), st4.mem, st4.queries⟩
        have estore := Stmt.Exec.store (oracle := oracle) (qr := mainQr) mAddr mValA st5
          targetAddr (by simp [st5])
        let st6 : RS (MainReg d) :=
          ⟨st5.regs, Function.update st5.mem targetAddr (st5.regs mValA), st5.queries⟩
        have hm51 : st5.mem = st1.mem := hm4.trans hm2
        refine ⟨st6,
          Stmt.Exec.seq eload (Stmt.Exec.seq etmp (Stmt.Exec.seq eite (Stmt.Exec.seq eaddr estore))),
          by simp [st6, st5, hcr4],
          by simp [st6, st5, hv4],
          hq4.trans (hq2.trans hq1), ?_, ?_, ?_⟩
        · intro r hr
          simp only [st6]
          by_cases hrc : r.val = cr
          · have hre : r = r₀ := Fin.ext hrc
            rw [hrc, Function.update_self, hre]
            simp [st5, hval4, bitVal]
          · have hne_a : incBase + cj * V + r.val ≠ targetAddr := by dsimp [targetAddr]; omega
            rw [Function.update_of_ne hne_a, hm51]
            exact hlo r (by omega)
        · intro addr haddr
          simp only [st6]
          have hne_a : addr ≠ targetAddr := by dsimp [targetAddr]; omega
          rw [Function.update_of_ne hne_a, hm51]
          exact hoth addr (by omega)
        · intro c r1 r2 r3 r4 r5 r6 r7
          have hne_addr : mCore c ≠ mAddr := fun e => r6 (by simpa using e)
          have hne_vala : mCore c ≠ mValA := fun e => r5 (by simpa using e)
          have hne_tmp : mCore c ≠ mTmp := fun e => r4 (by simpa using e)
          have hne_ix : mCore c ≠ mIx := fun e => r3 (by simpa using e)
          have hne_vb : ∀ l, mCore c ≠ mVecB l := fun l e => r7 l (by simpa using e)
          simp only [st6, st5, Function.update_of_ne hne_addr]
          rw [hpr4 (mCore c) hne_vala]
          simp only [st3, Function.update_of_ne hne_tmp]
          rw [hpr2 (mCore c) hne_ix hne_vb]
          exact hpr c r1 r2 r3 r4 r5 r6 r7)
      st hV
      ⟨rfl, fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨hq', hlo', hoth', hpr'⟩ := hInv
  refine ⟨st', exec, hq', fun r => hlo' r r.isLt, fun addr ha => hoth' addr ?_, hpr'⟩
  rcases ha with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by nlinarith)

def buildIncTable (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mIncBase
      ((PExpr.const 2 * (PExpr.reg mK + PExpr.reg mV + PExpr.const 1)) * PExpr.nat d))
    (Stmt.forNat mCnt1 mK mCond1
      (.seq
        (Stmt.loadFam mVecA mIx fun l =>
          (PExpr.const 2 * PExpr.reg mCnt1) * PExpr.nat d + PExpr.nat l.val)
        (buildIncRow d)))

theorem buildIncTable_spec {d k V : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (st : RS (MainReg d))
    (ha_mem : ∀ (j : Fin k) (l : Fin d), st.mem ((2 * j.val) * d + l.val) = a j l)
    (hv_mem : ∀ (c : Fin V) (l : Fin d), st.mem ((2 * c.val + 1) * d + l.val) = vVec c l)
    (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ)) :
    let incBase := (2 * (k + V + 1)) * d
    ∃ st', Stmt.Exec oracle mainQr (buildIncTable d) st st' ∧
      st'.queries = st.queries ∧
      st'.regs mK = (k : ℝ) ∧ st'.regs mV = (V : ℝ) ∧
      st'.regs mIncBase = (incBase : ℝ) ∧
      (∀ (j : Fin k) (r : Fin V), st'.mem (incBase + j.val * V + r.val) =
        if dot (a j) (vVec r) = 1 then 1 else 0) := by
  intro incBase
  have einc := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mIncBase
    ((PExpr.const 2 * (PExpr.reg mK + PExpr.reg mV + PExpr.const 1)) * PExpr.nat d) st
    (incBase : ℝ) (by simp [hK, hV, incBase])
  let st₀ : RS (MainReg d) := ⟨Function.update st.regs mIncBase (incBase : ℝ), st.mem, st.queries⟩
  have hK0 : st₀.regs mK = (k : ℝ) := by simp [st₀, hK]
  have hinc_a : ∀ (j : Fin k) (l : Fin d), (2 * j.val) * d + l.val < incBase := by
    intro j l; have := j.isLt; have := l.isLt; dsimp [incBase]; nlinarith
  have hinc_v : ∀ (c : Fin V) (l : Fin d), (2 * c.val + 1) * d + l.val < incBase := by
    intro c l; have := c.isLt; have := l.isLt; dsimp [incBase]; nlinarith
  obtain ⟨st', eloop, _, hK', _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt1) (boundReg := mK) (condReg := mCond1)
      (by simp) (by simp) (by simp)
      (fun cj st1 =>
        st1.queries = st.queries ∧
        st1.regs mV = (V : ℝ) ∧
        st1.regs mIncBase = (incBase : ℝ) ∧
        (∀ addr, addr < incBase → st1.mem addr = st.mem addr) ∧
        (∀ (j : Fin k), j.val < cj → ∀ r : Fin V,
          st1.mem (incBase + j.val * V + r.val) =
            if dot (a j) (vVec r) = 1 then 1 else 0))
      (by
        intro cj st1 v₁ v₂ ⟨hq1, hv1, hi1, hlow, hdone⟩
        refine ⟨hq1, ?_, ?_, hlow, hdone⟩
        · simp [hv1]
        · simp [hi1])
      (by
        intro cj hcj st1 hcnt1 hbnd1 _ ⟨hq1, hv1, hi1, hlow, hdone⟩
        let j₀ : Fin k := ⟨cj, hcj⟩
        obtain ⟨st2, eload, ha2, hpr2, hm2, hq2⟩ :=
          Stmt.Exec.loadFam (oracle := oracle) (qr := mainQr) (ix := mIx) (mVecA_injective d)
            (fun _ => by simp)
            (fun l => (PExpr.const 2 * PExpr.reg mCnt1) * PExpr.nat d + PExpr.nat l.val)
            st1 (fun l => (2 * cj) * d + l.val)
            (by
              intro l regs' hreg
              have hc' : regs' mCnt1 = (cj : ℝ) :=
                (hreg mCnt1 (by simp) (fun _ => by simp)).trans hcnt1
              simp [hc'])
        have ha2' : ∀ l : Fin d, st2.regs (mVecA l) = a j₀ l := by
          intro l
          rw [ha2 l, hlow _ (hinc_a j₀ l), ha_mem j₀ l]
        have hv_mem2 : ∀ (c : Fin V) (l : Fin d), st2.mem ((2 * c.val + 1) * d + l.val) = vVec c l := by
          intro c l
          rw [hm2, hlow _ (hinc_v c l), hv_mem c l]
        have hv2 : st2.regs mV = (V : ℝ) :=
          (hpr2 mV (by simp) (fun _ => by simp)).trans hv1
        have hi2 : st2.regs mIncBase = (incBase : ℝ) :=
          (hpr2 mIncBase (by simp) (fun _ => by simp)).trans hi1
        have hcnt2 : st2.regs mCnt1 = (cj : ℝ) :=
          (hpr2 mCnt1 (by simp) (fun _ => by simp)).trans hcnt1
        have hbnd2 : st2.regs mK = (k : ℝ) :=
          (hpr2 mK (by simp) (fun _ => by simp)).trans hbnd1
        obtain ⟨st3, erow, hq3, hrow3, hoth3, hpr3⟩ :=
          buildIncRow_spec (a j₀) vVec incBase cj hinc_v st2 hv_mem2 ha2' hv2 hi2 hcnt2
        refine ⟨st3, Stmt.Exec.seq eload erow,
          (hpr3 (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp)).trans hcnt2,
          (hpr3 (Sum.inl 0) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp)).trans hbnd2,
          hq3.trans (hq2.trans hq1),
          (hpr3 (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp)).trans hv2,
          (hpr3 (Sum.inl 6) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (fun _ => by simp)).trans hi2,
          ?_, ?_⟩
        · intro addr haddr
          rw [hoth3 addr (Or.inl (by omega)), hm2]
          exact hlow addr haddr
        · intro j hj r
          by_cases hjc : j.val < cj
          · have hlt : incBase + j.val * V + r.val < incBase + cj * V := by
              have := r.isLt; nlinarith
            rw [hoth3 _ (Or.inl hlt), hm2]
            exact hdone j hjc r
          · have hje : j = j₀ := Fin.ext (by dsimp [j₀]; omega)
            rw [hje]
            exact hrow3 r)
      st₀ hK0
      ⟨rfl, by simp [st₀, hV], by simp [st₀], fun _ _ => rfl, fun _ h => by omega⟩
  obtain ⟨hq', hv', hi', _, hdone'⟩ := hInv
  exact ⟨st', Stmt.Exec.seq einc eloop, hq', hK', hv', hi', fun j r => hdone' j j.isLt r⟩

/-! ### Memory access helpers via `mAddr` -/

def loadAt {d : ℕ} (dst : MainReg d) (addr : PExpr (MainReg d)) : Stmt (MainReg d) :=
  .seq (Stmt.assign mAddr addr) (.load dst mAddr)

theorem loadAt_spec {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (dst : MainReg d) (addr : PExpr (MainReg d))
    (st : RS (MainReg d)) (n : ℕ) (hn : addr.eval st.regs = (n : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (loadAt dst addr) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      st'.regs dst = st.mem n ∧
      (∀ r, r ≠ dst → r ≠ mAddr → st'.regs r = st.regs r) := by
  have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAddr addr st (n : ℝ) hn
  let st₁ : RS (MainReg d) := ⟨Function.update st.regs mAddr (n : ℝ), st.mem, st.queries⟩
  have el := Stmt.Exec.load (oracle := oracle) (qr := mainQr) dst mAddr st₁ n (by simp [st₁])
  refine ⟨⟨Function.update st₁.regs dst (st.mem n), st.mem, st.queries⟩,
    Stmt.Exec.seq ea el, rfl, rfl, by simp [st₁], ?_⟩
  intro r hr1 hr2
  simp only [st₁, Function.update_of_ne hr1, Function.update_of_ne hr2]

def storeAt {d : ℕ} (addr : PExpr (MainReg d)) (src : MainReg d) : Stmt (MainReg d) :=
  .seq (Stmt.assign mAddr addr) (.store mAddr src)

theorem storeAt_spec {d : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (addr : PExpr (MainReg d)) (src : MainReg d) (hsrc : src ≠ mAddr)
    (st : RS (MainReg d)) (n : ℕ) (hn : addr.eval st.regs = (n : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (storeAt addr src) st st' ∧
      st'.mem = Function.update st.mem n (st.regs src) ∧
      st'.queries = st.queries ∧
      (∀ r, r ≠ mAddr → st'.regs r = st.regs r) := by
  have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAddr addr st (n : ℝ) hn
  let st₁ : RS (MainReg d) := ⟨Function.update st.regs mAddr (n : ℝ), st.mem, st.queries⟩
  have es := Stmt.Exec.store (oracle := oracle) (qr := mainQr) mAddr src st₁ n (by simp [st₁])
  refine ⟨⟨st₁.regs, Function.update st.mem n (st₁.regs src), st.queries⟩,
    Stmt.Exec.seq ea es, ?_, rfl, ?_⟩
  · simp only [st₁, Function.update_of_ne hsrc]
  · intro r hr
    simp only [st₁, Function.update_of_ne hr]

/-! ### Post-loop Phase 2: Face-lattice closure at `faceBase` -/

noncomputable def incBit {d k V : ℕ} (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (J : Finset (Fin k)) : Fin V → ℝ :=
  fun r => if ∀ j ∈ J, dot (a j) (vVec r) = 1 then 1 else 0

def FaceSet {d k V : ℕ} (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ) (cj : ℕ) :
    Set (Fin V → ℝ) :=
  { fun _ : Fin V => (0 : ℝ) } ∪
    { b | ∃ J : Finset (Fin k), (∀ j ∈ J, j.val < cj) ∧ b = incBit a vVec J }

theorem incBit_insert {d k V : ℕ} (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (j₀ : Fin k) (J : Finset (Fin k)) (r : Fin V) :
    incBit a vVec J r * (if dot (a j₀) (vVec r) = 1 then 1 else 0) =
      incBit a vVec (insert j₀ J) r := by
  simp only [incBit, Finset.forall_mem_insert]
  by_cases h0 : dot (a j₀) (vVec r) = 1 <;>
    by_cases hJ : ∀ j ∈ J, dot (a j) (vVec r) = 1 <;>
    simp [h0, hJ]

def initFaceRows (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mFaceBase (PExpr.reg mIncBase + PExpr.reg mK * PExpr.reg mV))
    (.seq
      (.par [(mValA, PExpr.const 0), (mValB, PExpr.const 1)])
      (.seq
        (Stmt.forNat mCnt3 mV mCond3
          (.seq
            (storeAt (PExpr.reg mFaceBase + PExpr.reg mCnt3) mValA)
            (storeAt (PExpr.reg mFaceBase + PExpr.reg mV + PExpr.reg mCnt3) mValB)))
        (Stmt.assign mCurN (PExpr.const 2))))

theorem initFaceRows_spec {d k V : ℕ} (hV_pos : 0 < V)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ) (incBase : ℕ)
    (st : RS (MainReg d))
    (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ))
    (hInc : st.regs mIncBase = (incBase : ℝ)) :
    let faceBase := incBase + k * V
    ∃ (st' : RS (MainReg d)) (faceBit : Fin 2 → Fin V → ℝ),
      Stmt.Exec oracle mainQr (initFaceRows d) st st' ∧
      st'.queries = st.queries ∧
      st'.regs mK = (k : ℝ) ∧ st'.regs mV = (V : ℝ) ∧
      st'.regs mIncBase = (incBase : ℝ) ∧
      st'.regs mFaceBase = (faceBase : ℝ) ∧
      st'.regs mCurN = (2 : ℝ) ∧
      Function.Injective faceBit ∧
      (∀ i r, faceBit i r = 0 ∨ faceBit i r = 1) ∧
      Set.range faceBit = FaceSet a vVec 0 ∧
      (∀ (i : Fin 2) (r : Fin V), st'.mem (faceBase + i.val * V + r.val) = faceBit i r) ∧
      (∀ addr, addr < faceBase → st'.mem addr = st.mem addr) := by
  intro faceBase
  have efb := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mFaceBase
    (PExpr.reg mIncBase + PExpr.reg mK * PExpr.reg mV) st (faceBase : ℝ)
    (by simp [hInc, hK, hV, faceBase])
  let st₁ : RS (MainReg d) := ⟨Function.update st.regs mFaceBase (faceBase : ℝ), st.mem, st.queries⟩
  have epar := Stmt.Exec.par (oracle := oracle) (qr := mainQr)
    [(mValA, PExpr.const 0), (mValB, PExpr.const 1)] st₁
  let st₂ : RS (MainReg d) :=
    ⟨parUpd st₁.regs [(mValA, PExpr.const 0), (mValB, PExpr.const 1)] st₁.regs, st₁.mem, st₁.queries⟩
  have hv2 : st₂.regs mV = (V : ℝ) := by simp [st₂, parUpd, st₁, hV]
  obtain ⟨st₃, eloop, _, hv3, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt3) (boundReg := mV) (condReg := mCond3)
      (by simp) (by simp) (by simp)
      (fun cr s =>
        s.queries = st.queries ∧
        s.regs mK = (k : ℝ) ∧ s.regs mIncBase = (incBase : ℝ) ∧
        s.regs mFaceBase = (faceBase : ℝ) ∧
        s.regs mValA = 0 ∧ s.regs mValB = 1 ∧
        (∀ r : Fin V, r.val < cr →
          s.mem (faceBase + r.val) = 0 ∧ s.mem (faceBase + V + r.val) = 1) ∧
        (∀ addr, addr < faceBase → s.mem addr = st.mem addr))
      (by
        intro cr s v₁ v₂ ⟨hq, hk, hi, hf, ha, hb, hdone, hlow⟩
        refine ⟨hq, ?_, ?_, ?_, ?_, ?_, hdone, hlow⟩ <;> simp [hk, hi, hf, ha, hb])
      (by
        intro cr hcr s hcnt hbnd _ ⟨hq, hk, hi, hf, ha, hb, hdone, hlow⟩
        obtain ⟨s1, es1, hm1, hq1, hpr1⟩ :=
          storeAt_spec (oracle := oracle) (PExpr.reg mFaceBase + PExpr.reg mCnt3) mValA (by simp)
            s (faceBase + cr) (by simp [hf, hcnt])
        have hf1 : s1.regs mFaceBase = (faceBase : ℝ) := (hpr1 mFaceBase (by simp)).trans hf
        have hv1 : s1.regs mV = (V : ℝ) := (hpr1 mV (by simp)).trans hbnd
        have hcnt1 : s1.regs mCnt3 = (cr : ℝ) := (hpr1 mCnt3 (by simp)).trans hcnt
        have hb1 : s1.regs mValB = 1 := (hpr1 mValB (by simp)).trans hb
        obtain ⟨s2, es2, hm2, hq2, hpr2⟩ :=
          storeAt_spec (oracle := oracle)
            (PExpr.reg mFaceBase + PExpr.reg mV + PExpr.reg mCnt3) mValB (by simp)
            s1 (faceBase + V + cr) (by simp [hf1, hv1, hcnt1])
        refine ⟨s2, Stmt.Exec.seq es1 es2,
          (hpr2 mCnt3 (by simp)).trans hcnt1,
          (hpr2 mV (by simp)).trans hv1,
          hq2.trans (hq1.trans hq),
          (hpr2 mK (by simp)).trans ((hpr1 mK (by simp)).trans hk),
          (hpr2 mIncBase (by simp)).trans ((hpr1 mIncBase (by simp)).trans hi),
          (hpr2 mFaceBase (by simp)).trans hf1,
          (hpr2 mValA (by simp)).trans ((hpr1 mValA (by simp)).trans ha),
          (hpr2 mValB (by simp)).trans hb1,
          ?_, ?_⟩
        · intro r hr
          rw [hm2]
          by_cases hrc : r.val = cr
          · rw [hrc, Function.update_of_ne (by omega : faceBase + cr ≠ faceBase + V + cr),
              Function.update_self, hm1, Function.update_self, ha, hb1]
            exact ⟨rfl, rfl⟩
          · have hlt : r.val < cr := by omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm1,
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hdone r hlt
        · intro addr haddr
          rw [hm2, Function.update_of_ne (by omega), hm1, Function.update_of_ne (by omega)]
          exact hlow addr haddr)
      st₂ hv2
      ⟨rfl, by simp [st₂, parUpd, st₁, hK], by simp [st₂, parUpd, st₁, hInc],
       by simp [st₂, parUpd, st₁],
       by simp only [st₂, parUpd, PExpr.eval_const]; rw [Function.update_of_ne (by simp : mValA ≠ mValB), Function.update_self]; norm_num,
       by simp [st₂, parUpd],
       fun _ h => by omega, fun _ _ => rfl⟩
  obtain ⟨hq3, hk3, hi3, hf3, _, _, hdone3, hlow3⟩ := hInv
  have ecn := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mCurN
    (PExpr.const 2) st₃ (2 : ℝ) (by norm_num)
  let st₄ : RS (MainReg d) := ⟨Function.update st₃.regs mCurN 2, st₃.mem, st₃.queries⟩
  let faceBit : Fin 2 → Fin V → ℝ := fun i => if i.val = 0 then (fun _ => 0) else (fun _ => 1)
  refine ⟨st₄, faceBit,
    Stmt.Exec.seq efb (Stmt.Exec.seq epar (Stmt.Exec.seq eloop ecn)),
    hq3,
    by simp [st₄, hk3], by simp [st₄, hv3], by simp [st₄, hi3], by simp [st₄, hf3],
    by simp [st₄],
    ?_, ?_, ?_, ?_, fun addr h => hlow3 addr h⟩
  · intro i j hij
    have hr0 := congrFun hij ⟨0, hV_pos⟩
    fin_cases i <;> fin_cases j <;> simp [faceBit] at hr0 ⊢
  · intro i r
    fin_cases i <;> simp [faceBit]
  · ext b; constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · right
        refine ⟨∅, fun _ h => by simp at h, ?_⟩
        ext r; simp [faceBit, incBit]
    · rintro (rfl | ⟨J, hJ, rfl⟩)
      · exact ⟨0, rfl⟩
      · have hJe : J = ∅ := by
          ext j; constructor
          · intro hj; have := hJ j hj; omega
          · intro hj; simp at hj
        subst hJe
        refine ⟨1, ?_⟩
        ext r; simp [faceBit, incBit]
  · intro i r
    change st₃.mem _ = _
    have hd := hdone3 r r.isLt
    fin_cases i
    · simpa [faceBit] using hd.1
    · simpa [faceBit, Nat.add_assoc] using hd.2

def writeCandRow (d : ℕ) : Stmt (MainReg d) :=
  Stmt.forNat mCnt3 mV mCond3
    (.seq
      (loadAt mValA (PExpr.reg mFaceBase + PExpr.reg mCnt2 * PExpr.reg mV + PExpr.reg mCnt3))
      (.seq
        (loadAt mValB (PExpr.reg mIncBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt3))
        (.seq
          (Stmt.assign mScratch (PExpr.reg mValA * PExpr.reg mValB))
          (storeAt (PExpr.reg mFaceBase + PExpr.reg mCurN * PExpr.reg mV + PExpr.reg mCnt3)
            mScratch))))

theorem writeCandRow_spec {d k V cur_n : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (rowSrc incRow : Fin V → ℝ) (incBase faceBase cj idx : ℕ)
    (hcj : cj < k) (hidx : idx < cur_n) (hfb_eq : faceBase = incBase + k * V)
    (st : RS (MainReg d))
    (hrow_mem : ∀ r : Fin V, st.mem (faceBase + idx * V + r.val) = rowSrc r)
    (hinc_mem : ∀ r : Fin V, st.mem (incBase + cj * V + r.val) = incRow r)
    (hV : st.regs mV = (V : ℝ)) (hInc : st.regs mIncBase = (incBase : ℝ))
    (hFb : st.regs mFaceBase = (faceBase : ℝ)) (hCurN : st.regs mCurN = (cur_n : ℝ))
    (hcj_reg : st.regs mCnt1 = (cj : ℝ)) (hidx_reg : st.regs mCnt2 = (idx : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (writeCandRow d) st st' ∧
      st'.queries = st.queries ∧
      (∀ r : Fin V, st'.mem (faceBase + cur_n * V + r.val) = rowSrc r * incRow r) ∧
      (∀ addr, addr < faceBase + cur_n * V → st'.mem addr = st.mem addr) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 20 →
        c ≠ Sum.inl 21 → c ≠ Sum.inl 22 → c ≠ Sum.inl 23 →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt3) (boundReg := mV) (condReg := mCond3)
      (by simp) (by simp) (by simp)
      (fun cr s =>
        s.queries = st.queries ∧
        (∀ r : Fin V, r.val < cr →
          s.mem (faceBase + cur_n * V + r.val) = rowSrc r * incRow r) ∧
        (∀ addr, addr < faceBase + cur_n * V → s.mem addr = st.mem addr) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 20 →
          c ≠ Sum.inl 21 → c ≠ Sum.inl 22 → c ≠ Sum.inl 23 →
          s.regs (mCore c) = st.regs (mCore c)))
      (by
        intro cr s v₁ v₂ ⟨hq, hdone, hlow, hpr⟩
        refine ⟨hq, hdone, hlow, ?_⟩
        intro c r1 r2 r3 r4 r5 r6
        have hne1 : mCore c ≠ mCond3 := fun e => r2 (by simpa using e)
        have hne2 : mCore c ≠ mCnt3 := fun e => r1 (by simpa using e)
        simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hpr c r1 r2 r3 r4 r5 r6)
      (by
        intro cr hcr s hcnt hbnd _ ⟨hq, hdone, hlow, hpr⟩
        let r₀ : Fin V := ⟨cr, hcr⟩
        have hfb_s : s.regs mFaceBase = (faceBase : ℝ) :=
          (hpr (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hFb
        have hinc_s : s.regs mIncBase = (incBase : ℝ) :=
          (hpr (Sum.inl 6) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hInc
        have hcn_s : s.regs mCurN = (cur_n : ℝ) :=
          (hpr (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hCurN
        have hcj_s : s.regs mCnt1 = (cj : ℝ) :=
          (hpr (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcj_reg
        have hidx_s : s.regs mCnt2 = (idx : ℝ) :=
          (hpr (Sum.inl 12) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hidx_reg
        obtain ⟨s1, el1, hm1, hq1, hva1, hpr1⟩ :=
          loadAt_spec (oracle := oracle) mValA
            (PExpr.reg mFaceBase + PExpr.reg mCnt2 * PExpr.reg mV + PExpr.reg mCnt3)
            s (faceBase + idx * V + cr) (by simp [hfb_s, hidx_s, hbnd, hcnt])
        have hva1_eq : s1.regs mValA = rowSrc r₀ := by
          rw [hva1, hlow _ (by nlinarith), hrow_mem r₀]
        obtain ⟨s2, el2, hm2, hq2, hvb2, hpr2⟩ :=
          loadAt_spec (oracle := oracle) mValB
            (PExpr.reg mIncBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt3)
            s1 (incBase + cj * V + cr)
            (by
              simp only [PExpr.eval_add, PExpr.eval_mul, PExpr.eval_reg]
              rw [hpr1 mIncBase (by simp) (by simp), hpr1 mCnt1 (by simp) (by simp),
                hpr1 mV (by simp) (by simp), hpr1 mCnt3 (by simp) (by simp)]
              simp [hinc_s, hcj_s, hbnd, hcnt])
        have hvb2_eq : s2.regs mValB = incRow r₀ := by
          rw [hvb2, hm1, hlow _ (by nlinarith), hinc_mem r₀]
        have hva2_eq : s2.regs mValA = rowSrc r₀ :=
          (hpr2 mValA (by simp) (by simp)).trans hva1_eq
        have escr := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mScratch
          (PExpr.reg mValA * PExpr.reg mValB) s2 (rowSrc r₀ * incRow r₀)
          (by simp [hva2_eq, hvb2_eq])
        let s3 : RS (MainReg d) :=
          ⟨Function.update s2.regs mScratch (rowSrc r₀ * incRow r₀), s2.mem, s2.queries⟩
        have hfb3 : s3.regs mFaceBase = (faceBase : ℝ) := by
          simp only [s3, Function.update_of_ne (by simp : mFaceBase ≠ mScratch)]
          rw [hpr2 mFaceBase (by simp) (by simp), hpr1 mFaceBase (by simp) (by simp)]
          exact hfb_s
        have hcn3 : s3.regs mCurN = (cur_n : ℝ) := by
          simp only [s3, Function.update_of_ne (by simp : mCurN ≠ mScratch)]
          rw [hpr2 mCurN (by simp) (by simp), hpr1 mCurN (by simp) (by simp)]
          exact hcn_s
        have hv3 : s3.regs mV = (V : ℝ) := by
          simp only [s3, Function.update_of_ne (by simp : mV ≠ mScratch)]
          rw [hpr2 mV (by simp) (by simp), hpr1 mV (by simp) (by simp)]
          exact hbnd
        have hcnt3 : s3.regs mCnt3 = (cr : ℝ) := by
          simp only [s3, Function.update_of_ne (by simp : mCnt3 ≠ mScratch)]
          rw [hpr2 mCnt3 (by simp) (by simp), hpr1 mCnt3 (by simp) (by simp)]
          exact hcnt
        obtain ⟨s4, es4, hm4, hq4, hpr4⟩ :=
          storeAt_spec (oracle := oracle)
            (PExpr.reg mFaceBase + PExpr.reg mCurN * PExpr.reg mV + PExpr.reg mCnt3)
            mScratch (by simp) s3 (faceBase + cur_n * V + cr)
            (by simp [hfb3, hcn3, hv3, hcnt3])
        have hm3s : s3.mem = s.mem := hm2.trans hm1
        refine ⟨s4, Stmt.Exec.seq el1 (Stmt.Exec.seq el2 (Stmt.Exec.seq escr es4)),
          (hpr4 mCnt3 (by simp)).trans hcnt3,
          (hpr4 mV (by simp)).trans hv3,
          hq4.trans (hq2.trans (hq1.trans hq)),
          ?_, ?_, ?_⟩
        · intro r hr
          rw [hm4]
          by_cases hrc : r.val = cr
          · have hre : r = r₀ := Fin.ext hrc
            rw [hrc, Function.update_self, hre]
            simp [s3]
          · rw [Function.update_of_ne (by omega), hm3s]
            exact hdone r (by omega)
        · intro addr haddr
          rw [hm4, Function.update_of_ne (by omega), hm3s]
          exact hlow addr haddr
        · intro c r1 r2 r3 r4 r5 r6
          have hne_addr : mCore c ≠ mAddr := fun e => r5 (by simpa using e)
          have hne_scr : mCore c ≠ mScratch := fun e => r6 (by simpa using e)
          have hne_va : mCore c ≠ mValA := fun e => r3 (by simpa using e)
          have hne_vb : mCore c ≠ mValB := fun e => r4 (by simpa using e)
          rw [hpr4 (mCore c) hne_addr]
          simp only [s3, Function.update_of_ne hne_scr]
          rw [hpr2 (mCore c) hne_vb hne_addr, hpr1 (mCore c) hne_va hne_addr]
          exact hpr c r1 r2 r3 r4 r5 r6)
      st hV
      ⟨rfl, fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨hq', hdone', hlow', hpr'⟩ := hInv
  exact ⟨st', eloop, hq', fun r => hdone' r r.isLt, hlow', hpr'⟩

def diffSqRow (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mAcc (PExpr.const 0))
    (Stmt.forNat mCnt4 mV mCond4
      (.seq
        (loadAt mValA (PExpr.reg mFaceBase + PExpr.reg mCurN * PExpr.reg mV + PExpr.reg mCnt4))
        (.seq
          (loadAt mValB (PExpr.reg mFaceBase + PExpr.reg mCnt3 * PExpr.reg mV + PExpr.reg mCnt4))
          (Stmt.assign mAcc
            (PExpr.reg mAcc +
              (PExpr.reg mValA - PExpr.reg mValB) * (PExpr.reg mValA - PExpr.reg mValB))))))

theorem diffSqRow_spec {d V cur_n : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (cand rowT : Fin V → ℝ) (faceBase t : ℕ)
    (st : RS (MainReg d))
    (hcand_mem : ∀ r : Fin V, st.mem (faceBase + cur_n * V + r.val) = cand r)
    (hrow_mem : ∀ r : Fin V, st.mem (faceBase + t * V + r.val) = rowT r)
    (hV : st.regs mV = (V : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hCurN : st.regs mCurN = (cur_n : ℝ)) (ht_reg : st.regs mCnt3 = (t : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (diffSqRow d) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      0 ≤ st'.regs mAcc ∧
      (st'.regs mAcc = 0 ↔ cand = rowT) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 16 → c ≠ Sum.inl 17 → c ≠ Sum.inl 19 →
        c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  have eacc0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAcc
    (PExpr.const 0) st 0 (by simp)
  let st₀ : RS (MainReg d) := ⟨Function.update st.regs mAcc 0, st.mem, st.queries⟩
  have hv0 : st₀.regs mV = (V : ℝ) := by simp [st₀, hV]
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt4) (boundReg := mV) (condReg := mCond4)
      (by simp) (by simp) (by simp)
      (fun cr s =>
        s.mem = st.mem ∧ s.queries = st.queries ∧
        s.regs mAcc =
          (∑ r ∈ Finset.univ.filter (fun r : Fin V => r.val < cr),
            (cand r - rowT r) * (cand r - rowT r)) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 16 → c ≠ Sum.inl 17 → c ≠ Sum.inl 19 →
          c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
          s.regs (mCore c) = st.regs (mCore c)))
      (by
        intro cr s v₁ v₂ ⟨hm, hq, hacc, hpr⟩
        refine ⟨hm, hq, ?_, ?_⟩
        · simp [hacc]
        · intro c r1 r2 r3 r4 r5 r6
          have hne1 : mCore c ≠ mCond4 := fun e => r2 (by simpa using e)
          have hne2 : mCore c ≠ mCnt4 := fun e => r1 (by simpa using e)
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hpr c r1 r2 r3 r4 r5 r6)
      (by
        intro cr hcr s hcnt hbnd _ ⟨hm, hq, hacc, hpr⟩
        let r₀ : Fin V := ⟨cr, hcr⟩
        have hfb_s : s.regs mFaceBase = (faceBase : ℝ) :=
          (hpr (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hFb
        have hcn_s : s.regs mCurN = (cur_n : ℝ) :=
          (hpr (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hCurN
        have ht_s : s.regs mCnt3 = (t : ℝ) :=
          (hpr (Sum.inl 14) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans ht_reg
        obtain ⟨s1, el1, hm1, hq1, hva1, hpr1⟩ :=
          loadAt_spec (oracle := oracle) mValA
            (PExpr.reg mFaceBase + PExpr.reg mCurN * PExpr.reg mV + PExpr.reg mCnt4)
            s (faceBase + cur_n * V + cr) (by simp [hfb_s, hcn_s, hbnd, hcnt])
        have hva1_eq : s1.regs mValA = cand r₀ := by
          rw [hva1, hm, hcand_mem r₀]
        obtain ⟨s2, el2, hm2, hq2, hvb2, hpr2⟩ :=
          loadAt_spec (oracle := oracle) mValB
            (PExpr.reg mFaceBase + PExpr.reg mCnt3 * PExpr.reg mV + PExpr.reg mCnt4)
            s1 (faceBase + t * V + cr)
            (by
              simp only [PExpr.eval_add, PExpr.eval_mul, PExpr.eval_reg]
              rw [hpr1 mFaceBase (by simp) (by simp), hpr1 mCnt3 (by simp) (by simp),
                hpr1 mV (by simp) (by simp), hpr1 mCnt4 (by simp) (by simp)]
              simp [hfb_s, ht_s, hbnd, hcnt])
        have hvb2_eq : s2.regs mValB = rowT r₀ := by
          rw [hvb2, hm1, hm, hrow_mem r₀]
        have hva2_eq : s2.regs mValA = cand r₀ :=
          (hpr2 mValA (by simp) (by simp)).trans hva1_eq
        have hacc2 : s2.regs mAcc = s.regs mAcc := by
          rw [hpr2 mAcc (by simp) (by simp), hpr1 mAcc (by simp) (by simp)]
        have eadd := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAcc
          (PExpr.reg mAcc +
            (PExpr.reg mValA - PExpr.reg mValB) * (PExpr.reg mValA - PExpr.reg mValB)) s2
          (s.regs mAcc + (cand r₀ - rowT r₀) * (cand r₀ - rowT r₀))
          (by simp [hacc2, hva2_eq, hvb2_eq])
        let s3 : RS (MainReg d) :=
          ⟨Function.update s2.regs mAcc
            (s.regs mAcc + (cand r₀ - rowT r₀) * (cand r₀ - rowT r₀)),
           s2.mem, s2.queries⟩
        have hfilt : Finset.univ.filter (fun r : Fin V => r.val < cr + 1) =
            insert r₀ (Finset.univ.filter (fun r : Fin V => r.val < cr)) := by
          ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hr
            by_cases hrc : r.val = cr
            · exact Or.inl (Fin.ext hrc)
            · exact Or.inr (by omega)
          · rintro (rfl | hr)
            · dsimp [r₀]; omega
            · omega
        have hnotmem : r₀ ∉ Finset.univ.filter (fun r : Fin V => r.val < cr) := by
          simp [r₀]
        refine ⟨s3, Stmt.Exec.seq el1 (Stmt.Exec.seq el2 eadd),
          by
            simp only [s3, Function.update_of_ne (by simp : mCnt4 ≠ mAcc)]
            rw [hpr2 mCnt4 (by simp) (by simp), hpr1 mCnt4 (by simp) (by simp)]
            exact hcnt,
          by
            simp only [s3, Function.update_of_ne (by simp : mV ≠ mAcc)]
            rw [hpr2 mV (by simp) (by simp), hpr1 mV (by simp) (by simp)]
            exact hbnd,
          hm2.trans (hm1.trans hm),
          hq2.trans (hq1.trans hq),
          ?_, ?_⟩
        · simp only [s3, Function.update_self, hfilt, Finset.sum_insert hnotmem, hacc]
          ring
        · intro c r1 r2 r3 r4 r5 r6
          have hne_acc : mCore c ≠ mAcc := fun e => r3 (by simpa using e)
          have hne_va : mCore c ≠ mValA := fun e => r4 (by simpa using e)
          have hne_vb : mCore c ≠ mValB := fun e => r5 (by simpa using e)
          have hne_addr : mCore c ≠ mAddr := fun e => r6 (by simpa using e)
          simp only [s3, Function.update_of_ne hne_acc]
          rw [hpr2 (mCore c) hne_vb hne_addr, hpr1 (mCore c) hne_va hne_addr]
          exact hpr c r1 r2 r3 r4 r5 r6)
      st₀ hv0
      ⟨rfl, rfl, by simp [st₀], fun c _ _ r3 _ _ _ => by
        have hne : mCore c ≠ mAcc := fun e => r3 (by simpa using e)
        simp only [st₀, Function.update_of_ne hne]⟩
  obtain ⟨hm', hq', hacc', hpr'⟩ := hInv
  have hfilt_all : Finset.univ.filter (fun r : Fin V => r.val < V) = Finset.univ := by
    ext r; simp
  rw [hfilt_all] at hacc'
  refine ⟨st', Stmt.Exec.seq eacc0 eloop, hm', hq', ?_, ?_, hpr'⟩
  · rw [hacc']
    exact Finset.sum_nonneg fun r _ => mul_self_nonneg _
  · rw [hacc', Finset.sum_eq_zero_iff_of_nonneg (fun r _ => mul_self_nonneg _)]
    constructor
    · intro hall
      funext r
      have hr := mul_self_eq_zero.1 (hall r (Finset.mem_univ r))
      linarith
    · rintro rfl r _
      simp

def checkCandNew (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mIsNew (PExpr.const 1))
    (Stmt.forNat mCnt3 mCurN mCond3
      (.seq (diffSqRow d)
        (.ite mAcc .skip (Stmt.assign mIsNew (PExpr.const 0)) .skip)))

theorem checkCandNew_spec {d V cur_n : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (faceBit : Fin cur_n → Fin V → ℝ) (cand : Fin V → ℝ) (faceBase : ℕ)
    (st : RS (MainReg d))
    (hfb_mem : ∀ (i : Fin cur_n) (r : Fin V), st.mem (faceBase + i.val * V + r.val) = faceBit i r)
    (hcand_mem : ∀ r : Fin V, st.mem (faceBase + cur_n * V + r.val) = cand r)
    (hV : st.regs mV = (V : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hCurN : st.regs mCurN = (cur_n : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (checkCandNew d) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      ((st'.regs mIsNew = 1 ∧ ∀ i : Fin cur_n, cand ≠ faceBit i) ∨
       (st'.regs mIsNew = 0 ∧ cand ∈ Set.range faceBit)) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 16 →
        c ≠ Sum.inl 17 → c ≠ Sum.inl 18 → c ≠ Sum.inl 19 →
        c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  have eis := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mIsNew
    (PExpr.const 1) st 1 (by simp)
  let st₀ : RS (MainReg d) := ⟨Function.update st.regs mIsNew 1, st.mem, st.queries⟩
  have hcn0 : st₀.regs mCurN = (cur_n : ℝ) := by simp [st₀, hCurN]
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt3) (boundReg := mCurN) (condReg := mCond3)
      (by simp) (by simp) (by simp)
      (body := .seq (diffSqRow d) (.ite mAcc .skip (Stmt.assign mIsNew (PExpr.const 0)) .skip))
      (fun t s =>
        s.mem = st.mem ∧ s.queries = st.queries ∧
        ((s.regs mIsNew = 1 ∧ ∀ i : Fin cur_n, i.val < t → cand ≠ faceBit i) ∨
         (s.regs mIsNew = 0 ∧ ∃ i : Fin cur_n, i.val < t ∧ cand = faceBit i)) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 16 →
          c ≠ Sum.inl 17 → c ≠ Sum.inl 18 → c ≠ Sum.inl 19 →
          c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
          s.regs (mCore c) = st.regs (mCore c)))
      (by
        intro t s v₁ v₂ ⟨hm, hq, hflag, hpr⟩
        refine ⟨hm, hq, ?_, ?_⟩
        · simpa using hflag
        · intro c r1 r2 r3 r4 r5 r6 r7 r8 r9
          have hne1 : mCore c ≠ mCond3 := fun e => r2 (by simpa using e)
          have hne2 : mCore c ≠ mCnt3 := fun e => r1 (by simpa using e)
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hpr c r1 r2 r3 r4 r5 r6 r7 r8 r9)
      (by
        intro t ht s hcnt hbnd _ ⟨hm, hq, hflag, hpr⟩
        let i₀ : Fin cur_n := ⟨t, ht⟩
        have hv_s : s.regs mV = (V : ℝ) :=
          (hpr (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hV
        have hfb_s : s.regs mFaceBase = (faceBase : ℝ) :=
          (hpr (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hFb
        obtain ⟨s1, ediff, hm1, hq1, hacc_nn, hacc_iff, hpr1⟩ :=
          diffSqRow_spec (oracle := oracle) cand (faceBit i₀) faceBase t s
            (fun r => by rw [hm, hcand_mem r])
            (fun r => by rw [hm, hfb_mem i₀ r])
            hv_s hfb_s hbnd hcnt
        have his1 : s1.regs mIsNew = s.regs mIsNew :=
          hpr1 (Sum.inl 18) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        have hcnt1 : s1.regs mCnt3 = (t : ℝ) :=
          (hpr1 (Sum.inl 14) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcnt
        have hbnd1 : s1.regs mCurN = (cur_n : ℝ) :=
          (hpr1 (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hbnd
        by_cases heq0 : s1.regs mAcc = 0
        · have hce : cand = faceBit i₀ := hacc_iff.1 heq0
          have ez := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mIsNew
            (PExpr.const 0) s1 0 (by simp)
          let s2 : RS (MainReg d) := ⟨Function.update s1.regs mIsNew 0, s1.mem, s1.queries⟩
          refine ⟨s2, Stmt.Exec.seq ediff (Stmt.Exec.ite_zero heq0 ez),
            by simp [s2, hcnt1], by simp [s2, hbnd1],
            hm1.trans hm, hq1.trans hq,
            Or.inr ⟨by simp [s2], i₀, by dsimp [i₀]; omega, hce⟩, ?_⟩
          intro c r1 r2 r3 r4 r5 r6 r7 r8 r9
          have hne_is : mCore c ≠ mIsNew := fun e => r5 (by simpa using e)
          simp only [s2, Function.update_of_ne hne_is]
          rw [hpr1 c r3 r4 r6 r7 r8 r9]
          exact hpr c r1 r2 r3 r4 r5 r6 r7 r8 r9
        · have hpos : 0 < s1.regs mAcc := lt_of_le_of_ne hacc_nn (Ne.symm heq0)
          have hcne : cand ≠ faceBit i₀ := fun h => heq0 (hacc_iff.2 h)
          refine ⟨s1, Stmt.Exec.seq ediff (Stmt.Exec.ite_pos hpos (Stmt.Exec.skip s1)),
            hcnt1, hbnd1, hm1.trans hm, hq1.trans hq, ?_, ?_⟩
          · rw [his1]
            rcases hflag with ⟨h1, hall⟩ | ⟨h0, i, hi, hci⟩
            · left
              refine ⟨h1, fun i hi => ?_⟩
              by_cases hit : i.val = t
              · have hie : i = i₀ := Fin.ext hit
                rw [hie]; exact hcne
              · exact hall i (by omega)
            · exact Or.inr ⟨h0, i, by omega, hci⟩
          · intro c r1 r2 r3 r4 r5 r6 r7 r8 r9
            rw [hpr1 c r3 r4 r6 r7 r8 r9]
            exact hpr c r1 r2 r3 r4 r5 r6 r7 r8 r9)
      st₀ hcn0
      ⟨rfl, rfl, Or.inl ⟨by simp [st₀], fun _ h => by omega⟩,
       fun c _ _ _ _ r5 _ _ _ _ => by
        have hne : mCore c ≠ mIsNew := fun e => r5 (by simpa using e)
        simp only [st₀, Function.update_of_ne hne]⟩
  obtain ⟨hm', hq', hflag', hpr'⟩ := hInv
  refine ⟨st', Stmt.Exec.seq eis eloop, hm', hq', ?_, hpr'⟩
  · rcases hflag' with ⟨h1, hall⟩ | ⟨h0, i, _, hci⟩
    · exact Or.inl ⟨h1, fun i => hall i i.isLt⟩
    · exact Or.inr ⟨h0, i, hci.symm⟩

def closeFacesStep (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mOldN (PExpr.reg mCurN))
    (Stmt.forNat mCnt2 mOldN mCond2
      (.seq (writeCandRow d)
        (.seq (checkCandNew d)
          (.ite mIsNew .skip .skip
            (Stmt.assign mCurN (PExpr.reg mCurN + PExpr.const 1))))))

theorem closeFacesStep_spec {d k V old_n : ℕ}
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ)
    (faceBit₀ : Fin old_n → Fin V → ℝ) (incBase faceBase cj : ℕ)
    (hcj : cj < k) (hfb_eq : faceBase = incBase + k * V) (hold_ge : 2 ≤ old_n)
    (hf₀_inj : Function.Injective faceBit₀)
    (hf₀_zo : ∀ i r, faceBit₀ i r = 0 ∨ faceBit₀ i r = 1)
    (hf₀_range : Set.range faceBit₀ = FaceSet a vVec cj)
    (st : RS (MainReg d))
    (hinc_mem : ∀ (j : Fin k) (r : Fin V), st.mem (incBase + j.val * V + r.val) =
      if dot (a j) (vVec r) = 1 then 1 else 0)
    (hfb_mem : ∀ (i : Fin old_n) (r : Fin V), st.mem (faceBase + i.val * V + r.val) = faceBit₀ i r)
    (hV : st.regs mV = (V : ℝ)) (hK : st.regs mK = (k : ℝ))
    (hInc : st.regs mIncBase = (incBase : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hCurN : st.regs mCurN = (old_n : ℝ)) (hcj_reg : st.regs mCnt1 = (cj : ℝ)) :
    ∃ (st' : RS (MainReg d)) (new_n : ℕ) (faceBit' : Fin new_n → Fin V → ℝ),
      Stmt.Exec oracle mainQr (closeFacesStep d) st st' ∧
      2 ≤ new_n ∧
      st'.queries = st.queries ∧
      st'.regs mV = (V : ℝ) ∧ st'.regs mK = (k : ℝ) ∧
      st'.regs mIncBase = (incBase : ℝ) ∧ st'.regs mFaceBase = (faceBase : ℝ) ∧
      st'.regs mCurN = (new_n : ℝ) ∧ st'.regs mCnt1 = (cj : ℝ) ∧
      Function.Injective faceBit' ∧
      (∀ i r, faceBit' i r = 0 ∨ faceBit' i r = 1) ∧
      Set.range faceBit' = FaceSet a vVec (cj + 1) ∧
      (∀ (j : Fin k) (r : Fin V), st'.mem (incBase + j.val * V + r.val) =
        if dot (a j) (vVec r) = 1 then 1 else 0) ∧
      (∀ (i : Fin new_n) (r : Fin V), st'.mem (faceBase + i.val * V + r.val) = faceBit' i r) := by
  let j₀ : Fin k := ⟨cj, hcj⟩
  let incRow : Fin V → ℝ := fun r => if dot (a j₀) (vVec r) = 1 then 1 else 0
  have eold := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mOldN
    (PExpr.reg mCurN) st (old_n : ℝ) (by simp [hCurN])
  let st₀ : RS (MainReg d) := ⟨Function.update st.regs mOldN (old_n : ℝ), st.mem, st.queries⟩
  have hold0 : st₀.regs mOldN = (old_n : ℝ) := by simp [st₀]
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt2) (boundReg := mOldN) (condReg := mCond2)
      (by simp) (by simp) (by simp)
      (body := .seq (writeCandRow d)
        (.seq (checkCandNew d)
          (.ite mIsNew .skip .skip (Stmt.assign mCurN (PExpr.reg mCurN + PExpr.const 1)))))
      (fun idx s =>
        s.queries = st.queries ∧
        s.regs mV = (V : ℝ) ∧ s.regs mK = (k : ℝ) ∧
        s.regs mIncBase = (incBase : ℝ) ∧ s.regs mFaceBase = (faceBase : ℝ) ∧
        s.regs mCnt1 = (cj : ℝ) ∧
        (∀ addr, addr < faceBase → s.mem addr = st.mem addr) ∧
        ∃ (cur_n : ℕ) (faceBit : Fin cur_n → Fin V → ℝ) (hle : old_n ≤ cur_n),
          s.regs mCurN = (cur_n : ℝ) ∧
          (∀ i : Fin old_n, faceBit ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩ = faceBit₀ i) ∧
          Function.Injective faceBit ∧
          (∀ i r, faceBit i r = 0 ∨ faceBit i r = 1) ∧
          Set.range faceBit ⊆ FaceSet a vVec (cj + 1) ∧
          (∀ i : Fin old_n, i.val < idx →
            (fun r => faceBit₀ i r * incRow r) ∈ Set.range faceBit) ∧
          (∀ (i : Fin cur_n) (r : Fin V), s.mem (faceBase + i.val * V + r.val) = faceBit i r))
      (by
        intro idx s v₁ v₂ ⟨hq, hv, hk, hi, hf, hc1, hlow, cur_n, faceBit, hle, hcn, hpre, hinj, hzo, hsub, hcov, hmem⟩
        refine ⟨hq, ?_, ?_, ?_, ?_, ?_, hlow, cur_n, faceBit, hle, ?_, hpre, hinj, hzo, hsub, hcov, hmem⟩ <;>
          simp [hv, hk, hi, hf, hc1, hcn])
      (by
        intro idx hidx s hcnt hbnd _
          ⟨hq, hv, hk, hi, hf, hc1, hlow, cur_n, faceBit, hle, hcn, hpre, hinj, hzo, hsub, hcov, hmem⟩
        let i₀ : Fin old_n := ⟨idx, hidx⟩
        have hidx_cur : idx < cur_n := Nat.lt_of_lt_of_le hidx hle
        have hrow_s : ∀ r : Fin V, s.mem (faceBase + idx * V + r.val) = faceBit₀ i₀ r := by
          intro r
          have hm := hmem ⟨idx, hidx_cur⟩ r
          rw [hpre i₀] at hm
          exact hm
        have hinc_s : ∀ r : Fin V, s.mem (incBase + cj * V + r.val) = incRow r := by
          intro r
          rw [hlow _ (by have := r.isLt; nlinarith), hinc_mem j₀ r]
        obtain ⟨s1, ew, hq1, hcand_mem1, hlow1, hpr1⟩ :=
          writeCandRow_spec (oracle := oracle) (faceBit₀ i₀) incRow incBase faceBase cj idx
            hcj hidx_cur hfb_eq s hrow_s hinc_s hv hi hf hcn hc1 hcnt
        let cand : Fin V → ℝ := fun r => faceBit₀ i₀ r * incRow r
        have hv1 : s1.regs mV = (V : ℝ) :=
          (hpr1 (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hv
        have hk1 : s1.regs mK = (k : ℝ) :=
          (hpr1 (Sum.inl 0) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hk
        have hi1 : s1.regs mIncBase = (incBase : ℝ) :=
          (hpr1 (Sum.inl 6) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hi
        have hf1 : s1.regs mFaceBase = (faceBase : ℝ) :=
          (hpr1 (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hf
        have hcn1 : s1.regs mCurN = (cur_n : ℝ) :=
          (hpr1 (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcn
        have hold1 : s1.regs mOldN = (old_n : ℝ) :=
          (hpr1 (Sum.inl 9) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hbnd
        have hc1_1 : s1.regs mCnt1 = (cj : ℝ) :=
          (hpr1 (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hc1
        have hcnt1 : s1.regs mCnt2 = (idx : ℝ) :=
          (hpr1 (Sum.inl 12) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcnt
        have hfb_mem1 : ∀ (i : Fin cur_n) (r : Fin V), s1.mem (faceBase + i.val * V + r.val) = faceBit i r := by
          intro i r
          rw [hlow1 _ (by have := i.isLt; have := r.isLt; nlinarith)]
          exact hmem i r
        obtain ⟨s2, echk, hm2, hq2, hflag, hpr2⟩ :=
          checkCandNew_spec (oracle := oracle) faceBit cand faceBase s1 hfb_mem1 hcand_mem1 hv1 hf1 hcn1
        have hv2 : s2.regs mV = (V : ℝ) :=
          (hpr2 (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hv1
        have hk2 : s2.regs mK = (k : ℝ) :=
          (hpr2 (Sum.inl 0) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hk1
        have hi2 : s2.regs mIncBase = (incBase : ℝ) :=
          (hpr2 (Sum.inl 6) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hi1
        have hf2 : s2.regs mFaceBase = (faceBase : ℝ) :=
          (hpr2 (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hf1
        have hcn2 : s2.regs mCurN = (cur_n : ℝ) :=
          (hpr2 (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hcn1
        have hold2 : s2.regs mOldN = (old_n : ℝ) :=
          (hpr2 (Sum.inl 9) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hold1
        have hc1_2 : s2.regs mCnt1 = (cj : ℝ) :=
          (hpr2 (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hc1_1
        have hcnt2 : s2.regs mCnt2 = (idx : ℝ) :=
          (hpr2 (Sum.inl 12) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hcnt1
        have hlow2 : ∀ addr, addr < faceBase → s2.mem addr = st.mem addr := by
          intro addr haddr
          rw [hm2, hlow1 addr (by omega)]
          exact hlow addr haddr
        have hcand_zo : ∀ r, cand r = 0 ∨ cand r = 1 := by
          intro r
          dsimp [cand, incRow]
          rcases hf₀_zo i₀ r with h0 | h1
          · split_ifs <;> simp [h0]
          · split_ifs <;> simp [h1]
        have hcand_in_next : cand ∈ FaceSet a vVec (cj + 1) := by
          have hi₀_in : faceBit₀ i₀ ∈ FaceSet a vVec cj := by
            rw [← hf₀_range]; exact ⟨i₀, rfl⟩
          rcases hi₀_in with hzero | ⟨J, hJ, hfbJ⟩
          · left
            funext r; dsimp [cand]; rw [congrFun hzero r, zero_mul]
          · right
            refine ⟨insert j₀ J, ?_, ?_⟩
            · intro j hj
              rcases Finset.mem_insert.1 hj with rfl | hjJ
              · dsimp [j₀]; omega
              · have := hJ j hjJ; omega
            · funext r
              dsimp [cand, incRow]
              rw [congrFun hfbJ r]
              exact incBit_insert a vVec j₀ J r
        rcases hflag with ⟨his1, hcand_new⟩ | ⟨his0, hcand_old⟩
        · have hpos : 0 < s2.regs mIsNew := by linarith
          have einc_n := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mCurN
            (PExpr.reg mCurN + PExpr.const 1) s2 ((cur_n + 1 : ℕ) : ℝ)
            (by simp [hcn2])
          let s3 : RS (MainReg d) :=
            ⟨Function.update s2.regs mCurN ((cur_n + 1 : ℕ) : ℝ), s2.mem, s2.queries⟩
          let faceBit' := snocVec faceBit cand
          refine ⟨s3,
            Stmt.Exec.seq ew (Stmt.Exec.seq echk (Stmt.Exec.ite_pos hpos einc_n)),
            by simp [s3, hcnt2], by simp [s3, hold2],
            hq2.trans (hq1.trans hq),
            by simp [s3, hv2], by simp [s3, hk2], by simp [s3, hi2], by simp [s3, hf2],
            by simp [s3, hc1_2], hlow2,
            cur_n + 1, faceBit', by omega, by simp [s3], ?_,
            snocVec_injective hinj hcand_new, ?_, ?_, ?_, ?_⟩
          · intro i
            dsimp only [faceBit']
            rw [snocVec_lt _ _ ⟨i.val, _⟩ (Nat.lt_of_lt_of_le i.isLt hle)]
            exact hpre i
          · intro i r
            dsimp only [faceBit']
            by_cases hi_lt : i.val < cur_n
            · rw [snocVec_lt _ _ i hi_lt]; exact hzo ⟨i.val, hi_lt⟩ r
            · have hie : i = ⟨cur_n, Nat.lt_succ_self cur_n⟩ := Fin.ext (by dsimp; omega)
              rw [hie, snocVec_last]; exact hcand_zo r
          · dsimp only [faceBit']
            rw [snocVec_range]
            rintro b (rfl | hb)
            · exact hcand_in_next
            · exact hsub hb
          · intro i hi_lt
            dsimp only [faceBit']
            rw [snocVec_range]
            by_cases hie : i.val = idx
            · have hi_eq : i = i₀ := Fin.ext hie
              rw [hi_eq]; exact Or.inl rfl
            · exact Or.inr (hcov i (by omega))
          · intro i r
            change s2.mem _ = _
            rw [hm2]
            dsimp only [faceBit']
            by_cases hi_lt : i.val < cur_n
            · rw [snocVec_lt _ _ i hi_lt]; exact hfb_mem1 ⟨i.val, hi_lt⟩ r
            · have hie : i = ⟨cur_n, Nat.lt_succ_self cur_n⟩ := Fin.ext (by dsimp; omega)
              rw [hie, snocVec_last]; exact hcand_mem1 r
        · refine ⟨s2,
            Stmt.Exec.seq ew (Stmt.Exec.seq echk (Stmt.Exec.ite_zero his0 (Stmt.Exec.skip s2))),
            hcnt2, hold2, hq2.trans (hq1.trans hq),
            hv2, hk2, hi2, hf2, hc1_2, hlow2,
            cur_n, faceBit, hle, hcn2, hpre, hinj, hzo, hsub, ?_, ?_⟩
          · intro i hi_lt
            by_cases hie : i.val = idx
            · have hi_eq : i = i₀ := Fin.ext hie
              rw [hi_eq]; exact hcand_old
            · exact hcov i (by omega)
          · intro i r
            rw [hm2]; exact hfb_mem1 i r)
      st₀ hold0
      ⟨rfl, by simp [st₀, hV], by simp [st₀, hK], by simp [st₀, hInc], by simp [st₀, hFb],
       by simp [st₀, hcj_reg], fun _ _ => rfl,
       old_n, faceBit₀, le_refl _, by simp [st₀, hCurN], fun _ => rfl,
       hf₀_inj, hf₀_zo,
       by
         rw [hf₀_range]
         rintro b (rfl | ⟨J, hJ, rfl⟩)
         · exact Or.inl rfl
         · exact Or.inr ⟨J, fun j hj => by have := hJ j hj; omega, rfl⟩,
       fun _ h => by omega, hfb_mem⟩
  obtain ⟨hq', hv', hk', hi', hf', hc1', hlow', new_n, faceBit', hle', hcn', hpre', hinj', hzo', hsub', hcov', hmem'⟩ := hInv
  refine ⟨st', new_n, faceBit', Stmt.Exec.seq eold eloop, by omega,
    hq', hv', hk', hi', hf', hcn', hc1', hinj', hzo', ?_, ?_, hmem'⟩
  · apply Set.Subset.antisymm hsub'
    rintro b (rfl | ⟨J, hJ, rfl⟩)
    · have h0_in : (fun _ : Fin V => (0 : ℝ)) ∈ Set.range faceBit₀ := by
        rw [hf₀_range]; exact Or.inl rfl
      obtain ⟨i, hi⟩ := h0_in
      exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hle'⟩, by rw [hpre' i, hi]⟩
    · by_cases hj₀J : j₀ ∈ J
      · let J' := J.erase j₀
        have hJ'_lt : ∀ j ∈ J', j.val < cj := by
          intro j hj
          have hne : j ≠ j₀ := (Finset.mem_erase.1 hj).1
          have hjJ : j ∈ J := (Finset.mem_erase.1 hj).2
          have hlt1 := hJ j hjJ
          have hval_ne : j.val ≠ cj := fun e => hne (Fin.ext e)
          omega
        have hJ'_in : incBit a vVec J' ∈ Set.range faceBit₀ := by
          rw [hf₀_range]; exact Or.inr ⟨J', hJ'_lt, rfl⟩
        obtain ⟨i, hi⟩ := hJ'_in
        have hins : insert j₀ J' = J := Finset.insert_erase hj₀J
        have hmul : (fun r => faceBit₀ i r * incRow r) = incBit a vVec J := by
          funext r
          rw [congrFun hi r]
          dsimp [incRow]
          rw [incBit_insert a vVec j₀ J' r, hins]
        rw [← hmul]
        exact hcov' i i.isLt
      · have hJ_lt : ∀ j ∈ J, j.val < cj := by
          intro j hj
          have hne : j ≠ j₀ := fun e => hj₀J (e ▸ hj)
          have hlt1 := hJ j hj
          have hval_ne : j.val ≠ cj := fun e => hne (Fin.ext e)
          omega
        have hJ_in : incBit a vVec J ∈ Set.range faceBit₀ := by
          rw [hf₀_range]; exact Or.inr ⟨J, hJ_lt, rfl⟩
        obtain ⟨i, hi⟩ := hJ_in
        exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hle'⟩, by rw [hpre' i, hi]⟩
  · intro j r
    rw [hlow' _ (by have := j.isLt; have := r.isLt; nlinarith)]
    exact hinc_mem j r

def closeFaces (d : ℕ) : Stmt (MainReg d) :=
  .seq (initFaceRows d)
    (Stmt.forNat mCnt1 mK mCond1 (closeFacesStep d))

theorem closeFaces_spec {d k V : ℕ} (hV_pos : 0 < V)
    {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (a : Fin k → Fin d → ℝ) (vVec : Fin V → Fin d → ℝ) (incBase : ℕ)
    (st : RS (MainReg d))
    (hK : st.regs mK = (k : ℝ)) (hV : st.regs mV = (V : ℝ))
    (hInc : st.regs mIncBase = (incBase : ℝ))
    (hinc_mem : ∀ (j : Fin k) (r : Fin V), st.mem (incBase + j.val * V + r.val) =
      if dot (a j) (vVec r) = 1 then 1 else 0) :
    let faceBase := incBase + k * V
    ∃ (st' : RS (MainReg d)) (n : ℕ) (faceBit : Fin n → Fin V → ℝ),
      Stmt.Exec oracle mainQr (closeFaces d) st st' ∧
      2 ≤ n ∧
      st'.queries = st.queries ∧
      st'.regs mV = (V : ℝ) ∧
      st'.regs mFaceBase = (faceBase : ℝ) ∧
      st'.regs mCurN = (n : ℝ) ∧
      Function.Injective faceBit ∧
      (∀ i r, faceBit i r = 0 ∨ faceBit i r = 1) ∧
      Set.range faceBit =
        { fun _ : Fin V => (0 : ℝ) } ∪
          Set.range (fun J : Finset (Fin k) => fun r : Fin V =>
            if ∀ j ∈ J, dot (a j) (vVec r) = 1 then (1 : ℝ) else 0) ∧
      (∀ (i : Fin n) (r : Fin V), st'.mem (faceBase + i.val * V + r.val) = faceBit i r) := by
  intro faceBase
  obtain ⟨st₀, faceBit₀, einit, hq0, hk0, hv0, hi0, hf0, hcn0, hinj0, hzo0, hrng0, hfb0, hlow0⟩ :=
    initFaceRows_spec hV_pos a vVec incBase st hK hV hInc
  have hinc0 : ∀ (j : Fin k) (r : Fin V), st₀.mem (incBase + j.val * V + r.val) =
      if dot (a j) (vVec r) = 1 then 1 else 0 := by
    intro j r
    rw [hlow0 _ (by have := j.isLt; have := r.isLt; nlinarith)]
    exact hinc_mem j r
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt1) (boundReg := mK) (condReg := mCond1)
      (by simp) (by simp) (by simp)
      (fun cj s =>
        s.queries = st.queries ∧
        s.regs mV = (V : ℝ) ∧ s.regs mIncBase = (incBase : ℝ) ∧
        s.regs mFaceBase = (faceBase : ℝ) ∧
        (∀ (j : Fin k) (r : Fin V), s.mem (incBase + j.val * V + r.val) =
          if dot (a j) (vVec r) = 1 then 1 else 0) ∧
        ∃ (cur_n : ℕ) (faceBit : Fin cur_n → Fin V → ℝ),
          2 ≤ cur_n ∧
          s.regs mCurN = (cur_n : ℝ) ∧
          Function.Injective faceBit ∧
          (∀ i r, faceBit i r = 0 ∨ faceBit i r = 1) ∧
          Set.range faceBit = FaceSet a vVec cj ∧
          (∀ (i : Fin cur_n) (r : Fin V), s.mem (faceBase + i.val * V + r.val) = faceBit i r))
      (by
        intro cj s v₁ v₂ ⟨hq, hv, hi, hf, hinc, cur_n, faceBit, hge, hcn, hinj, hzo, hrng, hmem⟩
        refine ⟨hq, ?_, ?_, ?_, hinc, cur_n, faceBit, hge, ?_, hinj, hzo, hrng, hmem⟩ <;>
          simp [hv, hi, hf, hcn])
      (by
        intro cj hcj s hcnt hbnd _
          ⟨hq, hv, hi, hf, hinc, cur_n, faceBit, hge, hcn, hinj, hzo, hrng, hmem⟩
        obtain ⟨s1, new_n, faceBit', estep, hge', hq1, hv1, hk1, hi1, hf1, hcn1, hc1, hinj', hzo', hrng', hinc1, hmem1⟩ :=
          closeFacesStep_spec a vVec faceBit incBase faceBase cj hcj rfl hge
            hinj hzo hrng s hinc hmem hv hbnd hi hf hcn hcnt
        exact ⟨s1, estep, hc1, hk1, hq1.trans hq, hv1, hi1, hf1, hinc1,
          new_n, faceBit', hge', hcn1, hinj', hzo', hrng', hmem1⟩)
      st₀ hk0
      ⟨hq0, hv0, hi0, hf0, hinc0, 2, faceBit₀, le_refl _, hcn0, hinj0, hzo0, hrng0, hfb0⟩
  obtain ⟨hq', hv', _, hf', _, n, faceBit, hge', hcn', hinj', hzo', hrng', hmem'⟩ := hInv
  have hfs_k : FaceSet a vVec k =
      { fun _ : Fin V => (0 : ℝ) } ∪
        Set.range (fun J : Finset (Fin k) => fun r : Fin V =>
          if ∀ j ∈ J, dot (a j) (vVec r) = 1 then (1 : ℝ) else 0) := by
    ext b; dsimp only [FaceSet, incBit]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | ⟨J, _, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨J, rfl⟩
    · rintro (rfl | ⟨J, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨J, fun j _ => j.isLt, rfl⟩
  rw [hfs_k] at hrng'
  exact ⟨st', n, faceBit, Stmt.Exec.seq einit eloop,
    hge', hq', hv', hf', hcn', hinj', hzo', hrng', hmem'⟩

/-! ### Post-loop Phase 3: Writing the face-lattice encoding to `outBase` -/

def computeViol (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mAcc (PExpr.const 0))
    (Stmt.forNat mCnt3 mV mCond3
      (.seq
        (loadAt mValA (PExpr.reg mFaceBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt3))
        (.seq
          (loadAt mValB (PExpr.reg mFaceBase + PExpr.reg mCnt2 * PExpr.reg mV + PExpr.reg mCnt3))
          (Stmt.assign mAcc
            (PExpr.reg mAcc + PExpr.reg mValA * (PExpr.const 1 - PExpr.reg mValB))))))

theorem computeViol_spec {d V : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (rowI rowJ : Fin V → ℝ) (faceBase ci cj : ℕ)
    (st : RS (MainReg d))
    (hi_mem : ∀ r : Fin V, st.mem (faceBase + ci * V + r.val) = rowI r)
    (hj_mem : ∀ r : Fin V, st.mem (faceBase + cj * V + r.val) = rowJ r)
    (hV : st.regs mV = (V : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hci_reg : st.regs mCnt1 = (ci : ℝ)) (hcj_reg : st.regs mCnt2 = (cj : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (computeViol d) st st' ∧
      st'.mem = st.mem ∧ st'.queries = st.queries ∧
      st'.regs mAcc = (∑ r : Fin V, rowI r * (1 - rowJ r)) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 19 →
        c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  have eacc0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAcc
    (PExpr.const 0) st 0 (by simp)
  let st₀ : RS (MainReg d) := ⟨Function.update st.regs mAcc 0, st.mem, st.queries⟩
  have hv0 : st₀.regs mV = (V : ℝ) := by simp [st₀, hV]
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt3) (boundReg := mV) (condReg := mCond3)
      (by simp) (by simp) (by simp)
      (fun cr s =>
        s.mem = st.mem ∧ s.queries = st.queries ∧
        s.regs mAcc =
          (∑ r ∈ Finset.univ.filter (fun r : Fin V => r.val < cr),
            rowI r * (1 - rowJ r)) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 14 → c ≠ Sum.inl 15 → c ≠ Sum.inl 19 →
          c ≠ Sum.inl 20 → c ≠ Sum.inl 21 → c ≠ Sum.inl 22 →
          s.regs (mCore c) = st.regs (mCore c)))
      (by
        intro cr s v₁ v₂ ⟨hm, hq, hacc, hpr⟩
        refine ⟨hm, hq, ?_, ?_⟩
        · simp [hacc]
        · intro c r1 r2 r3 r4 r5 r6
          have hne1 : mCore c ≠ mCond3 := fun e => r2 (by simpa using e)
          have hne2 : mCore c ≠ mCnt3 := fun e => r1 (by simpa using e)
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hpr c r1 r2 r3 r4 r5 r6)
      (by
        intro cr hcr s hcnt hbnd _ ⟨hm, hq, hacc, hpr⟩
        let r₀ : Fin V := ⟨cr, hcr⟩
        have hfb_s : s.regs mFaceBase = (faceBase : ℝ) :=
          (hpr (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hFb
        have hci_s : s.regs mCnt1 = (ci : ℝ) :=
          (hpr (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hci_reg
        have hcj_s : s.regs mCnt2 = (cj : ℝ) :=
          (hpr (Sum.inl 12) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcj_reg
        obtain ⟨s1, el1, hm1, hq1, hva1, hpr1⟩ :=
          loadAt_spec (oracle := oracle) mValA
            (PExpr.reg mFaceBase + PExpr.reg mCnt1 * PExpr.reg mV + PExpr.reg mCnt3)
            s (faceBase + ci * V + cr) (by simp [hfb_s, hci_s, hbnd, hcnt])
        have hva1_eq : s1.regs mValA = rowI r₀ := by
          rw [hva1, hm, hi_mem r₀]
        obtain ⟨s2, el2, hm2, hq2, hvb2, hpr2⟩ :=
          loadAt_spec (oracle := oracle) mValB
            (PExpr.reg mFaceBase + PExpr.reg mCnt2 * PExpr.reg mV + PExpr.reg mCnt3)
            s1 (faceBase + cj * V + cr)
            (by
              simp only [PExpr.eval_add, PExpr.eval_mul, PExpr.eval_reg]
              rw [hpr1 mFaceBase (by simp) (by simp), hpr1 mCnt2 (by simp) (by simp),
                hpr1 mV (by simp) (by simp), hpr1 mCnt3 (by simp) (by simp)]
              simp [hfb_s, hcj_s, hbnd, hcnt])
        have hvb2_eq : s2.regs mValB = rowJ r₀ := by
          rw [hvb2, hm1, hm, hj_mem r₀]
        have hva2_eq : s2.regs mValA = rowI r₀ :=
          (hpr2 mValA (by simp) (by simp)).trans hva1_eq
        have hacc2 : s2.regs mAcc = s.regs mAcc := by
          rw [hpr2 mAcc (by simp) (by simp), hpr1 mAcc (by simp) (by simp)]
        have eadd := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mAcc
          (PExpr.reg mAcc + PExpr.reg mValA * (PExpr.const 1 - PExpr.reg mValB)) s2
          (s.regs mAcc + rowI r₀ * (1 - rowJ r₀))
          (by simp [hacc2, hva2_eq, hvb2_eq])
        let s3 : RS (MainReg d) :=
          ⟨Function.update s2.regs mAcc (s.regs mAcc + rowI r₀ * (1 - rowJ r₀)),
           s2.mem, s2.queries⟩
        have hfilt : Finset.univ.filter (fun r : Fin V => r.val < cr + 1) =
            insert r₀ (Finset.univ.filter (fun r : Fin V => r.val < cr)) := by
          ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hr
            by_cases hrc : r.val = cr
            · exact Or.inl (Fin.ext hrc)
            · exact Or.inr (by omega)
          · rintro (rfl | hr)
            · dsimp [r₀]; omega
            · omega
        have hnotmem : r₀ ∉ Finset.univ.filter (fun r : Fin V => r.val < cr) := by
          simp [r₀]
        refine ⟨s3, Stmt.Exec.seq el1 (Stmt.Exec.seq el2 eadd),
          by
            simp only [s3, Function.update_of_ne (by simp : mCnt3 ≠ mAcc)]
            rw [hpr2 mCnt3 (by simp) (by simp), hpr1 mCnt3 (by simp) (by simp)]
            exact hcnt,
          by
            simp only [s3, Function.update_of_ne (by simp : mV ≠ mAcc)]
            rw [hpr2 mV (by simp) (by simp), hpr1 mV (by simp) (by simp)]
            exact hbnd,
          hm2.trans (hm1.trans hm),
          hq2.trans (hq1.trans hq),
          ?_, ?_⟩
        · simp only [s3, Function.update_self, hfilt, Finset.sum_insert hnotmem, hacc]
          ring
        · intro c r1 r2 r3 r4 r5 r6
          have hne_acc : mCore c ≠ mAcc := fun e => r3 (by simpa using e)
          have hne_va : mCore c ≠ mValA := fun e => r4 (by simpa using e)
          have hne_vb : mCore c ≠ mValB := fun e => r5 (by simpa using e)
          have hne_addr : mCore c ≠ mAddr := fun e => r6 (by simpa using e)
          simp only [s3, Function.update_of_ne hne_acc]
          rw [hpr2 (mCore c) hne_vb hne_addr, hpr1 (mCore c) hne_va hne_addr]
          exact hpr c r1 r2 r3 r4 r5 r6)
      st₀ hv0
      ⟨rfl, rfl, by simp [st₀], fun c _ _ r3 _ _ _ => by
        have hne : mCore c ≠ mAcc := fun e => r3 (by simpa using e)
        simp only [st₀, Function.update_of_ne hne]⟩
  obtain ⟨hm', hq', hacc', hpr'⟩ := hInv
  have hfilt_all : Finset.univ.filter (fun r : Fin V => r.val < V) = Finset.univ := by
    ext r; simp
  rw [hfilt_all] at hacc'
  exact ⟨st', Stmt.Exec.seq eacc0 eloop, hm', hq', hacc', hpr'⟩

def writeMatrixRow (d : ℕ) : Stmt (MainReg d) :=
  Stmt.forNat mCnt2 mCurN mCond2
    (.seq (computeViol d)
      (.seq
        (.ite mAcc
          (Stmt.assign mScratch (PExpr.const 0))
          (Stmt.assign mScratch (PExpr.const 1))
          (Stmt.assign mScratch (PExpr.const 0)))
        (storeAt
          (PExpr.reg mOut + PExpr.reg mCurN + PExpr.const 1 +
            PExpr.reg mCnt1 * PExpr.reg mCurN + PExpr.reg mCnt2)
          mScratch)))

theorem writeMatrixRow_spec {d V n : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (faceBit : Fin n → Fin V → ℝ) (faceBase outBase : ℕ) (i₀ : Fin n)
    (hout_eq : outBase = faceBase + (n + 1) * V)
    (st : RS (MainReg d))
    (hfb_mem : ∀ (i : Fin n) (r : Fin V), st.mem (faceBase + i.val * V + r.val) = faceBit i r)
    (hV : st.regs mV = (V : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hOut : st.regs mOut = (outBase : ℝ)) (hCurN : st.regs mCurN = (n : ℝ))
    (hci : st.regs mCnt1 = (i₀.val : ℝ)) :
    ∃ st', Stmt.Exec oracle mainQr (writeMatrixRow d) st st' ∧
      st'.queries = st.queries ∧
      (∀ j : Fin n, st'.mem (outBase + n + 1 + i₀.val * n + j.val) =
        if (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j r)) = 0 then 1 else 0) ∧
      (∀ addr, addr < outBase + n + 1 + i₀.val * n → st'.mem addr = st.mem addr) ∧
      (∀ c : MainCore d, c ≠ Sum.inl 12 → c ≠ Sum.inl 13 → c ≠ Sum.inl 14 →
        c ≠ Sum.inl 15 → c ≠ Sum.inl 19 → c ≠ Sum.inl 20 →
        c ≠ Sum.inl 21 → c ≠ Sum.inl 22 → c ≠ Sum.inl 23 →
        st'.regs (mCore c) = st.regs (mCore c)) := by
  obtain ⟨st', eloop, _, _, _, hInv⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt2) (boundReg := mCurN) (condReg := mCond2)
      (by simp) (by simp) (by simp)
      (fun cj s =>
        s.queries = st.queries ∧
        (∀ j : Fin n, j.val < cj →
          s.mem (outBase + n + 1 + i₀.val * n + j.val) =
            if (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j r)) = 0 then 1 else 0) ∧
        (∀ addr, addr < outBase + n + 1 + i₀.val * n → s.mem addr = st.mem addr) ∧
        (∀ c : MainCore d, c ≠ Sum.inl 12 → c ≠ Sum.inl 13 → c ≠ Sum.inl 14 →
          c ≠ Sum.inl 15 → c ≠ Sum.inl 19 → c ≠ Sum.inl 20 →
          c ≠ Sum.inl 21 → c ≠ Sum.inl 22 → c ≠ Sum.inl 23 →
          s.regs (mCore c) = st.regs (mCore c)))
      (by
        intro cj s v₁ v₂ ⟨hq, hdone, hlow, hpr⟩
        refine ⟨hq, hdone, hlow, ?_⟩
        intro c r1 r2 r3 r4 r5 r6 r7 r8 r9
        have hne1 : mCore c ≠ mCond2 := fun e => r2 (by simpa using e)
        have hne2 : mCore c ≠ mCnt2 := fun e => r1 (by simpa using e)
        simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hpr c r1 r2 r3 r4 r5 r6 r7 r8 r9)
      (by
        intro cj hcj s hcnt hbnd _ ⟨hq, hdone, hlow, hpr⟩
        let j₀ : Fin n := ⟨cj, hcj⟩
        have hv_s : s.regs mV = (V : ℝ) :=
          (hpr (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hV
        have hfb_s : s.regs mFaceBase = (faceBase : ℝ) :=
          (hpr (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hFb
        have hout_s : s.regs mOut = (outBase : ℝ) :=
          (hpr (Sum.inl 3) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hOut
        have hci_s : s.regs mCnt1 = (i₀.val : ℝ) :=
          (hpr (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hci
        have hfb_s_mem : ∀ (i : Fin n) (r : Fin V), s.mem (faceBase + i.val * V + r.val) = faceBit i r := by
          intro i r
          rw [hlow _ (by have := i.isLt; have := r.isLt; nlinarith), hfb_mem i r]
        obtain ⟨s1, eviol, hm1, hq1, hacc1, hpr1⟩ :=
          computeViol_spec (oracle := oracle) (faceBit i₀) (faceBit j₀) faceBase i₀.val cj s
            (hfb_s_mem i₀) (hfb_s_mem j₀) hv_s hfb_s hci_s hcnt
        let bitVal : ℝ := if (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j₀ r)) = 0 then 1 else 0
        have ebit : ∃ s2, Stmt.Exec oracle mainQr
            (.ite mAcc
              (Stmt.assign mScratch (PExpr.const 0))
              (Stmt.assign mScratch (PExpr.const 1))
              (Stmt.assign mScratch (PExpr.const 0))) s1 s2 ∧
            s2.mem = s1.mem ∧ s2.queries = s1.queries ∧
            s2.regs mScratch = bitVal ∧
            (∀ r, r ≠ mScratch → s2.regs r = s1.regs r) := by
          rcases lt_trichotomy (s1.regs mAcc) 0 with hlt | heq | hgt
          · have hne0 : (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j₀ r)) ≠ 0 := by linarith
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mScratch (PExpr.const 0) s1 0 (by simp)
            exact ⟨_, Stmt.Exec.ite_neg hlt ea, rfl, rfl, by simp [bitVal, hne0],
              fun r hr => by simp [Function.update_of_ne hr]⟩
          · have heq0 : (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j₀ r)) = 0 := by linarith
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mScratch (PExpr.const 1) s1 1 (by simp)
            exact ⟨_, Stmt.Exec.ite_zero heq ea, rfl, rfl, by simp [bitVal, heq0],
              fun r hr => by simp [Function.update_of_ne hr]⟩
          · have hne0 : (∑ r : Fin V, faceBit i₀ r * (1 - faceBit j₀ r)) ≠ 0 := by linarith
            have ea := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mScratch (PExpr.const 0) s1 0 (by simp)
            exact ⟨_, Stmt.Exec.ite_pos hgt ea, rfl, rfl, by simp [bitVal, hne0],
              fun r hr => by simp [Function.update_of_ne hr]⟩
        obtain ⟨s2, eite, hm2, hq2, hscr2, hpr2⟩ := ebit
        have hout2 : s2.regs mOut = (outBase : ℝ) := by
          rw [hpr2 mOut (by simp)]
          exact (hpr1 (Sum.inl 3) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hout_s
        have hcn2 : s2.regs mCurN = (n : ℝ) := by
          rw [hpr2 mCurN (by simp)]
          exact (hpr1 (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hbnd
        have hci2 : s2.regs mCnt1 = (i₀.val : ℝ) := by
          rw [hpr2 mCnt1 (by simp)]
          exact (hpr1 (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hci_s
        have hcnt2 : s2.regs mCnt2 = (cj : ℝ) := by
          rw [hpr2 mCnt2 (by simp)]
          exact (hpr1 (Sum.inl 12) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hcnt
        let targetAddr := outBase + n + 1 + i₀.val * n + cj
        obtain ⟨s3, es3, hm3, hq3, hpr3⟩ :=
          storeAt_spec (oracle := oracle)
            (PExpr.reg mOut + PExpr.reg mCurN + PExpr.const 1 +
              PExpr.reg mCnt1 * PExpr.reg mCurN + PExpr.reg mCnt2)
            mScratch (by simp) s2 targetAddr
            (by simp [hout2, hcn2, hci2, hcnt2, targetAddr])
        have hm2s : s2.mem = s.mem := hm2.trans hm1
        refine ⟨s3, Stmt.Exec.seq eviol (Stmt.Exec.seq eite es3),
          (hpr3 mCnt2 (by simp)).trans hcnt2,
          (hpr3 mCurN (by simp)).trans hcn2,
          hq3.trans (hq2.trans (hq1.trans hq)),
          ?_, ?_, ?_⟩
        · intro j hj
          rw [hm3]
          by_cases hjc : j.val = cj
          · have hje : j = j₀ := Fin.ext hjc
            rw [hjc, Function.update_self, hscr2, hje]
          · rw [Function.update_of_ne (by dsimp [targetAddr]; omega), hm2s]
            exact hdone j (by omega)
        · intro addr haddr
          rw [hm3, Function.update_of_ne (by dsimp [targetAddr]; omega), hm2s]
          exact hlow addr haddr
        · intro c r1 r2 r3 r4 r5 r6 r7 r8 r9
          have hne_addr : mCore c ≠ mAddr := fun e => r8 (by simpa using e)
          have hne_scr : mCore c ≠ mScratch := fun e => r9 (by simpa using e)
          rw [hpr3 (mCore c) hne_addr, hpr2 (mCore c) hne_scr, hpr1 c r3 r4 r5 r6 r7 r8]
          exact hpr c r1 r2 r3 r4 r5 r6 r7 r8 r9)
      st hCurN
      ⟨rfl, fun _ h => by omega, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨hq', hdone', hlow', hpr'⟩ := hInv
  exact ⟨st', eloop, hq', fun j => hdone' j j.isLt, hlow', hpr'⟩

def writeOutput (d : ℕ) : Stmt (MainReg d) :=
  .seq
    (Stmt.assign mOut (PExpr.reg mFaceBase + (PExpr.reg mCurN + PExpr.const 1) * PExpr.reg mV))
    (.seq
      (Stmt.assign mValA (PExpr.const 1))
      (.seq
        (Stmt.forNat mCnt1 mCurN mCond1
          (storeAt (PExpr.reg mOut + PExpr.reg mCnt1) mValA))
        (.seq
          (Stmt.assign mValA (PExpr.const 0))
          (.seq
            (storeAt (PExpr.reg mOut + PExpr.reg mCurN) mValA)
            (Stmt.forNat mCnt1 mCurN mCond1 (writeMatrixRow d))))))

theorem writeOutput_spec {d V n : ℕ} {oracle : (Fin d → ℝ) → Fin d → ℝ}
    (faceBit : Fin n → Fin V → ℝ) (faceBase : ℕ)
    (st : RS (MainReg d))
    (hV : st.regs mV = (V : ℝ)) (hFb : st.regs mFaceBase = (faceBase : ℝ))
    (hCurN : st.regs mCurN = (n : ℝ))
    (hfb_mem : ∀ (i : Fin n) (r : Fin V), st.mem (faceBase + i.val * V + r.val) = faceBit i r) :
    let outBase := faceBase + (n + 1) * V
    ∃ st', Stmt.Exec oracle mainQr (writeOutput d) st st' ∧
      st'.queries = st.queries ∧
      st'.regs mOut = (outBase : ℝ) ∧
      (∀ i : Fin n, st'.mem (outBase + i.val) = 1) ∧
      st'.mem (outBase + n) = 0 ∧
      (∀ i j : Fin n, st'.mem (outBase + n + 1 + i.val * n + j.val) =
        if (∑ r : Fin V, faceBit i r * (1 - faceBit j r)) = 0 then 1 else 0) := by
  intro outBase
  have eout := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mOut
    (PExpr.reg mFaceBase + (PExpr.reg mCurN + PExpr.const 1) * PExpr.reg mV) st
    (outBase : ℝ) (by simp [hFb, hCurN, hV, outBase])
  let st₁ : RS (MainReg d) := ⟨Function.update st.regs mOut (outBase : ℝ), st.mem, st.queries⟩
  have eva1 := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mValA
    (PExpr.const 1) st₁ 1 (by simp)
  let st₂ : RS (MainReg d) := ⟨Function.update st₁.regs mValA 1, st₁.mem, st₁.queries⟩
  have hcn2 : st₂.regs mCurN = (n : ℝ) := by simp [st₂, st₁, hCurN]
  obtain ⟨st₃, eones, _, hcn3, _, hInv1⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt1) (boundReg := mCurN) (condReg := mCond1)
      (by simp) (by simp) (by simp)
      (fun ci s =>
        s.queries = st.queries ∧
        s.regs mV = (V : ℝ) ∧ s.regs mFaceBase = (faceBase : ℝ) ∧
        s.regs mOut = (outBase : ℝ) ∧ s.regs mValA = 1 ∧
        (∀ i : Fin n, i.val < ci → s.mem (outBase + i.val) = 1) ∧
        (∀ addr, addr < outBase → s.mem addr = st.mem addr))
      (by
        intro ci s v₁ v₂ ⟨hq, hv, hf, ho, ha, hdone, hlow⟩
        refine ⟨hq, ?_, ?_, ?_, ?_, hdone, hlow⟩ <;> simp [hv, hf, ho, ha])
      (by
        intro ci hci s hcnt hbnd _ ⟨hq, hv, hf, ho, ha, hdone, hlow⟩
        obtain ⟨s1, es1, hm1, hq1, hpr1⟩ :=
          storeAt_spec (oracle := oracle) (PExpr.reg mOut + PExpr.reg mCnt1) mValA (by simp)
            s (outBase + ci) (by simp [ho, hcnt])
        refine ⟨s1, es1,
          (hpr1 mCnt1 (by simp)).trans hcnt,
          (hpr1 mCurN (by simp)).trans hbnd,
          hq1.trans hq,
          (hpr1 mV (by simp)).trans hv,
          (hpr1 mFaceBase (by simp)).trans hf,
          (hpr1 mOut (by simp)).trans ho,
          (hpr1 mValA (by simp)).trans ha,
          ?_, ?_⟩
        · intro i hi
          rw [hm1]
          by_cases hic : i.val = ci
          · rw [hic, Function.update_self, ha]
          · rw [Function.update_of_ne (by omega)]
            exact hdone i (by omega)
        · intro addr haddr
          rw [hm1, Function.update_of_ne (by omega)]
          exact hlow addr haddr)
      st₂ hcn2
      ⟨rfl, by simp [st₂, st₁, hV], by simp [st₂, st₁, hFb], by simp [st₂, st₁],
       by simp [st₂], fun _ h => by omega, fun _ _ => rfl⟩
  obtain ⟨hq3, hv3, hf3, ho3, _, hones3, hlow3⟩ := hInv1
  have eva0 := Stmt.Exec.assign_eval (oracle := oracle) (qr := mainQr) mValA
    (PExpr.const 0) st₃ 0 (by simp)
  let st₄ : RS (MainReg d) := ⟨Function.update st₃.regs mValA 0, st₃.mem, st₃.queries⟩
  obtain ⟨st₅, esep, hm5, hq5, hpr5⟩ :=
    storeAt_spec (oracle := oracle) (PExpr.reg mOut + PExpr.reg mCurN) mValA (by simp)
      st₄ (outBase + n) (by simp [st₄, ho3, hcn3])
  have hcn5 : st₅.regs mCurN = (n : ℝ) := by
    rw [hpr5 mCurN (by simp)]; simp [st₄, hcn3]
  have hv5 : st₅.regs mV = (V : ℝ) := by
    rw [hpr5 mV (by simp)]; simp [st₄, hv3]
  have hf5 : st₅.regs mFaceBase = (faceBase : ℝ) := by
    rw [hpr5 mFaceBase (by simp)]; simp [st₄, hf3]
  have ho5 : st₅.regs mOut = (outBase : ℝ) := by
    rw [hpr5 mOut (by simp)]; simp [st₄, ho3]
  obtain ⟨st₆, emat, _, _, _, hInv2⟩ :=
    Stmt.Exec.forNat (oracle := oracle) (qr := mainQr)
      (cntReg := mCnt1) (boundReg := mCurN) (condReg := mCond1)
      (by simp) (by simp) (by simp)
      (fun ci s =>
        s.queries = st.queries ∧
        s.regs mV = (V : ℝ) ∧ s.regs mFaceBase = (faceBase : ℝ) ∧
        s.regs mOut = (outBase : ℝ) ∧
        (∀ addr, addr < outBase + n + 1 → s.mem addr = st₅.mem addr) ∧
        (∀ i : Fin n, i.val < ci → ∀ j : Fin n,
          s.mem (outBase + n + 1 + i.val * n + j.val) =
            if (∑ r : Fin V, faceBit i r * (1 - faceBit j r)) = 0 then 1 else 0))
      (by
        intro ci s v₁ v₂ ⟨hq, hv, hf, ho, hlow, hdone⟩
        refine ⟨hq, ?_, ?_, ?_, hlow, hdone⟩ <;> simp [hv, hf, ho])
      (by
        intro ci hci s hcnt hbnd _ ⟨hq, hv, hf, ho, hlow, hdone⟩
        let i₀ : Fin n := ⟨ci, hci⟩
        have hfb_s : ∀ (i : Fin n) (r : Fin V), s.mem (faceBase + i.val * V + r.val) = faceBit i r := by
          intro i r
          have hlt1 : faceBase + i.val * V + r.val < outBase := by
            have := i.isLt; have := r.isLt; dsimp [outBase]; nlinarith
          rw [hlow _ (by omega), hm5, Function.update_of_ne (by omega)]
          change st₃.mem _ = _
          rw [hlow3 _ hlt1, hfb_mem i r]
        obtain ⟨s1, erow, hq1, hrow1, hlow1, hpr1⟩ :=
          writeMatrixRow_spec (oracle := oracle) faceBit faceBase outBase i₀ rfl s
            hfb_s hv hf ho hbnd hcnt
        refine ⟨s1, erow,
          (hpr1 (Sum.inl 10) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hcnt,
          (hpr1 (Sum.inl 8) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hbnd,
          hq1.trans hq,
          (hpr1 (Sum.inl 1) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hv,
          (hpr1 (Sum.inl 7) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans hf,
          (hpr1 (Sum.inl 3) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp) (by simp)).trans ho,
          ?_, ?_⟩
        · intro addr haddr
          rw [hlow1 addr (by omega)]
          exact hlow addr haddr
        · intro i hi j
          by_cases hic : i.val < ci
          · have hlt : outBase + n + 1 + i.val * n + j.val < outBase + n + 1 + ci * n := by
              have := j.isLt; nlinarith
            rw [hlow1 _ hlt]
            exact hdone i hic j
          · have hie : i = i₀ := Fin.ext (by dsimp [i₀]; omega)
            rw [hie]
            exact hrow1 j)
      st₅ hcn5
      ⟨hq5.trans hq3, hv5, hf5, ho5, fun _ _ => rfl, fun _ h => by omega⟩
  obtain ⟨hq6, _, _, ho6, hlow6, hmat6⟩ := hInv2
  refine ⟨st₆,
    Stmt.Exec.seq eout (Stmt.Exec.seq eva1
      (Stmt.Exec.seq eones (Stmt.Exec.seq eva0 (Stmt.Exec.seq esep emat)))),
    hq6, ho6, ?_, ?_, fun i j => hmat6 i i.isLt j⟩
  · intro i
    rw [hlow6 _ (by have := i.isLt; omega), hm5,
      Function.update_of_ne (by have := i.isLt; omega)]
    exact hones3 i i.isLt
  · rw [hlow6 _ (by omega), hm5, Function.update_self]
    simp [st₄]

/-! ### Complete RAM program and main theorem -/

noncomputable def fullProg (d : ℕ) (hd : 2 ≤ d) : Stmt (MainReg d) :=
  .seq (discoveryLoop d hd)
    (.seq (buildIncTable d)
      (.seq (closeFaces d) (writeOutput d)))

end Lattice
end RayAlg

theorem ray_oracle_face_lattice_reconstruction_ge_two (d : ℕ) (hd : 2 ≤ d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P c := by
  obtain ⟨program, hrealize⟩ :=
    RayAlg.Stmt.realize RayAlg.Lattice.mainQr (RayAlg.Lattice.mainQr_injective d)
      (RayAlg.Lattice.fullProg d hd) RayAlg.Lattice.mOut
  refine ⟨program, ?_⟩
  intro P hPpoly hzero oracle horacle
  obtain ⟨hm_lb, L, hP, _⟩ :=
    polytope_normalized_halfspace_presentation_and_facet_lower_bound
      d (by omega) P hPpoly hzero oracle horacle
  let m := faceCount P (d - 1)
  let st₀ : RayAlg.RS (RayAlg.Lattice.MainReg d) := ⟨fun _ => 0, fun _ => 0, 0⟩
  obtain ⟨st₁, k, V, a, vVec, edisc, hk_le, hV_pos, hV_le, _, hQP_eq, hV_range,
    ha_mem, hv_mem, hK1, hV1, hq1⟩ :=
    RayAlg.Lattice.discoveryLoop_spec hd hPpoly hzero L hP horacle st₀ rfl
  obtain ⟨st₂, einc, hq2, hK2, hV2, hInc2, hinc_mem⟩ :=
    RayAlg.Lattice.buildIncTable_spec (oracle := oracle) a vVec st₁ ha_mem hv_mem hK1 hV1
  obtain ⟨st₃, n, faceBit, eclose, _, hq3, hV3, hFb3, hCurN3, hf_inj, hf_zo, hf_range, hfb_mem⟩ :=
    RayAlg.Lattice.closeFaces_spec hV_pos a vVec ((2 * (k + V + 1)) * d) st₂ hK2 hV2 hInc2 hinc_mem
  obtain ⟨st₄, eout, hq4, hOut4, hones_mem, hsep_mem, hmat_mem⟩ :=
    RayAlg.Lattice.writeOutput_spec (oracle := oracle) faceBit
      ((2 * (k + V + 1)) * d + k * V) st₃ hV3 hFb3 hCurN3 hfb_mem
  let outBase := ((2 * (k + V + 1)) * d + k * V) + (n + 1) * V
  have efull : RayAlg.Stmt.Exec oracle RayAlg.Lattice.mainQr
      (RayAlg.Lattice.fullProg d hd) st₀ st₄ :=
    RayAlg.Stmt.Exec.seq edisc (RayAlg.Stmt.Exec.seq einc (RayAlg.Stmt.Exec.seq eclose eout))
  obtain ⟨t, c, hrun, hhalt, hcq, hctape⟩ := hrealize oracle st₄ outBase efull hOut4
  refine ⟨t, c, hrun, hhalt, ?_, ?_⟩
  · have hq_eq : c.queries = st₁.queries := by rw [hcq, hq4, hq3, hq2]
    have hsum_mono :
        ∑ s ∈ Finset.range k, (1 + (d - 1) * (2 * (m - s) + 2)) ≤
          ∑ s ∈ Finset.range m, (1 + (d - 1) * (2 * (m - s) + 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk_le) fun _ _ _ => Nat.zero_le _
    have hbud := RayAlg.query_budget_le d m (faceCount P 0) hd hm_lb
    dsimp [m] at hsum_mono hbud
    omega
  · refine RayAlg.face_lattice_output_of_closure hPpoly a hQP_eq.symm vVec hV_range
      faceBit hf_inj hf_zo hf_range c ?_ ?_ ?_
    · intro i
      rw [hctape i.val]
      exact hones_mem i
    · rw [hctape n]
      exact hsep_mem
    · intro i j
      rw [hctape (n + 1 + i.val * n + j.val)]
      have haddr : outBase + (n + 1 + i.val * n + j.val) =
          outBase + n + 1 + i.val * n + j.val := by omega
      rw [haddr]
      exact hmat_mem i j

end Grunbaum2003

open Grunbaum2003 in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P c :=
  Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two d hd
