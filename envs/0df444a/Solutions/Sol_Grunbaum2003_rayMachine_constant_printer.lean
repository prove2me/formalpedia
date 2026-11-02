-- Prove2me | solution 1 for Grunbaum2003.rayMachine_constant_printer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:09:27.775278+00:00
-- url     : https://prove2.me/submissions/0e5e3f57-6a7c-4afe-9c73-99170028d8de

import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace Grunbaum2003

private theorem rayMachineRun_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (s t : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (s + t) c =
      (rayMachineRun program oracle s c).bind (rayMachineRun program oracle t) := by
  induction s generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ s ih =>
    simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

private theorem rayMachineRun_succ_last {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (t + 1) c =
      (rayMachineRun program oracle t c).bind (rayMachineStep program oracle) := by
  rw [rayMachineRun_add program oracle t 1 c]
  simp only [rayMachineRun, Option.bind_fun_some]

theorem rayMachine_constant_printer (cells : List ℚ) :
    ∃ program : List RayInstruction,
      ∀ (d : ℕ) (oracle : (Fin d → ℝ) → (Fin d → ℝ)),
        ∃ c : RayConfiguration,
          rayMachineRun program oracle cells.length
            ⟨0, 0, fun _ => 0, 0⟩ = some c ∧
          program[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = 0 ∧
          ∀ i : Fin cells.length, c.tape (i.val : ℤ) = (cells.get i : ℝ) := by
  classical
  let program : List RayInstruction :=
    List.ofFn (fun i : Fin cells.length =>
      RayInstruction.constant (i.val : ℤ) (cells.get i) (i.val + 1)) ++ [.halt]
  refine ⟨program, ?_⟩
  intro d oracle
  have hRun : ∀ n, n ≤ cells.length → ∃ c : RayConfiguration,
      rayMachineRun program oracle n ⟨0, 0, fun _ => 0, 0⟩ = some c ∧
      c.pc = n ∧ c.head = 0 ∧ c.queries = 0 ∧
      ∀ i : Fin cells.length, i.val < n → c.tape (i.val : ℤ) = (cells.get i : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨⟨0, 0, fun _ => 0, 0⟩, rfl, rfl, rfl, rfl, ?_⟩
      intro i hi
      omega
    | succ n ih =>
      intro hn
      obtain ⟨c, hc, hpc, hhead, hq, htape⟩ := ih (by omega)
      have hnlt : n < cells.length := by omega
      let c' : RayConfiguration :=
        { c with pc := n + 1, tape := Function.update c.tape (n : ℤ) (cells.get ⟨n, hnlt⟩ : ℝ) }
      have hInstruction : program[c.pc]? =
          some (.constant (n : ℤ) (cells.get ⟨n, hnlt⟩) (n + 1)) := by
        simp only [hpc, program, List.getElem?_append, List.length_ofFn]
        simp only [List.getElem?_ofFn, hnlt, ↓reduceDIte, ↓reduceIte]
      have hStep : rayMachineStep program oracle c = some c' := by
        simp only [rayMachineStep, hInstruction, hhead, zero_add, c']
      refine ⟨c', ?_, rfl, hhead, hq, ?_⟩
      · rw [rayMachineRun_succ_last, hc, Option.bind_some, hStep]
      · intro i hi
        by_cases hin : i.val = n
        · have heq : (i.val : ℤ) = (n : ℤ) := congrArg Int.ofNat hin
          change Function.update c.tape (n : ℤ) (cells.get ⟨n, hnlt⟩ : ℝ) (i.val : ℤ) = _
          rw [heq, Function.update_self]
          exact congrArg (fun j : Fin cells.length => (cells.get j : ℝ)) (Fin.ext hin.symm)
        · have hilt : i.val < n := by omega
          have hne : (i.val : ℤ) ≠ (n : ℤ) := by exact_mod_cast hin
          simpa only [c', Function.update_of_ne hne] using htape i hilt
  obtain ⟨c, hc, hpc, hhead, hq, htape⟩ := hRun cells.length le_rfl
  refine ⟨c, hc, ?_, hhead, hq, fun i => htape i i.isLt⟩
  simp only [hpc, program, List.getElem?_append, List.length_ofFn, lt_self_iff_false,
    ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero]

end Grunbaum2003


open Grunbaum2003

theorem solution (cells : List ℚ) :
    ∃ program : List RayInstruction,
      ∀ (d : ℕ) (oracle : (Fin d → ℝ) → (Fin d → ℝ)),
        ∃ c : RayConfiguration,
          rayMachineRun program oracle cells.length
            ⟨0, 0, fun _ => 0, 0⟩ = some c ∧
          program[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = 0 ∧
          ∀ i : Fin cells.length, c.tape (i.val : ℤ) = (cells.get i : ℝ) :=
  Grunbaum2003.rayMachine_constant_printer cells
