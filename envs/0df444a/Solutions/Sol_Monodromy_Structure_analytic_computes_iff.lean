-- Prove2me | solution 1 for Monodromy.Structure.analytic_computes_iff
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:42.909008+00:00
-- url     : https://prove2.me/submissions/219babe6-cf26-4a9a-a188-3d650a39b796

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Effectiveness
public import Definitions.Def_Monodromy_Structure
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_AnalyticComparison_eval_embed
public import Theorems.Thm_Monodromy_CoupledContinuation_Program_eval_prepareInt

@[expose] public section


-- Inline helper skeleton from Monodromy.Effectiveness.


/-!
# The effective content of cover execution

Fixed words of the five native loops have primitive recursive integer
interpretations. Complete native word execution
agrees with this proof interpretation, including results and divergence.
The trajectory-generating core uses the actual covering lifts throughout.
-/

@[expose] public section

namespace Monodromy.Effectiveness



end Monodromy.Effectiveness

noncomputable section

namespace Monodromy.CoupledContinuation





namespace Program

variable {degree : ℕ} [NeZero degree]













end Program

end Monodromy.CoupledContinuation

namespace Monodromy.PrimeReadout









end Monodromy.PrimeReadout

namespace Monodromy.TapeCode.Readout







section Decoder

variable {a : ℕ} [NeZero a]





















variable (read : Fin a → ℕ → ℕ) (neutral : ∀ initial, read 0 initial = initial)

































end Decoder

end Monodromy.TapeCode.Readout

/-!
## Direct analytic comparison

The same finite word table has a globally real analytic successor on three
real coordinates. Its complete execution on the exact integer lattice agrees
with native transport. The comparison evaluates formulas directly and carries
no assertion about off-lattice conjugacy, physical robustness, or equal cost.
-/



namespace Monodromy.AnalyticComparison

















end Monodromy.AnalyticComparison

namespace Monodromy.AnalyticComparison

open CoupledContinuation





theorem embed_injective : Function.Injective embed := by
  rintro ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩ same
  have hx : (x : ℝ) = x' := congrArg (fun s : State => s.1.1) same
  have hy : (y : ℝ) = y' := congrArg (fun s : State => s.1.2) same
  have hz : (z : ℝ) = z' := congrArg (fun s : State => s.2) same
  have : x = x' := by exact_mod_cast hx
  have : y = y' := by exact_mod_cast hy
  have : z = z' := by exact_mod_cast hz
  aesop



















variable {degree : ℕ} [NeZero degree]























theorem result_iff (program : Program degree) (initial final : Labels) :
    embed final ∈ eval program (embed initial) ↔
      Labels.prepare final ∈ program.eval (Labels.prepare initial) := by
  rw [eval_embed, Program.eval_prepareInt]
  simp only [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨found, reaches, same⟩
    exact ⟨found, reaches, congrArg Labels.prepare (embed_injective same)⟩
  · rintro ⟨found, reaches, same⟩
    have injective : Function.Injective Labels.prepare := by
      rintro ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩ same
      simpa [Labels.prepare] using prepare_injective same
    exact ⟨found, reaches, congrArg embed (injective same)⟩





end Monodromy.AnalyticComparison

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Structure
open CoupledContinuation NativeInterface
theorem solution {degree : ℕ} [NeZero degree]
    (program : Program degree) (function : ℕ → Part ℕ) :
    (∀ input value, value ∈ function input ↔ ∃ labels : Labels,
      AnalyticComparison.embed labels ∈ AnalyticComparison.eval program
        (AnalyticComparison.embed (inputLabels input)) ∧ outputLabels labels = value) ↔
      Computes program function := by
  simp_rw [AnalyticComparison.result_iff]
  rfl
