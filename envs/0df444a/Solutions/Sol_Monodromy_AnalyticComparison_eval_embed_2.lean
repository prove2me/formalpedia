-- Prove2me | solution 2 for Monodromy.AnalyticComparison.eval_embed
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:55:13.286693+00:00
-- url     : https://prove2.me/submissions/733a7bb8-b98f-461f-99e1-ae4ad74e5fcd

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Effectiveness
public import Definitions.Def_Monodromy_Radix
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
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Inline helper skeleton from Monodromy.Radix.


/-!
# Finite-root observations

The power covering reads a finite residue of the retained logarithmic branch.
Normalized kernels select its regular roots; integer residues occur only in proofs.
-/

@[expose] public section

namespace Monodromy.Radix

variable (B : ℕ) [NeZero B]





















theorem kernel_root (marked digit : Fin B) :
    Choice.kernel (fun z : ℂ => z ^ B) (omega B marked : ℂ) (omega B digit : ℂ) =
      if marked = digit then 1 else 0 := by
  classical
  by_cases same : marked = digit
  · subst digit
    simpa using Choice.kernel_self (omega_regular B marked)
  · simp only [same, ↓reduceIte]
    apply Choice.kernel_other
    · intro equal
      exact same ((omega_injective B) (Subtype.ext equal)).symm
    · exact (omega_complex_pow B digit).trans (omega_complex_pow B marked).symm

end Monodromy.Radix

namespace Monodromy.Radix.Tower













end Monodromy.Radix.Tower

end


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





theorem zero_int (n : ℤ) : zero (n : ℝ) = if n = 0 then 1 else 0 := by
  by_cases same : n = 0
  · subst n
    simp [zero]
  · have nonzero : Real.pi * (n : ℝ) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by exact_mod_cast same)
    rw [zero, Real.sinc_of_ne_zero nonzero, mul_comm Real.pi (n : ℝ),
      Real.sin_int_mul_pi, zero_div, ite_eq_right same]





theorem weight_int_digit (degree : ℕ) [NeZero degree]
    (quotient : ℤ) (marked digit : Fin degree) :
    weight degree marked (((degree : ℤ) * quotient + digit.val : ℤ) : ℝ) =
      if marked = digit then 1 else 0 := by
  unfold weight
  rw [Radix.readRoot_digit, Radix.kernel_root]
  split_ifs <;> simp





end Monodromy.AnalyticComparison

namespace Monodromy.AnalyticComparison

open CoupledContinuation











theorem gate_embed (operation : Gate) (backward : Bool) (labels : Labels) :
    gate operation backward (embed labels) = embed (operation.evalInt backward labels) := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases operation <;> cases backward <;>
    simp [gate, Gate.evalInt, embed, zero_int]











theorem word_embed (operations : Word) (labels : Labels) :
    word operations (embed labels) = embed (operations.evalInt labels) := by
  induction operations generalizing labels with
  | nil => rfl
  | cons atom rest recursive =>
      simp only [word, Word.evalInt, gate_embed, recursive]

variable {degree : ℕ} [NeZero degree]









theorem weight_label (marked : Fin degree) (labels : Labels) :
    weight degree marked (labels.2 : ℝ) =
      if marked = Program.indexInt degree labels then 1 else 0 := by
  have result := weight_int_digit degree (labels.2 / (degree : ℤ)) marked
    (Program.indexInt degree labels)
  rw [Program.control_decomposition] at result
  exact result

theorem next_embed (program : Program degree) (labels : Labels) :
    next program (embed labels) = embed (program.nextInt labels) := by
  classical
  simp only [next, embed, weight_label]
  rw [Finset.sum_eq_single (Program.indexInt degree labels)]
  · simp only [ite_true, one_smul]
    exact word_embed _ labels
  · intro index _ different
    simp [different]
  · simp

theorem halt_embed (program : Program degree) (labels : Labels) :
    halt program (embed labels) = if program.haltInt labels then 1 else 0 := by
  classical
  simp only [halt, embed, weight_label]
  rw [Finset.sum_eq_single (Program.indexInt degree labels)]
  · simp [Program.haltInt]
    rfl
  · intro index _ different
    simp [different]
  · simp





theorem step_embed (program : Program degree) (labels : Labels) :
    step program (embed labels) = (program.stepInt labels).map embed := by
  unfold step Program.stepInt
  rw [halt_embed]
  cases program.haltInt labels <;> simp [next_embed]









end Monodromy.AnalyticComparison

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.AnalyticComparison
open CoupledContinuation
variable {degree : ℕ} [NeZero degree]
theorem solution (program : Program degree) (labels : Labels) :
    eval program (embed labels) = embed <$> program.evalInt labels := by
  have refinement : StateTransition.Respects program.stepInt (step program)
      (fun first second => embed first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : program.stepInt source with
    | none =>
        change step program (embed source) = none
        simp [step_embed, result]
    | some successor =>
        apply Relation.TransGen.single
        simp [step_embed, result]
  exact StateTransition.tr_eval' program.stepInt (step program) embed refinement labels
