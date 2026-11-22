-- Prove2me | solution 1 for Lean4LPD.PauliString.trotterTraj_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:04.692177+00:00
-- url     : https://prove2.me/submissions/8eff1786-e770-463e-bad7-9531c90c6485

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trotterTraj Gs θ period wstar O (g + 1) =
      truncOp (trotterSchedule period wstar g)
        (rot (toMatrix (Gs (g % period))) (θ (g % period)) *
          trotterTraj Gs θ period wstar O g *
          rot (toMatrix (Gs (g % period))) (-(θ (g % period)))) := rfl
end Lean4LPD.PauliString
