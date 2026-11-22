-- Prove2me | solution 1 for Lean4LPD.PauliString.highNorm_trajTrunc_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:19.996573+00:00
-- url     : https://prove2.me/submissions/0a223189-5c54-406d-9058-2f33e6e9b14a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_truncOp_compl

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n ko kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (wstar : ℕ) (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    highNorm wstar (trajTrunc Gs θ (fun _ => (highSet n wstar)ᶜ) O (g + 1)) = 0 := by
  rw [trajTrunc_succ]
  exact highNorm_truncOp_compl wstar _
end Lean4LPD.PauliString
