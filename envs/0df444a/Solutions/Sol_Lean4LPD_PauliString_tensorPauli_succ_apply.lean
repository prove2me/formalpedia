-- Prove2me | solution 1 for Lean4LPD.PauliString.tensorPauli_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:29.273505+00:00
-- url     : https://prove2.me/submissions/7e21bb88-d69f-4781-bd22-28fcddd3101a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution {n : ℕ} (x z a b : Bits (n + 1)) :
    tensorPauli (n + 1) x z a b =
      qubitPauli (x 0) (z 0) (a 0) (b 0) *
        tensorPauli n (Fin.tail x) (Fin.tail z) (Fin.tail a) (Fin.tail b) := rfl
end Lean4LPD.PauliString
