-- Prove2me | solution 1 for Lean4LPD.l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:03.987439+00:00
-- url     : https://prove2.me/submissions/c6d77d52-3cd3-4ebb-b172-07ac6d8782d7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_BlockNorm

set_option autoImplicit true
@[expose] public section
open scoped Matrix.Norms.L2Operator
open Matrix Finset WithLp
public section
open Lean4LPD
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
omit [DecidableEq m]
namespace Lean4LPD
theorem _root_.solution {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) (P Q : n → Prop) [DecidablePred P] [DecidablePred Q] :
    ‖O.toBlock P Q‖ ≤ 1 :=
  l2_opNorm_toBlock_le_one_of_mem_unitary hO P Q
end Lean4LPD
