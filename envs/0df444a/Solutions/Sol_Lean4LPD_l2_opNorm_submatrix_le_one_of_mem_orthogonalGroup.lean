-- Prove2me | solution 1 for Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:59.6673+00:00
-- url     : https://prove2.me/submissions/6825434e-7cb5-49d1-bdf1-3eff61518b4f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_BlockNorm
public import Theorems.Thm_Lean4LPD_l2_opNorm_submatrix_le_one_of_mem_unitary

set_option autoImplicit true
@[expose] public section
open scoped Matrix.Norms.L2Operator
open Matrix Finset WithLp
public section
open Lean4LPD
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
omit [DecidableEq m] [DecidableEq p]
namespace Lean4LPD
theorem _root_.solution {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖O.submatrix f g‖ ≤ 1 :=
  l2_opNorm_submatrix_le_one_of_mem_unitary hO hf hg
end Lean4LPD
