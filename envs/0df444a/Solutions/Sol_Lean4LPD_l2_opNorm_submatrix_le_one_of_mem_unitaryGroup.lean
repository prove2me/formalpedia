-- Prove2me | solution 1 for Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:56.877432+00:00
-- url     : https://prove2.me/submissions/185951a5-5045-40f5-928c-cc006e3f5f51

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
theorem _root_.solution {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖U.submatrix f g‖ ≤ 1 :=
  l2_opNorm_submatrix_le_one_of_mem_unitary hU hf hg
end Lean4LPD
