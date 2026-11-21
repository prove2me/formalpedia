-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:23:56.492431+00:00
-- url     : https://prove2.me/submissions/449c633d-e6db-406b-bdf8-b0261f991e59

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ x i j =
      (μ / euclideanRadius x ^ 5) *
        (3 * x i * x j -
          euclideanRadius x ^ 2 * (if i = j then 1 else 0)) := by
  simp only [newtonianJacobianMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    smul_eq_mul]
  ring
end NewtonianLipschitz
