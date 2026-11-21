-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:45.553444+00:00
-- url     : https://prove2.me/submissions/9c072d62-fbde-43d3-b59d-384f4e557f10

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
    (μ : ℝ) (x : Vec3) :
    (newtonianJacobianMatrix μ x).IsSymm := by
  have houter :
      (Matrix.vecMulVec x x).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.vecMulVec_apply]
    ring
  have hid : (1 : Matrix (Fin 3) (Fin 3) ℝ).IsSymm :=
    Matrix.isSymm_one
  change ((μ / euclideanRadius x ^ 5) •
    ((3 : ℝ) • Matrix.vecMulVec x x -
      (euclideanRadius x ^ 2) •
        (1 : Matrix (Fin 3) (Fin 3) ℝ))).IsSymm
  exact ((houter.smul (3 : ℝ)).sub
    (hid.smul (euclideanRadius x ^ 2))).smul
      (μ / euclideanRadius x ^ 5)
end NewtonianLipschitz
