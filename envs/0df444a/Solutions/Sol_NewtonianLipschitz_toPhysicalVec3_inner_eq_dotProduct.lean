-- Prove2me | solution 1 for NewtonianLipschitz.toPhysicalVec3_inner_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:47.991337+00:00
-- url     : https://prove2.me/submissions/709f26ff-230d-4e5f-826c-479a8d0772af

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
theorem _root_.solution (x h : Vec3) :
    ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ = x ⬝ᵥ h := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [ofLp_toPhysicalVec3, dotProduct, Fin.sum_univ_three,
    Pi.star_apply, star_trivial]
  ring
end NewtonianLipschitz
