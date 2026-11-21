-- Prove2me | solution 1 for NewtonianLipschitz.physicalNewtonianAcceleration_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:28.166181+00:00
-- url     : https://prove2.me/submissions/8d514399-99a7-4270-81e3-c59b9c0703f0

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (μ : ℝ) (q : PhysicalVec3) :
    physicalNewtonianAcceleration μ q = (-(μ) / ‖q‖ ^ 3) • q := by
  rfl
end NewtonianLipschitz
