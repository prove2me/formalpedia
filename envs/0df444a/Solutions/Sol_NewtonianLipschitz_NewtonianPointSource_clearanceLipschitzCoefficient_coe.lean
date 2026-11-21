-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.clearanceLipschitzCoefficient_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:54:12.397852+00:00
-- url     : https://prove2.me/submissions/f215b2fe-e42d-4ab8-bf45-07a29fb1e586

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d) :
    ((NewtonianPointSource.clearanceLipschitzCoefficient d M hd : ℝ≥0) : ℝ) =
      10 * (M : ℝ) / d ^ 3 := by
  change (Real.toNNReal (((10 : ℕ) : ℝ) * (M : ℝ) / d ^ 3) : ℝ) =
    10 * (M : ℝ) / d ^ 3
  simpa using
    (Real.coe_toNNReal
      (((10 : ℕ) : ℝ) * (M : ℝ) / d ^ 3) (by positivity))
end NewtonianPointSource
end NewtonianLipschitz
