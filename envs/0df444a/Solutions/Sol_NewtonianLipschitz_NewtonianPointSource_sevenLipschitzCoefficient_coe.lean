-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.sevenLipschitzCoefficient_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:01:46.542484+00:00
-- url     : https://prove2.me/submissions/1eb7c0be-f1d4-4a3f-8211-fb94a3f592e7

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
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
    ((NewtonianPointSource.sevenLipschitzCoefficient d M hd : ℝ≥0) : ℝ) =
      7 * (M : ℝ) / d ^ 3 := by
  change (Real.toNNReal (((7 : ℕ) : ℝ) * (M : ℝ) / d ^ 3) : ℝ) =
    7 * (M : ℝ) / d ^ 3
  simpa using
    (Real.coe_toNNReal
      (((7 : ℕ) : ℝ) * (M : ℝ) / d ^ 3) (by positivity))
end NewtonianPointSource
end NewtonianLipschitz
