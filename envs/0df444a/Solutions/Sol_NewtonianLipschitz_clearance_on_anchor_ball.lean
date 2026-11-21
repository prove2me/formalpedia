-- Prove2me | solution 1 for NewtonianLipschitz.clearance_on_anchor_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:29.551708+00:00
-- url     : https://prove2.me/submissions/9034a1af-2347-466f-a864-e9720210c0fc

module
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Theorems.Thm_NewtonianLipschitz_clearance_of_anchor
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_ge_of_cartesian_distance
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (anchor : Vec3) (ρ d : ℝ)
    (hd : 0 < d) (hanchor : d + ρ ≤ dist anchor (0 : Vec3)) :
    ∀ x ∈ Metric.ball anchor ρ, d ≤ euclideanRadius x := by
  intro x hx
  have hx' : dist x anchor < ρ := Metric.mem_ball.mp hx
  have hxclear :=
    clearance_of_anchor anchor anchor x 0 ρ d hd hx' (by simp) (by simpa using hanchor)
  exact euclideanRadius_ge_of_cartesian_distance x d hxclear.1
end NewtonianLipschitz
