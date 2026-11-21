-- Prove2me | solution 1 for NewtonianLipschitz.clearance_of_anchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:39.349369+00:00
-- url     : https://prove2.me/submissions/fee46515-614e-4ca3-8b97-ddad3d6d97ca

module
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Clearance
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
    (anchor center x : Vec3) (ε ρ d : ℝ)
    (hd : 0 < d)
    (hx : dist x center < ρ)
    (hcenter : dist center anchor ≤ ε)
    (hanchor : d + ε + ρ ≤ dist anchor (0 : Vec3)) :
    d ≤ dist x (0 : Vec3) ∧ x ≠ 0 := by
  have hdist : dist x anchor < ρ + ε := by
    calc
      dist x anchor ≤ dist x center + dist center anchor := dist_triangle _ _ _
      _ < ρ + ε := add_lt_add_of_lt_of_le hx hcenter
  have htriangle :
      dist anchor (0 : Vec3) ≤
        dist anchor x + dist x (0 : Vec3) := dist_triangle _ _ _
  have hclear : d ≤ dist x (0 : Vec3) := by
    rw [dist_comm anchor x] at htriangle
    linarith
  refine ⟨hclear, ?_⟩
  intro heq
  have : d ≤ 0 := by simpa [heq] using hclear
  linarith
end NewtonianLipschitz
