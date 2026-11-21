-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:47.036674+00:00
-- url     : https://prove2.me/submissions/fdf381b7-24aa-4c35-932a-9369bc36bdd2

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_lipschitzOnWith_of_clearance
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_ge_of_cartesian_distance


set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (anchor : Vec3) (ρ d : ℝ) (hd : 0 < d)
    (hanchor : d + ρ ≤ dist anchor (0 : Vec3)) :
    LipschitzOnWith
      (NewtonianPointSource.clearanceLipschitzCoefficient
        d (1 : ℝ≥0) hd)
      NewtonianPointSource.unitAxis.accelerationField
      (Metric.ball anchor ρ) := by
  have hsafe : ∀ x ∈ Metric.ball anchor ρ,
      d ≤ euclideanRadius x := by
    intro x hx
    have hxball : dist x anchor < ρ := Metric.mem_ball.mp hx
    have htriangle :
        dist anchor (0 : Vec3) ≤ dist anchor x + dist x 0 :=
      dist_triangle _ _ _
    have hcart : d ≤ dist x (0 : Vec3) := by
      rw [dist_comm anchor x] at htriangle
      linarith
    exact euclideanRadius_ge_of_cartesian_distance x d hcart
  have hunitMass :
      NewtonianPointSource.unitAxis.gravitationalParameter ≤ (1 : ℝ) := by
    rw [NewtonianPointSource.unitAxis_gravitationalParameter_eq_one]
  exact NewtonianPointSource.accelerationField_lipschitzOnWith_of_clearance
    NewtonianPointSource.unitAxis (Metric.ball anchor ρ)
    (convex_ball _ _) d (1 : ℝ≥0) hd hsafe hunitMass
end NewtonianPointSource
end NewtonianLipschitz
