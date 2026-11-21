-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:07:28.699078+00:00
-- url     : https://prove2.me/submissions/94e78947-5d4b-4928-9ca4-477230c73256

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_lipschitzOnWith_seven
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_clearance_on_anchor_ball


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
      (NewtonianPointSource.sevenLipschitzCoefficient
        d (1 : ℝ≥0) hd)
      NewtonianPointSource.unitAxis.accelerationField
      (Metric.ball anchor ρ) := by
  have hsafe : ∀ x ∈ Metric.ball anchor ρ,
      d ≤ euclideanRadius x :=
    clearance_on_anchor_ball anchor ρ d hd hanchor
  have hmass :
      NewtonianPointSource.unitAxis.gravitationalParameter ≤ (1 : ℝ) := by
    rw [NewtonianPointSource.unitAxis_gravitationalParameter_eq_one]
  exact NewtonianPointSource.accelerationField_lipschitzOnWith_seven
    NewtonianPointSource.unitAxis (Metric.ball anchor ρ)
    (convex_ball _ _) d (1 : ℝ≥0) hd hsafe hmass
end NewtonianPointSource
end NewtonianLipschitz
