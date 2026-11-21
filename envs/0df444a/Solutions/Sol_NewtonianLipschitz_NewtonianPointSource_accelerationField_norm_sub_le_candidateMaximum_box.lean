-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:14:17.100911+00:00
-- url     : https://prove2.me/submissions/85019e6c-9090-4469-bebf-1424da1303d9

module
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
public import Theorems.Thm_NewtonianLipschitz_cartesianBox_clearance_of_center_margin
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_convex


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource)
    (anchor : Vec3) (ρ d : ℝ)
    (hd : 0 < d) (hmargin : d + ρ ≤ dist anchor (0 : Vec3))
    (x y : Vec3)
    (hx : x ∈ Metric.ball anchor ρ)
    (hy : y ∈ Metric.ball anchor ρ) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by
  exact c.accelerationField_norm_sub_le_candidateMaximum_convex
    (Metric.ball anchor ρ) (convex_ball _ _) d hd
    (cartesianBox_clearance_of_center_margin anchor ρ d hd hmargin)
    x y hx hy
end NewtonianPointSource
end NewtonianLipschitz
