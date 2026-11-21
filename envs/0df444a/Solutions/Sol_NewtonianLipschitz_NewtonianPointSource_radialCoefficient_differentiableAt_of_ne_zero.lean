-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.radialCoefficient_differentiableAt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:48.347436+00:00
-- url     : https://prove2.me/submissions/443bb81d-467f-4b00-854b-d3984e7bea31

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_contDiffAt

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    DifferentiableAt ℝ c.radialCoefficient x := by
  exact (c.radialCoefficient_contDiffAt x hx).differentiableAt_one
end NewtonianPointSource
end NewtonianLipschitz
