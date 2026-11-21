-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.inverse_cube_parameter_le_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:05.817855+00:00
-- url     : https://prove2.me/submissions/f53fd98a-1da5-4413-acfc-161ffac69729

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_power_parameter_le_of_clearance

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    c.gravitationalParameter / euclideanRadius x ^ 3 ≤
      M / d ^ 3 := by
  exact c.inverse_power_parameter_le_of_clearance x d M 3 hd hclear hM
end NewtonianPointSource
end NewtonianLipschitz
