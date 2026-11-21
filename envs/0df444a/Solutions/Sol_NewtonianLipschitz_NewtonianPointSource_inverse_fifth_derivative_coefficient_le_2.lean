-- Prove2me | solution 2 for NewtonianLipschitz.NewtonianPointSource.inverse_fifth_derivative_coefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:54:09.715558+00:00
-- url     : https://prove2.me/submissions/ec0ab534-0a58-4794-a825-ec6f897a55e3

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
    3 * c.gravitationalParameter / euclideanRadius x ^ 5 ≤
      3 * M / d ^ 5 := by
  have h :=
    c.inverse_power_parameter_le_of_clearance x d M 5 hd hclear hM
  calc
    3 * c.gravitationalParameter / euclideanRadius x ^ 5 =
        3 * (c.gravitationalParameter / euclideanRadius x ^ 5) := by ring
    _ ≤ 3 * (M / d ^ 5) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 3 * M / d ^ 5 := by ring
end NewtonianPointSource
end NewtonianLipschitz
