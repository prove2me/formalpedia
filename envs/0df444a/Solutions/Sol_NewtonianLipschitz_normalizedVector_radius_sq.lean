-- Prove2me | solution 1 for NewtonianLipschitz.normalizedVector_radius_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:23:57.564162+00:00
-- url     : https://prove2.me/submissions/6f79dffc-810c-42b6-a74d-7d5cddf5368f

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates


set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (u v : ℝ) :
    euclideanRadius (normalizedVector u v) ^ 2 =
      1 + u ^ 2 + v ^ 2 := by
  rw [euclideanRadius_eq_coordinates]
  change Real.sqrt ((1 : ℝ) ^ 2 + u ^ 2 + v ^ 2) ^ 2 =
    1 + u ^ 2 + v ^ 2
  rw [Real.sq_sqrt (by positivity : 0 ≤ (1 : ℝ) ^ 2 + u ^ 2 + v ^ 2)]
  ring
end NewtonianLipschitz
