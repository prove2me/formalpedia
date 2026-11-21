-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_swapYZVec
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:48:19.755377+00:00
-- url     : https://prove2.me/submissions/825df93c-3168-4388-afbd-0e8edffad4f8

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution (x : Vec3) :
    euclideanRadius (swapYZVec x) = euclideanRadius x := by
  simp [euclideanRadius, swapYZVec]
  ring_nf
