-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:33.165878+00:00
-- url     : https://prove2.me/submissions/f78f5309-709c-4e5a-8ca0-917248b09a4a

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution (x : Vec3) :
    euclideanRadius (coordinateAbs x) = euclideanRadius x := by
  simp [euclideanRadius, coordinateAbs, sq_abs]
