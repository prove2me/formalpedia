-- Prove2me | solution 1 for NewtonianLipschitz.coordinateAbs_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:25:40.636343+00:00
-- url     : https://prove2.me/submissions/77a191c8-1772-49bb-bd56-05b93049ff8b

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) (i : Fin 3) :
    coordinateAbs x i = |x i| := by
  rfl
end NewtonianLipschitz
