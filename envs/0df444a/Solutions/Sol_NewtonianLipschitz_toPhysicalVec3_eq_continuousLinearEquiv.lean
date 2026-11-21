-- Prove2me | solution 1 for NewtonianLipschitz.toPhysicalVec3_eq_continuousLinearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:21:02.945572+00:00
-- url     : https://prove2.me/submissions/0e8fd3d8-9c36-4395-9b7f-208f8ddd4b6c

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (q : Vec3) :
    toPhysicalVec3 q =
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm) q := by
  rfl
end NewtonianLipschitz
