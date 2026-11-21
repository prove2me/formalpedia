-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:23:58.171242+00:00
-- url     : https://prove2.me/submissions/33429bf5-83fc-43df-ac98-dbd3288c49ac

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x =
      (-(c.gravitationalParameter) / euclideanRadius x ^ 3) • x := by
  rfl
end NewtonianPointSource
end NewtonianLipschitz
