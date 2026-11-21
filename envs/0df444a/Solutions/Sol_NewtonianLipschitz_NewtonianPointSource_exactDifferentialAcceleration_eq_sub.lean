-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:20.132602+00:00
-- url     : https://prove2.me/submissions/4b59c2b7-7193-4ddc-8340-d243727175a4

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
    (c : NewtonianPointSource) (q : Vec3) :
    c.exactDifferentialAcceleration q =
      c.accelerationField (c.displacement + q) -
        c.accelerationField c.displacement := by
  rfl
end NewtonianPointSource
end NewtonianLipschitz
