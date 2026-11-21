-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_gravitationalParameter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:21:36.135535+00:00
-- url     : https://prove2.me/submissions/d63406bd-0936-4d45-947b-90735d447993

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution :
    NewtonianPointSource.unitAxis.gravitationalParameter = 1 := by
  rfl
end NewtonianPointSource
end NewtonianLipschitz
