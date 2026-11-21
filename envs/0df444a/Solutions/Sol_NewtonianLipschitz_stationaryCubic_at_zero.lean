-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:39.928244+00:00
-- url     : https://prove2.me/submissions/da65b5d2-9dee-4657-bc6f-599f2b03acef

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : stationaryCubic 0 = 1 := by
  norm_num [stationaryCubic]
end NewtonianLipschitz
