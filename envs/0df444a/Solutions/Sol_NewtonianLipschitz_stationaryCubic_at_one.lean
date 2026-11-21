-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_at_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:41.013171+00:00
-- url     : https://prove2.me/submissions/1f0d54ed-384f-45df-b38e-08411086f9e8

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : stationaryCubic 1 = -9 := by
  norm_num [stationaryCubic]
end NewtonianLipschitz
