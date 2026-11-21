-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:25:43.263105+00:00
-- url     : https://prove2.me/submissions/002fc581-cbc8-41d3-bed8-2f45ac30deb3

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (t : ℝ) :
    stationaryCubic t = 2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 := by
  rfl
end NewtonianLipschitz
