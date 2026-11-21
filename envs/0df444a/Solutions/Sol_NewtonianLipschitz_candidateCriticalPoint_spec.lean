-- Prove2me | solution 1 for NewtonianLipschitz.candidateCriticalPoint_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:21:38.388916+00:00
-- url     : https://prove2.me/submissions/f9fe4585-6d99-4fba-b3f4-843c6edccdf1

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    (9 / 50 : ℝ) ≤ candidateCriticalPoint ∧
      candidateCriticalPoint ≤ 1 / 5 ∧
      stationaryCubic candidateCriticalPoint = 0 :=
  Classical.choose_spec stationaryCubic_exists_root_bracket
end NewtonianLipschitz
