-- Prove2me | solution 1 for NewtonianLipschitz.dominantRowNumerator_eq
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:33.226609+00:00
-- url     : https://prove2.me/submissions/6a92cf3b-3969-452c-8111-d8b50a06c219

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution (u v : ℝ) :
    dominantRowNumerator u v = 2 - u ^ 2 - v ^ 2 + 3 * (u + v) := by
  rfl
