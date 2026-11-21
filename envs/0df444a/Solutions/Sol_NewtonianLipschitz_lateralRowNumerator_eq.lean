-- Prove2me | solution 1 for NewtonianLipschitz.lateralRowNumerator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:32.78053+00:00
-- url     : https://prove2.me/submissions/c2c2721c-625e-4e9f-8fa5-12d033aa376d

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (u v : ℝ) :
    lateralRowNumerator u v =
      |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * (1 + v) := by
  rfl
end NewtonianLipschitz
