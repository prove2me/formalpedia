-- Prove2me | solution 1 for NewtonianLipschitz.normalized_diagonal_radius
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:48:19.712314+00:00
-- url     : https://prove2.me/submissions/eea539d6-65dd-4346-b516-29b4a78f9df6

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution (t : ℝ) :
    euclideanRadius (normalizedVector t t) =
      Real.sqrt (1 + 2 * t ^ 2) := by
  simp [euclideanRadius, normalizedVector]
  ring_nf
