-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:54.746176+00:00
-- url     : https://prove2.me/submissions/9ddff3c9-66f8-4d86-b649-f10bd6b598b7

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    candidateMaximum = candidateCoefficient candidateCriticalPoint := by
  rfl
end NewtonianLipschitz
