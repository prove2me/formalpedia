-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConstCoeffODE.step_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:53:59.460257+00:00
-- url     : https://prove2.me/submissions/5c89d7e7-416d-49f0-91ce-e06bece9ef38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpace
import Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_stepMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConstCoeffODE
namespace GlobalTheory.CompanionTheory.ConstCoeffODE
theorem _root_.solution (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (step c S) :=
  FiniteDimensional.of_injective (stepMap c S) (stepMap_injective c S)
end GlobalTheory.CompanionTheory.ConstCoeffODE
