-- Prove2me | solution 1 for GlobalTheory.T.eigenvector_lift_of_surjection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:51.755353+00:00
-- url     : https://prove2.me/submissions/0bffe455-c932-4644-9641-80b04287d532

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjection
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjectionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_EigenLift_nonzero_eigenvalue_lifts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'), Function.Surjective f → f ∘ₗ T = S ∘ₗ f → ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  first | exact @GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | exact GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | (intros; apply GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts <;> assumption)
end _root_.GlobalTheory.T
