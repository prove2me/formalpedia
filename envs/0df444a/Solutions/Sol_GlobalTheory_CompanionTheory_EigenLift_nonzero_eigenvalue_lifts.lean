-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:42.416805+00:00
-- url     : https://prove2.me/submissions/47a28f7e-13f6-4ced-9d9c-50db27bf7c35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjection
import Theorems.Thm_GlobalTheory_CompanionTheory_EigenLift_exists_eigenvector_of_surjective_intertwiner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EigenLift
namespace GlobalTheory.CompanionTheory.EigenLift
theorem _root_.solution :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS
end GlobalTheory.CompanionTheory.EigenLift
