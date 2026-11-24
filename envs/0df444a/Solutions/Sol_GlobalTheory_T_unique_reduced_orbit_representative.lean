-- Prove2me | solution 1 for GlobalTheory.T.unique_reduced_orbit_representative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:26:05.57538+00:00
-- url     : https://prove2.me/submissions/15779f90-f4b4-453d-8ca4-4deaf4a31d56

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_UniqueReducedOrbitRepresentative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_UniqueReducedOrbitRepresentativeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelKlingen_exists_unique_minimal_translate


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
theorem _root_.solution : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
end _root_.GlobalTheory.T
