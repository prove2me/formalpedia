-- Prove2me | solution 1 for GlobalTheory.T.involution_stable_subspace_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:00.983617+00:00
-- url     : https://prove2.me/submissions/a6e69e2a-33e6-4095-9155-604170167e0e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspaceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_exists_KG_coordinate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by
  first | exact @GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | exact GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | (intros; apply GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate <;> assumption)
end _root_.GlobalTheory.T
