-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:39.865604+00:00
-- url     : https://prove2.me/submissions/0bac8478-3619-4f6d-9105-25fcd3e310be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsHomogeneousRangeMulVecLin
import Theorems.Thm_GlobalTheory_isGradedMap_mulVecLin
import Theorems.Thm_GlobalTheory_IsGradedMap_isHomogeneous_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range
end GlobalTheory
