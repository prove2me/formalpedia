-- Prove2me | solution 1 for GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:52.422911+00:00
-- url     : https://prove2.me/submissions/2d1a27f9-5fd7-4b8e-a95b-a2451d1cec31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteTypeStatement
import Theorems.Thm_GlobalTheory_ringKrullDim_lt_top_of_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D], ringKrullDim D < ⊤ := by
  first | exact @GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | exact GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | (intros; apply GlobalTheory.ringKrullDim_lt_top_of_essFiniteType <;> assumption)
end _root_.GlobalTheory.T
