-- Prove2me | solution 1 for GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:03.236271+00:00
-- url     : https://prove2.me/submissions/8ec0632e-9b8b-4bf0-8041-51f6c58bffd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Theorems.Thm_GlobalTheory_isOpen_of_stableUnderGeneralization_of_locally_open_in_closure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)), (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) → (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) → IsOpen U := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure <;> assumption)
end _root_.GlobalTheory.T
