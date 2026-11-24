-- Prove2me | solution 1 for GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:15.016687+00:00
-- url     : https://prove2.me/submissions/2a5612fd-ea76-4e52-9b79-72eb7dabe183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegersStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_map_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ x : K.O, ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  first | exact @GlobalTheory.UnitLemma.Unr.map_int | exact GlobalTheory.UnitLemma.Unr.map_int | (intros; apply GlobalTheory.UnitLemma.Unr.map_int <;> assumption)
end _root_.GlobalTheory.T
