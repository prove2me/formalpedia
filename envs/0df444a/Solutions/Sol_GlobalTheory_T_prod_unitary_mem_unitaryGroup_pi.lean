-- Prove2me | solution 1 for GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:24.21598+00:00
-- url     : https://prove2.me/submissions/7779688c-8dc1-4cd1-8d39-6f885146c284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryTensorPlacesSlots
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryTensorPlacesSlotsStatement
import Theorems.Thm_GlobalTheory_unitary_tensor_places_positions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) → (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈ Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  first | exact @GlobalTheory.unitary_tensor_places_positions | exact GlobalTheory.unitary_tensor_places_positions | (intros; apply GlobalTheory.unitary_tensor_places_positions <;> assumption)
end _root_.GlobalTheory.T
