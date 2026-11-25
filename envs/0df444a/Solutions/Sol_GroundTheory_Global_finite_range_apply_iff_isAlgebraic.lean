-- Prove2me | solution 1 for GroundTheory.Global.finite_range_apply_iff_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:21.135264+00:00
-- url     : https://prove2.me/submissions/53890d41-3ff2-40cd-ac92-fba0bd873cec

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_infinite_range_apply_of_transcendental
import Theorems.Thm_GroundTheory_Global_finite_range_apply_of_isAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
variable [CharZero Ω]
namespace GroundTheory.Global
theorem _root_.solution {x : Ω} :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite ↔ IsAlgebraic ℚ x :=
  ⟨fun h => by_contra fun hx => infinite_range_apply_of_transcendental hx h,
    finite_range_apply_of_isAlgebraic⟩
end GroundTheory.Global
