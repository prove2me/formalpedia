-- Prove2me | solution 1 for GroundTheory.Global.Complex.isAlgebraic_of_finite_conjugates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:10.630796+00:00
-- url     : https://prove2.me/submissions/a2241aeb-b6da-4642-b1e4-d0cbf5e5b0aa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_finite_range_apply_iff_isAlgebraic

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
namespace GroundTheory.Global
namespace Complex
theorem _root_.solution {x : ℂ}
    (hx : (Set.range fun σ : ℂ ≃+* ℂ => σ x).Finite) : IsAlgebraic ℚ x :=
  finite_range_apply_iff_isAlgebraic.mp hx
end Complex
end GroundTheory.Global
