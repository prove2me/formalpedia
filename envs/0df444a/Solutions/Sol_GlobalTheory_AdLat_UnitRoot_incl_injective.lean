-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.incl_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:12.263013+00:00
-- url     : https://prove2.me/submissions/46d7398b-70cf-47a8-95b0-a3b2dca62d72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_incl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution : Function.Injective (incl F) := fun a b h =>
  funext fun v => Subtype.ext (by rw [← incl_apply, ← incl_apply, h])
end GlobalTheory.AdLat.UnitRoot
