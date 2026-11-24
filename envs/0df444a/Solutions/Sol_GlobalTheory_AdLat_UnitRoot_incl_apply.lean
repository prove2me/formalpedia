-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.incl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:13.990864+00:00
-- url     : https://prove2.me/submissions/00f5c1e3-daaf-42c3-bcf6-236e80dc086f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele

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
theorem _root_.solution (a : IntAd F) (v) : incl F a v = a v := rfl
end GlobalTheory.AdLat.UnitRoot
