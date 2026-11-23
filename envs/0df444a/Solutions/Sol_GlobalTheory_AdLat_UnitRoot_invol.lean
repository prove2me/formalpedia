-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.invol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:44.984797+00:00
-- url     : https://prove2.me/submissions/43eed8cb-da04-4611-9dca-b39c7b821344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Theorems.Thm_GlobalTheory_AdLat_UnitRoot_eq_one_or

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  rcases eq_one_or c h2 hc (c * c) with h | h
  · exact congrArg (fun g : E ≃ₐ[F] E => g x) h
  · exact absurd (mul_left_cancel (a := c) (h.trans (mul_one c).symm)) hc
end GlobalTheory.AdLat.UnitRoot
