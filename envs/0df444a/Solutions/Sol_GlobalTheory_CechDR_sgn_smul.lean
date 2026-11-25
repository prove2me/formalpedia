-- Prove2me | solution 1 for GlobalTheory.CechDR.sgn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:29.339804+00:00
-- url     : https://prove2.me/submissions/ace393d5-c708-4652-9a5a-a0ad8c1f59e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}
namespace GlobalTheory.CechDR
theorem _root_.solution (r : R) (x : DR R B) : sgn (r • x) = r • sgn x := by
  rw [← algebraMap_smul B r x, map_smul, algebraMap_smul]
end GlobalTheory.CechDR
