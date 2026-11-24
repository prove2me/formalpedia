-- Prove2me | solution 1 for GlobalTheory.CechDR.dTwo_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:26.840964+00:00
-- url     : https://prove2.me/submissions/2cb8093b-1d3d-46ef-aab2-b0a8fc97e5b0

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
theorem _root_.solution {a b : Ω[B⁄R]} (ha : dOne R B a = 0) (hb : dOne R B b = 0) :
    dTwo R B (wedge R B a b) = 0 := by
  have ha' : dDR R B (ι1 a) = 0 := congrArg Subtype.val ha
  have hb' : dDR R B (ι1 b) = 0 := congrArg Subtype.val hb
  exact Subtype.ext (by simp [dDR_mul, ha', hb'])
end GlobalTheory.CechDR
