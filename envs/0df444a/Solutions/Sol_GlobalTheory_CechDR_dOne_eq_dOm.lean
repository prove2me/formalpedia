-- Prove2me | solution 1 for GlobalTheory.CechDR.dOne_eq_dOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:33.770218+00:00
-- url     : https://prove2.me/submissions/d2c07c2e-6012-4e92-a0d0-0f5a53dd8d60

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
theorem _root_.solution (ω : Ω[B⁄R]) : dOne R B ω = dOm R B 1 ⟨ι1 ω, ι_mem ω⟩ := rfl
end GlobalTheory.CechDR
