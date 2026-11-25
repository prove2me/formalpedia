-- Prove2me | solution 1 for GlobalTheory.CechDR.dOm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:24.170937+00:00
-- url     : https://prove2.me/submissions/7d9ce03e-95f1-48e9-98cd-e646d23a7a28

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
theorem _root_.solution (b : B) (h : algebraMap B (DR R B) b ∈ ⋀[B]^0 Ω[B⁄R]) :
    dOm R B 0 ⟨_, h⟩ = ⟨ι1 (D R B b), ι_mem _⟩ := Subtype.ext (dDR_algebraMap b)
end GlobalTheory.CechDR
