-- Prove2me | solution 1 for GlobalTheory.UnimodMass.dcOfCoset_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:35:47.829401+00:00
-- url     : https://prove2.me/submissions/80b4648c-44cd-4909-936e-6eb947a11182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
namespace GlobalTheory.UnimodMass
theorem _root_.solution (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := rfl
end GlobalTheory.UnimodMass
