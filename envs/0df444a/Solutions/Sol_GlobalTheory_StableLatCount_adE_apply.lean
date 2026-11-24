-- Prove2me | solution 1 for GlobalTheory.StableLatCount.adE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:29.171118+00:00
-- url     : https://prove2.me/submissions/6ffac71c-c48f-45c0-bf4c-3b553eaf0d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
namespace GlobalTheory.StableLatCount
theorem _root_.solution (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl
end GlobalTheory.StableLatCount
