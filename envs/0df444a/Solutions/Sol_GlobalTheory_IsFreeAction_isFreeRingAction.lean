-- Prove2me | solution 1 for GlobalTheory.IsFreeAction.isFreeRingAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:26.939239+00:00
-- url     : https://prove2.me/submissions/afff225b-fdc7-4ed9-a3e9-a373fef3e62c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsFreeAction_of_equivariant
import Theorems.Thm_GlobalTheory_isFreeAction_specAction_iff
import Theorems.Thm_GlobalTheory_specAction_fromSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
namespace GlobalTheory
namespace IsFreeAction
theorem _root_.solution {ρ : G →* Aut X} (h : IsFreeAction ρ) {U : X.Opens}
    (hU : IsAffineOpen U) (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) :
    letI := sectionsAction ρ U hst
    IsFreeRingAction G Γ(X, U) :=
  letI := sectionsAction ρ U hst
  (isFreeAction_specAction_iff _).mp (h.of_equivariant _ (specAction_fromSpec ρ hU hst))
end IsFreeAction
end GlobalTheory
