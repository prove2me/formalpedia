-- Prove2me | solution 1 for GlobalTheory.specAction_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:12.917449+00:00
-- url     : https://prove2.me/submissions/2b46f88d-9111-495f-b911-3d572b8e7f2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (ρ : G →* Aut X) {U : X.Opens} (hU : IsAffineOpen U)
    (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) (g : G) :
    letI := sectionsAction ρ U hst
    (specAction G Γ(X, U) g).hom ≫ hU.fromSpec = hU.fromSpec ≫ (ρ g).hom := by
  let := sectionsAction ρ U hst
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (ρ g).hom hU hU (hst g), specAction_hom]
  congr 2
  ext s
  change (ρ g⁻¹⁻¹).hom.appLE U U (hst _) s = _
  simp only [inv_inv]
end GlobalTheory
