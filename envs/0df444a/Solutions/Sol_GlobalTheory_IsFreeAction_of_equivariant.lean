-- Prove2me | solution 1 for GlobalTheory.IsFreeAction.of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:36.106378+00:00
-- url     : https://prove2.me/submissions/99b530ed-7d30-496a-83ca-5f1d0218a6e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

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
theorem _root_.solution {ρ : G →* Aut X} (h : IsFreeAction ρ) {ρ' : G →* Aut Y}
    (p : Y ⟶ X) (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) : IsFreeAction ρ' := fun k _ x g hx ↦
  h k (x ≫ p) g (by rw [Category.assoc, ← hp, reassoc_of% hx])
end IsFreeAction
end GlobalTheory
