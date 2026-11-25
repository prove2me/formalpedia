-- Prove2me | solution 1 for GlobalTheory.IsFreeAction.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:42.576305+00:00
-- url     : https://prove2.me/submissions/0c6fe1b2-2450-4a00-96c9-52840cc53bed

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
theorem _root_.solution {ρ : G →* Aut X} (h : IsFreeAction ρ) {T : Scheme.{u}} [Nonempty T]
    (x : T ⟶ X) {g : G} (hx : x ≫ (ρ g).hom = x) : g = 1 :=
  h (T.residueField (Classical.arbitrary T)) (T.fromSpecResidueField _ ≫ x) g
    (by rw [Category.assoc, hx])
end IsFreeAction
end GlobalTheory
