-- Prove2me | solution 1 for GlobalTheory.IsFreeAction.of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:45.252172+00:00
-- url     : https://prove2.me/submissions/e83eaa88-89e0-4f53-b9ee-5a273938a2bc

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
theorem _root_.solution {ρ : G →* Aut X}
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) (g : G),
      x ≫ (ρ g).hom = x → g = 1) : IsFreeAction ρ := fun k _ x g hx ↦
  h (AlgebraicClosure k) (Spec.map (CommRingCat.ofHom (algebraMap k _)) ≫ x) g
    (by rw [Category.assoc, hx])
end IsFreeAction
end GlobalTheory
