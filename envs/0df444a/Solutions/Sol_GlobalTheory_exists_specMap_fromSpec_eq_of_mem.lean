-- Prove2me | solution 1 for GlobalTheory.exists_specMap_fromSpec_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:31:14.814812+00:00
-- url     : https://prove2.me/submissions/cec91fe2-5811-4c11-a33d-1e9b89291d26

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
open GlobalTheory.IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]
namespace GlobalTheory.IsAffineQuotient
namespace _root_.GlobalTheory
theorem _root_.solution (x : Spec (.of k) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x default ∈ U) :
    ∃ φ : Γ(X, U) ⟶ .of k, Spec.map φ ≫ hU.fromSpec = x := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec x (by
    rintro _ ⟨z, rfl⟩
    rwa [hU.range_fromSpec, Subsingleton.elim z default]))
  exact ⟨φ, by rw [hφ]; exact IsOpenImmersion.lift_fac ..⟩
end _root_.GlobalTheory
end GlobalTheory.IsAffineQuotient
