-- Prove2me | solution 1 for GlobalTheory.apply_valCentre_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:54.387637+00:00
-- url     : https://prove2.me/submissions/375d6de7-046d-4cde-9902-02fd79c5a74c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {X X' S S' : Scheme.{u}}
variable (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p] (r : Spec (.of V) ⟶ S)
  (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r)
variable {V' K' : Type u} [CommRing V'] [IsDomain V'] [ValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']
namespace GlobalTheory
theorem _root_.solution : p (valCentre p r y h) = r (closedPoint V) :=
  congrArg (fun l : Spec (.of V) ⟶ S ↦ l (closedPoint V)) (valExt_over p r y h)
end GlobalTheory
