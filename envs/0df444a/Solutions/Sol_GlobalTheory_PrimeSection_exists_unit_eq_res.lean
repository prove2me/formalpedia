-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_unit_eq_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:34.085955+00:00
-- url     : https://prove2.me/submissions/adbfbdc7-cfc5-4105-b912-a7c1f8b11536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X : Scheme.{u}} (t : Γ(X, ⊤)) :
    ∃ τ : Γ(X, X.basicOpen t)ˣ,
      (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t := by
  refine ⟨(X.toRingedSpace.isUnit_res_basicOpen t).unit, ?_⟩
  rfl
end GlobalTheory.PrimeSection
