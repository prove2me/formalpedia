-- Prove2me | solution 1 for GlobalTheory.PrimeSection.res_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:48.773743+00:00
-- url     : https://prove2.me/submissions/3847ef83-83b2-4e22-8a33-523b30495ddb

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
theorem _root_.solution {X : Scheme.{u}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl
end GlobalTheory.PrimeSection
