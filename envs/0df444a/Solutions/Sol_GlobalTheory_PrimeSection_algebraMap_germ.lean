-- Prove2me | solution 1 for GlobalTheory.PrimeSection.algebraMap_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:32:49.4249+00:00
-- url     : https://prove2.me/submissions/90b83b02-2a2e-424a-aa3c-1fad1521637e

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
variable {X : Scheme.{u}} [IsIntegral X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution {W : X.Opens} {x : X} (hx : x ∈ W) (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx s) =
      X.presheaf.germ W (genericPoint X) (genericPoint_mem hx) s := by
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
end GlobalTheory.PrimeSection
