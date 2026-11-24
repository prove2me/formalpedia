-- Prove2me | solution 1 for GlobalTheory.PrimeSection.germ_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:27.60675+00:00
-- url     : https://prove2.me/submissions/1c006a8e-e7a4-4df3-af1e-cb87c33a14b1

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
theorem _root_.solution {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s) = X.presheaf.germ U x (h hx) s := by
  rw [X.presheaf.germ_res_apply (homOfLE h) x hx s]
end GlobalTheory.PrimeSection
