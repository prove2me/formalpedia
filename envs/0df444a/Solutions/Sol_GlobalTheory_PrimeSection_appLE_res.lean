-- Prove2me | solution 1 for GlobalTheory.PrimeSection.appLE_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:44.630827+00:00
-- url     : https://prove2.me/submissions/d23c79b6-d21d-4b3d-930b-903bf70de703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X Y : Scheme.{u}} (j : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U') (h' : U' ≤ U) (s : Γ(X, U)) :
    j.appLE U' W h (X.presheaf.map (homOfLE h').op s) =
      j.appLE U W (h.trans (j.preimage_mono h')) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
end GlobalTheory.PrimeSection
