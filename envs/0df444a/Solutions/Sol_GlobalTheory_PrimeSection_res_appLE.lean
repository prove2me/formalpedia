-- Prove2me | solution 1 for GlobalTheory.PrimeSection.res_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:30.247572+00:00
-- url     : https://prove2.me/submissions/d980396b-d7c0-4abc-94e9-fdc249fdf6c1

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
theorem _root_.solution {X Y : Scheme.{u}} (j : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U) (h' : W' ≤ W) (s : Γ(X, U)) :
    Y.presheaf.map (homOfLE h').op (j.appLE U W h s) = j.appLE U W' (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
end GlobalTheory.PrimeSection
