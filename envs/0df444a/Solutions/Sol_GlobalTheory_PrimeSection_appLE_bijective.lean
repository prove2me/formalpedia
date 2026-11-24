-- Prove2me | solution 1 for GlobalTheory.PrimeSection.appLE_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:32.443962+00:00
-- url     : https://prove2.me/submissions/9c6c958f-079c-41cb-a5c0-b8dd9081451a

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
theorem _root_.solution {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {U : X.Opens}
    (hU : U ≤ j.opensRange) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Bijective (j.appLE U W h.le) := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  have := j.isIso_app U hU
  exact ConcreteCategory.bijective_of_isIso _
end GlobalTheory.PrimeSection
