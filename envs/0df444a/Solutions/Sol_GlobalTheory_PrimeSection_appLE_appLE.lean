-- Prove2me | solution 1 for GlobalTheory.PrimeSection.appLE_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:49.360799+00:00
-- url     : https://prove2.me/submissions/849db0a3-9b80-4c78-8531-3c76e1dbff27

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
theorem _root_.solution {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) {k : Z ⟶ X} (hk : i ≫ j = k)
    {U : X.Opens} {W : Y.Opens} {A : Z.Opens} (h : W ≤ j ⁻¹ᵁ U) (h' : A ≤ i ⁻¹ᵁ W)
    (h'' : A ≤ k ⁻¹ᵁ U) (s : Γ(X, U)) :
    i.appLE W A h' (j.appLE U W h s) = k.appLE U A h'' s := by
  subst hk
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.PrimeSection
