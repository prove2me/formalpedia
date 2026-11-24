-- Prove2me | solution 1 for GlobalTheory.Retract.base_appLE_comp_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:37.058205+00:00
-- url     : https://prove2.me/submissions/cca8363e-ba84-4126-b887-6d4111cf37a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_appLE_comp_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
namespace GlobalTheory.Retract
theorem _root_.solution (hr : r ≫ f = g) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    f.appLE W U hUW ≫ r.appLE U V hVU = g.appLE W V hVW := by
  subst hr
  rw [Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.Retract
