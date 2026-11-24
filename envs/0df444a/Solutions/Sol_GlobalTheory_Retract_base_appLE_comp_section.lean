-- Prove2me | solution 1 for GlobalTheory.Retract.base_appLE_comp_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:07.871994+00:00
-- url     : https://prove2.me/submissions/fafc3e6b-adec-4c3b-b325-bc6022e9efe3

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
theorem _root_.solution (hi : i ≫ g = f) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    g.appLE W V hVW ≫ i.appLE V U hUV = f.appLE W U hUW := by
  subst hi
  rw [Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.Retract
