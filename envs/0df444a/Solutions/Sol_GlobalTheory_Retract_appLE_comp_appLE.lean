-- Prove2me | solution 1 for GlobalTheory.Retract.appLE_comp_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:00.42981+00:00
-- url     : https://prove2.me/submissions/eccd8efa-a60c-40aa-820b-2e47a7cc7633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation

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
theorem _root_.solution (hir : i ≫ r = 𝟙 X) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) :
    r.appLE U V hVU ≫ i.appLE V U hUV = 𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  generalize_proofs e
  revert e
  rw [hir]
  intro e
  exact (Category.id_comp _).trans (X.presheaf.map_id _)
end GlobalTheory.Retract
