-- Prove2me | solution 1 for GlobalTheory.Retract.geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:24.269643+00:00
-- url     : https://prove2.me/submissions/dd700a96-979a-424b-8b46-f886f2386482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_isIntegral
import Theorems.Thm_GlobalTheory_Retract_geometrically

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
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr
namespace GlobalTheory.Retract
theorem _root_.solution [hg : GeometricallyIntegral g] : GeometricallyIntegral f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ isIntegral h) hg.1⟩
end GlobalTheory.Retract
