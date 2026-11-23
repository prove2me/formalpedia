-- Prove2me | solution 1 for GlobalTheory.Retract.geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:33.667831+00:00
-- url     : https://prove2.me/submissions/71c8f517-b297-49c7-ac56-d6f3b2f40d0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_connectedSpace
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
theorem _root_.solution [hg : GeometricallyConnected g] : GeometricallyConnected f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ connectedSpace h) hg.1⟩
end GlobalTheory.Retract
