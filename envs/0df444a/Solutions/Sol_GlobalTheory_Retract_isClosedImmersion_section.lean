-- Prove2me | solution 1 for GlobalTheory.Retract.isClosedImmersion_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:00.458563+00:00
-- url     : https://prove2.me/submissions/0c3cc602-ac13-4c3f-912d-fdcc472a5b31

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
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr
namespace GlobalTheory.Retract
theorem _root_.solution [IsSeparated g] : IsClosedImmersion i := by
  subst hr
  have : IsSeparated r := IsSeparated.of_comp r f
  have : IsClosedImmersion (i ≫ r) := by rw [hir]; infer_instance
  exact IsClosedImmersion.of_comp i r
end GlobalTheory.Retract
