-- Prove2me | solution 1 for GlobalTheory.Retract.isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:00.320234+00:00
-- url     : https://prove2.me/submissions/55d14917-e8b4-451c-a102-3e2c9f1e15a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_section_comp
import Theorems.Thm_GlobalTheory_Retract_isClosedImmersion_section

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
theorem _root_.solution [IsFinite g] : IsFinite f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance
end GlobalTheory.Retract
