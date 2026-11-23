-- Prove2me | solution 1 for GlobalTheory.Retract.isAffineHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.17502+00:00
-- url     : https://prove2.me/submissions/1ce6583a-fd7e-4faf-8cdc-4bd4587e86a6

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
theorem _root_.solution [IsAffineHom g] : IsAffineHom f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance
end GlobalTheory.Retract
