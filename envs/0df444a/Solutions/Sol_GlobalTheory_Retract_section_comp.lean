-- Prove2me | solution 1 for GlobalTheory.Retract.section_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:59.160813+00:00
-- url     : https://prove2.me/submissions/7156d75e-c658-4482-9227-163f89ae18a1

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
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) : i ≫ g = f := by
  rw [← hr, reassoc_of% hir]
end GlobalTheory.Retract
