-- Prove2me | solution 1 for GlobalTheory.Retract.apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:07.2288+00:00
-- url     : https://prove2.me/submissions/84fbc068-8f70-478f-88b5-aea4707078c1

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
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (x : X) : r (i x) = x := by
  rw [← Scheme.Hom.comp_apply, hir]; rfl
end GlobalTheory.Retract
