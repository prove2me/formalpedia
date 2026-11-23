-- Prove2me | solution 1 for GlobalTheory.Retract.over_left_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.771365+00:00
-- url     : https://prove2.me/submissions/863ede07-91b6-45ea-9212-a726fc00a780

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
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.Retract
theorem _root_.solution (h : CategoryTheory.Retract X Y) : h.i.left ≫ h.r.left = 𝟙 X.left := by
  rw [← Over.comp_left, h.retract, Over.id_left]
end GlobalTheory.Retract
