-- Prove2me | solution 1 for GlobalTheory.Retract.quasiSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:11:26.386949+00:00
-- url     : https://prove2.me/submissions/f45e5109-c99d-4729-b98c-baaa43e76781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_section_comp
import Theorems.Thm_GlobalTheory_Retract_mono_section

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
theorem _root_.solution [QuasiSeparated g] : QuasiSeparated f := by
  have := mono_section hir
  rw [← section_comp hir hr]
  infer_instance
end GlobalTheory.Retract
