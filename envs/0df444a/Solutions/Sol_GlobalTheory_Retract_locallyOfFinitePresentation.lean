-- Prove2me | solution 1 for GlobalTheory.Retract.locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:50:14.723648+00:00
-- url     : https://prove2.me/submissions/759856fe-5a8f-4848-a97a-97922480f3f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_finitePresentation_algebra
import Theorems.Thm_GlobalTheory_Retract_of_hasRingHomProperty

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
variable (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr
namespace GlobalTheory.Retract
theorem _root_.solution [hg : LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation f :=
  of_hasRingHomProperty @LocallyOfFinitePresentation (fun s p h H ↦ by
    rw [RingHom.finitePresentation_algebraMap] at H ⊢
    exact finitePresentation_algebra s p h) hir hr hg
end GlobalTheory.Retract
