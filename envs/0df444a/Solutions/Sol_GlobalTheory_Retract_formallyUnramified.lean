-- Prove2me | solution 1 for GlobalTheory.Retract.formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:19.605371+00:00
-- url     : https://prove2.me/submissions/ea9cf622-d155-457f-a9a5-b2776f575765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_formallyUnramified_algebra
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
theorem _root_.solution [hg : FormallyUnramified g] : FormallyUnramified f :=
  of_hasRingHomProperty @FormallyUnramified (fun s p h H ↦ by
    rw [RingHom.formallyUnramified_algebraMap] at H ⊢
    exact formallyUnramified_algebra s p h) hir hr hg
end GlobalTheory.Retract
