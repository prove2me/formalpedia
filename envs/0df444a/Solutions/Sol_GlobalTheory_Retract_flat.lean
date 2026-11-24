-- Prove2me | solution 1 for GlobalTheory.Retract.flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:50:24.084519+00:00
-- url     : https://prove2.me/submissions/54485f5a-9611-48f5-bfa6-9b102196b0e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_flat_algebra
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
theorem _root_.solution [hg : Flat g] : Flat f :=
  of_hasRingHomProperty @Flat (fun s p h H ↦ by
    rw [RingHom.flat_algebraMap_iff] at H ⊢
    exact flat_algebra s p h) hir hr hg
end GlobalTheory.Retract
