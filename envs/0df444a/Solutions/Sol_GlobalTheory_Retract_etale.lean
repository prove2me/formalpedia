-- Prove2me | solution 1 for GlobalTheory.Retract.etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:53.994866+00:00
-- url     : https://prove2.me/submissions/0c805808-e013-48f8-ab66-3819b05ce099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_etale_algebra
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
theorem _root_.solution [hg : Etale g] : Etale f :=
  of_hasRingHomProperty @Etale (fun s p h H ↦ by
    rw [RingHom.etale_algebraMap] at H ⊢
    exact etale_algebra s p h) hir hr hg
end GlobalTheory.Retract
