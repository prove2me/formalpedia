-- Prove2me | solution 1 for GlobalTheory.Retract.locallyQuasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:11:23.872053+00:00
-- url     : https://prove2.me/submissions/5d8bb00b-92a7-47bd-a85c-062dea65aebb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_quasiFinite_algebra
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
theorem _root_.solution [hg : LocallyQuasiFinite g] : LocallyQuasiFinite f :=
  of_hasRingHomProperty @LocallyQuasiFinite (fun s p h H ↦ by
    rw [RingHom.quasiFinite_algebraMap] at H ⊢
    exact quasiFinite_algebra s p h) hir hr hg
end GlobalTheory.Retract
