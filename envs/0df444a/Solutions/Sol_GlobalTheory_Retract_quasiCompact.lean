-- Prove2me | solution 1 for GlobalTheory.Retract.quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:07.190105+00:00
-- url     : https://prove2.me/submissions/93b7f6c0-091a-4101-a375-7776f35e5ce5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_surjective_retraction

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
theorem _root_.solution [QuasiCompact g] : QuasiCompact f := by
  subst hr
  refine ⟨fun U hU hU' ↦ ?_⟩
  have := (QuasiCompact.isCompact_preimage (f := r ≫ f) U hU hU').image r.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
    Set.image_preimage_eq _ (surjective_retraction hir).surj] at this
end GlobalTheory.Retract
