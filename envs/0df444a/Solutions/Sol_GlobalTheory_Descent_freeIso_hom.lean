-- Prove2me | solution 1 for GlobalTheory.Descent.freeIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:38.713739+00:00
-- url     : https://prove2.me/submissions/3598ed8b-7b92-4c85-aeaf-4c3bd3fb82c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (F : X.Modules)
variable {F} {U : X.Opens} {s : Γ(F, U)}
namespace GlobalTheory.Descent
theorem _root_.solution
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s) :
    (freeIso h).hom = sectionHom s := rfl
end GlobalTheory.Descent
