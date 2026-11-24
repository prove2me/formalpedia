-- Prove2me | solution 1 for GlobalTheory.Retract.over_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:09.15827+00:00
-- url     : https://prove2.me/submissions/37d39695-61b1-4103-8a56-f996a209b07f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_properties
import Theorems.Thm_GlobalTheory_Retract_over_left_comp

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
theorem _root_.solution (h : CategoryTheory.Retract X Y) :
    (LocallyOfFiniteType Y.hom → LocallyOfFiniteType X.hom) ∧
    (LocallyOfFinitePresentation Y.hom → LocallyOfFinitePresentation X.hom) ∧
    (Flat Y.hom → Flat X.hom) ∧ (Smooth Y.hom → Smooth X.hom) ∧ (Etale Y.hom → Etale X.hom) ∧
    (QuasiCompact Y.hom → QuasiCompact X.hom) ∧ (IsSeparated Y.hom → IsSeparated X.hom) ∧
    (UniversallyClosed Y.hom → UniversallyClosed X.hom) ∧ (IsProper Y.hom → IsProper X.hom) ∧
    (IsFinite Y.hom → IsFinite X.hom) ∧
    (GeometricallyConnected Y.hom → GeometricallyConnected X.hom) ∧
    Surjective h.r.left ∧ (IsSeparated Y.hom → IsClosedImmersion h.i.left) :=
  properties (over_left_comp h) (Over.w h.r)
end GlobalTheory.Retract
