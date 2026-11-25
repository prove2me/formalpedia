-- Prove2me | solution 1 for GlobalTheory.QCoh.map_fibreMk_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:46.026358+00:00
-- url     : https://prove2.me/submissions/b020441f-e905-42c3-8615-cef4ce3228cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution [IsFiniteQC F] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) :
    N.map (fibreMk F x) = ⊤ ↔ N = ⊤ :=
  IsLocalRing.map_tensorProduct_mk_eq_top
end GlobalTheory.QCoh
