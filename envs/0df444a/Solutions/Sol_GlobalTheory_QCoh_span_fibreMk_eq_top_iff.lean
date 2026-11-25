-- Prove2me | solution 1 for GlobalTheory.QCoh.span_fibreMk_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:49.843793+00:00
-- url     : https://prove2.me/submissions/211be16e-5335-462b-a4a9-59dcc543c822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_map_fibreMk_eq_top_iff

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
theorem _root_.solution [IsFiniteQC F] (x : X) (s : Set (F.presheaf.stalk x :)) :
    Submodule.span (X.residueField x) (fibreMk F x '' s) = ⊤ ↔
      Submodule.span (X.presheaf.stalk x) s = ⊤ := by
  rw [← map_fibreMk_eq_top_iff, Submodule.map_span,
    ← Submodule.restrictScalars_span _ (X.residueField x) (X.residue_surjective x),
    Submodule.restrictScalars_eq_top_iff]
end GlobalTheory.QCoh
