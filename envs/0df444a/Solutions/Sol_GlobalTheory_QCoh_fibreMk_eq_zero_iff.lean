-- Prove2me | solution 1 for GlobalTheory.QCoh.fibreMk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:09:04.186799+00:00
-- url     : https://prove2.me/submissions/a17226d2-095e-4338-b11e-4f231b588dc1

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
theorem _root_.solution (x : X) (t : (F.presheaf.stalk x :)) :
    fibreMk F x t = 0 ↔ t ∈ (maximalIdeal (X.presheaf.stalk x) • ⊤ :
      Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) := by
  rw [← (fibreEquivQuotient F x).map_eq_zero_iff, fibreEquivQuotient_fibreMk,
    Submodule.Quotient.mk_eq_zero]
end GlobalTheory.QCoh
