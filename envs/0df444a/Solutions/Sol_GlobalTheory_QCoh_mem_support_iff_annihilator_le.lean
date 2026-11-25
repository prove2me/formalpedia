-- Prove2me | solution 1 for GlobalTheory.QCoh.mem_support_iff_annihilator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:59.928059+00:00
-- url     : https://prove2.me/submissions/fe18af2b-d3c0-4d9f-869a-4c15376856a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_mem_support_iff_primeIdealOf

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
theorem _root_.solution [IsFiniteQC F] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support F ↔
      Module.annihilator Γ(X, U) Γ(F, U) ≤ (hU.primeIdealOf x).asIdeal :=
  have := finite_sections F hU
  (mem_support_iff_primeIdealOf hU x).trans Module.mem_support_iff_of_finite
end GlobalTheory.QCoh
