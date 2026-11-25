-- Prove2me | solution 1 for GlobalTheory.QCoh.pointOfPrime_mem_assPoints_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:19.660832+00:00
-- url     : https://prove2.me/submissions/57e1d111-b79f-4d4f-94bc-a0e1ee95c60f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_primeIdealOf_pointOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.primeIdealOf_pointOfPrime



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) :
    (pointOfPrime hU P : X) ∈ assPoints F ↔ P.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  rw [mem_assPoints_iff_primeIdealOf hU, primeIdealOf_pointOfPrime]
end GlobalTheory.QCoh
