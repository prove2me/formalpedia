-- Prove2me | solution 1 for GlobalTheory.QCoh.fromSpec_preimage_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:56.479255+00:00
-- url     : https://prove2.me/submissions/1a6f4d33-19cc-4ce9-bcaf-6e457320241f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_mem_support_iff_primeIdealOf
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
variable (F)
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) :
    hU.fromSpec ⁻¹' support F = Module.support Γ(X, U) Γ(F, U) := by
  refine Set.ext fun P : PrimeSpectrum Γ(X, U) ↦ ?_
  have := mem_support_iff_primeIdealOf (F := F) hU (pointOfPrime hU P)
  rwa [primeIdealOf_pointOfPrime] at this
end GlobalTheory.QCoh
