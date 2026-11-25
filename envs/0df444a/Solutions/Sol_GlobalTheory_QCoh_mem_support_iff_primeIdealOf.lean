-- Prove2me | solution 1 for GlobalTheory.QCoh.mem_support_iff_primeIdealOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:46.549239+00:00
-- url     : https://prove2.me/submissions/ea93cd1c-6755-4cdf-a69e-282599e7c465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear


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
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support F ↔ hU.primeIdealOf x ∈ Module.support Γ(X, U) Γ(F, U) :=
  have := isLocalizedModule_germLinear F hU x
  (IsLocalizedModule.iso (hU.primeIdealOf x).asIdeal.primeCompl
    (germLinear F x)).toEquiv.nontrivial_congr.symm
end GlobalTheory.QCoh
