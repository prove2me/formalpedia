-- Prove2me | solution 1 for GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:32.092804+00:00
-- url     : https://prove2.me/submissions/ab459cdc-e886-4395-a0d4-fa94eeb35268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (hU : IsAffineOpen U) (x : U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf x).asIdeal.primeCompl ↔ (x : X) ∈ X.basicOpen f := by
  have := hU.isLocalization_stalk x
  rw [X.mem_basicOpen']
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (x : X))
    (hU.primeIdealOf x).asIdeal f).symm
end GlobalTheory.QCoh
