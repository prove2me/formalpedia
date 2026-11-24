-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.map_mul_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:55.509793+00:00
-- url     : https://prove2.me/submissions/fc99b206-088d-4819-8d3d-16cabd041cda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution {G : Type} [CommGroup G] (φ : S m →* G) {I J : Ideal R} (hI : IsCoprime I m)
    (hJ : IsCoprime J m) : φ ⟨I * J, hI.mul_left hJ⟩ = φ ⟨I, hI⟩ * φ ⟨J, hJ⟩ := by
  have h : (⟨I * J, hI.mul_left hJ⟩ : S m) = (⟨I, hI⟩ : S m) * (⟨J, hJ⟩ : S m) :=
    Subtype.ext (Submonoid.coe_mul (S m) ⟨I, hI⟩ ⟨J, hJ⟩).symm
  rw [h, map_mul]
end GlobalTheory.Mem.RayEx
