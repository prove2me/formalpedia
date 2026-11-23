-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.isUnit_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:28.807531+00:00
-- url     : https://prove2.me/submissions/21cc9971-9300-4c81-b2f0-c5b399f28a0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.CplMap
variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}
namespace GlobalTheory.Pat.CplMap
theorem _root_.solution (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {b : R} (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b)) := by
  have h1 : IsUnit (ψ b) := by
    by_contra h
    exact hb (hψ ▸ (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr h)))
  exact h1.map _
end GlobalTheory.Pat.CplMap
