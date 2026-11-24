-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.ext_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:52.106824+00:00
-- url     : https://prove2.me/submissions/0aa68dc9-baa3-4a05-995d-385473db0c95

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
theorem _root_.solution (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) {F : S →+* S'}
    (hF : F.comp φ = ψ) (n : ℕ) {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    F x ∈ maximalIdeal S' ^ n := by
  have h1 : (maximalIdeal S).map F ≤ maximalIdeal S' := by
    rw [hφ.max_eq, Ideal.map_map, hF]
    exact Ideal.map_le_iff_le_comap.mpr hψ.ge
  have h2 : (maximalIdeal S ^ n).map F ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem F hx)
end GlobalTheory.Pat.CplMap
