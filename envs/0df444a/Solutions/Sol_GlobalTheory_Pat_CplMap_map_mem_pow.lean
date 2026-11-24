-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.map_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:53.175241+00:00
-- url     : https://prove2.me/submissions/4a65e650-fc62-4fe2-a373-da9746ff184c

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
theorem _root_.solution (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {a : R} (ha : a ∈ q ^ n) :
    ψ a ∈ maximalIdeal S' ^ n := by
  have h : (q ^ n).map ψ ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hψ.ge) n
  exact h (Ideal.mem_map_of_mem ψ ha)
end GlobalTheory.Pat.CplMap
