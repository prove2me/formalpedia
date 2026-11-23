-- Prove2me | solution 1 for GlobalTheory.Pat.CplMap.val_unique_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:26.744228+00:00
-- url     : https://prove2.me/submissions/692be416-1efd-421d-987c-5888de05caff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
import Theorems.Thm_GlobalTheory_Pat_CplMap_isUnit_mk

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
variable [hq : q.IsPrime]
omit hq
namespace GlobalTheory.Pat.CplMap
theorem _root_.solution (hψ : (maximalIdeal S').comap ψ = q) {n : ℕ} {s : S}
    {t t' : S' ⧸ maximalIdeal S' ^ n} (ht : IsVal q φ ψ n s t) {a b : R} (hb : b ∉ q)
    (h : φ b * s - φ a ∈ maximalIdeal S ^ n)
    (e : Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t' =
      Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)) : t = t' :=
  (isUnit_mk hψ n hb).mul_left_cancel ((ht a b hb h).trans e.symm)
end GlobalTheory.Pat.CplMap
