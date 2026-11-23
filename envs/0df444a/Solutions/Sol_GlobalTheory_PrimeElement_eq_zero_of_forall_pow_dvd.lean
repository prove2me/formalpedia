-- Prove2me | solution 1 for GlobalTheory.PrimeElement.eq_zero_of_forall_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:12.583403+00:00
-- url     : https://prove2.me/submissions/9a8658a5-77cd-4920-8599-0df369af2abc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
namespace GlobalTheory.PrimeElement
theorem _root_.solution [IsDomain R] [IsNoetherianRing R] (hπ : ¬ IsUnit π) {x : R}
    (hx : ∀ e : ℕ, π ^ e ∣ x) : x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hπ h
  exact hn (hx _)
end GlobalTheory.PrimeElement
