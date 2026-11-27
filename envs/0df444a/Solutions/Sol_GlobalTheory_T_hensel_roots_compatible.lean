-- Prove2me | solution 1 for GlobalTheory.T.hensel_roots_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:03.631259+00:00
-- url     : https://prove2.me/submissions/4cdfbe1c-34a6-49cf-af6d-56ac73dde0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatibleStatement
import Theorems.Thm_GlobalTheory_lift_of_compatible_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V), IsLocalHom α → ∀ (θ : R) (η : V) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (q.map α).eval η = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) → ∃ ψ : R →+* V, ψ.comp φ = α ∧ IsLocalHom ψ := by
  first | exact @GlobalTheory.lift_of_compatible_approx | exact GlobalTheory.lift_of_compatible_approx | (intros; apply GlobalTheory.lift_of_compatible_approx <;> assumption)
end _root_.GlobalTheory.T
