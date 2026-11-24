-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadraticUnit.exists_eq_mul_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:33.544549+00:00
-- url     : https://prove2.me/submissions/5ae8db31-0bad-46d8-9e1c-58529c4a974f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_isUnit_add_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadraticUnit
open Polynomial IsLocalRing
namespace GlobalTheory.CompanionTheory.QuadraticUnit
theorem _root_.solution {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by
  obtain ⟨p, q, rfl⟩ := hspan y
  rcases ValuationRing.dvd_total p q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨p, 1 + ι r * δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns 1 r (Or.inl isUnit_one)
  · refine ⟨q, ι r + δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns r 1 (Or.inr isUnit_one)
end GlobalTheory.CompanionTheory.QuadraticUnit
