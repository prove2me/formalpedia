-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:15.750808+00:00
-- url     : https://prove2.me/submissions/3ea54fca-833b-4d23-8c79-706113323787

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_exists_eq_mul_isUnit

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
theorem _root_.solution :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ _ ι δ D hδ hspan _ hD h2 hns
  refine ⟨fun I => ⟨?_⟩⟩
  obtain ⟨g₀, hg₀⟩ := (IsPrincipalIdealRing.principal (Ideal.comap ι I)).principal
  have hg₀I : ι g₀ ∈ I := by
    have hmem : g₀ ∈ Ideal.comap ι I := by
      rw [hg₀]
      exact Submodule.mem_span_singleton_self g₀
    exact Ideal.mem_comap.1 hmem
  refine ⟨ι g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hg₀I)⟩
  intro y hy
  obtain ⟨g, u, hu, rfl⟩ := exists_eq_mul_isUnit ι δ D hδ hspan hD h2 hns y
  have hg : g ∈ Ideal.comap ι I := by
    rw [Ideal.mem_comap]
    have he : ι g = ι g * u * ↑hu.unit⁻¹ := by rw [mul_assoc, hu.mul_val_inv, mul_one]
    rw [he]
    exact I.mul_mem_right _ hy
  rw [hg₀] at hg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hg
  refine Ideal.mem_span_singleton.2 ⟨ι r * u, ?_⟩
  rw [← hr, smul_eq_mul, map_mul]
  ring
end GlobalTheory.CompanionTheory.QuadraticUnit
