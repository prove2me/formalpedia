-- Prove2me | solution 1 for GlobalTheory.ChebCross.exists_pow_eq_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:50.170199+00:00
-- url     : https://prove2.me/submissions/4a01b52b-060c-4a79-b046-5acb0877c316

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.ChebCross
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.ChebCross
theorem _root_.solution (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by
  let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M
  have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x := fun f x =>
    AlgEquiv.restrictNormal_commutes f M x
  have h1 : ρ σ ∈ Subgroup.zpowers (ρ h) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply Subtype.ext
    rw [hρ]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine hσ _ ⟨x.2, ?_⟩
    change (x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨n, rfl⟩
    have := hx (ρ (h ^ n)) ⟨n, by simp⟩
    rw [← hρ, this]
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, fun x hx => ?_⟩
  have := hρ σ ⟨x, hx⟩
  rw [← hk] at this
  simp only [← map_pow] at this
  rw [hρ] at this
  exact this.symm
end GlobalTheory.ChebCross
