-- Prove2me | solution 1 for GlobalTheory.ChebCross.cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:38.838977+00:00
-- url     : https://prove2.me/submissions/67416cf4-de78-4f23-af98-8aea131f785e

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius
import Theorems.Thm_GlobalTheory_ChebCross_autToPow_eq_iff
import Theorems.Thm_GlobalTheory_ChebCross_exists_fixing
import Theorems.Thm_GlobalTheory_ChebCross_irreducible_of_onto
import Theorems.Thm_GlobalTheory_ChebCross_exists_pow_eq_on

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
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  intro F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod m)ˣ)
  obtain ⟨u, hu, hu'⟩ := exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)
  set h := u * g with hh
  have hχ : hζ.autToPow F h = τ := by rw [hh, map_mul, hu']; simp
  haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} F _
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _
  let M : IntermediateField F Ω := L ⊔ IntermediateField.adjoin F {ζ}
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI : IsGalois F M := { }
  have hζM : ζ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)
  refine ⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  · refine irreducible_of_onto _ hζ fun j => ?_
    obtain ⟨n, rfl⟩ := hτ j
    refine ⟨h ^ n, ?_, by simp [hχ]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩
  · intro σ hσ hσζ
    obtain ⟨k, hk⟩ := exists_pow_eq_on M h σ hσ
    have h1 : hζ.autToPow F (h ^ k) = τ := by
      rw [autToPow_eq_iff, ← hk ζ hζM]
      exact hσζ ζ hζ.pow_eq_one
    rw [map_pow, hχ] at h1
    have hord : orderOf τ = m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmod : k ≡ 1 [MOD m - 1] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]
    let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L
    have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x := fun f x =>
      AlgEquiv.restrictNormal_commutes f L x
    have h2 : ρ σ = ρ (h ^ k) := by
      ext x
      rw [hρ, hρ]
      exact hk _ ((le_sup_left : L ≤ M) x.2)
    have h3 : ρ h ^ k = ρ h := by
      conv_rhs => rw [← pow_one (ρ h)]
      rw [pow_eq_pow_iff_modEq]
      refine hmod.of_dvd (dvd_trans ?_ hdiv)
      rw [← IsGalois.card_aut_eq_finrank]
      exact orderOf_dvd_natCard _
    have h4 : ρ u = 1 := by
      rw [← IntermediateField.restrictNormalHom_ker] at hu
      exact hu
    rw [← IntermediateField.restrictNormalHom_ker]
    change ρ (σ * g⁻¹) = 1
    rw [map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]
    simp
end GlobalTheory.ChebCross
