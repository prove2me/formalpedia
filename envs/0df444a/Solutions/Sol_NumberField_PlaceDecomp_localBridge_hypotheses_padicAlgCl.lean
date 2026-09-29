-- Prove2me | solution 1 for NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/893adbe1-1bbe-5b5c-97ea-0bff9be96faa

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_NumberField_PlaceDecomp_exists_extension_fixed_of_injective_padicAlgCl
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_map_eq_of_forall_apply_eq_padicAlgCl
import Theorems.Thm_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (hsurj : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
    (heqv : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x))
    (hcont : Continuous Φ) :

    (∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.adicCompletion ↥F)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (PadicAlgCl q)ˣ,
        (∀ v : V, ψ (f v) = Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (φ v)))) ∧
        ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x : W, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (ψ x) = ψ x) ∧

    (∀ a : (PadicAlgCl q)ˣ,
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) = 1 → τ (a : PadicAlgCl q) = a) →
      ∃ x : (w.adicCompletion ↥F)ˣ, Φ (x : w.adicCompletion ↥F) = a) ∧

    (∀ (α : Type) [Finite α]
        (π : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
        (_ : ∀ τ, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
          AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))),
      groupCohomology.IsLevelConstant₁ (localGaloisToGlobal q)
        (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) →
      ∃ χ : (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (groupCohomology.d₀₁ _).hom χ = (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → _)) := by
  exact ⟨NumberField.PlaceDecomp.exists_extension_fixed_of_injective_padicAlgCl q F w σ Φ hΦF hmem hsurj heqv hcont,
    NumberField.PlaceDecomp.exists_unit_map_eq_of_forall_apply_eq_padicAlgCl q F w σ Φ hΦF hmem hsurj heqv hcont,
    NumberField.PlaceDecomp.exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl q F w σ Φ hΦF hmem hsurj heqv hcont⟩

end S_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl
end P2MW
export P2MW.S_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl (solution)
