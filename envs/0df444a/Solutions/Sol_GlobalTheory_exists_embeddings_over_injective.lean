-- Prove2me | solution 1 for GlobalTheory.exists_embeddings_over_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:16.771627+00:00
-- url     : https://prove2.me/submissions/ff10e6cd-96de-42ce-9b54-f22fc71a5c0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R A Ω : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] :
    ∃ n : ℕ, ∀ τ : R →+* ℂ, Function.Injective τ → ∃ T : Finset (Ω →+* ℂ), T.card ≤ n ∧
      (∀ σ ∈ T, σ.comp ((algebraMap A Ω).comp (algebraMap R A)) = τ) ∧
      ∀ (b : A) (r : ℂ), ((minpoly R b).map τ).IsRoot r → ∃ σ ∈ T, σ (algebraMap A Ω b) = r := by
  classical
  let _ : Algebra R Ω := ((algebraMap A Ω).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2
    ((IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A))
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Ω :=
    inferInstance
  have : FiniteDimensional F Ω := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  refine ⟨Module.finrank F Ω, fun τ hτ => ?_⟩
  let _ : Algebra F ℂ := (IsFractionRing.lift hτ : F →+* ℂ).toAlgebra
  have hF : ∀ x : R, algebraMap F ℂ (algebraMap R F x) = τ x := fun x =>
    IsFractionRing.lift_algebraMap hτ x
  let _ : Fintype (Ω →ₐ[F] ℂ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun ψ : Ω →ₐ[F] ℂ => (ψ : Ω →+* ℂ), ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_algHom_le_finrank F Ω ℂ
  · intro σ hσ
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hσ
    ext x
    change ψ (algebraMap R Ω x) = τ x
    rw [IsScalarTower.algebraMap_apply R F Ω, AlgHom.commutes, hF]
  · intro b r hr
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    have h1 : r ∈ (minpoly F (algebraMap A Ω b)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F Ω hb, Polynomial.aeval_def,
        Polynomial.eval₂_map, show (algebraMap F ℂ).comp (algebraMap R F) = τ from RingHom.ext hF,
        Polynomial.eval₂_eq_eval_map]
      exact hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ] at h1
    obtain ⟨ψ, hψ⟩ := h1
    exact ⟨ψ, Finset.mem_image.2 ⟨ψ, Finset.mem_univ _, rfl⟩, hψ⟩
end GlobalTheory
