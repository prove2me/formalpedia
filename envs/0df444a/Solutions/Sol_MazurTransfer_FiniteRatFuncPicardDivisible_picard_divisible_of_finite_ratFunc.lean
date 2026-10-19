-- Prove2me | solution 1 for MazurTransfer.FiniteRatFuncPicardDivisible.picard_divisible_of_finite_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:17:20.843738+00:00
-- url     : https://prove2.me/submissions/7ea9e67a-6458-4660-b68a-e449f5f6cde3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The four proofs below are reused from Anthropic FLT, Apache-2.0,
P2M/Sol/S_AlgebraicCurve_Pic0_exists_weilPairing.lean at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: divisibility of Picard classes for a field finite over
RatFunc K, with K algebraically closed of characteristic zero.
Named downstream consumer: injectivity of the actual order-13 divisorial
nineteen-pairing on its existing finite rational-function-field tower.
-/
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Mathlib.FieldTheory.RatFunc.Basic

noncomputable section
namespace MazurTransfer.FiniteRatFuncPicardDivisibilityProofHelpers20261018
open AlgebraicCurve

theorem transcendental_algHom {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (ψ : A →ₐ[K] B) (hinj : Function.Injective ψ)
    {a : A} (ha : Transcendental K a) : Transcendental K (ψ a) := by
  rintro ⟨p, hp0, hpe⟩
  refine ha ⟨p, hp0, hinj ?_⟩
  rw [← Polynomial.aeval_algHom_apply, hpe, map_zero]

theorem transcendental_ratFunc_X {K : Type*} [Field K] :
    Transcendental K (RatFunc.X : RatFunc K) := by
  have h := transcendental_algHom (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
    (IsFractionRing.injective (Polynomial K) (RatFunc K)) (Polynomial.transcendental_X K)
  simpa [RatFunc.algebraMap_X] using h

theorem ratFuncAlgHom_fieldRange_eq_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (φ : RatFunc K →ₐ[K] F) :
    φ.fieldRange = IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
  have key : ∀ p : Polynomial K,
      φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p := by
    intro p
    have h2 : φ.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
        = Polynomial.aeval (φ RatFunc.X) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h2 p
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply RatFunc.induction_on z
    intro p q hq
    show φ (algebraMap (Polynomial K) (RatFunc K) p
        / algebraMap (Polynomial K) (RatFunc K) q)
      ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F)
    rw [map_div₀, key, key]
    have hmem : ∀ r : Polynomial K,
        Polynomial.aeval (φ RatFunc.X) r
          ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin K _
        (Polynomial.aeval_mem_adjoin_singleton K _)
    exact div_mem (hmem p) (hmem q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩



end MazurTransfer.FiniteRatFuncPicardDivisibilityProofHelpers20261018
open AlgebraicCurve
open MazurTransfer.FiniteRatFuncPicardDivisibilityProofHelpers20261018

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (L' : Type*) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'] :
    ∀ m : ℤ, m ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x := by
  intro m hm x

  set ψ : RatFunc K →ₐ[K] L' := IsScalarTower.toAlgHom K (RatFunc K) L' with hψ
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  set x₀ : L' := ψ RatFunc.X with hx₀
  have hx₀tr : Transcendental K x₀ := transcendental_algHom ψ hψinj transcendental_ratFunc_X

  have hE : ψ.fieldRange = IntermediateField.adjoin K ({x₀} : Set L') :=
    ratFuncAlgHom_fieldRange_eq_adjoin ψ

  haveI hfdE : FiniteDimensional (↥ψ.fieldRange) L' := by
    let ε : RatFunc K ≃ₐ[K] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
    letI : Algebra (RatFunc K) ψ.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower (RatFunc K) ψ.fieldRange L' :=
      IsScalarTower.of_algebraMap_eq fun z => rfl
    exact Module.Finite.of_restrictScalars_finite (RatFunc K) (↥ψ.fieldRange) L'
  haveI hfd : FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set L')) L' := by
    rw [← hE]; exact hfdE

  haveI : CharZero (IntermediateField.adjoin K ({x₀} : Set L')) :=
    charZero_of_injective_algebraMap
      (algebraMap K (IntermediateField.adjoin K ({x₀} : Set L'))).injective
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x₀} : Set L')) L' :=
    inferInstance

  haveI : IsCurveOver K L' := isCurveOver_of_transcendental hx₀tr hfd hsep
  obtain ⟨y, hy⟩ := Pic0.exists_nsmul_eq K L' ⟨x₀, hx₀tr, hfd⟩ m.natAbs
    (Int.natAbs_ne_zero.mpr hm) x
  rcases Int.natAbs_eq m with h | h
  · exact ⟨y, by rw [h, natCast_zsmul, hy]⟩
  · refine ⟨-y, ?_⟩
    rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul, hy]

#print axioms solution
