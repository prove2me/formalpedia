-- Prove2me | solution 1 for GlobalTheory.splitExt_intClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:48.518242+00:00
-- url     : https://prove2.me/submissions/989f6a79-0c4d-4af0-bbe2-44abe9a2ec71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (f : Polynomial (FractionRing A)), f ≠ 0 → ∀ q : ℕ, q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A') (σ : FractionRing A →+* FractionRing A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ (f.map σ).Splits ∧ σ.comp (algebraMap A (FractionRing A)) = (algebraMap A' (FractionRing A')).comp (algebraMap A A') := by
  intro A _ _ _ _ _ f hf q hq
  let K := FractionRing A
  let g : K[X] := f * cyclotomic q K
  let L := SplittingField g
  haveI : Algebra.IsSeparable K L := inferInstance
  let A' := integralClosure A L
  haveI : IsFractionRing A' L := integralClosure.isFractionRing_of_finite_extension K L
  let e : L ≃ₐ[A'] FractionRing A' := IsLocalization.algEquiv (nonZeroDivisors A') L (FractionRing A')
  have hg0 : g ≠ 0 := mul_ne_zero hf (cyclotomic_ne_zero q K)
  have hgL : (g.map (algebraMap K L)).Splits := SplittingField.splits g
  have hgL0 : g.map (algebraMap K L) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hg0
  refine ⟨A', inferInstance, inferInstance, inferInstance, e.toRingHom.comp (algebraMap K L), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsIntegralClosure.finite A K L A'
  · intro x y h
    have h2 : algebraMap A L x = algebraMap A L y := by
      rw [IsScalarTower.algebraMap_apply A A' L, h, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L y] at h2
    exact IsFractionRing.injective A K ((algebraMap K L).injective h2)
  · exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  · haveI : NeZero (q : L) := ⟨Nat.cast_ne_zero.2 hq⟩
    have hc : (cyclotomic q L).Splits := by
      refine hgL.of_dvd hgL0 ?_
      rw [← map_cyclotomic q (algebraMap K L)]
      exact Polynomial.map_dvd _ (dvd_mul_left _ _)
    have hdeg : (cyclotomic q L).degree ≠ 0 := (degree_cyclotomic_pos q L (Nat.pos_of_ne_zero hq)).ne'
    obtain ⟨ζ, hζ⟩ := hc.exists_eval_eq_zero hdeg
    have hprim : IsPrimitiveRoot ζ q := (isRoot_cyclotomic_iff).1 hζ
    have hint : IsIntegral A ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hq)
      (by rw [hprim.pow_eq_one]; exact isIntegral_one)
    refine ⟨⟨ζ, hint⟩, ?_⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := (integralClosure A L).val.toRingHom.toMonoidHom)
      (by exact hprim) Subtype.val_injective
  · have hfL : (f.map (algebraMap K L)).Splits := by
      refine hgL.of_dvd hgL0 ?_
      exact Polynomial.map_dvd _ (dvd_mul_right _ _)
    rw [← Polynomial.map_map]
    exact hfL.map _
  · ext a
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A A' L]
    exact e.commutes _
end GlobalTheory
