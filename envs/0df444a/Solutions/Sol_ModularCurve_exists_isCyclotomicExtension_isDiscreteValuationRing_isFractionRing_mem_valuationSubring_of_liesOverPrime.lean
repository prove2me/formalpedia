-- Prove2me | solution 1 for ModularCurve.exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/87154dac-7396-5b73-8421-b73cf9e66f53

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : IsCyclotomicExtension {p} ℚ L) (ζ : L) (_ : IsPrimitiveRoot ζ p)
      (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra A L) (_ : IsFractionRing A L)
      (_ : (p : A) ∈ IsLocalRing.maximalIdeal A) (_ : ∃ z : A, algebraMap A L z = ζ)
      (_ : Algebra A (AlgebraicClosure ℚ)) (_ : Algebra L (AlgebraicClosure ℚ)) (_ : IsScalarTower A L (AlgebraicClosure ℚ)),
      (∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ P) ∧
      (∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ P.valuation (algebraMap A (AlgebraicClosure ℚ) a) < 1) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) := CyclotomicField.isCyclotomicExtension p ℚ

  let ζ : (CyclotomicField p ℚ) := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  let σ : (CyclotomicField p ℚ) →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI instL : Algebra (CyclotomicField p ℚ) (AlgebraicClosure ℚ) := σ.toRingHom.toAlgebra
  have hσ : ∀ x : (CyclotomicField p ℚ), algebraMap (CyclotomicField p ℚ) (AlgebraicClosure ℚ) x = σ x := fun _ => rfl

  haveI hT : IsScalarTower ℤ P (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun n => by
      rw [show algebraMap ℤ P n = (n : P) from rfl, map_intCast]; rfl
  have hint : ∀ x : AlgebraicClosure ℚ, IsIntegral ℤ x → x ∈ P := by
    intro x hx
    have hx' : IsIntegral P x := @IsIntegral.tower_top ℤ P (AlgebraicClosure ℚ) _ _ _ _ _ _ hT _ hx
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := AlgebraicClosure ℚ)).1 hx'
    rw [← hy]; exact y.2

  let O := NumberField.RingOfIntegers (CyclotomicField p ℚ)
  have hOP : ∀ x : O, σ (x : (CyclotomicField p ℚ)) ∈ P := fun x =>
    hint _ (map_isIntegral_int σ (NumberField.RingOfIntegers.isIntegral_coe x))
  let φO : O →+* P :=
    { toFun := fun x => ⟨σ (x : (CyclotomicField p ℚ)), hOP x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφO : ∀ x : O, ((φO x : P) : AlgebraicClosure ℚ) = σ (x : (CyclotomicField p ℚ)) := fun _ => rfl
  let 𝔭 : Ideal O := (IsLocalRing.maximalIdeal P).comap φO
  haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime φO _
  have hmem𝔭 : ∀ x : O, x ∈ 𝔭 ↔ P.valuation (σ (x : (CyclotomicField p ℚ))) < 1 := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]; rfl
  have hpval : P.valuation (p : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff P).1 hP
  have hp𝔭 : (p : O) ∈ 𝔭 := by rw [hmem𝔭]; simpa using hpval
  have h𝔭0 : 𝔭 ≠ ⊥ := fun h => by
    have : (p : O) = 0 := by rw [← Ideal.mem_bot, ← h]; exact hp𝔭
    exact hp.ne_zero (by exact_mod_cast this)

  let A := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O h𝔭0 A
  have hs0 : ∀ s : 𝔭.primeCompl, (s : O) ≠ 0 := fun s h0 => s.2 (by rw [h0]; exact 𝔭.zero_mem)
  have hOL : ∀ s : 𝔭.primeCompl, IsUnit (algebraMap O (CyclotomicField p ℚ) s) := fun s =>
    IsUnit.mk0 _ (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr (hs0 s))
  let jL : A →+* (CyclotomicField p ℚ) := IsLocalization.lift (M := 𝔭.primeCompl) (S := A) hOL
  letI instAL : Algebra A (CyclotomicField p ℚ) := jL.toAlgebra
  have hjL : ∀ x : O, algebraMap A (CyclotomicField p ℚ) (algebraMap O A x) = (x : (CyclotomicField p ℚ)) := fun x => IsLocalization.lift_eq hOL x
  haveI : IsScalarTower O A (CyclotomicField p ℚ) := IsScalarTower.of_algebraMap_eq fun x => (hjL x).symm
  haveI : IsFractionRing A (CyclotomicField p ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl A (CyclotomicField p ℚ)
  letI instAQ : Algebra A (AlgebraicClosure ℚ) := ((algebraMap (CyclotomicField p ℚ) (AlgebraicClosure ℚ)).comp (algebraMap A (CyclotomicField p ℚ))).toAlgebra
  haveI : IsScalarTower A (CyclotomicField p ℚ) (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAQ : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a = σ (algebraMap A (CyclotomicField p ℚ) a) := fun _ => rfl

  have hval1 : ∀ s : 𝔭.primeCompl, P.valuation (σ ((s : O) : (CyclotomicField p ℚ))) = 1 := by
    intro s
    have hle : P.valuation (σ ((s : O) : (CyclotomicField p ℚ))) ≤ 1 := (P.valuation_le_one_iff _).2 (hOP s)
    have hnlt : ¬ P.valuation (σ ((s : O) : (CyclotomicField p ℚ))) < 1 := fun hlt => s.2 ((hmem𝔭 s).2 hlt)
    exact le_antisymm hle (not_lt.1 hnlt)

  have hmk : ∀ a : A, ∃ (x : O) (s : 𝔭.primeCompl), IsLocalization.mk' A x s = a := fun a =>
    by obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a; exact ⟨x, s, h⟩
  have hmk' : ∀ (x : O) (s : 𝔭.primeCompl), σ (algebraMap A (CyclotomicField p ℚ) (IsLocalization.mk' A x s)) * σ ((s : O) : (CyclotomicField p ℚ)) = σ ((x : O) : (CyclotomicField p ℚ)) := by
    intro x s
    rw [← map_mul, ← hjL s, ← map_mul, IsLocalization.mk'_spec, hjL]
  have hσs0 : ∀ s : 𝔭.primeCompl, σ ((s : O) : (CyclotomicField p ℚ)) ≠ 0 := fun s =>
    (map_ne_zero σ).2 (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr (hs0 s))

  have hAP : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ P := by
    intro a
    obtain ⟨x, s, rfl⟩ := hmk a
    rw [hAQ, ← P.valuation_le_one_iff]
    have h := congrArg P.valuation (hmk' x s)
    rw [map_mul, hval1, mul_one] at h
    rw [h]; exact (P.valuation_le_one_iff _).2 (hOP x)

  have hAmax : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ P.valuation (algebraMap A (AlgebraicClosure ℚ) a) < 1 := by
    intro a
    obtain ⟨x, s, rfl⟩ := hmk a
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff A 𝔭 x s, hmem𝔭, hAQ]
    have h := congrArg P.valuation (hmk' x s)
    rw [map_mul, hval1, mul_one] at h
    rw [h]

  have hpA : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (p : A) = algebraMap O A (p : O) := (map_natCast (algebraMap O A) p).symm
    rw [this, IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔭]; exact hp𝔭
  have hζint : IsIntegral ℤ ζ := hζ.isIntegral hp.pos
  let z : O := ⟨ζ, hζint⟩
  have hζA : ∃ a : A, algebraMap A (CyclotomicField p ℚ) a = ζ := ⟨algebraMap O A z, hjL z⟩
  exact ⟨(CyclotomicField p ℚ), inferInstance, inferInstance, inferInstance, ζ, hζ, A, inferInstance, inferInstance, inferInstance, instAL,
    inferInstance, hpA, hζA, instAQ, instL, inferInstance, hAP, hAmax⟩

end S_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime (solution)
