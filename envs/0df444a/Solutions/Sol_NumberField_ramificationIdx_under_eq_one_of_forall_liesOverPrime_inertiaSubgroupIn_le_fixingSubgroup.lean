-- Prove2me | solution 1 for NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a6e6c16b-f498-5a26-a6a9-ae766d9e3160

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
p2m_open "NumberField P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"
p2m_open_scoped "NumberField P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers.not_isField RingOfIntegers RingOfIntegers.algebraMap.injective exists_lift_mem_inertia_integralClosure"
namespace RamificationIdxUnderEqOne
p2m_open "NumberField"

scoped instance instIsGaloisRatAlgebraicClosure : IsGalois ℚ (AlgebraicClosure ℚ) := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  exact ⟨⟩

end NumberField.RamificationIdxUnderEqOne
p2m_reactivate "P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField.RamificationIdxUnderEqOne"
p2m_reactivate "P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"

open NumberField.RamificationIdxUnderEqOne in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (φL : K →ₐ[ℚ] L)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    letI : Algebra K L := φL.toRingHom.toAlgebra
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Q.under (𝓞 K)) Q = 1 := by
  classical
  letI algKL : Algebra K (↥L) := φL.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K (↥L) :=
    IsScalarTower.of_algebraMap_eq fun q => (φL.commutes q).symm
  haveI : NumberField L := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ L›
  intro Q hQm hℓQ
  haveI := hQm
  have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm
    (NumberField.RingOfIntegers.not_isField L)
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot

  have hInert_bot : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτI
    rw [Subgroup.mem_bot]
    obtain ⟨σ, hστ, 𝔔, h𝔔max, hℓ𝔔, hσ𝔔⟩ :=
      NumberField.exists_lift_mem_inertia_integralClosure L Q hℓQ τ hτI
    haveI := h𝔔max
    obtain ⟨A, hA, hσA⟩ :=
      ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn 𝔔 hℓ hℓ𝔔 σ hσ𝔔
    have hσL : σ ∈ L.fixingSubgroup := hHin A hA hσA
    rw [← hστ]
    ext x
    have hx : σ (x : AlgebraicClosure ℚ) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσL x x.2
    have hc : ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L σ x : L) :
        AlgebraicClosure ℚ) = σ x := σ.restrictNormal_commutes L x
    rw [AlgEquiv.one_apply]
    exact hc.trans hx

  haveI : IsScalarTower ℤ (𝓞 K) (𝓞 L) := AddCommGroup.intIsScalarTower
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 L) := Algebra.IsIntegral.of_finite (𝓞 K) (𝓞 L)
  haveI : IsScalarTower ℤ (𝓞 (↥L)) (↥L) := AddCommGroup.intIsScalarTower
  haveI : IsScalarTower ℤ ℚ (↥L) := AddCommGroup.intIsScalarTower
  set 𝔭 : Ideal (𝓞 K) := Q.under (𝓞 K) with h𝔭def
  haveI hQ𝔭 : Q.LiesOver 𝔭 := ⟨rfl⟩
  have h𝔭bot : 𝔭 ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭bot
  set q₀ : Ideal ℤ := Q.under ℤ with hq₀def
  haveI hQq₀ : Q.LiesOver q₀ := ⟨rfl⟩
  have hq₀bot : q₀ ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  haveI h𝔭q₀ : 𝔭.LiesOver q₀ := ⟨(Ideal.under_under Q).symm⟩

  haveI hGG : IsGaloisGroup (↥L ≃ₐ[ℚ] ↥L) ℤ (𝓞 (↥L)) := by
    have hST : IsScalarTower ℤ (𝓞 (↥L)) (↥L) := AddCommGroup.intIsScalarTower
    exact @IsGaloisGroup.of_isFractionRing (↥L ≃ₐ[ℚ] ↥L) ℤ (𝓞 (↥L)) ℚ (↥L)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hST _ _ _ _ _
  haveI hq₀prime : q₀.IsPrime := Ideal.comap_isPrime _ Q
  haveI hq₀max : q₀.IsMaximal := Ideal.IsPrime.isMaximal hq₀prime hq₀bot
  letI : Field (ℤ ⧸ q₀) := Ideal.Quotient.field q₀
  haveI : Finite (ℤ ⧸ q₀) := Ideal.finiteQuotientOfFreeOfNeBot q₀ hq₀bot
  haveI : Module.Finite (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := inferInstance
  have h1 : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = q₀.ramificationIdxIn (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) q₀ Q
  rw [hInert_bot, Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx q₀ Q (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx q₀ Q hq₀bot] at h1

  have hmap𝔭 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭 ≠ ⊥ := fun h =>
    h𝔭bot ((Ideal.map_eq_bot_iff_of_injective
      (RingOfIntegers.algebraMap.injective K L)).mp h)
  have hmapq₀ : Ideal.map (algebraMap ℤ (𝓞 L)) q₀ ≠ ⊥ := fun h =>
    hq₀bot ((Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 L))).mp h)
  have hmaple : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭 ≤ Q := Ideal.map_comap_le
  have htower := Ideal.ramificationIdx_algebra_tower (p := q₀) (P := 𝔭) (Q := Q)
    hmap𝔭 hmapq₀ hmaple
  exact Nat.eq_one_of_mul_eq_one_left (htower.symm.trans h1.symm)

end S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
end P2MW
export P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup (solution)
