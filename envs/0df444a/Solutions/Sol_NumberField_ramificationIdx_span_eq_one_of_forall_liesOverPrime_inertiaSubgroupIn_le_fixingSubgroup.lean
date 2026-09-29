-- Prove2me | solution 1 for NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d2c06cdb-4521-5ab5-b134-7c3192b8a31d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
p2m_open "NumberField P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"
p2m_open_scoped "NumberField P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers.not_isField RingOfIntegers exists_lift_mem_inertia_integralClosure"
namespace RamificationIdxSpanEqOne
p2m_open "NumberField"

scoped instance instIsGaloisRatAlgebraicClosure : IsGalois ℚ (AlgebraicClosure ℚ) := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  exact ⟨⟩

end NumberField.RamificationIdxSpanEqOne
p2m_reactivate "P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField.RamificationIdxSpanEqOne"
p2m_reactivate "P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.NumberField"

open NumberField.RamificationIdxSpanEqOne in
theorem solution
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Ideal.span {(ℓ : ℤ)}) Q = 1 := by
  classical
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

  haveI : IsScalarTower ℤ (𝓞 (↥L)) (↥L) := AddCommGroup.intIsScalarTower
  haveI : IsScalarTower ℤ ℚ (↥L) := AddCommGroup.intIsScalarTower
  set q₀ : Ideal ℤ := Q.under ℤ with hq₀def
  haveI hQq₀ : Q.LiesOver q₀ := ⟨rfl⟩
  have hq₀bot : q₀ ≠ ⊥ := fun h => hQbot (Ideal.eq_bot_of_comap_eq_bot h)
  haveI hq₀prime : q₀.IsPrime := Ideal.comap_isPrime _ Q
  haveI hq₀max : q₀.IsMaximal := Ideal.IsPrime.isMaximal hq₀prime hq₀bot
  have hℓmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hℓq₀ : (ℓ : ℤ) ∈ q₀ := by
    rw [hq₀def, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hℓQ
  have hq₀eq : q₀ = Ideal.span {(ℓ : ℤ)} :=
    (hℓmax.eq_of_le hq₀prime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hℓq₀)).symm

  haveI hGG : IsGaloisGroup (↥L ≃ₐ[ℚ] ↥L) ℤ (𝓞 (↥L)) := by
    have hST : IsScalarTower ℤ (𝓞 (↥L)) (↥L) := AddCommGroup.intIsScalarTower
    exact @IsGaloisGroup.of_isFractionRing (↥L ≃ₐ[ℚ] ↥L) ℤ (𝓞 (↥L)) ℚ (↥L)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hST _ _ _ _ _
  letI : Field (ℤ ⧸ q₀) := Ideal.Quotient.field q₀
  haveI : Finite (ℤ ⧸ q₀) := Ideal.finiteQuotientOfFreeOfNeBot q₀ hq₀bot
  haveI : Module.Finite (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (ℤ ⧸ q₀) ((𝓞 L) ⧸ Q) := inferInstance
  have h1 : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = q₀.ramificationIdxIn (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) q₀ Q
  rw [hInert_bot, Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx q₀ Q (L ≃ₐ[ℚ] L)] at h1
  rw [← hq₀eq]
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := q₀) Q hq₀bot).trans h1.symm

end S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
end P2MW
export P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup (solution)
