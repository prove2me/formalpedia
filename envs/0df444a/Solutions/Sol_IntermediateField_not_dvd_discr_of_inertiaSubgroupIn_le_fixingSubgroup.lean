-- Prove2me | solution 1 for IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/11af4d0f-082e-5197-a78f-19721b4445ad

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Theorems.Thm_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup

set_option autoImplicit false

p2m_open "NumberField Ideal NumberField.Ideal UniqueFactorizationMonoid"

namespace S15
namespace ConvBridge

theorem exists_prime_mem_and_absNorm_eq (K : Type*) [Field K] [NumberField K]
    (Q : Ideal (𝓞 K)) [hQ : Q.IsMaximal] (hQ0 : Q ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ Q ∧ ∃ k : ℕ, absNorm Q = q ^ (k + 1) := by
  haveI : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  letI : Fintype (𝓞 K ⧸ Q) := Fintype.ofFinite _
  letI : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  obtain ⟨k, hq, hcard⟩ := FiniteField.card (𝓞 K ⧸ Q) (ringChar (𝓞 K ⧸ Q))
  refine ⟨ringChar (𝓞 K ⧸ Q), hq, ?_, (k : ℕ) - 1, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  · rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card,
      Nat.sub_add_cancel k.pos]
    exact hcard

theorem main (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hFd : FiniteDimensional ℚ F]
    [IsGalois ℚ F] (q : ℕ) (hq : q.Prime)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup) :
    haveI : NumberField F := @NumberField.mk _ _ inferInstance hFd
    ¬ (q : ℤ) ∣ NumberField.discr F := by
  haveI : NumberField F := @NumberField.mk _ _ inferInstance hFd
  intro hdvd

  have hker_le : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker
      ≤ F.fixingSubgroup := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := AlgEquiv.restrictNormal_commutes σ F ⟨x, hx⟩
    have h1 : σ.restrictNormal F = 1 := hσ
    rw [h1, AlgEquiv.one_apply] at hc
    exact hc.symm
  have hle_ker : F.fixingSubgroup
      ≤ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    change σ.restrictNormal F = 1
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hc := AlgEquiv.restrictNormal_commutes σ F x
    change ((σ.restrictNormal F x : F) : AlgebraicClosure ℚ) = ((x : F) : AlgebraicClosure ℚ)
    have h2 : ((σ.restrictNormal F x : F) : AlgebraicClosure ℚ) =
        algebraMap F (AlgebraicClosure ℚ) (σ.restrictNormal F x) := rfl
    rw [h2, hc]
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ x x.2
  have hunr' : GlobalGaloisRep.IsUnramifiedAt
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F) q :=
    fun A hA => (hunr A hA).trans hle_ker

  set 𝔇 := differentIdeal ℤ (𝓞 F) with h𝔇_def
  have hnorm : absNorm 𝔇 = (discr F).natAbs := absNorm_differentIdeal F (𝓞 F)
  have h𝔇 : 𝔇 ≠ ⊥ := by
    intro h
    have : absNorm 𝔇 = 0 := by rw [h]; exact absNorm_eq_zero_iff.mpr rfl
    rw [hnorm] at this
    exact discr_ne_zero F (Int.natAbs_eq_zero.mp this)
  have h1 : q ∣ absNorm 𝔇 := by rw [hnorm]; exact Int.natCast_dvd.mp hdvd
  have hprod : (normalizedFactors 𝔇).prod = 𝔇 :=
    associated_iff_eq.mp (prod_normalizedFactors h𝔇)
  have h2 : q ∣ ((normalizedFactors 𝔇).map absNorm).prod := by
    rw [← map_multiset_prod, hprod]; exact h1
  obtain ⟨n, hn, hqn⟩ := (Nat.prime_iff.mp hq).exists_mem_multiset_dvd h2
  obtain ⟨Q, hQmem, rfl⟩ := Multiset.mem_map.mp hn
  have hQprime : Prime Q := prime_of_normalized_factor Q hQmem
  have hQ0 : Q ≠ ⊥ := hQprime.ne_zero
  haveI hQmax : Q.IsMaximal := (isPrime_of_prime hQprime).isMaximal hQ0
  have hQdvd : Q ∣ 𝔇 := dvd_of_mem_normalizedFactors hQmem

  obtain ⟨q', hq', hq'Q, k, hk⟩ := exists_prime_mem_and_absNorm_eq F Q hQ0
  have hqq : q = q' := by
    rw [hk] at hqn
    exact (Nat.prime_dvd_prime_iff_eq hq hq').mp (hq.dvd_of_dvd_pow hqn)
  subst hqq

  have hU : Algebra.IsUnramifiedAt ℤ Q :=
    GlobalGaloisRep.IsUnramifiedAt.algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
      hq hunr' F hker_le Q hq'Q

  exact (not_dvd_differentIdeal_iff.mpr hU) hQdvd

end S15.ConvBridge

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup) :
    haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›
    ¬ (q : ℤ) ∣ NumberField.discr F :=
  S15.ConvBridge.main F q hq hunr

end S_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
end P2MW
export P2MW.S_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup (solution)
