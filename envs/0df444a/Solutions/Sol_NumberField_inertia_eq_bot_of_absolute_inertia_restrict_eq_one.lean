-- Prove2me | solution 1 for NumberField.inertia_eq_bot_of_absolute_inertia_restrict_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:59.948698+00:00
-- url     : https://prove2.me/submissions/b3973506-ddcb-4469-bb2c-78bd30817c18

import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq

set_option autoImplicit false

open IsDedekindDomain

namespace NumberField

/-- Trivial restriction of absolute valuation inertia implies trivial inertia
at every finite prime of a finite Galois extension. -/
theorem _root_.solution
    (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsGalois K (AlgebraicClosure ℚ)]
    (M : IntermediateField K (AlgebraicClosure ℚ))
    [NumberField M] [Normal K M]
    (hur : ∀ (q : ℕ), q.Prime → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime q → ∀
      (σ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ),
      σ ∈ A.inertiaSubgroupIn K → σ.restrictNormal M = 1)
    (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by
  obtain ⟨A, hA⟩ := exists_valuationSubring_forall_map_mem_iff_valuation_le_one
    M (algebraMap M (AlgebraicClosure ℚ)) w
  have hcomap : A.comap (algebraMap M (AlgebraicClosure ℚ)) =
      (w.valuation M).valuationSubring := by
    ext x
    exact hA x
  have hequiv : (Valuation.comap (algebraMap M (AlgebraicClosure ℚ)) A.valuation).IsEquiv
      (w.valuation M) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change A.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1 ↔ _
    rw [A.valuation_le_one_iff]
    exact hA x
  letI : w.asIdeal.IsMaximal :=
    (inferInstance : w.asIdeal.IsPrime).isMaximal w.ne_bot
  obtain ⟨q, _, _, hqmem, hq, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
  have hqval : w.valuation M (q : M) < 1 := by
    simpa using (w.valuation_lt_one_iff_mem (K := M) (q : 𝓞 M)).mpr hqmem
  have hAq : A.LiesOverPrime q := by
    change A.valuation (q : AlgebraicClosure ℚ) < 1
    simpa using hequiv.lt_one_iff_lt_one.mpr hqval
  apply le_antisymm _ bot_le
  intro τ hτ
  have hτ' : τ ∈ ((w.valuation M).valuationSubring).inertiaSubgroupIn K := by
    rw [ValuationSubring.inertiaSubgroupIn,
      HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia K M w]
    exact hτ
  rw [← hcomap] at hτ'
  obtain ⟨σ, hσ, heq⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq M A τ hτ'
  exact Subgroup.mem_bot.mpr (heq.symm.trans (hur q hq A hAq σ hσ))

end NumberField
