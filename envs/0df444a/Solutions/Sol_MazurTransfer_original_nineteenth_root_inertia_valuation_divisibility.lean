-- Prove2me | solution 1 for MazurTransfer.original_nineteenth_root_inertia_valuation_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:44:06.473222+00:00
-- url     : https://prove2.me/submissions/d48db66b-3c1d-4f54-a596-2484ddb1275b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: away from nineteen, one original inertia-fixed nineteenth root forces all roots of the same radicand to be fixed. The complete checked official FLT inertia theorem then gives divisibility of the same original number-field prime valuation.
Named downstream consumer: genuine prime valuation divisibility for the original actual selected pi Selmer rational radicands.
-/
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
noncomputable section
open NumberField IsDedekindDomain
namespace MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityBoundary20261019
end MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: away from nineteen, inertia fixing one nineteenth root
fixes every root of the same nonzero radicand. Fixed roots at every
valuation over q force divisibility by nineteen of the number-field
prime valuation. The two arithmetic inputs are complete checked FLT proofs.
Named downstream consumer: rational power-class bounds for the actual
selected pi Selmer subspace.
-/

noncomputable section
namespace MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019
open NumberField IsDedekindDomain
local notation "F" => AlgebraicClosure ℚ

theorem not_dvd_nineteen_of_prime_ne (q : ℕ) (hq : q.Prime) (hne : q ≠ 19) : ¬ q ∣ 19 := by
  intro h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 19)).mp h with h | h
  · exact hq.ne_one h
  · exact hne h

theorem fixed_root_transfer (q : ℕ) (hq : q.Prime) (hne : q ≠ 19)
    (A : ValuationSubring F) (hA : A.LiesOverPrime q)
    (a α β : F) (ha : a ≠ 0) (hα : α ^ 19 = a) (hβ : β ^ 19 = a)
    (hfix : ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α) :
    ∀ σ : A.inertiaSubgroupIn ℚ, σ.val β = β := by
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hα
    exact ha hα.symm
  have hζ : (β / α) ^ 19 = 1 := by rw [div_pow, hβ, hα, div_self ha]
  intro σ
  have h := ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
    hq A hA σ.property (not_dvd_nineteen_of_prime_ne q hq hne) hζ
  rw [map_div₀, hfix σ] at h
  exact (div_left_inj' hα0).mp h

theorem valuation_dvd_of_all_inertia_fixed
    (L' : IntermediateField ℚ F) [NumberField L']
    (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (y : F) (hy : y ^ 19 = ((x : L') : F))
    (hfix : ∀ (A : ValuationSubring F), A.LiesOverPrime q →
      ∀ σ : A.inertiaSubgroupIn ℚ, σ.val y = y) :
    (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  by_contra hv
  obtain ⟨A, hA, σ, hσ, -, hne⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
      L' 19 (by decide) x v q hq hqv hv y hy
  exact hne (hfix A hA ⟨σ, hσ⟩)

theorem valuation_dvd_of_exists_inertia_fixed_roots
    (L' : IntermediateField ℚ F) [NumberField L']
    (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (h19 : q ≠ 19) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (y : F) (hy : y ^ 19 = ((x : L') : F))
    (hfix : ∀ (A : ValuationSubring F), A.LiesOverPrime q →
      ∃ α : F, α ≠ 0 ∧ α ^ 19 = ((x : L') : F) ∧
        ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α) :
    (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  apply valuation_dvd_of_all_inertia_fixed L' x v q hq hqv y hy
  intro A hA
  obtain ⟨α, -, hp, hα⟩ := hfix A hA
  have hx0 : ((x : L') : F) ≠ 0 :=
    (map_ne_zero (algebraMap (↥L') F)).mpr (Units.ne_zero x)
  exact fixed_root_transfer q hq h19 A hA _ α y hx0 hp hy hα

end MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019

theorem solution : (∀ (q : ℕ) (hq : q.Prime) (hne : q ≠ 19), ¬ q ∣ 19) ∧ (∀ (q : ℕ) (hq : q.Prime) (hne : q ≠ 19) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (a α β : (AlgebraicClosure ℚ)) (ha : a ≠ 0) (hα : α ^ 19 = a) (hβ : β ^ 19 = a) (hfix : ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α), ∀ σ : A.inertiaSubgroupIn ℚ, σ.val β = β) ∧ (∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (x : (L : Type)ˣ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L) ∈ v.asIdeal) (y : (AlgebraicClosure ℚ)) (hy : y ^ 19 = ((x : L) : (AlgebraicClosure ℚ))) (hfix : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q → ∀ σ : A.inertiaSubgroupIn ℚ, σ.val y = y), (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)) ∧ (∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (x : (L : Type)ˣ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ) (hq : q.Prime) (h19 : q ≠ 19) (hqv : (q : 𝓞 L) ∈ v.asIdeal) (y : (AlgebraicClosure ℚ)) (hy : y ^ 19 = ((x : L) : (AlgebraicClosure ℚ))) (hfix : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime q → ∃ α : (AlgebraicClosure ℚ), α ≠ 0 ∧ α ^ 19 = ((x : L) : (AlgebraicClosure ℚ)) ∧ ∀ σ : A.inertiaSubgroupIn ℚ, σ.val α = α), (19 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)) := by
  exact ⟨MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019.not_dvd_nineteen_of_prime_ne, MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019.fixed_root_transfer, MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019.valuation_dvd_of_all_inertia_fixed, MazurTransfer.OriginalNineteenthRootInertiaValuationDivisibilityProof20261019.valuation_dvd_of_exists_inertia_fixed_roots⟩
#print axioms solution
