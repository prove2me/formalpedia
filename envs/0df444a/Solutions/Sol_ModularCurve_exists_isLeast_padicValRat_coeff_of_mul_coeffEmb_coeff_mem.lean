-- Prove2me | solution 1 for ModularCurve.exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e2fdb9b7-ab32-52f1-9b82-52f50342d0a5

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem

set_option autoImplicit false
set_option Elab.async false

open ModularCurve

theorem solution
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (g : LaurentSeries ℚ) (hg : g ≠ 0) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hcA : ∀ k : ℤ, c * (coeffEmb (AlgebraicClosure ℚ) g).coeff k ∈ A) :
    ∃ n : ℤ, (∀ k : ℤ, g.coeff k ≠ 0 → n ≤ padicValRat p (g.coeff k)) ∧
      ∃ k₀ : ℤ, g.coeff k₀ ≠ 0 ∧ padicValRat p (g.coeff k₀) = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAp : A.valuation (p : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA

  obtain ⟨B, hB⟩ := ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime hp hc
  have hBc : (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A := (hB A hA).2

  have hbound : ∀ k : ℤ, g.coeff k ≠ 0 → -(B : ℤ) ≤ padicValRat p (g.coeff k) := by
    intro k hk
    have hmem : (((p : ℚ) ^ B * g.coeff k : ℚ) : AlgebraicClosure ℚ) ∈ A := by
      have h1 := mul_mem hBc (hcA k)
      rw [coeffEmb_coeff, eq_ratCast] at h1
      have : ((p : AlgebraicClosure ℚ) ^ B * c⁻¹) * (c * (g.coeff k : AlgebraicClosure ℚ))
          = (((p : ℚ) ^ B * g.coeff k : ℚ) : AlgebraicClosure ℚ) := by
        rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
        field_simp
      rw [this] at h1
      exact h1
    have hne : (p : ℚ) ^ B * g.coeff k ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hk
    have h2 := (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hne).mp hmem
    rw [padicValRat.mul (pow_ne_zero _ hp0) hk, padicValRat.pow _, padicValRat.self hp.one_lt,
      mul_one] at h2
    linarith

  have hex : ∃ k : ℤ, g.coeff k ≠ 0 := by
    by_contra h
    apply hg
    ext k
    by_contra hk
    exact h ⟨k, hk⟩

  obtain ⟨n, ⟨k₀, hk₀, hk₀n⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun v : ℤ => ∃ k : ℤ, g.coeff k ≠ 0 ∧ padicValRat p (g.coeff k) = v)
    ⟨-(B : ℤ), fun v ⟨k, hk, hkv⟩ => hkv ▸ hbound k hk⟩
    (hex.elim fun k hk => ⟨_, k, hk, rfl⟩)
  exact ⟨n, fun k hk => hmin _ ⟨k, hk, rfl⟩, k₀, hk₀, hk₀n⟩

end S_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
end P2MW
export P2MW.S_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem (solution)
