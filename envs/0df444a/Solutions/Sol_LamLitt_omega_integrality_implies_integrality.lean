-- Prove2me | solution 1 for LamLitt.omega_integrality_implies_integrality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:29:05.355809+00:00
-- url     : https://prove2.me/submissions/0772b4bc-2d31-44c0-b629-e781ee7c7cd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_factorial_mul_coeff_denominator_bound
import Theorems.Thm_LamLitt_isSolutionOfAlgebraicODE_smul_rescale
import Theorems.Thm_LamLitt_omega_integrality_iff_first_coeffs
import Theorems.Thm_LamLitt_omega_integrality_implies_integrality_hurwitz
import Mathlib

set_option autoImplicit false

open PowerSeries

/-!
# Lam–Litt conjecture, implication (3) ⇒ (2): reduction of "`ω`-integral ⇒ coefficients in `ℤ[1/N]`"

Reduction of `LamLitt.omega_integrality_implies_integrality` to four lemmas:

* `LamLitt.factorial_mul_coeff_denominator_bound` : `D ^ (k + 1) * (k! * a_k) ∈ ℤ`;
* `LamLitt.isSolutionOfAlgebraicODE_smul_rescale` : `a • f(b z)` again solves an algebraic ODE;
* `LamLitt.omega_integrality_iff_first_coeffs` : `ω`-integrality for a superlinear `ω` is the
  quantifier statement "for every `m`, for all large `p`, `a_k` is `p`-integral for `k < m p`";
* `LamLitt.omega_integrality_implies_integrality_hurwitz` : the case where all `k! * a_k` are
  integers.

The only mathematics done here is the (elementary) transfer of the hypotheses to
`F(z) = D · f(D z)` and of the conclusion back from `F` to `f`.
-/

namespace LamLittAuxM2

/-- Multiplying by a natural number does not enlarge the denominator. -/
theorem den_natCast_mul_dvd (c : ℕ) (x : ℚ) : ((c : ℚ) * x).den ∣ x.den := by
  have h := Rat.mul_den_dvd (c : ℚ) x
  rwa [Rat.den_natCast, one_mul] at h

/-- Coefficients of `F(z) = D · f(D z)`. -/
theorem coeff_smul_rescale (D : ℕ) (f : PowerSeries ℚ) (k : ℕ) :
    coeff k ((D : ℚ) • rescale (D : ℚ) f) = ((D ^ (k + 1) : ℕ) : ℚ) * coeff k f := by
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul]
  push_cast
  ring

/-- If the generator `1 / N'` lies in `ℤ[1/N]` then `ℤ[1/N'] ≤ ℤ[1/N]`. -/
theorem adjoin_le_of_mem (N' N : ℕ)
    (h : (1 / (N' : ℚ)) ∈ Algebra.adjoin ℤ {(1 / (N : ℚ))}) :
    Algebra.adjoin ℤ {(1 / (N' : ℚ))} ≤ Algebra.adjoin ℤ {(1 / (N : ℚ))} :=
  Algebra.adjoin_le (Set.singleton_subset_iff.mpr h)

/-- `1 / A = B * (1 / (A * B))` puts `1 / A` inside `ℤ[1/(A B)]` for `B ≠ 0`. -/
theorem one_div_mem_adjoin_mul (A B : ℕ) (hB : B ≠ 0) :
    (1 / (A : ℚ)) ∈ Algebra.adjoin ℤ {(1 / ((A * B : ℕ) : ℚ))} := by
  have hB' : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB
  have hgen : (1 / ((A * B : ℕ) : ℚ)) ∈ Algebra.adjoin ℤ {(1 / ((A * B : ℕ) : ℚ))} :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have heq : (1 / (A : ℚ)) = (B : ℚ) * (1 / ((A * B : ℕ) : ℚ)) := by
    by_cases hA : (A : ℚ) = 0
    · simp [hA]
    · push_cast
      field_simp
  rw [heq]
  exact mul_mem (natCast_mem _ B) hgen

/-- Transfer back: if all coefficients of `F(z) = D · f(D z)` lie in `ℤ[1/N']` then all
coefficients of `f` lie in `ℤ[1/N]` for a suitable `N`. -/
theorem exists_adjoin_of_smul_rescale (D : ℕ) (hD : D ≠ 0) (f : PowerSeries ℚ) (N' : ℕ)
    (hF : ∀ k : ℕ, coeff k ((D : ℚ) • rescale (D : ℚ) f) ∈ Algebra.adjoin ℤ {(1 / (N' : ℚ))}) :
    ∃ N : ℕ, ∀ k : ℕ, coeff k f ∈ Algebra.adjoin ℤ {(1 / (N : ℚ))} := by
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  -- it suffices to find `N` with `1 / N'` and `1 / D` both in `ℤ[1/N]`
  suffices hkey : ∃ N : ℕ, (1 / (N' : ℚ)) ∈ Algebra.adjoin ℤ {(1 / (N : ℚ))} ∧
      (1 / (D : ℚ)) ∈ Algebra.adjoin ℤ {(1 / (N : ℚ))} by
    obtain ⟨N, h1, h2⟩ := hkey
    refine ⟨N, fun k => ?_⟩
    have hk : coeff k f =
        coeff k ((D : ℚ) • rescale (D : ℚ) f) * (1 / (D : ℚ)) ^ (k + 1) := by
      rw [coeff_smul_rescale]
      push_cast
      rw [one_div, inv_pow, mul_comm ((D : ℚ) ^ (k + 1)), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hD'), mul_one]
    rw [hk]
    exact mul_mem (adjoin_le_of_mem N' N h1 (hF k)) (pow_mem h2 _)
  by_cases hN' : N' = 0
  · refine ⟨D, ?_, Algebra.subset_adjoin (Set.mem_singleton _)⟩
    subst hN'
    simp
  · refine ⟨N' * D, one_div_mem_adjoin_mul N' D hD, ?_⟩
    have h := one_div_mem_adjoin_mul D N' hN'
    rwa [mul_comm D N'] at h

end LamLittAuxM2

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (ω : Nat.Primes → ℤ) (hω : omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f)) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  -- Step 1: condition (3) in quantifier form for `f`.
  have h3 : ∀ m : ℕ, ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) →
      ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (PowerSeries.coeff k f).den p :=
    (omega_integrality_iff_first_coeffs (PowerSeries.coeff · f)).mp ⟨ω, hω⟩
  -- Step 2: a geometric bound `D ^ (k + 1) * (k! * a_k) ∈ ℤ`.
  obtain ⟨D, hDpos, hD⟩ := factorial_mul_coeff_denominator_bound f g hODE
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  -- Step 3: `F(z) = D · f(D z)` solves an algebraic ODE of the same order.
  obtain ⟨g', hODE'⟩ := isSolutionOfAlgebraicODE_smul_rescale f g hODE (D : ℚ) (D : ℚ) hD0 hD0
  -- Step 4: `k! * coeff k F ∈ ℤ`.
  have hH : ∀ k : ℕ, ∃ m : ℤ, (k.factorial : ℚ) *
      PowerSeries.coeff k ((D : ℚ) • PowerSeries.rescale (D : ℚ) f) = (m : ℚ) := by
    intro k
    obtain ⟨m, hm⟩ := hD k
    refine ⟨m, ?_⟩
    rw [← hm, LamLittAuxM2.coeff_smul_rescale]
    push_cast
    ring
  -- Step 5: condition (3) is inherited by `F`, whose denominators divide those of `f`.
  have h3' : ∀ m : ℕ, ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) → ∀ k : ℕ, k < m * (p : ℕ) →
      Nat.Coprime (PowerSeries.coeff k ((D : ℚ) • PowerSeries.rescale (D : ℚ) f)).den p := by
    intro m
    obtain ⟨P₀, hP₀⟩ := h3 m
    refine ⟨P₀, fun p hp k hk => ?_⟩
    rw [LamLittAuxM2.coeff_smul_rescale]
    exact Nat.Coprime.coprime_dvd_left (LamLittAuxM2.den_natCast_mul_dvd _ _) (hP₀ p hp k hk)
  -- Step 6: the Hurwitz case applied to `F`.
  obtain ⟨N', hN'⟩ := omega_integrality_implies_integrality_hurwitz _ g' hODE' hH h3'
  -- Step 7: transfer back from `F` to `f`.
  exact LamLittAuxM2.exists_adjoin_of_smul_rescale D hDpos.ne' f N' hN'
