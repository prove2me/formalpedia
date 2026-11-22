-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreSource_not_polyExact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:39.694517+00:00
-- url     : https://prove2.me/submissions/a1621113-6bbc-4e7a-be84-5587206bd1d6

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FP3NotPolyExact

open MvPolynomial HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

private abbrev R4 := MvPolynomial (Fin 4) ℂ
private abbrev Exps := ℕ × ℕ × ℕ × ℕ

private def toFS (e : Exps) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![e.1, e.2.1, e.2.2.1, e.2.2.2]

private lemma toFS_apply_0 (a b c d : ℕ) : toFS (a, b, c, d) 0 = a := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 0 = a
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

private lemma toFS_apply_1 (a b c d : ℕ) : toFS (a, b, c, d) 1 = b := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 1 = b
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

private lemma toFS_apply_2 (a b c d : ℕ) : toFS (a, b, c, d) 2 = c := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 2 = c
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

private lemma toFS_apply_3 (a b c d : ℕ) : toFS (a, b, c, d) 3 = d := by
  change (Finsupp.equivFunOnFinite (toFS (a, b, c, d))) 3 = d
  unfold toFS; rw [Equiv.apply_symm_apply]; rfl

private lemma eq_toFS (s : Fin 4 →₀ ℕ) : s = toFS (s 0, s 1, s 2, s 3) := by
  ext i
  fin_cases i
  · exact (toFS_apply_0 _ _ _ _).symm
  · exact (toFS_apply_1 _ _ _ _).symm
  · exact (toFS_apply_2 _ _ _ _).symm
  · exact (toFS_apply_3 _ _ _ _).symm

private def monP (a b c d : ℕ) : R4 := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

private lemma monP_eq_monomial (a b c d : ℕ) : monP a b c d = monomial (toFS (a, b, c, d)) 1 := by
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_four, toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3]
  rfl

private lemma coeff_3030_monP_zero (a b c d : ℕ) (hne : ¬ (a = 3 ∧ b = 0 ∧ c = 3 ∧ d = 0)) :
    coeff (toFS (3, 0, 3, 0)) (monP a b c d) = 0 := by
  rw [monP_eq_monomial, coeff_monomial]
  split_ifs with h
  · exfalso
    have k0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) h
    have k1 := congrArg (fun f : Fin 4 →₀ ℕ => f 1) h
    have k2 := congrArg (fun f : Fin 4 →₀ ℕ => f 2) h
    have k3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) h
    simp only [toFS_apply_0, toFS_apply_1, toFS_apply_2, toFS_apply_3] at k0 k1 k2 k3
    exact hne ⟨k0, k1, k2, k3⟩
  · rfl

private lemma coeff_3030_two_source :
    coeff (toFS (3, 0, 3, 0)) (2 * coreSource) = 2 := by
  have hcs : (2 : R4) * coreSource = C 2 * monP 3 0 3 0 := by
    unfold coreSource monP
    rw [← map_ofNat C 2]
    simp only [pow_zero, mul_one]
  rw [hcs, monP_eq_monomial, C_mul_monomial, mul_one, coeff_monomial, if_pos rfl]

private lemma hom_one_eq_linear {P : R4} (hP : P.IsHomogeneous 1) :
    ∃ c0 c1 c2 c3 : ℂ, P = C c0 * X 0 + C c1 * X 1 + C c2 * X 2 + C c3 * X 3 := by
  refine ⟨coeff (toFS (1, 0, 0, 0)) P, coeff (toFS (0, 1, 0, 0)) P,
    coeff (toFS (0, 0, 1, 0)) P, coeff (toFS (0, 0, 0, 1)) P, ?_⟩
  have hX0 : C (coeff (toFS (1, 0, 0, 0)) P) * X 0 =
      monomial (toFS (1, 0, 0, 0)) (coeff (toFS (1, 0, 0, 0)) P) := by
    rw [← mul_one (coeff _ P), ← C_mul_monomial, ← monP_eq_monomial]
    simp [monP]
  have hX1 : C (coeff (toFS (0, 1, 0, 0)) P) * X 1 =
      monomial (toFS (0, 1, 0, 0)) (coeff (toFS (0, 1, 0, 0)) P) := by
    rw [← mul_one (coeff _ P), ← C_mul_monomial, ← monP_eq_monomial]
    simp [monP]
  have hX2 : C (coeff (toFS (0, 0, 1, 0)) P) * X 2 =
      monomial (toFS (0, 0, 1, 0)) (coeff (toFS (0, 0, 1, 0)) P) := by
    rw [← mul_one (coeff _ P), ← C_mul_monomial, ← monP_eq_monomial]
    simp [monP]
  have hX3 : C (coeff (toFS (0, 0, 0, 1)) P) * X 3 =
      monomial (toFS (0, 0, 0, 1)) (coeff (toFS (0, 0, 0, 1)) P) := by
    rw [← mul_one (coeff _ P), ← C_mul_monomial, ← monP_eq_monomial]
    simp [monP]
  rw [hX0, hX1, hX2, hX3]
  ext m
  simp only [coeff_add, coeff_monomial]
  by_cases hm : m ∈ P.support
  · have hdeg : m 0 + m 1 + m 2 + m 3 = 1 := by
      have h := hP (mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
    have hcases : (m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0) ∨
        (m 0 = 0 ∧ m 1 = 1 ∧ m 2 = 0 ∧ m 3 = 0) ∨
        (m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 1 ∧ m 3 = 0) ∨
        (m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 1) := by omega
    have hneq01 : toFS (1, 0, 0, 0) ≠ toFS (0, 1, 0, 0) := by
      intro h; have k := congrArg (fun f => f 0) h; simp [toFS_apply_0] at k
    have hneq02 : toFS (1, 0, 0, 0) ≠ toFS (0, 0, 1, 0) := by
      intro h; have k := congrArg (fun f => f 0) h; simp [toFS_apply_0] at k
    have hneq03 : toFS (1, 0, 0, 0) ≠ toFS (0, 0, 0, 1) := by
      intro h; have k := congrArg (fun f => f 0) h; simp [toFS_apply_0] at k
    have hneq12 : toFS (0, 1, 0, 0) ≠ toFS (0, 0, 1, 0) := by
      intro h; have k := congrArg (fun f => f 1) h; simp [toFS_apply_1] at k
    have hneq13 : toFS (0, 1, 0, 0) ≠ toFS (0, 0, 0, 1) := by
      intro h; have k := congrArg (fun f => f 1) h; simp [toFS_apply_1] at k
    have hneq23 : toFS (0, 0, 1, 0) ≠ toFS (0, 0, 0, 1) := by
      intro h; have k := congrArg (fun f => f 2) h; simp [toFS_apply_2] at k
    rcases hcases with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · have hm_eq : m = toFS (1, 0, 0, 0) := by rw [eq_toFS m, h0, h1, h2, h3]
      rw [hm_eq, if_pos rfl, if_neg hneq01.symm, if_neg hneq02.symm, if_neg hneq03.symm]; ring
    · have hm_eq : m = toFS (0, 1, 0, 0) := by rw [eq_toFS m, h0, h1, h2, h3]
      rw [hm_eq, if_neg hneq01, if_pos rfl, if_neg hneq12.symm, if_neg hneq13.symm]; ring
    · have hm_eq : m = toFS (0, 0, 1, 0) := by rw [eq_toFS m, h0, h1, h2, h3]
      rw [hm_eq, if_neg hneq02, if_neg hneq12, if_pos rfl, if_neg hneq23.symm]; ring
    · have hm_eq : m = toFS (0, 0, 0, 1) := by rw [eq_toFS m, h0, h1, h2, h3]
      rw [hm_eq, if_neg hneq03, if_neg hneq13, if_neg hneq23, if_pos rfl]; ring
  · have hz : ∀ e : Exps, (if toFS e = m then coeff (toFS e) P else 0) = 0 := by
      intro e
      split_ifs with he
      · subst he; exact notMem_support_iff.mp hm
      · rfl
    rw [notMem_support_iff.mp hm, hz (1, 0, 0, 0), hz (0, 1, 0, 0), hz (0, 0, 1, 0), hz (0, 0, 0, 1)]
    ring

private lemma pderiv_X_pow_succ (i j : Fin 4) : ∀ n : ℕ,
    pderiv i (X j ^ (n + 1) : R4) = if j = i then ((n + 1 : ℕ) : R4) * X j ^ n else 0
  | 0 => by
      simp only [zero_add, pow_one, pow_zero, Nat.cast_one, one_mul, pderiv_X]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
  | n + 1 => by
      rw [pow_succ _ (n + 1), pderiv_mul, pderiv_X_pow_succ i j n, pderiv_X]
      by_cases hji : j = i
      · subst hji; simp; ring
      · simp [hji]

private lemma core_eq_monP : core =
    monP 6 0 0 0 + C (5 / 7 : ℂ) * monP 5 1 0 0 + C (5 / 7 : ℂ) * monP 3 1 1 1 +
      C (10 / 7 : ℂ) * monP 1 5 0 0 + C (10 / 7 : ℂ) * monP 1 1 3 1 + monP 0 6 0 0 +
      monP 0 0 6 0 + C (5 / 7 : ℂ) * monP 0 0 5 1 + C (15 / 7 : ℂ) * monP 0 0 1 5 +
      monP 0 0 0 6 := by
  apply MvPolynomial.funext; intro x
  simp only [core, monP, map_add, map_mul, map_pow, eval_C, eval_X]
  ring

private lemma pd0_core_eq : pderiv 0 core =
    C 6 * monP 5 0 0 0 + C (25 / 7 : ℂ) * monP 4 1 0 0 + C (15 / 7 : ℂ) * monP 2 1 1 1 +
      C (10 / 7 : ℂ) * monP 0 5 0 0 + C (10 / 7 : ℂ) * monP 0 1 3 1 := by
  unfold core monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_C, eval_X]
  ring

private lemma pd1_core_eq : pderiv 1 core =
    C (5 / 7 : ℂ) * monP 5 0 0 0 + C (5 / 7 : ℂ) * monP 3 0 1 1 + C (50 / 7 : ℂ) * monP 1 4 0 0 +
      C (10 / 7 : ℂ) * monP 1 0 3 1 + C 6 * monP 0 5 0 0 := by
  unfold core monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_C, eval_X]
  ring

private lemma pd2_core_eq : pderiv 2 core =
    C (5 / 7 : ℂ) * monP 3 1 0 1 + C (30 / 7 : ℂ) * monP 1 1 2 1 + C 6 * monP 0 0 5 0 +
      C (25 / 7 : ℂ) * monP 0 0 4 1 + C (15 / 7 : ℂ) * monP 0 0 0 5 := by
  unfold core monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_C, eval_X]
  ring

private lemma pd3_core_eq : pderiv 3 core =
    C (5 / 7 : ℂ) * monP 3 1 1 0 + C (10 / 7 : ℂ) * monP 1 1 3 0 + C (5 / 7 : ℂ) * monP 0 0 5 0 +
      C (75 / 7 : ℂ) * monP 0 0 1 4 + C 6 * monP 0 0 0 5 := by
  unfold core monP
  simp only [pow_zero, mul_one, one_mul, pow_one,
    show ∀ j : Fin 4, (X j : R4) ^ 6 = X j ^ (5 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 5 = X j ^ (4 + 1) from fun _ => rfl,
    show ∀ j : Fin 4, (X j : R4) ^ 3 = X j ^ (2 + 1) from fun _ => rfl,
    map_add, pderiv_mul, pderiv_C, pderiv_X_pow_succ, pderiv_X]
  simp
  apply MvPolynomial.funext; intro x
  simp only [map_add, map_mul, map_pow, map_ofNat, eval_C, eval_X]
  ring

private lemma coeff_3030_mul_X0_zero (a b c d : ℕ) (h : ¬ (a + 1 = 3 ∧ b = 0 ∧ c = 3 ∧ d = 0)) :
    coeff (toFS (3, 0, 3, 0)) (monP a b c d * X 0) = 0 := by
  have heq : monP a b c d * X 0 = monP (a + 1) b c d := by unfold monP; ring
  rw [heq]; exact coeff_3030_monP_zero _ _ _ _ h

private lemma coeff_3030_mul_X1_zero (a b c d : ℕ) :
    coeff (toFS (3, 0, 3, 0)) (monP a b c d * X 1) = 0 := by
  have heq : monP a b c d * X 1 = monP a (b + 1) c d := by unfold monP; ring
  rw [heq]; exact coeff_3030_monP_zero _ _ _ _ (by omega)

private lemma coeff_3030_mul_X2_zero (a b c d : ℕ) (h : ¬ (a = 3 ∧ b = 0 ∧ c + 1 = 3 ∧ d = 0)) :
    coeff (toFS (3, 0, 3, 0)) (monP a b c d * X 2) = 0 := by
  have heq : monP a b c d * X 2 = monP a b (c + 1) d := by unfold monP; ring
  rw [heq]; exact coeff_3030_monP_zero _ _ _ _ h

private lemma coeff_3030_mul_X3_zero (a b c d : ℕ) :
    coeff (toFS (3, 0, 3, 0)) (monP a b c d * X 3) = 0 := by
  have heq : monP a b c d * X 3 = monP a b c (d + 1) := by unfold monP; ring
  rw [heq]; exact coeff_3030_monP_zero _ _ _ _ (by omega)

private lemma coeff_3030_core_zero : coeff (toFS (3, 0, 3, 0)) core = 0 := by
  rw [core_eq_monP]
  simp only [coeff_add, coeff_C_mul]
  repeat rw [coeff_3030_monP_zero _ _ _ _ (by omega)]
  ring

private lemma pderiv_linear_eq_C (i : Fin 4) (c0 c1 c2 c3 : ℂ) :
    pderiv i (C c0 * X 0 + C c1 * X 1 + C c2 * X 2 + C c3 * X 3 : R4) =
      C (if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else c3) := by
  fin_cases i <;> simp [map_add, pderiv_X]

theorem coeff_3030_polyExact_zero (L : Fin 4 → R4) (hL : ∀ i, (L i).IsHomogeneous 1) :
    coeff (toFS (3, 0, 3, 0))
      (2 * (∑ i, pderiv i core * L i) - 3 * core * (∑ i, pderiv i (L i))) = 0 := by
  obtain ⟨a0, a1, a2, a3, h0⟩ := hom_one_eq_linear (hL 0)
  obtain ⟨b0, b1, b2, b3, h1⟩ := hom_one_eq_linear (hL 1)
  obtain ⟨c0, c1, c2, c3, h2⟩ := hom_one_eq_linear (hL 2)
  obtain ⟨d0, d1, d2, d3, h3⟩ := hom_one_eq_linear (hL 3)
  simp only [Fin.sum_univ_four, h0, h1, h2, h3, pderiv_linear_eq_C]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  have hexp : 2 * (pderiv 0 core * (C a0 * X 0 + C a1 * X 1 + C a2 * X 2 + C a3 * X 3) +
        pderiv 1 core * (C b0 * X 0 + C b1 * X 1 + C b2 * X 2 + C b3 * X 3) +
        pderiv 2 core * (C c0 * X 0 + C c1 * X 1 + C c2 * X 2 + C c3 * X 3) +
        pderiv 3 core * (C d0 * X 0 + C d1 * X 1 + C d2 * X 2 + C d3 * X 3)) -
      3 * core * (C a0 + C b1 + C c2 + C d3) =
      C (2 * a0) * (pderiv 0 core * X 0) + C (2 * a1) * (pderiv 0 core * X 1) +
      C (2 * a2) * (pderiv 0 core * X 2) + C (2 * a3) * (pderiv 0 core * X 3) +
      C (2 * b0) * (pderiv 1 core * X 0) + C (2 * b1) * (pderiv 1 core * X 1) +
      C (2 * b2) * (pderiv 1 core * X 2) + C (2 * b3) * (pderiv 1 core * X 3) +
      C (2 * c0) * (pderiv 2 core * X 0) + C (2 * c1) * (pderiv 2 core * X 1) +
      C (2 * c2) * (pderiv 2 core * X 2) + C (2 * c3) * (pderiv 2 core * X 3) +
      C (2 * d0) * (pderiv 3 core * X 0) + C (2 * d1) * (pderiv 3 core * X 1) +
      C (2 * d2) * (pderiv 3 core * X 2) + C (2 * d3) * (pderiv 3 core * X 3) -
      C (3 * (a0 + b1 + c2 + d3)) * core := by
    simp only [← map_ofNat C 2, ← map_ofNat C 3, map_mul, map_add]; ring
  rw [hexp, pd0_core_eq, pd1_core_eq, pd2_core_eq, pd3_core_eq]
  simp only [add_mul, mul_assoc, coeff_sub, coeff_add, coeff_C_mul,
    coeff_3030_mul_X1_zero, coeff_3030_mul_X3_zero, coeff_3030_core_zero]
  repeat rw [coeff_3030_mul_X0_zero _ _ _ _ (by omega)]
  repeat rw [coeff_3030_mul_X2_zero _ _ _ _ (by omega)]
  ring

end FP3NotPolyExact

theorem solution :
    (∀ S : MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.PolyExactCoreSource S ↔
        ∃ L : Fin 4 → MvPolynomial (Fin 4) ℂ,
          (∀ i, (L i).IsHomogeneous 1) ∧
            HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S 1 L) ∧
    ¬ HodgeComputer.FourPlusTwoResidual.PolyExactCoreSource
        HodgeComputer.FourPlusTwoResidual.coreSource := by
  open MvPolynomial HodgeComputer.FourPlusTwoResidual in
  refine ⟨?_, ?_⟩
  · intro S
    constructor
    · rintro ⟨L, hL, hS⟩
      refine ⟨L, hL, ⟨one_ne_zero, ⟨0, isHomogeneous_one (Fin 4) ℂ, ?_⟩, ?_⟩⟩
      · intro i; simpa using hL i
      · unfold coreResidual
        have hp1 : ∀ i : Fin 4, pderiv i (1 : MvPolynomial (Fin 4) ℂ) = 0 := fun i => by simp
        simp only [one_pow, mul_one, one_mul, hp1, zero_mul, Finset.sum_const_zero, sub_zero]
        linear_combination hS
    · rintro ⟨L, hL, ⟨-, -, hres⟩⟩
      refine ⟨L, hL, ?_⟩
      unfold coreResidual at hres
      have hp1 : ∀ i : Fin 4, pderiv i (1 : MvPolynomial (Fin 4) ℂ) = 0 := fun i => by simp
      simp only [one_pow, mul_one, one_mul, hp1, zero_mul, Finset.sum_const_zero, sub_zero] at hres
      linear_combination hres
  · rintro ⟨L, hL, hS⟩
    have hc := congrArg (coeff (FP3NotPolyExact.toFS (3, 0, 3, 0))) hS
    rw [FP3NotPolyExact.coeff_3030_two_source,
      FP3NotPolyExact.coeff_3030_polyExact_zero L hL] at hc
    norm_num at hc
