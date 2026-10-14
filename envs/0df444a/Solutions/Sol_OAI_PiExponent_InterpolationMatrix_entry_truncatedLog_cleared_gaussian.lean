-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.entry_truncatedLog_cleared_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:48:31.658219+00:00
-- url     : https://prove2.me/submissions/643ea42c-eb36-4a8b-9440-b65e0ab348b3

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Theorems.Thm_OAI_PiExponent_Arithmetic_shifted_truncation_product_coeff_gaussian

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

omit [DecidableEq σ] in
@[simp] theorem multiIndex_apply (a : σ → ℕ) (i : σ) : multiIndex a i = a i := by
  simp [multiIndex]

omit [Fintype σ] [DecidableEq σ] in
theorem shifted_X_pow (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem shifted_product_expansion (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_X_pow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator]
  rw [hidx]

omit [DecidableEq σ] in
theorem shift_monomial_one (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

theorem shiftCoefficient_eq (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial_one, shifted_product_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by ext i; simp [b₀]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]

end FiniteExpansion

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by
  simp [exponentVector]

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

theorem entry_eq_binomial_product {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) :
    entry r G j s β h α =
      (∏ i, ((α i).choose (β i) : ℂ)) *
        (((1 + Polynomial.X) ^ h * ∏ i,
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)).coeff s) := by
  classical
  have hexp := RowTranslation.shiftCoefficient_eq
    (fun i => Polynomial.C ((j : ℂ) * r i) + G i)
    (exponentVector β) (exponentVector α)
  rw [RowTranslation.shiftCoefficient, RowTranslation.shift_monomial_one] at hexp
  simp only [exponentVector_apply] at hexp
  have hp : (monomialImage r G j h α).coeff (exponentVector β) =
      (1 + Polynomial.X) ^ h * ∏ i,
        ((α i).choose (β i) : Polynomial ℂ) *
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i) := by
    rw [monomialImage, MvPolynomial.coeff_C_mul]
    simpa only [add_comm] using congrArg (fun x => (1 + Polynomial.X) ^ h * x) hexp
  rw [entry, hp, Finset.prod_mul_distrib]
  have hc : (∏ i, ((α i).choose (β i) : Polynomial ℂ)) =
      Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) := by simp
  rw [hc]
  rw [show (1 + Polynomial.X) ^ h *
      (Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) *
        ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) =
      Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) *
        ((1 + Polynomial.X) ^ h *
          ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) by ring]
  rw [Polynomial.coeff_C_mul]

theorem entry_eq_zero_of_not_le {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) (hβα : ¬ ∀ i, β i ≤ α i) :
    entry r G j s β h α = 0 := by
  classical
  push Not at hβα
  obtain ⟨i, hi⟩ := hβα
  rw [entry_eq_binomial_product]
  have hprod : (∏ k, ((α k).choose (β k) : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  rw [hprod, zero_mul]

theorem scalar_product_mul_coeff {m : ℕ} (q : Fin m → ℂ)
    (d : Fin m → ℕ) (P : Polynomial ℂ) (F : Fin m → Polynomial ℂ) (s : ℕ) :
    (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i).coeff s =
      (P * ∏ i, (Polynomial.C (q i) * F i) ^ d i).coeff s := by
  have he : P * ∏ i, (Polynomial.C (q i) * F i) ^ d i =
      Polynomial.C (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    ring
  rw [he, Polynomial.coeff_C_mul]

theorem gaussian_center_cast (j : ℕ) (p : ℤ) :
    (((⟨0, 2 * (j : ℤ) * p⟩ : GaussianInt) : ℂ)) =
      (j : ℂ) * (2 * Complex.I * (p : ℂ)) := by
  simp only [GaussianInt.toComplex_def', Int.cast_zero, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, zero_add]
  ring

end OAI.PiExponent.InterpolationMatrix

open OAI.PiExponent OAI.PiExponent.InterpolationMatrix
open scoped BigOperators

theorem solution {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h α ∈ GaussianInt.toComplex.range := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβα, mul_zero]
    exact GaussianInt.toComplex.range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβα i)).symm
  let z : Fin m → GaussianInt := fun i => ⟨0, 2 * (j : ℤ) * p i⟩
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * (2 * Complex.I * (p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    rw [show (z i : ℂ) = (j : ℂ) * (2 * Complex.I * (p i : ℂ)) from
      gaussian_center_cast j (p i)]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_gaussian Finset.univ
    T q e (fun i => α i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (α i) (β i)).trans (hα i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial GaussianInt).map GaussianInt.toComplex) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((α i).choose (β i) : ℂ)) ∈ GaussianInt.toComplex.range := by
    apply GaussianInt.toComplex.range.prod_mem
    intro i hi
    exact ⟨((α i).choose (β i) : GaussianInt), by simp⟩
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => α i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * (2 * Complex.I * (p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  have he := GaussianInt.toComplex.range.mul_mem hchoose hclear
  rw [← hscalar] at he
  convert he using 1
  ring
