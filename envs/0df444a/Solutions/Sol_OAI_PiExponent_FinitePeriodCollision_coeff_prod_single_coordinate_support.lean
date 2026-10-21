-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:24:02.293313+00:00
-- url     : https://prove2.me/submissions/5e2e9f0e-d907-4445-86f8-1e7a84fd6d78

import Mathlib.Algebra.MvPolynomial.Basic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_single_coordinate_support_as_sum
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_single_coordinate_support_mem_iff
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_prod_single_coordinate_monomial_sum

open scoped BigOperators

theorem solution
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (f : σ → MvPolynomial σ R) (A : σ → ℕ)
    (hsupport : ∀ (i : σ) (s : σ →₀ ℕ), (f i).coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    (∏ i, f i).coeff (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, (f i).coeff (Finsupp.single i (A i)) := by
  classical
  let S : σ → Finset ℕ := fun i => (f i).support.image (fun s => s i)
  have hexp (i : σ) :
      f i = ∑ n ∈ S i,
        MvPolynomial.monomial (Finsupp.single i n)
          ((f i).coeff (Finsupp.single i n)) := by
    exact OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
      (f i) i (fun s hs => hsupport i s hs)
  have hprod : (∏ i, f i) = ∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n)
        ((f i).coeff (Finsupp.single i n)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hexp i
  rw [hprod]
  rw [OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
    S (fun i n => (f i).coeff (Finsupp.single i n)) A]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : A i ∈ S i
  · have hne : (f i).coeff (Finsupp.single i (A i)) ≠ 0 :=
      (OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
        (f i) i (fun s hs => hsupport i s hs) (A i)).mp hmem
    simp [hmem, hne]
  · have hz : (f i).coeff (Finsupp.single i (A i)) = 0 := by
      by_contra hne
      exact hmem ((OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
        (f i) i (fun s hs => hsupport i s hs) (A i)).mpr hne)
    simp [hmem, hz]