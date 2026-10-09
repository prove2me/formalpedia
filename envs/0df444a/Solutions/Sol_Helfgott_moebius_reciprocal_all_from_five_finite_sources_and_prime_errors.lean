-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_all_from_five_finite_sources_and_prime_errors
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T03:31:33.072042+00:00
-- url     : https://prove2.me/submissions/3d80dcb9-62a3-4b4e-aaa4-8c70318d8c17

import Theorems.Thm_Helfgott_cdem_mertens4345_tail_of_finite_sources
import Theorems.Thm_Helfgott_moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail
import Theorems.Thm_Helfgott_moebius_reciprocal_point_zero_three_finite
import Theorems.Thm_Helfgott_moebius_reciprocal_high_of_prime_errors_and_tail_mertens

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem moebius_reciprocal_all_from_five_finite_sources_and_prime_errors_complete
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))

    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, (moebius d : ℝ)| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (hQhead1 : ∀ y : ℝ, 9243 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (755/10000 : ℝ)*Real.sqrt y)
    (hQhead2 : ∀ y : ℝ, 438429 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (285/10000 : ℝ)*Real.sqrt y)
    (C : ℝ) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (x : ℝ) (hx : 11815 ≤ x) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by
  have hM : ∀ k : ℕ, 10000000000000000 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ)/4345 := by
    intro k hk
    exact cdem_mertens4345_tail_of_finite_sources hU hV hHurst hQhead1 hQhead2 k hk
  by_cases hxsmall : x < 1200001
  · exact moebius_reciprocal_point_zero_three_finite x hx hxsmall
  · by_cases hxlarge : (10 ^ 28 : ℝ) ≤ x
    · exact moebius_reciprocal_high_of_prime_errors_and_tail_mertens x C
        (by norm_num at hxlarge ⊢; exact hxlarge) hC hRhigh hRmiddle hM
    · exact moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail hHurst
        (by norm_num; exact hM) x (by linarith) (le_of_not_ge hxlarge)

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution 
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))

    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, (moebius d : ℝ)| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (hQhead1 : ∀ y : ℝ, 9243 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (755/10000 : ℝ)*Real.sqrt y)
    (hQhead2 : ∀ y : ℝ, 438429 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (285/10000 : ℝ)*Real.sqrt y)
    (C : ℝ) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (x : ℝ) (hx : 11815 ≤ x) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := Helfgott.moebius_reciprocal_all_from_five_finite_sources_and_prime_errors_complete hU hV hHurst hQhead1 hQhead2 C hC hRhigh hRmiddle x hx
#print axioms solution
