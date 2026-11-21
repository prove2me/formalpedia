-- Prove2me | solution 1 for MasulloRH.finite_prime_comparison_iff_cofinal_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:41:05.488186+00:00
-- url     : https://prove2.me/submissions/ca910017-ba37-474c-b03c-221f8b099e55

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_prime_tail_reserve_to_four_mul
import Mathlib
open ArithmeticFunction MasulloRH Finset

theorem solution :
    let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
      ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
    let M := fun F : Finset (ZetaZerosInTraceStrip (1/2)) =>
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    (∀ N, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F) ↔
    (∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F + 1/((k:ℝ)+1)) := by
  classical
  dsimp only
  let a := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
  have hpos (j : ℕ) : 0 ≤ a j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [a]
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have h0 : 0 < (j:ℝ) := by linarith
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left (vonMangoldt_nonneg (n:=j)) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  constructor
  · intro hall k
    obtain ⟨F,hF,h⟩ := hall k
    exact ⟨k,le_rfl,F,hF,le_trans h (le_add_of_nonneg_right (by positivity))⟩
  · intro happ N
    let X := max N 196
    have hx : 196 ≤ X := le_max_right _ _
    have hNX : N ≤ X := le_max_left _ _
    let D := 128*(X:ℝ)^(3/2:ℝ)
    have hx0 : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hd : 0 < D := by dsimp [D]; positivity
    let k := max (4*X+1) ⌈D⌉₊
    obtain ⟨L,hL,F,hF,ha⟩ := happ k
    refine ⟨F,hF,?_⟩
    have hk : 4*X+1 ≤ k := le_max_left _ _
    have hk' : ⌈D⌉₊ ≤ k := le_max_right _ _
    have hd' : D ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk')
    have he : 1/((k:ℝ)+1) ≤ 1/D := one_div_le_one_div_of_le hd (by linarith)
    have hr : 1/D ≤ ∑ j ∈ Ioc X (4*X), a j := prime_tail_reserve_to_four_mul X hx
    have hdis : Disjoint (range N) (Ioc X (4*X)) := by
      apply disjoint_left.mpr
      intro j hj hj'
      have := mem_range.mp hj
      have := (mem_Ioc.mp hj').1
      omega
    have hsub : range N ∪ Ioc X (4*X) ⊆ range L := by
      intro j hj
      apply mem_range.mpr
      rcases mem_union.mp hj with h | h
      · have := mem_range.mp h; omega
      · have := (mem_Ioc.mp h).2; omega
    have htot := sum_le_sum_of_subset_of_nonneg (f:=a) hsub (fun j _ _ => hpos j)
    rw [sum_union hdis] at htot
    change _ + (∑ j ∈ range L, a j) ≤ _ at ha
    change _ + (∑ j ∈ range N, a j) ≤ _
    linarith only [ha,htot,he,hr]
