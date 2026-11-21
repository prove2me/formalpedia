-- Prove2me | solution 1 for MasulloRH.critical_line_mass_prime_comparison_through_359
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:19:38.641181+00:00
-- url     : https://prove2.me/submissions/b53de364-c59b-4128-9e12-30893fb16e90

-- Extend the verified finite-height witness by bounding the prime tail beyond the new cutoff.
import Theorems.Thm_MasulloRH_critical_line_mass_prime_comparison_through_331
import Theorems.Thm_MasulloRH_certified_prime_tail_from_359
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
theorem solution :
    let a := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ 199997/2) ∧ (∀ z ∈ F, z.val.re = 1/2) ∧
      let M := ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
      |C + (∑' j, a j) - M| ≤ 7/80000 ∧
      ∀ N : ℕ, N ≤ 359 → C + (∑ j ∈ Finset.range N, a j) ≤ M := by
  classical
  dsimp only
  let C := Real.log 2/2 + Real.pi/4-37/30
  let f (j : ℕ) := ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ)
  have hpos (j : ℕ) : 0 ≤ f j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [f]
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  obtain ⟨F,hFc,hon,herr,_⟩ := critical_line_mass_prime_comparison_through_331
  refine ⟨F,hFc,hon,herr,?_⟩
  intro N hN
  obtain ⟨P,hP,hval⟩ := certified_prime_tail_from_359
  have hdis : Disjoint (Finset.range N) P := Finset.disjoint_left.mpr
    (fun j hj h => (Nat.not_lt_of_ge (hN.trans (hP j h).2.1)) (Finset.mem_range.mp hj))
  have hpN : (∑ j ∈ Finset.range N,f j)+(∑ j ∈ P,f j) ≤ ∑' j,f j := by
    rw [←Finset.sum_union hdis]
    exact regularized_reference_mass_prime_series.summable.sum_le_tsum _ (fun j _ => hpos j)
  change (87592/1000000000:ℝ) ≤ ∑ j ∈ P,f j at hval
  change |C + (∑' j,f j) - _| ≤ (7/80000:ℝ) at herr
  change C + (∑ j ∈ Finset.range N,f j) ≤ _
  linarith only [hpN,hval,(abs_le.mp herr).2]
