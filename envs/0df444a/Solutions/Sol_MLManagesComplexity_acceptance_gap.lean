-- Prove2me | solution 1 for MLManagesComplexity.acceptance_gap
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T14:33:32.571456+00:00
-- url     : https://prove2.me/submissions/f5a272ab-77e1-4d8d-8862-6ce37393bcba

import Mathlib
import Definitions.Def_MLManagesComplexity_CompIndist

set_option autoImplicit false

open PPADSIS.SubexpSIS AutoregressiveCompression.Main

namespace MLManagesComplexity

theorem acceptance_gap {n : ℕ} (A : ProbCircuit) (K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (g : (Fin n → Bool) → ℝ) (D D' : PMF (Fin n → Bool))
    (hA : ∀ x : Fin n → Bool, |accept A x - g x / K| ≤ ε) :
    abs (|acceptUnder A D - acceptUnder A D'| - (1 / K) * |expectation D g - expectation D' g|)
      ≤ 2 * ε := by
  classical
  have hclose (P : PMF (Fin n → Bool)) :
      |acceptUnder A P - expectation P (fun x => g x / K)| ≤ ε := by
    have hmass : ∑ x, mass P x = 1 := by
      simp only [mass]
      calc
        _ = ∑' x, (P x).toReal := by simp
        _ = (∑' x, P x).toReal := (ENNReal.tsum_toReal_eq fun x => PMF.apply_ne_top P x).symm
        _ = 1 := by rw [PMF.tsum_coe]; norm_num
    have hmass_nonneg (x : Fin n → Bool) : 0 ≤ mass P x := ENNReal.toReal_nonneg
    have hsum :
        (∑ x, mass P x * accept A x) - (∑ x, mass P x * (g x / K)) =
          ∑ x, mass P x * (accept A x - g x / K) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    change |acceptUnder A P - expectation P (fun x => g x / K)| ≤ ε
    simp only [acceptUnder, expectation]
    rw [hsum]
    calc
      |∑ x, mass P x * (accept A x - g x / K)|
          ≤ ∑ x, |mass P x * (accept A x - g x / K)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, mass P x * |accept A x - g x / K| := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_mul, abs_of_nonneg (hmass_nonneg x)]
      _ ≤ ∑ x, mass P x * ε := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hA x) (hmass_nonneg x)
      _ = (∑ x, mass P x) * ε := by rw [Finset.sum_mul]
      _ = ε := by rw [hmass]; ring
  have hscale (P : PMF (Fin n → Bool)) :
      expectation P (fun x => g x / K) = expectation P g / K := by
    unfold expectation
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hD := hclose D
  have hD' := hclose D'
  have hscaled :
      (1 / K) * |expectation D g - expectation D' g| =
        |expectation D (fun x => g x / K) - expectation D' (fun x => g x / K)| := by
    rw [hscale D, hscale D', ← sub_div, abs_div, abs_of_pos hK]
    field_simp
  calc
    abs (|acceptUnder A D - acceptUnder A D'| - (1 / K) * |expectation D g - expectation D' g|)
        = abs (abs (acceptUnder A D - acceptUnder A D') -
            abs (expectation D (fun x => g x / K) - expectation D' (fun x => g x / K))) := by rw [hscaled]
    _ ≤ |(acceptUnder A D - acceptUnder A D') -
          (expectation D (fun x => g x / K) - expectation D' (fun x => g x / K))| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ = |(acceptUnder A D - expectation D (fun x => g x / K)) -
          (acceptUnder A D' - expectation D' (fun x => g x / K))| := by congr 1 <;> ring
    _ ≤ |acceptUnder A D - expectation D (fun x => g x / K)| +
          |acceptUnder A D' - expectation D' (fun x => g x / K)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          (acceptUnder A D - expectation D (fun x => g x / K)) 0
          (acceptUnder A D' - expectation D' (fun x => g x / K))
    _ ≤ ε + ε := add_le_add hD hD'
    _ = 2 * ε := by ring

end MLManagesComplexity

theorem solution {n : ℕ} (A : PPADSIS.SubexpSIS.ProbCircuit) (K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (g : (Fin n → Bool) → ℝ) (D D' : PMF (Fin n → Bool))
    (hA : ∀ x : Fin n → Bool, |MLManagesComplexity.accept A x - g x / K| ≤ ε) :
    abs (|MLManagesComplexity.acceptUnder A D - MLManagesComplexity.acceptUnder A D'| -
      (1 / K) * |AutoregressiveCompression.Main.expectation D g - AutoregressiveCompression.Main.expectation D' g|)
      ≤ 2 * ε := by
  exact MLManagesComplexity.acceptance_gap A K ε hK hε g D D' hA
