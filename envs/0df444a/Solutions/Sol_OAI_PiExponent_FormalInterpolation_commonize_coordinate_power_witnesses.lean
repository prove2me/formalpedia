-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.commonize_coordinate_power_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:43:31.874814+00:00
-- url     : https://prove2.me/submissions/ae0f8f0b-f715-42eb-b02d-423afce168e7

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (hcoord : ∀ i : Fin d, ∃ s n : Nat, 0 < s ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps / 2)) :
    ∃ s : Nat, 0 < s ∧ ∃ n : Fin d → Nat,
      (∀ i, 0 < n i) ∧
      (∀ i, MvPolynomial.X i ^ n i ∈ I ^ s) ∧
      (∀ i, (n i : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps / 2)) := by
  classical
  choose s n hs hn hmem hlt using hcoord
  let S : ℕ := ∏ i, s i
  have hS : 0 < S := Finset.prod_pos (fun i _ => hs i)
  have hdiv : ∀ i, s i ∣ S := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨S, hS, fun i => n i * (S / s i), fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact Nat.mul_pos (hn i) (Nat.div_pos (Nat.le_of_dvd hS (hdiv i)) (hs i))
  · have hSe : I ^ S = (I ^ s i) ^ (S / s i) := by rw [← pow_mul, Nat.mul_div_cancel' (hdiv i)]
    rw [pow_mul, hSe]
    exact Ideal.pow_mem_pow (hmem i) _
  · have hq : (0:ℝ) < ((S / s i : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hS (hdiv i)) (hs i)
    have hSe : (S : ℝ) = s i * ((S / s i : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hdiv i)).symm
    rw [hSe]; push_cast
    have := mul_lt_mul_of_pos_right (hlt i) hq
    nlinarith [this]
