-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weight_bound_implies_quotient_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:30:14.875236+00:00
-- url     : https://prove2.me/submissions/53d33142-f03d-407d-8186-4b6b46d58531

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (d : Fin (m + 1) →₀ ℕ)
    (hweight : (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    n ≤ ∑ i, d i / e i := by
  let q : ℕ := ∑ i, d i / e i
  have hscale_sum : (∑ i, ρ i * (d i : ℝ)) =
      R * ∑ i, (d i : ℝ) / (e i : ℝ) := by
    calc
      (∑ i, ρ i * (d i : ℝ)) =
          ∑ i, R * ((d i : ℝ) / (e i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hscale i]
        have heR : (0 : ℝ) < (e i : ℝ) := by exact_mod_cast he i
        field_simp [ne_of_gt heR]
      _ = R * ∑ i, (d i : ℝ) / (e i : ℝ) := by
        rw [Finset.mul_sum]
  have hratio : ((n + m : ℕ) : ℝ) ≤ ∑ i, (d i : ℝ) / (e i : ℝ) := by
    rw [hscale_sum] at hweight
    have hmul : R * ((n + m : ℕ) : ℝ) ≤
        R * ∑ i, (d i : ℝ) / (e i : ℝ) := by
      simpa [mul_comm] using hweight
    exact (mul_le_mul_iff_of_pos_left hR).mp hmul
  have hdiv : ∀ i : Fin (m + 1),
      (d i : ℝ) / (e i : ℝ) < ((d i / e i : ℕ) : ℝ) + 1 := by
    intro i
    have heR : (0 : ℝ) < (e i : ℝ) := by exact_mod_cast he i
    have hrem : d i % e i < e i := Nat.mod_lt _ (he i)
    have hremR : ((d i % e i : ℕ) : ℝ) < (e i : ℝ) := by exact_mod_cast hrem
    have hdivmod : (d i : ℝ) =
        (e i : ℝ) * ((d i / e i : ℕ) : ℝ) + ((d i % e i : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (d i) (e i)).symm
    rw [div_lt_iff₀ heR]
    rw [hdivmod]
    nlinarith
  have hsum_lt : (∑ i : Fin (m + 1), (d i : ℝ) / (e i : ℝ)) <
      ∑ i : Fin (m + 1), (((d i / e i : ℕ) : ℝ) + 1) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hdiv i).le
    · exact ⟨⟨0, Nat.zero_lt_succ m⟩, Finset.mem_univ _, hdiv ⟨0, Nat.zero_lt_succ m⟩⟩
  have hsum_cast :
      (∑ i : Fin (m + 1), (((d i / e i : ℕ) : ℝ) + 1)) =
        (q : ℝ) + ((m + 1 : ℕ) : ℝ) := by
    simp [q, Finset.sum_add_distrib, Nat.cast_sum]
  have hnltR : (n : ℝ) < (q : ℝ) + 1 := by
    rw [hsum_cast] at hsum_lt
    simp only [Nat.cast_add, Nat.cast_one] at hratio hsum_lt
    linarith
  have hnlt : n < q + 1 := by exact_mod_cast hnltR
  have hnle : n ≤ q := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hnlt)
  simpa [q] using hnle