-- Prove2me | solution 1 for GlobalTheory.newton_recursion_poly_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:28.574538+00:00
-- url     : https://prove2.me/submissions/824b056a-2ecd-4fb6-8e86-fa5de8a7a196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
import Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_top
import Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  intro m N p f r hmN hp0 hf hr hid
  have hlead : ∀ k : ℕ, ((X - C (m:ℂ)) ^ k).coeff k = 1 := fun k => by
    have h := ((monic_X_sub_C (m:ℂ)).pow k).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  set Pi : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * p k) * (X - C (m:ℂ)) ^ (N - k) with hPi
  set g : ℂ[X] := f.comp (X + 1) - f with hg
  have hpoly : (X - C (m:ℂ)) ^ (N + 1) * g - f * Pi = r := by
    apply Polynomial.funext
    intro u
    simp only [hg, hPi, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add,
      eval_one, eval_finset_sum]
    rw [← hid u]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPiN : Pi.coeff N = (m : ℂ) + 1 := by
    rw [hPi, finset_sum_coeff, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [pow_zero, one_mul, Nat.sub_zero, coeff_C_mul, hlead, hp0, mul_one, zero_add]
    · intro k hk
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_pow, natDegree_X_sub_C]
      simp at hk
      omega
  have hPideg : Pi.natDegree ≤ N := by
    rw [hPi]
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  set d := f.natDegree with hd
  have hcoef : ((X - C (m:ℂ)) ^ (N + 1) * g - f * Pi).coeff (d + N) = r.coeff (d + N) := by rw [hpoly]
  rw [coeff_sub] at hcoef
  have hr0 : r.coeff (d + N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (f * Pi).coeff (d + N) = f.coeff d * Pi.coeff N :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hPideg
  have h1 : ((X - C (m:ℂ)) ^ (N + 1) * g).coeff (d + N) = d * f.coeff d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hg0 : g = 0 := by
        ext n
        rw [coeff_zero]
        exact shiftDiffPoly_coeff_top f n (by omega)
      rw [hg0, mul_zero, coeff_zero, h0]
      simp
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hgdeg : g.natDegree ≤ e := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        exact shiftDiffPoly_coeff_top f n (by omega)
      have hidx : d + N = (N + 1) + e := by omega
      rw [hidx, coeff_mul_add_eq_of_natDegree_le (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]) hgdeg,
        hlead, one_mul, shiftDiffPoly_coeff_sub f e he, he]
      push_cast
      ring
  rw [h1, h2, hPiN, hr0] at hcoef
  have hne : (d : ℂ) - ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have h' : (d : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination h
    have := Nat.cast_injective h'
    omega
  have hc : f.coeff d = 0 := by
    have : f.coeff d * ((d : ℂ) - ((m : ℂ) + 1)) = 0 := by linear_combination hcoef
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  exact leadingCoeff_eq_zero.mp hc
end GlobalTheory
