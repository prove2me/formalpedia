-- Prove2me | solution 1 for LogBarrierIPM.Iterations.proposition_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:06:41.291304+00:00
-- url     : https://prove2.me/submissions/63bd0d58-a9bc-4971-aee6-5c0cfcaa0e47

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_TropicalLW

set_option autoImplicit false

open LogBarrierIPM.Iterations

namespace LBI20

/-- the real coordinate `n` (0-based) of the recursion, independent of `r` -/
noncomputable def xv (lam : ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then (xPair lam (n / 2)).1 else (xPair lam (n / 2)).2

lemma xLam_eq {r : ℕ} (lam : ℝ) (k : Fin (2 * r)) : xLam r lam k = xv lam k.val := rfl

lemma xv_zero (lam : ℝ) : xv lam 0 = min lam 2 := by simp [xv, xPair]
lemma xv_one (lam : ℝ) : xv lam 1 = 1 := by simp [xv, xPair]

lemma xv_even (lam : ℝ) (i : ℕ) :
    xv lam (2 * (i + 1)) = 1 + min (xv lam (2 * i)) (xv lam (2 * i + 1)) := by
  have h1 : (2 * (i + 1)) % 2 = 0 := by omega
  have h2 : (2 * (i + 1)) / 2 = i + 1 := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  have h5 : (2 * i + 1) % 2 = 1 := by omega
  have h6 : (2 * i + 1) / 2 = i := by omega
  simp [xv, h1, h2, h3, h4, h5, h6, xPair]

lemma xv_odd (lam : ℝ) (i : ℕ) :
    xv lam (2 * (i + 1) + 1) =
      (1 - 1 / 2 ^ (i + 1)) + max (xv lam (2 * i)) (xv lam (2 * i + 1)) := by
  have h1 : (2 * (i + 1) + 1) % 2 = 1 := by omega
  have h2 : (2 * (i + 1) + 1) / 2 = i + 1 := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  have h5 : (2 * i + 1) % 2 = 1 := by omega
  have h6 : (2 * i + 1) / 2 = i := by omega
  simp [xv, h1, h2, h3, h4, h5, h6, xPair]

lemma coord_eq {r : ℕ} (x : Fin (2 * r) → WithBot ℝ) (k : ℕ) (h : 1 ≤ k ∧ k ≤ 2 * r) :
    coord x k = x ⟨k - 1, by omega⟩ := dif_pos h

lemma coord_xlam {r : ℕ} (lam : ℝ) (k : ℕ) (h : 1 ≤ k ∧ k ≤ 2 * r) :
    coord (fun k => ((xLam r lam k : ℝ) : WithBot ℝ)) k = ((xv lam (k - 1) : ℝ) : WithBot ℝ) := by
  rw [coord_eq _ k h]; rfl

end LBI20

open LBI20

theorem solution (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    IsGreatest {x | x ∈ tropicalLWSet r ∧ coord x 1 ≤ (lam : WithBot ℝ)}
      (fun k => ((xLam r lam k : ℝ) : WithBot ℝ)) := by
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [coord_xlam lam 1 ⟨le_rfl, by omega⟩]
      simp only [Nat.sub_self, xv_zero]
      exact_mod_cast min_le_right _ _
    · rw [coord_xlam lam 2 ⟨by omega, by omega⟩]
      show ((xv lam 1 : ℝ) : WithBot ℝ) ≤ _
      rw [xv_one]
    · intro j hj1 hj2
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e1 : 2 * (i + 1) + 1 - 1 = 2 * (i + 1) := by omega
      have e2 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
      have e3 : 2 * (i + 1) + 2 - 1 = 2 * (i + 1) + 1 := by omega
      have e4 : 2 * (i + 1) - 1 - 1 = 2 * i := by omega
      have c1 := coord_xlam (r := r) lam (2 * (i + 1) + 1) ⟨by omega, by omega⟩
      have c2 := coord_xlam (r := r) lam (2 * (i + 1) - 1) ⟨by omega, by omega⟩
      have c3 := coord_xlam (r := r) lam (2 * (i + 1)) ⟨by omega, by omega⟩
      have c4 := coord_xlam (r := r) lam (2 * (i + 1) + 2) ⟨by omega, by omega⟩
      rw [e1] at c1
      rw [e4] at c2
      rw [e2] at c3
      rw [e3] at c4
      rw [c1, c2, c3, c4]
      refine ⟨?_, ?_, ?_⟩
      · rw [xv_even]
        exact_mod_cast (by linarith [min_le_left (xv lam (2 * i)) (xv lam (2 * i + 1))] :
          1 + min (xv lam (2 * i)) (xv lam (2 * i + 1)) ≤ 1 + xv lam (2 * i))
      · rw [xv_even]
        exact_mod_cast (by linarith [min_le_right (xv lam (2 * i)) (xv lam (2 * i + 1))] :
          1 + min (xv lam (2 * i)) (xv lam (2 * i + 1)) ≤ 1 + xv lam (2 * i + 1))
      · rw [xv_odd]
        exact_mod_cast le_refl _
    · rw [coord_xlam lam 1 ⟨le_rfl, by omega⟩]
      simp only [Nat.sub_self, xv_zero]
      exact_mod_cast min_le_left _ _
  · rintro x ⟨⟨h1, h2, h3⟩, hl⟩
    have claim : ∀ i, i < r →
        coord x (2 * i + 1) ≤ ((xv lam (2 * i) : ℝ) : WithBot ℝ) ∧
        coord x (2 * i + 2) ≤ ((xv lam (2 * i + 1) : ℝ) : WithBot ℝ) := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · simp only [Nat.mul_zero, Nat.zero_add, xv_zero]
          have : coord x 1 ≤ ((2 : ℝ) : WithBot ℝ) := h1
          rcases le_total lam 2 with h | h
          · rw [min_eq_left h]; exact hl
          · rw [min_eq_right h]; exact this
        · simp only [Nat.mul_zero, Nat.zero_add, xv_one]
          exact h2
      | succ i ih =>
        intro hi
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨a1, a2, a3⟩ := h3 (i + 1) (by omega) hi
        have e2 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
        have a1' : coord x (2 * (i + 1) + 1) ≤ ((1 : ℝ) : WithBot ℝ) + coord x (2 * i + 1) := by
          rw [e2] at a1; exact a1
        have a2' : coord x (2 * (i + 1) + 1) ≤ ((1 : ℝ) : WithBot ℝ) + coord x (2 * i + 2) := a2
        have a3' : coord x (2 * (i + 1) + 2) ≤ ((1 - 1 / 2 ^ (i + 1) : ℝ) : WithBot ℝ) +
            max (coord x (2 * i + 1)) (coord x (2 * i + 2)) := by
          rw [e2] at a3; exact a3
        refine ⟨?_, ?_⟩
        · rw [xv_even]
          rcases le_total (xv lam (2 * i)) (xv lam (2 * i + 1)) with h | h
          · rw [min_eq_left h]
            refine a1'.trans ?_
            have := add_le_add (le_refl ((1 : ℝ) : WithBot ℝ)) ih1
            exact_mod_cast this
          · rw [min_eq_right h]
            refine a2'.trans ?_
            have := add_le_add (le_refl ((1 : ℝ) : WithBot ℝ)) ih2
            exact_mod_cast this
        · rw [xv_odd]
          have hm : max (coord x (2 * i + 1)) (coord x (2 * i + 2)) ≤
              (((max (xv lam (2 * i)) (xv lam (2 * i + 1)) : ℝ)) : WithBot ℝ) :=
            max_le (ih1.trans (by exact_mod_cast le_max_left _ _))
              (ih2.trans (by exact_mod_cast le_max_right _ _))
          refine a3'.trans ?_
          have := add_le_add (le_refl (((1 - 1 / 2 ^ (i + 1) : ℝ)) : WithBot ℝ)) hm
          exact_mod_cast this
    intro k
    obtain ⟨n, hn⟩ := k
    have hi : n / 2 < r := by omega
    obtain ⟨c1, c2⟩ := claim (n / 2) hi
    show x ⟨n, hn⟩ ≤ ((xv lam n : ℝ) : WithBot ℝ)
    have e : coord x (n + 1) = x ⟨n, hn⟩ := coord_eq x (n + 1) ⟨by omega, by omega⟩
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hn2 : 2 * (n / 2) = n := by omega
      rw [hn2, e] at c1
      exact c1
    · have hn2 : 2 * (n / 2) + 1 = n := by omega
      have hn3 : 2 * (n / 2) + 2 = n + 1 := by omega
      rw [hn2, hn3, e] at c2
      exact c2
