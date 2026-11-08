-- Prove2me | solution 1 for KeskinZeevi.IncumbentSufficient.Jhat_linear_growth_on_goodEvent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:28:37.655565+00:00
-- url     : https://prove2.me/submissions/552ffd1b-c010-474c-a17e-929447d72443

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares

open KeskinZeevi.IncumbentSufficient in
theorem solution (M : Model) {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (κ₁ : ℝ) (t : ℕ) (ht : 3 ≤ t) (ω : Ω)
    (hii : ∑ s ∈ Finset.Icc 1 (t - 1),
        (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤ κ₁ * Real.log ((t : ℝ) - 1))
    (hA : ω ∈ goodEvent π β ε t) :
    (M.psi β ^ 2 / 8 - κ₁ * Real.log ((t : ℝ) - 1) / ((t : ℝ) - 1)) * ((t : ℝ) - 1) ≤
      Jhat π β ε t ω := by
  set a := (t - 1) / 2 with ha
  set S := Finset.Icc a (t - 1) with hS
  set p := M.psi β
  have ha1 : 1 ≤ a := by omega
  -- pointwise bound
  have hpt : ∀ s ∈ S, p ^ 2 / 4 - (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤
      dev π β ε (s + 1) ω ^ 2 := by
    intro s hs
    have h := hA s hs
    set q := M.psi (truncEst π β ε s ω)
    set x := dev π β ε (s + 1) ω
    nlinarith [sq_nonneg (p / 2 - 2 * (p - q)), sq_nonneg (2 * x - q)]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  -- the deviation sum over S is at most Jhat
  have hJ : ∑ s ∈ S, dev π β ε (s + 1) ω ^ 2 ≤ Jhat π β ε t ω := by
    unfold Jhat
    rw [← Finset.sum_image (f := fun s => dev π β ε s ω ^ 2) (s := S) (g := fun s => s + 1)
      (fun x _ y _ h => by simpa using h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      simp only [Finset.mem_image, hS, Finset.mem_Icc] at hy
      obtain ⟨s, ⟨h1, h2⟩, rfl⟩ := hy
      simp only [Finset.mem_Icc]; omega
    · intro _ _ _; exact sq_nonneg _
  -- the d-sum over S is at most the full sum
  have hD : ∑ s ∈ S, (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤
      κ₁ * Real.log ((t : ℝ) - 1) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)) hii
    intro s hs
    simp only [hS, Finset.mem_Icc] at hs ⊢; omega
  have hcard : ((t : ℝ) - 1) ≤ 2 * (S.card : ℝ) := by
    have : t - 1 ≤ 2 * S.card := by
      rw [hS, Nat.card_Icc]; omega
    have h2 : ((t - 1 : ℕ) : ℝ) ≤ ((2 * S.card : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [show 1 ≤ t by omega] at h2
    linarith
  have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (3 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hexp : (p ^ 2 / 8 - κ₁ * Real.log ((t : ℝ) - 1) / ((t : ℝ) - 1)) * ((t : ℝ) - 1) =
      p ^ 2 / 8 * ((t : ℝ) - 1) - κ₁ * Real.log ((t : ℝ) - 1) := by
    field_simp
  rw [hexp]
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg _
  nlinarith
