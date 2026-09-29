-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems7_8_equiv
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:05:25.442926+00:00
-- url     : https://prove2.me/submissions/59b8ac72-5694-446d-8c40-16e8180a2e22

import Definitions.Def_MurtyKabadi_Reduction_Construction

open MurtyKabadi.Reduction

private lemma f2_eq_f4_on_P {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (d0 δ : ℕ) (y s : Fin n → ℝ) (hp : (y, s) ∈ P n) :
    f2 d d0 δ y s = f4 d d0 δ y s := by
  have hsum : (∑ j, (y j + s j)) = (n : ℝ) := hp.2.2
  have hsq : (∑ j, (y j + s j - 1) ^ 2) =
      (∑ j, (y j + s j) ^ 2) - (n : ℝ) := by
    calc
      _ = ∑ j, ((y j + s j) ^ 2 - 2 * (y j + s j) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j, (y j + s j) ^ 2) - 2 * (∑ j, (y j + s j)) + (n : ℝ) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum]; ring
  have hcorr : (∑ j, (d j : ℝ) * y j * (1 - y j)) =
      (∑ j, (d j : ℝ) * y j) - ∑ j, (d j : ℝ) * y j ^ 2 := by
    calc
      _ = ∑ j, ((d j : ℝ) * y j - (d j : ℝ) * y j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold f2 f1 f4
  rw [hsq, hcorr, hsum]
  field_simp [hn0]
  ring

theorem solution {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    (∃ p ∈ P n, f2 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f4 d d0 δ p.1 p.2 ≤ 0 := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    exact ⟨p, hp, (f2_eq_f4_on_P hn d d0 δ p.1 p.2 hp) ▸ hfp⟩
  · rintro ⟨p, hp, hfp⟩
    exact ⟨p, hp, (f2_eq_f4_on_P hn d d0 δ p.1 p.2 hp).symm ▸ hfp⟩
