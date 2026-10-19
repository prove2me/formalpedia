-- Prove2me | solution 1 for GreenTao.bounded_model_for_progression_counts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T20:55:32.163145+00:00
-- url     : https://prove2.me/submissions/4a789edc-47a9-4535-be9f-4e145873ea6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GreenTao_gowers_uniform_decomposition
import Theorems.Thm_GreenTao_generalized_von_neumann
import Theorems.Thm_GreenTao_bounded_model_of_mixed_estimates
import Mathlib

open Filter GreenTao

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∃ g : ZMod (M n : ℕ) → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      GreenTao.avg (f n) - η ≤ GreenTao.avg g ∧
      GreenTao.apAvg k g - η ≤ GreenTao.apAvg k (f n) := by
  classical
  let ε : ℝ := min 1 (η / 4)
  let ξ : ℝ := η / (2 * (2 : ℝ) ^ k)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / 4 := min_le_right _ _
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  obtain ⟨ρ, hρ, hcount⟩ := generalized_von_neumann k hk M hprime hM ν hν ξ hξ
  have hstructure := gowers_uniform_decomposition k hk M hprime hM ν f hν hf ε ρ hε hρ
  filter_upwards [hstructure, hcount] with n hn hc
  obtain ⟨s, u, hs, hsu, hmean, huniform⟩ := hn
  have hsbound (x) : |s x| ≤ ν n x + 2 := by
    rw [abs_of_nonneg (hs x).1]
    have hνpos := hν.1 n x
    have hsx := (hs x).2
    linarith
  have hubound (x) : |u x| ≤ ν n x + 2 := by
    apply abs_le.mpr
    have hνpos := hν.1 n x
    have hsx := hs x
    have ht := hsu x
    have hfx := (hf n x).2
    constructor <;> linarith
  have hmixed (S : Finset (Fin k)) (hS : S.Nonempty) :
      |mixedAPAvg k (fun j x => if j ∈ S then u x else s x)| ≤ ξ := by
    apply hc
    · intro j x
      split_ifs <;> first | exact hubound x | exact hsbound x
    · obtain ⟨j, hj⟩ := hS
      refine ⟨j, ?_⟩
      simpa only [if_pos hj] using huniform
  obtain ⟨g, hg, hgmean, hgcount⟩ :=
    bounded_model_of_mixed_estimates k (M n) (f n) s u ε ξ hε.le hξ.le hs hsu hmean hmixed
  refine ⟨g, hg, ?_, ?_⟩
  · linarith
  · have hscale : (2 : ℝ) ^ k * ξ = η / 2 := by
      dsimp [ξ]
      field_simp
    rw [hscale] at hgcount
    linarith
