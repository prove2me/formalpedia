-- Prove2me | solution 1 for Hairer.grid_overlap_count
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T20:05:20.339765+00:00
-- url     : https://prove2.me/submissions/c0816d04-f40d-4a85-a32d-1c55e3cf57b0

import Definitions.Def_Hairer_TestFunctions

set_option autoImplicit false
noncomputable section
open Hairer

/-- A fine coordinate box meets at most `5^d` coarse grid boxes when its widths
are no greater than the coarse widths. The bound is independent of scale. -/
theorem solution {d : ℕ} (x : Pt d) (a c : Fin d → ℝ)
    (hc : ∀ i, 0 < c i) (hac : ∀ i, a i ≤ c i) :
    ∃ S : Finset (Fin d → ℤ), S.card ≤ 5 ^ d ∧
      ∀ k : Fin d → ℤ, (∃ y : Pt d, (∀ i, |y i - x i| < a i) ∧
        (∀ i, |y i / c i - (k i : ℝ)| < 1)) → k ∈ S := by
  classical
  let n : Fin d → ℤ := fun i ↦ ⌊x i / c i⌋
  let S : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i ↦ Finset.Icc (n i - 2) (n i + 2))
  refine ⟨S, ?_, ?_⟩
  · have hcard (i : Fin d) : (Finset.Icc (n i - 2) (n i + 2)).card = 5 := by
      rw [Int.card_Icc]
      omega
    dsimp [S]
    rw [Fintype.card_piFinset]
    simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact le_rfl
  · rintro k ⟨y, hy, hk⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    have hdist : |y i / c i - x i / c i| < 1 := by
      rw [← sub_div, abs_div, abs_of_pos (hc i)]
      exact (div_lt_one (hc i)).mpr ((hy i).trans_le (hac i))
    have hnear : |x i / c i - (k i : ℝ)| < 2 := by
      have ht := abs_add_le (x i / c i - y i / c i) (y i / c i - (k i : ℝ))
      rw [sub_add_sub_cancel] at ht
      rw [abs_sub_comm] at hdist
      linarith [hk i]
    have hnlo : (n i : ℝ) ≤ x i / c i := Int.floor_le _
    have hnhi : x i / c i < (n i : ℝ) + 1 := Int.lt_floor_add_one _
    have hlo : ((n i - 2 : ℤ) : ℝ) ≤ (k i : ℝ) := by
      push_cast
      linarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    have hhi : (k i : ℝ) < ((n i + 3 : ℤ) : ℝ) := by
      push_cast
      linarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    rw [Finset.mem_Icc]
    have hlo' : n i - 2 ≤ k i := by exact_mod_cast hlo
    have hhi' : k i < n i + 3 := by exact_mod_cast hhi
    omega


#print axioms solution
