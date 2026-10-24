-- Prove2me | solution 1 for HiringLP.ProbeTopK.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:32:55.703502+00:00
-- url     : https://prove2.me/submissions/61369f7b-616f-44d6-96b0-593ebda741a0

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank
import Theorems.Thm_HiringLP_ProbeTopK_lemma_3
import Theorems.Thm_HiringLP_ProbeTopK_lemma_4
import Theorems.Thm_HiringLP_ProbeTopK_independent_version_bound

open Finset HiringLP.ProbeTopK

lemma PTK1_DR_eq_indep {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hF : (fracSet y).card ≠ 2) (S : Finset (Fin n)) : DR y S = indepProb y S := by
  unfold DR indepProb
  rw [if_neg hF]
  have hzero : ∀ i, i ∉ onesSet y ∪ fracSet y → y i = 0 := by
    intro i hi
    simp only [onesSet, fracSet, mem_union, mem_filter, mem_univ, true_and, not_or,
      not_and_or, not_lt] at hi
    rcases hi with ⟨h1, h2 | h2⟩
    · linarith [(hy i).1]
    · exact absurd (le_antisymm (hy i).2 h2) h1
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    symm
    refine (prod_subset (subset_univ _) ?_).symm
    intro i _ hi
    by_cases hone : i ∈ onesSet y
    · have : y i = 1 := by simpa [onesSet] using hone
      rw [if_pos (h1 hone), this]
    · have hnot : i ∉ onesSet y ∪ fracSet y := by simp [hone, hi]
      have hiS : i ∉ S := fun h => hnot (h2 h)
      rw [if_neg hiS, hzero i hnot]; ring
  · symm
    rw [not_and_or] at h
    rcases h with h | h
    · obtain ⟨i, hi1, hi2⟩ := not_subset.1 h
      have : y i = 1 := by simpa [onesSet] using hi1
      exact prod_eq_zero (mem_univ i) (by rw [if_neg hi2, this]; ring)
    · obtain ⟨i, hi1, hi2⟩ := not_subset.1 h
      exact prod_eq_zero (mem_univ i) (by rw [if_pos hi1, hzero i hi2])

theorem solution {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hopt : IsLPOpt I x y)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I))
    (ord : Equiv.Perm (Fin n)) (hord : SortedBy ord (vbar I x)) :
    (1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / (I.k.factorial : ℝ)) * LPobj I x y ≤
      algReward I x y ord := by
  rw [lemma_3 I hI x y hext ord]
  have hind := independent_version_bound I hI x y hopt ord hord
  by_cases hF : (fracSet y).card = 2
  · exact hind.trans (lemma_4 I hI x y hext hF ord hord)
  · have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := hopt.1.2.2.2.2
    have : DR y = indepProb y := funext (PTK1_DR_eq_indep y hy hF)
    rw [this]; exact hind
