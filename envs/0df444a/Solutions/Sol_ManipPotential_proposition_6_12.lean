-- Prove2me | solution 1 for ManipPotential.proposition_6_12
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:17:01.244657+00:00
-- url     : https://prove2.me/submissions/66c23961-8e6f-45c0-a53b-9906cf5f7ab1

import Mathlib
import Theorems.Thm_ManipPotential_proposition_6_12_step1
import Theorems.Thm_ManipPotential_proposition_6_12_step2_uniform
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

open ManipPotential

theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    ∃ W : Submodule ℝ (Ranking m → ℝ), Module.finrank ℝ W = m - 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ w ∈ W, w ∈ Cmp ((K : ℝ) + 1) i j ∧
        dotProduct w (unitVec (ell i) - unitVec (ell j)) = 1 := by
  classical
  obtain ⟨T, hTfin, hstep⟩ := proposition_6_12_step1 hm K g hg
  let M : Fin m → Fin m → Set (Ranking m → ℝ) := fun i j =>
    if hij : i = j then Set.univ else Classical.choose (hstep i j hij)
  have hM (i j : Fin m) (hij : i ≠ j) :
      IsClosed (M i j) ∧ Convex ℝ (M i j) ∧ 0 ∈ M i j ∧
      (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M i j → a • x ∈ M i j) ∧
      (T : Set (Ranking m → ℝ)) ⊆ M i j ∧
      TransferVectors ((K : ℝ) + 1) i j ⊆ M i j ∧
      -(unitVec (ell i) - unitVec (ell j)) ∉ M i j := by
    simp only [M, dif_neg hij]
    exact Classical.choose_spec (hstep i j hij)
  apply proposition_6_12_step2_uniform hm ((K : ℝ) + 1) T hTfin M
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · exact (hM i j hij).1
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa [M] using (convex_univ : Convex ℝ (Set.univ : Set (Ranking m → ℝ)))
    · exact (hM i j hij).2.1
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · exact (hM i j hij).2.2.1
  · intro i j a ha x hx
    by_cases hij : i = j
    · simp [M, hij]
    · exact (hM i j hij).2.2.2.1 ha hx
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · exact (hM i j hij).2.2.2.2.1
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · exact (hM i j hij).2.2.2.2.2.1
  · exact fun i j hij => (hM i j hij).2.2.2.2.2.2
