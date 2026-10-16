-- Prove2me | solution 1 for OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-15T15:15:33.773768+00:00
-- url     : https://prove2.me/submissions/fe1bc085-b61f-4528-a807-8bfabce4fc09

import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_OAI_SevenEighths_HeckeDirichlet_exists_norm_base_change_factorization

/- Port of the transfer argument in OpenAI's
OAI/NumberTheory/DirichletL/Hecke/Dirichlet.lean,
`dirichlet_seven_eighths_of_hecke`. The factorization is an explicit open child;
the Hecke nonvanishing theorem is already proved on Prove2Me. -/
theorem solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) hge
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  obtain ⟨η, _hcoeff, hfactor⟩ :=
    OAI.SevenEighths.HeckeDirichlet.exists_norm_base_change_factorization χ
  have hη := OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
    η hs (fun h => hs1 h.2)
  rw [hfactor s hs0 hs1] at hη
  exact (mul_ne_zero_iff.mp hη).1
