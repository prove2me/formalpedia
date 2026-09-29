-- Prove2me | solution 1 for Leopoldt.exists_algHom_cyclotomicField
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:22:51.916237+00:00
-- url     : https://prove2.me/submissions/8545f98d-20cf-4034-9b1d-86960617542d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_NumberField_exists_algHom_cyclotomicField_of_finrank_le_two
import Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField_of_three_le_finrank

open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [IsMulCommutative (K ≃ₐ[ℚ] K)] :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  rcases le_or_gt (Module.finrank ℚ K) 2 with h | h
  · exact NumberField.exists_algHom_cyclotomicField_of_finrank_le_two K h
  · exact Leopoldt.exists_algHom_cyclotomicField_of_three_le_finrank K h
