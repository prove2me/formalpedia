-- Prove2me | solution 1 for MagicSquares.magic_three_normal_eight
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T07:24:59.340978+00:00
-- url     : https://prove2.me/submissions/16c4750a-a629-4df8-85ab-57c162b541ba

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Definitions.Def_MagicSquaresNormal3
import Theorems.Thm_MagicSquares_magic_three_normal_classify

set_option autoImplicit false
set_option maxHeartbeats 0

namespace MagicSquares

/-- The eight Lo Shu parameter pairs. -/
private def eightPairs : Finset (ℕ × ℕ) :=
  {(2, 4), (2, 6), (4, 2), (4, 8), (6, 2), (6, 8), (8, 4), (8, 6)}

/-- The parameter pairs giving a normal square are exactly the eight. -/
private lemma normalParamSet_five :
    normalParamSet 5 = eightPairs := by
  classical
  unfold normalParamSet
  ext ac
  rcases ac with ⟨a, c⟩
  constructor
  · intro h
    have hac : (a, c) ∈ paramSet 5 := (Finset.mem_filter.mp h).1
    have hN : IsNormal (mkMagic3 5 a c) := (Finset.mem_filter.mp h).2
    have hc := (magic_three_normal_classify a c hac).mp hN
    simp [eightPairs]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [eightPairs]
  · intro h
    simp [eightPairs] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      apply Finset.mem_filter.mpr
      constructor
      · norm_num [paramSet, IsParam3]
      · exact (magic_three_normal_classify _ _ (by norm_num [paramSet, IsParam3])).mpr (by simp)

end MagicSquares

open MagicSquares

theorem solution : normalParamCount 5 = 8 := by
  rw [normalParamCount, normalParamSet_five]
  norm_num [eightPairs]
