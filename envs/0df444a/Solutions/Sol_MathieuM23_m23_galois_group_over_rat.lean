-- Prove2me | solution 1 for MathieuM23.m23_galois_group_over_rat
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T09:39:24.098414+00:00
-- url     : https://prove2.me/submissions/bbcfa265-0e1d-41b4-9652-6a03ebe754d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MathieuM23_Group
import Definitions.Def_MathieuM23_Polynomials
import Theorems.Thm_MathieuM23_example_1_2

open MathieuM23

theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ Nonempty ((K ≃ₐ[ℚ] K) ≃* M23) := by
  -- Take K to be the splitting field of the Example 1.2 polynomial over ℚ.
  have hsplit : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField fEx12) fEx12 :=
    Polynomial.IsSplittingField.splittingField fEx12
  have : NumberField (Polynomial.SplittingField fEx12) := ⟨⟩
  obtain ⟨hG, hM, -⟩ := example_1_2 (Polynomial.SplittingField fEx12)
  exact ⟨Polynomial.SplittingField fEx12, inferInstance, inferInstance, inferInstance, hG, hM⟩
