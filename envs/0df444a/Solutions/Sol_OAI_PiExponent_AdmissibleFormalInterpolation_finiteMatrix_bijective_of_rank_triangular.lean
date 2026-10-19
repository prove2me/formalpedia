-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_bijective_of_rank_triangular
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:13:51.447121+00:00
-- url     : https://prove2.me/submissions/4cce98b1-3c95-46be-8b1f-b8528f5a2e18

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finiteMatrix_injective_of_rank_triangular

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (rank : ι → ℕ) (M : Matrix ι ι ℂ)
    (hdiag : ∀ i, M i i = 1)
    (htri : ∀ i j, i ≠ j → M i j ≠ 0 → rank i < rank j) :
    Function.Bijective M.mulVecLin := by
  have hinj : Function.Injective M.mulVecLin :=
    OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_injective_of_rank_triangular
      rank M hdiag htri
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := M.mulVecLin)).mp hinj⟩
