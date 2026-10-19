-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:08:57.641715+00:00
-- url     : https://prove2.me/submissions/b73c19ea-8c64-4426-84ee-b436f21891c9

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finiteMatrix_bijective_of_rank_triangular
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_entry_structure

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (S : Finset (Fin (m + 1) → ℕ))
    (delta : Fin m → PowerSeries ℂ) :
    Function.Bijective (finitePacketShearMatrix K S delta).mulVecLin := by
  apply OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_bijective_of_rank_triangular
    (rank := fun i : Fin K × ↥S =>
      ∑ k : Fin m, (InterpolationMatrix.exponentVector i.2.val) k.succ)
  · intro i
    exact (OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_entry_structure
      K S delta).1 i
  · intro i j hij hne
    exact (OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_entry_structure
      K S delta).2 i j hij hne