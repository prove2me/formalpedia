-- Prove2me | solution 1 for OAI.Saxl.Band.basis_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:26:15.483167+00:00
-- url     : https://prove2.me/submissions/788ac63e-2faf-46c1-a733-d596264dbd37

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices

open OAI OAI.Saxl OAI.Saxl.Band
open scoped TensorProduct
universe uA


theorem solution (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨(1 : ℂ), by norm_num, ⟨0, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨1, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨2, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨3, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨1, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨0, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨3, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨2, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨2, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(-1 : ℂ), by norm_num, ⟨3, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨0, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(-1 : ℂ), by norm_num, ⟨1, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨3, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(-1 : ℂ), by norm_num, ⟨2, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(1 : ℂ), by norm_num, ⟨1, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨(-1 : ℂ), by norm_num, ⟨0, by decide⟩, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;> simp [basis, Matrix.mul_apply, Fin.sum_univ_two]

