-- Prove2me | solution 2 for OAI.Saxl.Band.basis_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:16:54.512269+00:00
-- url     : https://prove2.me/submissions/c83fd590-b500-467b-899d-a0353b23a72f

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandMatrices.lean:L181-L246
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.Band.basis_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.RepresentationTheory.Saxl.BandMatrices ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
/- Consecutive segments with the original global position parities. -/
/- Enumeration of the finite symmetric group for the four small matrix calculations. -/
/- Only the original global parity matters. -/
lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/
end Saxl.Band

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl OAI.Saxl.Band
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.Band.basis_mul := @_root_.OAI.Saxl.Band.basis_mul
