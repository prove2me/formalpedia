-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureTable11_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:42:24.42919+00:00
-- url     : https://prove2.me/submissions/e3a8c1a2-e49b-4764-9b95-1d774d21c0d5

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData11_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData11_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData11_2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData11_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData11_4_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_3_pre (j : Fin 31) : (curvatureExpInput 1 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_3_mem (j : Fin 31) : (curvatureData11_3 j).Mem (curvatureWave 1 1 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData11_3_calc_x]
  exact curvatureBox_mem_x 1 1 3 j (curvatureData11_3_pre j)
lemma curvatureData11_4_pre (j : Fin 31) : (curvatureExpInput 1 1 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_4_mem (j : Fin 31) : (curvatureData11_4 j).Mem (curvatureWave 1 1 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData11_4_calc_x]
  exact curvatureBox_mem_x 1 1 4 j (curvatureData11_4_pre j)
lemma curvatureTable11_mem_x_oai (i : Fin 5) (j : Fin 31) : (curvatureTable11 i j).Mem (curvatureWave 1 1 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData11_0_mem_x j
  · exact curvatureData11_1_mem_x j
  · exact curvatureData11_2_mem_x j
  · exact curvatureData11_3_mem j
  · exact curvatureData11_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureTable11_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureTable11_mem_x_oai
