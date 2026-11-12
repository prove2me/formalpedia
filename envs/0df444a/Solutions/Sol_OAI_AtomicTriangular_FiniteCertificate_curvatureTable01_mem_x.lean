-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.997653+00:00
-- url     : https://prove2.me/submissions/91ea1173-a999-4a69-b321-4ec9c70d1e4d

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData01_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData01_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData01_2_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_3_calc (j : Fin 31) : curvatureBox 0 1 3 j=curvatureData01_3 j := by
  revert j
  decide +kernel
lemma curvatureData01_3_pre (j : Fin 31) : (curvatureExpInput 0 1 3 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_3_mem (j : Fin 31) : (curvatureData01_3 j).Mem (curvatureWave 0 1 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData01_3_calc]
  exact curvatureBox_mem_x 0 1 3 j (curvatureData01_3_pre j)
lemma curvatureData01_4_calc (j : Fin 31) : curvatureBox 0 1 4 j=curvatureData01_4 j := by
  revert j
  decide +kernel
lemma curvatureData01_4_pre (j : Fin 31) : (curvatureExpInput 0 1 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_4_mem (j : Fin 31) : (curvatureData01_4 j).Mem (curvatureWave 0 1 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData01_4_calc]
  exact curvatureBox_mem_x 0 1 4 j (curvatureData01_4_pre j)
lemma curvatureTable01_mem_x_oai (i : Fin 5) (j : Fin 31) : (curvatureTable01 i j).Mem (curvatureWave 0 1 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData01_0_mem_x j
  · exact curvatureData01_1_mem_x j
  · exact curvatureData01_2_mem_x j
  · exact curvatureData01_3_mem j
  · exact curvatureData01_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_x_oai
