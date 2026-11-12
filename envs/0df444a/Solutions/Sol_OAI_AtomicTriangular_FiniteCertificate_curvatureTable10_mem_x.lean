-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureTable10_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:42:23.353004+00:00
-- url     : https://prove2.me/submissions/47adab3e-c6f6-4232-950c-1b158a644727

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData10_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData10_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData10_2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData10_3_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData10_4_calc (j : Fin 31) : curvatureBox 1 0 4 j=curvatureData10_4 j := by
  revert j
  decide +kernel
lemma curvatureData10_4_pre (j : Fin 31) : (curvatureExpInput 1 0 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_4_mem (j : Fin 31) : (curvatureData10_4 j).Mem (curvatureWave 1 0 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData10_4_calc]
  exact curvatureBox_mem_x 1 0 4 j (curvatureData10_4_pre j)
lemma curvatureTable10_mem_x_oai (i : Fin 5) (j : Fin 31) : (curvatureTable10 i j).Mem (curvatureWave 1 0 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData10_0_mem_x j
  · exact curvatureData10_1_mem_x j
  · exact curvatureData10_2_mem_x j
  · exact curvatureData10_3_mem_x j
  · exact curvatureData10_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureTable10_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureTable10_mem_x_oai
