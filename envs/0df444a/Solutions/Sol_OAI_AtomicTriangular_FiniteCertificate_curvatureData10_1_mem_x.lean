-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData10_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:37.171752+00:00
-- url     : https://prove2.me/submissions/b8a93b07-e0b1-4057-9c17-39c44dd441f4

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x

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
lemma curvatureData10_1_calc (j : Fin 31) : curvatureBox 1 0 1 j=curvatureData10_1 j := by
  revert j
  decide +kernel
lemma curvatureData10_1_pre (j : Fin 31) : (curvatureExpInput 1 0 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData10_1_mem_x_oai (j : Fin 31) : (curvatureData10_1 j).Mem (curvatureWave 1 0 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData10_1_calc]
  exact curvatureBox_mem_x 1 0 1 j (curvatureData10_1_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData10_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData10_1_mem_x_oai
