-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:03.323673+00:00
-- url     : https://prove2.me/submissions/1fb16bfc-ee56-4479-a675-012ddc9749f6

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_1_calc (j : Fin 31) : curvatureBox 0 0 1 j=curvatureData00_1 j := by
  revert j
  decide +kernel
lemma curvatureData00_1_pre (j : Fin 31) : (curvatureExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_1_mem_x_oai (j : Fin 31) : (curvatureData00_1 j).Mem (curvatureWave 0 0 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData00_1_calc]
  exact curvatureBox_mem_x 0 0 1 j (curvatureData00_1_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData00_1_mem_x_oai
