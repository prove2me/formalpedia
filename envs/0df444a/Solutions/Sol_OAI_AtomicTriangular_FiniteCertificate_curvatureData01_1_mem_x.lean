-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:08.062869+00:00
-- url     : https://prove2.me/submissions/eed5e113-34af-470e-bc8a-ac38d52867c3

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x

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
lemma curvatureData01_1_calc (j : Fin 31) : curvatureBox 0 1 1 j=curvatureData01_1 j := by
  revert j
  decide +kernel
lemma curvatureData01_1_pre (j : Fin 31) : (curvatureExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_1_mem_x_oai (j : Fin 31) : (curvatureData01_1 j).Mem (curvatureWave 0 1 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData01_1_calc]
  exact curvatureBox_mem_x 0 1 1 j (curvatureData01_1_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_x_oai
