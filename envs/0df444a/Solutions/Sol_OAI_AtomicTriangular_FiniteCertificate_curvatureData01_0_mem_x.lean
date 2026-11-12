-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:06.955635+00:00
-- url     : https://prove2.me/submissions/48cc30e7-7bba-4273-bbf3-55493004d559

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
lemma curvatureData01_0_calc (j : Fin 31) : curvatureBox 0 1 0 j=curvatureData01_0 j := by
  revert j
  decide +kernel
lemma curvatureData01_0_pre (j : Fin 31) : (curvatureExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_0_mem_x_oai (j : Fin 31) : (curvatureData01_0 j).Mem (curvatureWave 0 1 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData01_0_calc]
  exact curvatureBox_mem_x 0 1 0 j (curvatureData01_0_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_0_mem_x_oai
