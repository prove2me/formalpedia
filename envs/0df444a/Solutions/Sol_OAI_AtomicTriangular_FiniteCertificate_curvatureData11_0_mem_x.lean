-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData11_0_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:05.084622+00:00
-- url     : https://prove2.me/submissions/c4c666af-91cc-49dd-904a-ee1706549250

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_x

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
lemma curvatureData11_0_calc (j : Fin 31) : curvatureBox 1 1 0 j=curvatureData11_0 j := by
  revert j
  decide +kernel
lemma curvatureData11_0_pre (j : Fin 31) : (curvatureExpInput 1 1 0 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData11_0_mem_x_oai (j : Fin 31) : (curvatureData11_0 j).Mem (curvatureWave 1 1 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData11_0_calc]
  exact curvatureBox_mem_x 1 1 0 j (curvatureData11_0_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData11_0_mem_x_oai
