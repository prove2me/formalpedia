-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:34.785416+00:00
-- url     : https://prove2.me/submissions/45d024e5-9fa6-417c-88e3-a74b324a11bc

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
lemma curvatureData01_2_calc (j : Fin 31) : curvatureBox 0 1 2 j=curvatureData01_2 j := by
  revert j
  decide +kernel
lemma curvatureData01_2_pre (j : Fin 31) : (curvatureExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_2_mem_x_oai (j : Fin 31) : (curvatureData01_2 j).Mem (curvatureWave 0 1 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData01_2_calc]
  exact curvatureBox_mem_x 0 1 2 j (curvatureData01_2_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_2_mem_x_oai
