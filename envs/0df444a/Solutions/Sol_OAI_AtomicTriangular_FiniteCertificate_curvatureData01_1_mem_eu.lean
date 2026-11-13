-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:31.893653+00:00
-- url     : https://prove2.me/submissions/268db4e8-4ff9-4b68-806d-d579ffe329e2

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData01_1_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_1_pre (j : Fin 31) : (curvatureExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData01_1_mem_eu_oai (j : Fin 31) : (curvatureData01_1 j).Mem (curvatureWave 0 1 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData01_1_calc_eu]
  exact curvatureBox_mem_eu 0 1 1 j (curvatureData01_1_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.curvatureData01_1_mem_eu_oai
