-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:43:23.877272+00:00
-- url     : https://prove2.me/submissions/edc13834-f4b3-42d6-b886-93c7eee8c261

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData1_00_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_00_pre (j : Fin 31) : (remainderExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_00_mem_x_oai (j : Fin 31) : (remainderData1_00 j).Mem (remainderWave 0 0 (nearNode 1) (nearRadius 1) (frequency j)) := by
  rw [← remainderData1_00_calc_x]
  exact remainderBox_mem_x 0 0 1 j (taylorNormTable_mem_x 0 0 j) (remainderData1_00_pre j).1 (remainderData1_00_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x_oai
