-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:42:55.750627+00:00
-- url     : https://prove2.me/submissions/e79f3c3b-b183-4f6f-b5b4-b4f60d7699a8

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_10_calc (j : Fin 31) : remainderBox 1 0 0 j (taylorNormTable 1 0 j)=remainderData0_10 j := by
  revert j
  decide +kernel
lemma remainderData0_10_pre (j : Fin 31) : (remainderExpInput 1 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_10_mem_x_oai (j : Fin 31) : (remainderData0_10 j).Mem (remainderWave 1 0 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_10_calc]
  exact remainderBox_mem_x 1 0 0 j (taylorNormTable_mem_x 1 0 j) (remainderData0_10_pre j).1 (remainderData0_10_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x_oai
