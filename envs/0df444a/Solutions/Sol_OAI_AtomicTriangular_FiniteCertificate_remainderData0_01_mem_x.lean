-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:42:54.925019+00:00
-- url     : https://prove2.me/submissions/fa6809ba-ccae-409c-8c49-bde767440f42

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData0_01_calc_x
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
lemma remainderData0_01_pre (j : Fin 31) : (remainderExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_01_mem_x_oai (j : Fin 31) : (remainderData0_01 j).Mem (remainderWave 0 1 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_01_calc_x]
  exact remainderBox_mem_x 0 1 0 j (taylorNormTable_mem_x 0 1 j) (remainderData0_01_pre j).1 (remainderData0_01_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x_oai
