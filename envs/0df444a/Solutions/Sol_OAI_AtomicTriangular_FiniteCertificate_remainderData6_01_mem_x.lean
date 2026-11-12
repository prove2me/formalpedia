-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:48:04.793628+00:00
-- url     : https://prove2.me/submissions/a1b7322b-0ca4-4997-aaa1-d6b47aa29745

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData6_01_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_01_pre (j : Fin 31) : (remainderExpInput 0 1 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_01_mem_x_oai (j : Fin 31) : (remainderData6_01 j).Mem (remainderWave 0 1 (nearNode 6) (nearRadius 6) (frequency j)) := by
  rw [← remainderData6_01_calc_x]
  exact remainderBox_mem_x 0 1 6 j (taylorNormTable_mem_x 0 1 j) (remainderData6_01_pre j).1 (remainderData6_01_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x_oai
