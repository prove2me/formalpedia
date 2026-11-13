-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData0_00_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:36.419456+00:00
-- url     : https://prove2.me/submissions/d101c80c-53b8-4da8-a54f-d4ee41d9e47e

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData0_00_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_00_pre (j : Fin 31) : (remainderExpInput 0 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_00_mem_eu_oai (j : Fin 31) : (remainderData0_00 j).Mem (remainderWave 0 0 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_00_calc_eu]
  exact remainderBox_mem_eu 0 0 0 j (taylorNormTable_mem_eu 0 0 j) (remainderData0_00_pre j).1 (remainderData0_00_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData0_00_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData0_00_mem_eu_oai
