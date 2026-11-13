-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:41.331564+00:00
-- url     : https://prove2.me/submissions/085a680c-5cea-41c5-ad47-f4faaa895158

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData2_00_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_00_pre (j : Fin 31) : (remainderExpInput 0 0 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_00_mem_eu_oai (j : Fin 31) : (remainderData2_00 j).Mem (remainderWave 0 0 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_00_calc_eu]
  exact remainderBox_mem_eu 0 0 2 j (taylorNormTable_mem_eu 0 0 j) (remainderData2_00_pre j).1 (remainderData2_00_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_eu_oai
