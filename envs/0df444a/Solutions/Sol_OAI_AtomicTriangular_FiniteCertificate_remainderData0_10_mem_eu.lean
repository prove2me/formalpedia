-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:37.969172+00:00
-- url     : https://prove2.me/submissions/80502841-c3e0-4d71-9f2a-d1e4631b76cd

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_eu
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
lemma remainderData0_10_calc (j : Fin 31) : remainderBox 1 0 0 j (taylorNormTable 1 0 j)=remainderData0_10 j := by
  revert j
  decide +kernel
lemma remainderData0_10_pre (j : Fin 31) : (remainderExpInput 1 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_10_mem_eu_oai (j : Fin 31) : (remainderData0_10 j).Mem (remainderWave 1 0 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_10_calc]
  exact remainderBox_mem_eu 1 0 0 j (taylorNormTable_mem_eu 1 0 j) (remainderData0_10_pre j).1 (remainderData0_10_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_eu_oai
