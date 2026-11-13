-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:34.701037+00:00
-- url     : https://prove2.me/submissions/31986933-c15f-469f-ae39-797c303af4a8

import Mathlib
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetBox_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullJetRow8_calc (col : Fin 23) : fullJetBox 8 col = fullJetRow8 col := by
  revert col
  decide +kernel
lemma fullJetRow8_mem_eu_oai (col : Fin 23) : (fullJetRow8 col).Mem (fullJetMatrix 8 col) := by
  rw [← fullJetRow8_calc]
  exact fullJetBox_mem_eu 8 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_eu_oai
