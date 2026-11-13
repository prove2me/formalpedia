-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow5_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:05.127678+00:00
-- url     : https://prove2.me/submissions/54e03d3c-ca4b-4d21-a0b1-c7df49c8c4b2

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
lemma fullJetRow5_calc (col : Fin 23) : fullJetBox 5 col = fullJetRow5 col := by
  revert col
  decide +kernel
lemma fullJetRow5_mem_eu_oai (col : Fin 23) : (fullJetRow5 col).Mem (fullJetMatrix 5 col) := by
  rw [← fullJetRow5_calc]
  exact fullJetBox_mem_eu 5 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow5_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow5_mem_eu_oai
