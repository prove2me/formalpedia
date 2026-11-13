-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:28.295251+00:00
-- url     : https://prove2.me/submissions/34572423-3ee0-4415-b45a-1588cab7141e

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
lemma fullJetRow13_calc (col : Fin 23) : fullJetBox 13 col = fullJetRow13 col := by
  revert col
  decide +kernel
lemma fullJetRow13_mem_eu_oai (col : Fin 23) : (fullJetRow13 col).Mem (fullJetMatrix 13 col) := by
  rw [← fullJetRow13_calc]
  exact fullJetBox_mem_eu 13 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_eu_oai
