-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:24.078512+00:00
-- url     : https://prove2.me/submissions/43878e8c-8f6a-49de-9bb2-90dd367135ca

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
lemma fullJetRow10_calc (col : Fin 23) : fullJetBox 10 col = fullJetRow10 col := by
  revert col
  decide +kernel
lemma fullJetRow10_mem_eu_oai (col : Fin 23) : (fullJetRow10 col).Mem (fullJetMatrix 10 col) := by
  rw [← fullJetRow10_calc]
  exact fullJetBox_mem_eu 10 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_eu_oai
