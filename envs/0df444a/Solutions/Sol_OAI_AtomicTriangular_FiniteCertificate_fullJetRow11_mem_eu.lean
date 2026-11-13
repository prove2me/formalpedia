-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow11_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:25.811059+00:00
-- url     : https://prove2.me/submissions/bcabd56b-1df1-4509-8cb1-34aa1fe67c02

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
lemma fullJetRow11_calc (col : Fin 23) : fullJetBox 11 col = fullJetRow11 col := by
  revert col
  decide +kernel
lemma fullJetRow11_mem_eu_oai (col : Fin 23) : (fullJetRow11 col).Mem (fullJetMatrix 11 col) := by
  rw [← fullJetRow11_calc]
  exact fullJetBox_mem_eu 11 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow11_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow11_mem_eu_oai
