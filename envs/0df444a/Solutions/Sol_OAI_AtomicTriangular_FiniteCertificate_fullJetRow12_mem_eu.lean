-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:27.032055+00:00
-- url     : https://prove2.me/submissions/9f35e56a-1d35-4d79-80d4-18e613f26c3a

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
lemma fullJetRow12_calc (col : Fin 23) : fullJetBox 12 col = fullJetRow12 col := by
  revert col
  decide +kernel
lemma fullJetRow12_mem_eu_oai (col : Fin 23) : (fullJetRow12 col).Mem (fullJetMatrix 12 col) := by
  rw [← fullJetRow12_calc]
  exact fullJetBox_mem_eu 12 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_eu_oai
