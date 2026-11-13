-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:31.961251+00:00
-- url     : https://prove2.me/submissions/68ea0cc3-973a-488c-afc4-2d65671863fd

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
lemma fullJetRow4_calc (col : Fin 23) : fullJetBox 4 col = fullJetRow4 col := by
  revert col
  decide +kernel
lemma fullJetRow4_mem_eu_oai (col : Fin 23) : (fullJetRow4 col).Mem (fullJetMatrix 4 col) := by
  rw [← fullJetRow4_calc]
  exact fullJetBox_mem_eu 4 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_eu_oai
