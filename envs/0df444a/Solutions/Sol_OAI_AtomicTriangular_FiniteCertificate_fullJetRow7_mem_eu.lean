-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:33.431316+00:00
-- url     : https://prove2.me/submissions/7d91164b-8541-4da8-adc6-df0ee4bfb436

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
lemma fullJetRow7_calc (col : Fin 23) : fullJetBox 7 col = fullJetRow7 col := by
  revert col
  decide +kernel
lemma fullJetRow7_mem_eu_oai (col : Fin 23) : (fullJetRow7 col).Mem (fullJetMatrix 7 col) := by
  rw [← fullJetRow7_calc]
  exact fullJetBox_mem_eu 7 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_eu_oai
