-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:35.252325+00:00
-- url     : https://prove2.me/submissions/c88c2a53-bf79-4ebd-bc6f-1c45810e0a15

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
lemma fullJetRow2_calc (col : Fin 23) : fullJetBox 2 col = fullJetRow2 col := by
  revert col
  decide +kernel
lemma fullJetRow2_mem_eu_oai (col : Fin 23) : (fullJetRow2 col).Mem (fullJetMatrix 2 col) := by
  rw [← fullJetRow2_calc]
  exact fullJetBox_mem_eu 2 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_eu_oai
