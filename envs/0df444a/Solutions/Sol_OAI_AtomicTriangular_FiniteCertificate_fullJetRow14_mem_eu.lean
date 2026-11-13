-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:30.18819+00:00
-- url     : https://prove2.me/submissions/0eab18a5-4d73-44a8-8ea7-96f31dbc209e

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
lemma fullJetRow14_calc (col : Fin 23) : fullJetBox 14 col = fullJetRow14 col := by
  revert col
  decide +kernel
lemma fullJetRow14_mem_eu_oai (col : Fin 23) : (fullJetRow14 col).Mem (fullJetMatrix 14 col) := by
  rw [← fullJetRow14_calc]
  exact fullJetBox_mem_eu 14 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_eu_oai
