-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:35.681225+00:00
-- url     : https://prove2.me/submissions/4bbd4289-c45b-4e4b-be6d-3bba7c0707a4

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
lemma fullJetRow9_calc (col : Fin 23) : fullJetBox 9 col = fullJetRow9 col := by
  revert col
  decide +kernel
lemma fullJetRow9_mem_eu_oai (col : Fin 23) : (fullJetRow9 col).Mem (fullJetMatrix 9 col) := by
  rw [← fullJetRow9_calc]
  exact fullJetBox_mem_eu 9 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_eu_oai
