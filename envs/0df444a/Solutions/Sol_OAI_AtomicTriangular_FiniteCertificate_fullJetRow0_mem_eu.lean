-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow0_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:22.578827+00:00
-- url     : https://prove2.me/submissions/5c960b3b-84b0-4f9d-be10-1d52c80b7e6f

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
lemma fullJetRow0_calc (col : Fin 23) : fullJetBox 0 col = fullJetRow0 col := by
  revert col
  decide +kernel
lemma fullJetRow0_mem_eu_oai (col : Fin 23) : (fullJetRow0 col).Mem (fullJetMatrix 0 col) := by
  rw [← fullJetRow0_calc]
  exact fullJetBox_mem_eu 0 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow0_mem_eu_oai
