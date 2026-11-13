-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:59:06.245147+00:00
-- url     : https://prove2.me/submissions/4e611c8b-77b4-4e69-89c5-da0d23db5aa8

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
lemma fullJetRow6_calc (col : Fin 23) : fullJetBox 6 col = fullJetRow6 col := by
  revert col
  decide +kernel
lemma fullJetRow6_mem_eu_oai (col : Fin 23) : (fullJetRow6 col).Mem (fullJetMatrix 6 col) := by
  rw [← fullJetRow6_calc]
  exact fullJetBox_mem_eu 6 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_eu_oai
