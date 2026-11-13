-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:34.145205+00:00
-- url     : https://prove2.me/submissions/5749fc5e-360a-45ed-9fc6-405c42bb2bbd

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
lemma fullJetRow19_calc (col : Fin 23) : fullJetBox 19 col = fullJetRow19 col := by
  revert col
  decide +kernel
lemma fullJetRow19_mem_eu_oai (col : Fin 23) : (fullJetRow19 col).Mem (fullJetMatrix 19 col) := by
  rw [← fullJetRow19_calc]
  exact fullJetBox_mem_eu 19 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu_oai
