-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:32.846375+00:00
-- url     : https://prove2.me/submissions/69048999-5f0b-4673-a746-dc86e9bad5d0

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
lemma fullJetRow17_calc (col : Fin 23) : fullJetBox 17 col = fullJetRow17 col := by
  revert col
  decide +kernel
lemma fullJetRow17_mem_eu_oai (col : Fin 23) : (fullJetRow17 col).Mem (fullJetMatrix 17 col) := by
  rw [← fullJetRow17_calc]
  exact fullJetBox_mem_eu 17 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_eu_oai
