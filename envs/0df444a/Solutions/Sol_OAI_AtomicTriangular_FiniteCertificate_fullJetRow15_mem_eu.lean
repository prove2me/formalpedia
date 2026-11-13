-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:31.343102+00:00
-- url     : https://prove2.me/submissions/45e15908-a143-44bb-8c68-9307a95c4244

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
lemma fullJetRow15_calc (col : Fin 23) : fullJetBox 15 col = fullJetRow15 col := by
  revert col
  decide +kernel
lemma fullJetRow15_mem_eu_oai (col : Fin 23) : (fullJetRow15 col).Mem (fullJetMatrix 15 col) := by
  rw [← fullJetRow15_calc]
  exact fullJetBox_mem_eu 15 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_eu_oai
