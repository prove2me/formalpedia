-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:58:33.660312+00:00
-- url     : https://prove2.me/submissions/0fc6917a-df12-4d56-88ff-41aa6fdc8e0e

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_jetTable_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullJetBox_mem (i : Fin 20) (col : Fin 23) : (fullJetBox i col).Mem (fullJetMatrix i col) := by
  have hh := (CI.mem_sum (fun j => CI.mem_mul (jetTable_mem_x (if col.val=22 then 0 else 1) i j)
    (columnTable_mem_x col j))).1
  by_cases hc : col.val=22
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh

lemma fullJetRow12_calc (col : Fin 23) : fullJetBox 12 col = fullJetRow12 col := by
  revert col
  decide +kernel
lemma fullJetRow12_mem_x_oai (col : Fin 23) : (fullJetRow12 col).Mem (fullJetMatrix 12 col) := by
  rw [← fullJetRow12_calc]
  exact fullJetBox_mem 12 col
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_x_oai
