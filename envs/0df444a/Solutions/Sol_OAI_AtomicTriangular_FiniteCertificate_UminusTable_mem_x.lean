-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:49.996622+00:00
-- url     : https://prove2.me/submissions/a04c0e77-8fd4-46ba-ba7b-16e4b5f3f52d

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UminusCachedBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma UminusTableRow0_calc (j : Fin 8) : UminusCachedBox 0 j = UminusTableRow0 j := by
  revert j
  decide +kernel
lemma UminusTableRow1_calc (j : Fin 8) : UminusCachedBox 1 j = UminusTableRow1 j := by
  revert j
  decide +kernel
lemma UminusTableRow2_calc (j : Fin 8) : UminusCachedBox 2 j = UminusTableRow2 j := by
  revert j
  decide +kernel
lemma UminusTableRow3_calc (j : Fin 8) : UminusCachedBox 3 j = UminusTableRow3 j := by
  revert j
  decide +kernel
lemma UminusTableRow4_calc (j : Fin 8) : UminusCachedBox 4 j = UminusTableRow4 j := by
  revert j
  decide +kernel
lemma UminusTableRow5_calc (j : Fin 8) : UminusCachedBox 5 j = UminusTableRow5 j := by
  revert j
  decide +kernel
lemma UminusTableRow6_calc (j : Fin 8) : UminusCachedBox 6 j = UminusTableRow6 j := by
  revert j
  decide +kernel
lemma UminusTableRow7_calc (j : Fin 8) : UminusCachedBox 7 j = UminusTableRow7 j := by
  revert j
  decide +kernel
lemma UminusTableRow8_calc (j : Fin 8) : UminusCachedBox 8 j = UminusTableRow8 j := by
  revert j
  decide +kernel
lemma UminusTableRow9_calc (j : Fin 8) : UminusCachedBox 9 j = UminusTableRow9 j := by
  revert j
  decide +kernel
lemma UminusTableRow10_calc (j : Fin 8) : UminusCachedBox 10 j = UminusTableRow10 j := by
  revert j
  decide +kernel
lemma UminusTableRow11_calc (j : Fin 8) : UminusCachedBox 11 j = UminusTableRow11 j := by
  revert j
  decide +kernel
lemma UminusTableRow12_calc (j : Fin 8) : UminusCachedBox 12 j = UminusTableRow12 j := by
  revert j
  decide +kernel
lemma UminusTableRow13_calc (j : Fin 8) : UminusCachedBox 13 j = UminusTableRow13 j := by
  revert j
  decide +kernel
lemma UminusTableRow14_calc (j : Fin 8) : UminusCachedBox 14 j = UminusTableRow14 j := by
  revert j
  decide +kernel
lemma UminusTableRow15_calc (j : Fin 8) : UminusCachedBox 15 j = UminusTableRow15 j := by
  revert j
  decide +kernel
lemma UminusTableRow16_calc (j : Fin 8) : UminusCachedBox 16 j = UminusTableRow16 j := by
  revert j
  decide +kernel
lemma UminusTableRow17_calc (j : Fin 8) : UminusCachedBox 17 j = UminusTableRow17 j := by
  revert j
  decide +kernel
lemma UminusTableRow18_calc (j : Fin 8) : UminusCachedBox 18 j = UminusTableRow18 j := by
  revert j
  decide +kernel
lemma UminusTableRow19_calc (j : Fin 8) : UminusCachedBox 19 j = UminusTableRow19 j := by
  revert j
  decide +kernel
lemma UminusTable_calc (i : Fin 20) (j : Fin 8) : UminusCachedBox i j = UminusTable i j := by
  fin_cases i
  · exact UminusTableRow0_calc j
  · exact UminusTableRow1_calc j
  · exact UminusTableRow2_calc j
  · exact UminusTableRow3_calc j
  · exact UminusTableRow4_calc j
  · exact UminusTableRow5_calc j
  · exact UminusTableRow6_calc j
  · exact UminusTableRow7_calc j
  · exact UminusTableRow8_calc j
  · exact UminusTableRow9_calc j
  · exact UminusTableRow10_calc j
  · exact UminusTableRow11_calc j
  · exact UminusTableRow12_calc j
  · exact UminusTableRow13_calc j
  · exact UminusTableRow14_calc j
  · exact UminusTableRow15_calc j
  · exact UminusTableRow16_calc j
  · exact UminusTableRow17_calc j
  · exact UminusTableRow18_calc j
  · exact UminusTableRow19_calc j
lemma UminusTable_mem_x_oai (i : Fin 20) (j : Fin 8) : (UminusTable i j).Mem (Uminus i j) := by
  rw [← UminusTable_calc]
  exact UminusCachedBox_mem_x i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x_oai
