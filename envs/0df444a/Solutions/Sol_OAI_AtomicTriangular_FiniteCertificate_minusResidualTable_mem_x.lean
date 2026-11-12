-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:02:54.99067+00:00
-- url     : https://prove2.me/submissions/081f21a5-445c-4638-83e5-4eedefdd5357

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusResidualBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma minusResidualRow0_calc (j : Fin 20) : minusResidualBox 0 j = minusResidualRow0 j := by
  revert j
  decide +kernel
lemma minusResidualRow0_mem (j : Fin 20) :
    (minusResidualRow0 j).Mem ((minusApprox*(1 - Construction.R)-1) 0 j) := by
  rw [← minusResidualRow0_calc]
  exact minusResidualBox_mem_x 0 j
lemma minusResidualRow1_calc (j : Fin 20) : minusResidualBox 1 j = minusResidualRow1 j := by
  revert j
  decide +kernel
lemma minusResidualRow1_mem (j : Fin 20) :
    (minusResidualRow1 j).Mem ((minusApprox*(1 - Construction.R)-1) 1 j) := by
  rw [← minusResidualRow1_calc]
  exact minusResidualBox_mem_x 1 j
lemma minusResidualRow2_calc (j : Fin 20) : minusResidualBox 2 j = minusResidualRow2 j := by
  revert j
  decide +kernel
lemma minusResidualRow2_mem (j : Fin 20) :
    (minusResidualRow2 j).Mem ((minusApprox*(1 - Construction.R)-1) 2 j) := by
  rw [← minusResidualRow2_calc]
  exact minusResidualBox_mem_x 2 j
lemma minusResidualRow3_calc (j : Fin 20) : minusResidualBox 3 j = minusResidualRow3 j := by
  revert j
  decide +kernel
lemma minusResidualRow3_mem (j : Fin 20) :
    (minusResidualRow3 j).Mem ((minusApprox*(1 - Construction.R)-1) 3 j) := by
  rw [← minusResidualRow3_calc]
  exact minusResidualBox_mem_x 3 j
lemma minusResidualRow4_calc (j : Fin 20) : minusResidualBox 4 j = minusResidualRow4 j := by
  revert j
  decide +kernel
lemma minusResidualRow4_mem (j : Fin 20) :
    (minusResidualRow4 j).Mem ((minusApprox*(1 - Construction.R)-1) 4 j) := by
  rw [← minusResidualRow4_calc]
  exact minusResidualBox_mem_x 4 j
lemma minusResidualRow5_calc (j : Fin 20) : minusResidualBox 5 j = minusResidualRow5 j := by
  revert j
  decide +kernel
lemma minusResidualRow5_mem (j : Fin 20) :
    (minusResidualRow5 j).Mem ((minusApprox*(1 - Construction.R)-1) 5 j) := by
  rw [← minusResidualRow5_calc]
  exact minusResidualBox_mem_x 5 j
lemma minusResidualRow6_calc (j : Fin 20) : minusResidualBox 6 j = minusResidualRow6 j := by
  revert j
  decide +kernel
lemma minusResidualRow6_mem (j : Fin 20) :
    (minusResidualRow6 j).Mem ((minusApprox*(1 - Construction.R)-1) 6 j) := by
  rw [← minusResidualRow6_calc]
  exact minusResidualBox_mem_x 6 j
lemma minusResidualRow7_calc (j : Fin 20) : minusResidualBox 7 j = minusResidualRow7 j := by
  revert j
  decide +kernel
lemma minusResidualRow7_mem (j : Fin 20) :
    (minusResidualRow7 j).Mem ((minusApprox*(1 - Construction.R)-1) 7 j) := by
  rw [← minusResidualRow7_calc]
  exact minusResidualBox_mem_x 7 j
lemma minusResidualRow8_calc (j : Fin 20) : minusResidualBox 8 j = minusResidualRow8 j := by
  revert j
  decide +kernel
lemma minusResidualRow8_mem (j : Fin 20) :
    (minusResidualRow8 j).Mem ((minusApprox*(1 - Construction.R)-1) 8 j) := by
  rw [← minusResidualRow8_calc]
  exact minusResidualBox_mem_x 8 j
lemma minusResidualRow9_calc (j : Fin 20) : minusResidualBox 9 j = minusResidualRow9 j := by
  revert j
  decide +kernel
lemma minusResidualRow9_mem (j : Fin 20) :
    (minusResidualRow9 j).Mem ((minusApprox*(1 - Construction.R)-1) 9 j) := by
  rw [← minusResidualRow9_calc]
  exact minusResidualBox_mem_x 9 j
lemma minusResidualRow10_calc (j : Fin 20) : minusResidualBox 10 j = minusResidualRow10 j := by
  revert j
  decide +kernel
lemma minusResidualRow10_mem (j : Fin 20) :
    (minusResidualRow10 j).Mem ((minusApprox*(1 - Construction.R)-1) 10 j) := by
  rw [← minusResidualRow10_calc]
  exact minusResidualBox_mem_x 10 j
lemma minusResidualRow11_calc (j : Fin 20) : minusResidualBox 11 j = minusResidualRow11 j := by
  revert j
  decide +kernel
lemma minusResidualRow11_mem (j : Fin 20) :
    (minusResidualRow11 j).Mem ((minusApprox*(1 - Construction.R)-1) 11 j) := by
  rw [← minusResidualRow11_calc]
  exact minusResidualBox_mem_x 11 j
lemma minusResidualRow12_calc (j : Fin 20) : minusResidualBox 12 j = minusResidualRow12 j := by
  revert j
  decide +kernel
lemma minusResidualRow12_mem (j : Fin 20) :
    (minusResidualRow12 j).Mem ((minusApprox*(1 - Construction.R)-1) 12 j) := by
  rw [← minusResidualRow12_calc]
  exact minusResidualBox_mem_x 12 j
lemma minusResidualRow13_calc (j : Fin 20) : minusResidualBox 13 j = minusResidualRow13 j := by
  revert j
  decide +kernel
lemma minusResidualRow13_mem (j : Fin 20) :
    (minusResidualRow13 j).Mem ((minusApprox*(1 - Construction.R)-1) 13 j) := by
  rw [← minusResidualRow13_calc]
  exact minusResidualBox_mem_x 13 j
lemma minusResidualRow14_calc (j : Fin 20) : minusResidualBox 14 j = minusResidualRow14 j := by
  revert j
  decide +kernel
lemma minusResidualRow14_mem (j : Fin 20) :
    (minusResidualRow14 j).Mem ((minusApprox*(1 - Construction.R)-1) 14 j) := by
  rw [← minusResidualRow14_calc]
  exact minusResidualBox_mem_x 14 j
lemma minusResidualRow15_calc (j : Fin 20) : minusResidualBox 15 j = minusResidualRow15 j := by
  revert j
  decide +kernel
lemma minusResidualRow15_mem (j : Fin 20) :
    (minusResidualRow15 j).Mem ((minusApprox*(1 - Construction.R)-1) 15 j) := by
  rw [← minusResidualRow15_calc]
  exact minusResidualBox_mem_x 15 j
lemma minusResidualRow16_calc (j : Fin 20) : minusResidualBox 16 j = minusResidualRow16 j := by
  revert j
  decide +kernel
lemma minusResidualRow16_mem (j : Fin 20) :
    (minusResidualRow16 j).Mem ((minusApprox*(1 - Construction.R)-1) 16 j) := by
  rw [← minusResidualRow16_calc]
  exact minusResidualBox_mem_x 16 j
lemma minusResidualRow17_calc (j : Fin 20) : minusResidualBox 17 j = minusResidualRow17 j := by
  revert j
  decide +kernel
lemma minusResidualRow17_mem (j : Fin 20) :
    (minusResidualRow17 j).Mem ((minusApprox*(1 - Construction.R)-1) 17 j) := by
  rw [← minusResidualRow17_calc]
  exact minusResidualBox_mem_x 17 j
lemma minusResidualRow18_calc (j : Fin 20) : minusResidualBox 18 j = minusResidualRow18 j := by
  revert j
  decide +kernel
lemma minusResidualRow18_mem (j : Fin 20) :
    (minusResidualRow18 j).Mem ((minusApprox*(1 - Construction.R)-1) 18 j) := by
  rw [← minusResidualRow18_calc]
  exact minusResidualBox_mem_x 18 j
lemma minusResidualRow19_calc (j : Fin 20) : minusResidualBox 19 j = minusResidualRow19 j := by
  revert j
  decide +kernel
lemma minusResidualRow19_mem (j : Fin 20) :
    (minusResidualRow19 j).Mem ((minusApprox*(1 - Construction.R)-1) 19 j) := by
  rw [← minusResidualRow19_calc]
  exact minusResidualBox_mem_x 19 j
lemma minusResidualTable_mem_x_oai (i j : Fin 20) :
    (minusResidualTable i j).Mem ((minusApprox*(1 - Construction.R)-1) i j) := by
  fin_cases i
  · exact minusResidualRow0_mem j
  · exact minusResidualRow1_mem j
  · exact minusResidualRow2_mem j
  · exact minusResidualRow3_mem j
  · exact minusResidualRow4_mem j
  · exact minusResidualRow5_mem j
  · exact minusResidualRow6_mem j
  · exact minusResidualRow7_mem j
  · exact minusResidualRow8_mem j
  · exact minusResidualRow9_mem j
  · exact minusResidualRow10_mem j
  · exact minusResidualRow11_mem j
  · exact minusResidualRow12_mem j
  · exact minusResidualRow13_mem j
  · exact minusResidualRow14_mem j
  · exact minusResidualRow15_mem j
  · exact minusResidualRow16_mem j
  · exact minusResidualRow17_mem j
  · exact minusResidualRow18_mem j
  · exact minusResidualRow19_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x_oai
