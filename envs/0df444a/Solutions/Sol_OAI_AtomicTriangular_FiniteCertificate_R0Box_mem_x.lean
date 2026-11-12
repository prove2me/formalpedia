-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:47.973192+00:00
-- url     : https://prove2.me/submissions/cf843be3-5398-41b7-8708-e7944effec67

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow10_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow11_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow12_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow13_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow14_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow15_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow17_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow19_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow3_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow4_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow5_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow6_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow7_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow8_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow9_mem_x
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

lemma fullJetRow16_calc (col : Fin 23) : fullJetBox 16 col = fullJetRow16 col := by
  revert col
  decide +kernel
lemma fullJetRow16_mem (col : Fin 23) : (fullJetRow16 col).Mem (fullJetMatrix 16 col) := by
  rw [← fullJetRow16_calc]
  exact fullJetBox_mem 16 col
lemma fullJetRow18_calc (col : Fin 23) : fullJetBox 18 col = fullJetRow18 col := by
  revert col
  decide +kernel
lemma fullJetRow18_mem (col : Fin 23) : (fullJetRow18 col).Mem (fullJetMatrix 18 col) := by
  rw [← fullJetRow18_calc]
  exact fullJetBox_mem 18 col
lemma jetMatrixTable_mem (i : Fin 20) (col : Fin 23) : (jetMatrixTable i col).Mem (fullJetMatrix i col) := by
  fin_cases i
  · exact fullJetRow0_mem_x col
  · exact fullJetRow1_mem_x col
  · exact fullJetRow2_mem_x col
  · exact fullJetRow3_mem_x col
  · exact fullJetRow4_mem_x col
  · exact fullJetRow5_mem_x col
  · exact fullJetRow6_mem_x col
  · exact fullJetRow7_mem_x col
  · exact fullJetRow8_mem_x col
  · exact fullJetRow9_mem_x col
  · exact fullJetRow10_mem_x col
  · exact fullJetRow11_mem_x col
  · exact fullJetRow12_mem_x col
  · exact fullJetRow13_mem_x col
  · exact fullJetRow14_mem_x col
  · exact fullJetRow15_mem_x col
  · exact fullJetRow16_mem col
  · exact fullJetRow17_mem_x col
  · exact fullJetRow18_mem col
  · exact fullJetRow19_mem_x col
lemma R0Box_mem_x_oai (i : Fin 20) (j : Fin 3) : (R0Box i j).Mem (Construction.R0 i j) :=
  jetMatrixTable_mem i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x_oai
