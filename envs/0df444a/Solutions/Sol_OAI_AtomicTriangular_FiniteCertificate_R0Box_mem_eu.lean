-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:13:17.96236+00:00
-- url     : https://prove2.me/submissions/522190e6-581e-47e9-aeb3-cb70307cc59e

import Mathlib
import Definitions.Def_OAIQ334E011
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow10_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow11_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow15_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow2_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow5_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow6_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow8_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow9_mem_eu

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
lemma fullJetRow14_calc (col : Fin 23) : fullJetBox 14 col = fullJetRow14 col := by
  revert col
  decide +kernel
lemma fullJetRow14_mem (col : Fin 23) : (fullJetRow14 col).Mem (fullJetMatrix 14 col) := by
  rw [← fullJetRow14_calc]
  exact fullJetBox_mem_eu 14 col
lemma fullJetRow16_calc (col : Fin 23) : fullJetBox 16 col = fullJetRow16 col := by
  revert col
  decide +kernel
lemma fullJetRow16_mem (col : Fin 23) : (fullJetRow16 col).Mem (fullJetMatrix 16 col) := by
  rw [← fullJetRow16_calc]
  exact fullJetBox_mem_eu 16 col
lemma fullJetRow17_calc (col : Fin 23) : fullJetBox 17 col = fullJetRow17 col := by
  revert col
  decide +kernel
lemma fullJetRow17_mem (col : Fin 23) : (fullJetRow17 col).Mem (fullJetMatrix 17 col) := by
  rw [← fullJetRow17_calc]
  exact fullJetBox_mem_eu 17 col
lemma fullJetRow18_calc (col : Fin 23) : fullJetBox 18 col = fullJetRow18 col := by
  revert col
  decide +kernel
lemma fullJetRow18_mem (col : Fin 23) : (fullJetRow18 col).Mem (fullJetMatrix 18 col) := by
  rw [← fullJetRow18_calc]
  exact fullJetBox_mem_eu 18 col
lemma fullJetRow19_calc (col : Fin 23) : fullJetBox 19 col = fullJetRow19 col := by
  revert col
  decide +kernel
lemma fullJetRow19_mem (col : Fin 23) : (fullJetRow19 col).Mem (fullJetMatrix 19 col) := by
  rw [← fullJetRow19_calc]
  exact fullJetBox_mem_eu 19 col
lemma jetMatrixTable_mem (i : Fin 20) (col : Fin 23) : (jetMatrixTable i col).Mem (fullJetMatrix i col) := by
  fin_cases i
  · exact fullJetRow0_mem_eu col
  · exact fullJetRow1_mem_eu col
  · exact fullJetRow2_mem_eu col
  · exact fullJetRow3_mem_eu col
  · exact fullJetRow4_mem_eu col
  · exact fullJetRow5_mem_eu col
  · exact fullJetRow6_mem_eu col
  · exact fullJetRow7_mem_eu col
  · exact fullJetRow8_mem_eu col
  · exact fullJetRow9_mem_eu col
  · exact fullJetRow10_mem_eu col
  · exact fullJetRow11_mem_eu col
  · exact fullJetRow12_mem_eu col
  · exact fullJetRow13_mem_eu col
  · exact fullJetRow14_mem col
  · exact fullJetRow15_mem_eu col
  · exact fullJetRow16_mem col
  · exact fullJetRow17_mem col
  · exact fullJetRow18_mem col
  · exact fullJetRow19_mem col
lemma R0Box_mem_eu_oai (i : Fin 20) (j : Fin 3) : (R0Box i j).Mem (Construction.R0 i j) :=
  jetMatrixTable_mem i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_eu_oai
