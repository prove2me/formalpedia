-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.plusBlockBox_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:00:11.410084+00:00
-- url     : https://prove2.me/submissions/4c485a76-8871-4e73-af2c-b8ab24e74132

import Mathlib
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow10_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow11_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow14_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow15_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow17_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow19_mem_eu
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
lemma fullJetRow16_calc (col : Fin 23) : fullJetBox 16 col = fullJetRow16 col := by
  revert col
  decide +kernel
lemma fullJetRow16_mem (col : Fin 23) : (fullJetRow16 col).Mem (fullJetMatrix 16 col) := by
  rw [← fullJetRow16_calc]
  exact fullJetBox_mem_eu 16 col
lemma fullJetRow18_calc (col : Fin 23) : fullJetBox 18 col = fullJetRow18 col := by
  revert col
  decide +kernel
lemma fullJetRow18_mem (col : Fin 23) : (fullJetRow18 col).Mem (fullJetMatrix 18 col) := by
  rw [← fullJetRow18_calc]
  exact fullJetBox_mem_eu 18 col
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
  · exact fullJetRow14_mem_eu col
  · exact fullJetRow15_mem_eu col
  · exact fullJetRow16_mem col
  · exact fullJetRow17_mem_eu col
  · exact fullJetRow18_mem col
  · exact fullJetRow19_mem_eu col
lemma RBox_mem (i j : Fin 20) : (RBox i j).Mem (Construction.R i j) := jetMatrixTable_mem i ⟨j.val+2,by omega⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
omit [Fintype n] in
lemma matrixOne_mem [DecidableEq n] (i j : n) : (matrixOne i j).Mem ((1:Matrix n n ℝ) i j) := by
  simpa only [matrixOne,Matrix.one_apply,Int.cast_ite,Int.cast_zero,Int.cast_one] using
    RI.mem_point (if i=j then 1 else 0)

end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma plusBlockBox_mem_eu_oai (i j : Fin 20) : (plusBlockBox i j).Mem ((1 + Construction.R) i j) :=
  RI.mem_add (matrixOne_mem i j) (RBox_mem i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.plusBlockBox_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.plusBlockBox_mem_eu_oai
