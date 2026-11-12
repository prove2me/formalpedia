-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:46.976421+00:00
-- url     : https://prove2.me/submissions/31284090-907a-4659-a4c2-c80a35ff7d20

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010
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
lemma RBox_mem (i j : Fin 20) : (RBox i j).Mem (Construction.R i j) := jetMatrixTable_mem i ⟨j.val+2,by omega⟩
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

lemma RI.mem_singleton (z : ℤ) : (RI.singleton z).Mem ((z:ℝ)/(scale:ℝ)) := by
  have hs : (scale:ℝ) ≠ 0 := scale_pos.ne'
  have hh : (scale:ℝ)*((z:ℝ)/(scale:ℝ)) = (z:ℝ) := by field_simp
  constructor <;> dsimp only [RI.Mem,RI.singleton] <;> rw [hh]

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
omit [Fintype m] [Fintype p] in
lemma matrixMul_mem {a : m → n → RI} {b : n → p → RI}
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} (ha : ∀ i j, (a i j).Mem (A i j))
    (hb : ∀ i j, (b i j).Mem (B i j)) (i : m) (j : p) :
    (matrixMul a b i j).Mem ((A*B) i j) :=
  RI.mem_sum (fun k => RI.mem_mul (ha i k) (hb k j))
omit [Fintype n] in
lemma matrixOne_mem [DecidableEq n] (i j : n) : (matrixOne i j).Mem ((1:Matrix n n ℝ) i j) := by
  simpa only [matrixOne,Matrix.one_apply,Int.cast_ite,Int.cast_zero,Int.cast_one] using
    RI.mem_point (if i=j then 1 else 0)

end AtomicTriangular.Interval
end

end OAI
end

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
lemma plusBlockBox_mem (i j : Fin 20) : (plusBlockBox i j).Mem ((1 + Construction.R) i j) :=
  RI.mem_add (matrixOne_mem i j) (RBox_mem i j)
lemma plusApproxBox_mem (i j : Fin 20) : (plusApproxBox i j).Mem (plusApprox i j) := RI.mem_singleton _
lemma plusResidualBox_mem_x_oai (i j : Fin 20) :
    (plusResidualBox i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) :=
  RI.mem_sub (matrixMul_mem plusApproxBox_mem plusBlockBox_mem i j) (matrixOne_mem i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x_oai
