-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:37:33.964532+00:00
-- url     : https://prove2.me/submissions/959ab7fc-b28e-4d28-a62d-3756508e3896

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UminusTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UplusCachedBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma gammaBox_mem (side : Fin 2) (i : Fin 3) (j : Fin 8) : (gammaBox side i j).Mem (gamma side i j) := by
  unfold gammaBox gamma
  split_ifs
  all_goals first
    | simpa using RI.mem_point 0
    | simpa using RI.mem_divNat (RI.mem_point 11) (by norm_num : 0<(25:ℕ))
    | simpa using RI.mem_neg (RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ)))
    | simpa using RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ))

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma UplusTableRow0_calc (j : Fin 8) : UplusCachedBox 0 j = UplusTableRow0 j := by
  revert j
  decide +kernel
lemma UplusTableRow1_calc (j : Fin 8) : UplusCachedBox 1 j = UplusTableRow1 j := by
  revert j
  decide +kernel
lemma UplusTableRow2_calc (j : Fin 8) : UplusCachedBox 2 j = UplusTableRow2 j := by
  revert j
  decide +kernel
lemma UplusTableRow3_calc (j : Fin 8) : UplusCachedBox 3 j = UplusTableRow3 j := by
  revert j
  decide +kernel
lemma UplusTableRow4_calc (j : Fin 8) : UplusCachedBox 4 j = UplusTableRow4 j := by
  revert j
  decide +kernel
lemma UplusTableRow5_calc (j : Fin 8) : UplusCachedBox 5 j = UplusTableRow5 j := by
  revert j
  decide +kernel
lemma UplusTableRow6_calc (j : Fin 8) : UplusCachedBox 6 j = UplusTableRow6 j := by
  revert j
  decide +kernel
lemma UplusTableRow7_calc (j : Fin 8) : UplusCachedBox 7 j = UplusTableRow7 j := by
  revert j
  decide +kernel
lemma UplusTableRow8_calc (j : Fin 8) : UplusCachedBox 8 j = UplusTableRow8 j := by
  revert j
  decide +kernel
lemma UplusTableRow9_calc (j : Fin 8) : UplusCachedBox 9 j = UplusTableRow9 j := by
  revert j
  decide +kernel
lemma UplusTableRow10_calc (j : Fin 8) : UplusCachedBox 10 j = UplusTableRow10 j := by
  revert j
  decide +kernel
lemma UplusTableRow11_calc (j : Fin 8) : UplusCachedBox 11 j = UplusTableRow11 j := by
  revert j
  decide +kernel
lemma UplusTableRow12_calc (j : Fin 8) : UplusCachedBox 12 j = UplusTableRow12 j := by
  revert j
  decide +kernel
lemma UplusTableRow13_calc (j : Fin 8) : UplusCachedBox 13 j = UplusTableRow13 j := by
  revert j
  decide +kernel
lemma UplusTableRow14_calc (j : Fin 8) : UplusCachedBox 14 j = UplusTableRow14 j := by
  revert j
  decide +kernel
lemma UplusTableRow15_calc (j : Fin 8) : UplusCachedBox 15 j = UplusTableRow15 j := by
  revert j
  decide +kernel
lemma UplusTableRow16_calc (j : Fin 8) : UplusCachedBox 16 j = UplusTableRow16 j := by
  revert j
  decide +kernel
lemma UplusTableRow17_calc (j : Fin 8) : UplusCachedBox 17 j = UplusTableRow17 j := by
  revert j
  decide +kernel
lemma UplusTableRow18_calc (j : Fin 8) : UplusCachedBox 18 j = UplusTableRow18 j := by
  revert j
  decide +kernel
lemma UplusTableRow19_calc (j : Fin 8) : UplusCachedBox 19 j = UplusTableRow19 j := by
  revert j
  decide +kernel
lemma UplusTable_calc (i : Fin 20) (j : Fin 8) : UplusCachedBox i j = UplusTable i j := by
  fin_cases i
  · exact UplusTableRow0_calc j
  · exact UplusTableRow1_calc j
  · exact UplusTableRow2_calc j
  · exact UplusTableRow3_calc j
  · exact UplusTableRow4_calc j
  · exact UplusTableRow5_calc j
  · exact UplusTableRow6_calc j
  · exact UplusTableRow7_calc j
  · exact UplusTableRow8_calc j
  · exact UplusTableRow9_calc j
  · exact UplusTableRow10_calc j
  · exact UplusTableRow11_calc j
  · exact UplusTableRow12_calc j
  · exact UplusTableRow13_calc j
  · exact UplusTableRow14_calc j
  · exact UplusTableRow15_calc j
  · exact UplusTableRow16_calc j
  · exact UplusTableRow17_calc j
  · exact UplusTableRow18_calc j
  · exact UplusTableRow19_calc j
lemma UplusTable_mem (i : Fin 20) (j : Fin 8) : (UplusTable i j).Mem (Uplus i j) := by
  rw [← UplusTable_calc]
  exact UplusCachedBox_mem_x i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma A1CachedBox_mem (i : Fin 23) (j : Fin 8) : (A1CachedBox i j).Mem (Acoefficient 0 i j) := by
  unfold A1CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_add (UplusTable_mem ⟨i.val-2,by omega⟩ j) (UminusTable_mem_x ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A1TableRow0_calc (j : Fin 8) : A1CachedBox 0 j = A1TableRow0 j := by
  revert j
  decide +kernel
lemma A1TableRow1_calc (j : Fin 8) : A1CachedBox 1 j = A1TableRow1 j := by
  revert j
  decide +kernel
lemma A1TableRow2_calc (j : Fin 8) : A1CachedBox 2 j = A1TableRow2 j := by
  revert j
  decide +kernel
lemma A1TableRow3_calc (j : Fin 8) : A1CachedBox 3 j = A1TableRow3 j := by
  revert j
  decide +kernel
lemma A1TableRow4_calc (j : Fin 8) : A1CachedBox 4 j = A1TableRow4 j := by
  revert j
  decide +kernel
lemma A1TableRow5_calc (j : Fin 8) : A1CachedBox 5 j = A1TableRow5 j := by
  revert j
  decide +kernel
lemma A1TableRow6_calc (j : Fin 8) : A1CachedBox 6 j = A1TableRow6 j := by
  revert j
  decide +kernel
lemma A1TableRow7_calc (j : Fin 8) : A1CachedBox 7 j = A1TableRow7 j := by
  revert j
  decide +kernel
lemma A1TableRow8_calc (j : Fin 8) : A1CachedBox 8 j = A1TableRow8 j := by
  revert j
  decide +kernel
lemma A1TableRow9_calc (j : Fin 8) : A1CachedBox 9 j = A1TableRow9 j := by
  revert j
  decide +kernel
lemma A1TableRow10_calc (j : Fin 8) : A1CachedBox 10 j = A1TableRow10 j := by
  revert j
  decide +kernel
lemma A1TableRow11_calc (j : Fin 8) : A1CachedBox 11 j = A1TableRow11 j := by
  revert j
  decide +kernel
lemma A1TableRow12_calc (j : Fin 8) : A1CachedBox 12 j = A1TableRow12 j := by
  revert j
  decide +kernel
lemma A1TableRow13_calc (j : Fin 8) : A1CachedBox 13 j = A1TableRow13 j := by
  revert j
  decide +kernel
lemma A1TableRow14_calc (j : Fin 8) : A1CachedBox 14 j = A1TableRow14 j := by
  revert j
  decide +kernel
lemma A1TableRow15_calc (j : Fin 8) : A1CachedBox 15 j = A1TableRow15 j := by
  revert j
  decide +kernel
lemma A1TableRow16_calc (j : Fin 8) : A1CachedBox 16 j = A1TableRow16 j := by
  revert j
  decide +kernel
lemma A1TableRow17_calc (j : Fin 8) : A1CachedBox 17 j = A1TableRow17 j := by
  revert j
  decide +kernel
lemma A1TableRow18_calc (j : Fin 8) : A1CachedBox 18 j = A1TableRow18 j := by
  revert j
  decide +kernel
lemma A1TableRow19_calc (j : Fin 8) : A1CachedBox 19 j = A1TableRow19 j := by
  revert j
  decide +kernel
lemma A1TableRow20_calc (j : Fin 8) : A1CachedBox 20 j = A1TableRow20 j := by
  revert j
  decide +kernel
lemma A1TableRow21_calc (j : Fin 8) : A1CachedBox 21 j = A1TableRow21 j := by
  revert j
  decide +kernel
lemma A1TableRow22_calc (j : Fin 8) : A1CachedBox 22 j = A1TableRow22 j := by
  revert j
  decide +kernel
lemma A1Table_calc (i : Fin 23) (j : Fin 8) : A1CachedBox i j = A1Table i j := by
  fin_cases i
  · exact A1TableRow0_calc j
  · exact A1TableRow1_calc j
  · exact A1TableRow2_calc j
  · exact A1TableRow3_calc j
  · exact A1TableRow4_calc j
  · exact A1TableRow5_calc j
  · exact A1TableRow6_calc j
  · exact A1TableRow7_calc j
  · exact A1TableRow8_calc j
  · exact A1TableRow9_calc j
  · exact A1TableRow10_calc j
  · exact A1TableRow11_calc j
  · exact A1TableRow12_calc j
  · exact A1TableRow13_calc j
  · exact A1TableRow14_calc j
  · exact A1TableRow15_calc j
  · exact A1TableRow16_calc j
  · exact A1TableRow17_calc j
  · exact A1TableRow18_calc j
  · exact A1TableRow19_calc j
  · exact A1TableRow20_calc j
  · exact A1TableRow21_calc j
  · exact A1TableRow22_calc j
lemma A1Table_mem (i : Fin 23) (j : Fin 8) : (A1Table i j).Mem ((Acoefficient 0) i j) := by
  rw [← A1Table_calc]
  exact A1CachedBox_mem i j
lemma A2CachedBox_mem (i : Fin 23) (j : Fin 8) : (A2CachedBox i j).Mem (Acoefficient 1 i j) := by
  unfold A2CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_sub (UplusTable_mem ⟨i.val-2,by omega⟩ j) (UminusTable_mem_x ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A2TableRow0_calc (j : Fin 8) : A2CachedBox 0 j = A2TableRow0 j := by
  revert j
  decide +kernel
lemma A2TableRow1_calc (j : Fin 8) : A2CachedBox 1 j = A2TableRow1 j := by
  revert j
  decide +kernel
lemma A2TableRow2_calc (j : Fin 8) : A2CachedBox 2 j = A2TableRow2 j := by
  revert j
  decide +kernel
lemma A2TableRow3_calc (j : Fin 8) : A2CachedBox 3 j = A2TableRow3 j := by
  revert j
  decide +kernel
lemma A2TableRow4_calc (j : Fin 8) : A2CachedBox 4 j = A2TableRow4 j := by
  revert j
  decide +kernel
lemma A2TableRow5_calc (j : Fin 8) : A2CachedBox 5 j = A2TableRow5 j := by
  revert j
  decide +kernel
lemma A2TableRow6_calc (j : Fin 8) : A2CachedBox 6 j = A2TableRow6 j := by
  revert j
  decide +kernel
lemma A2TableRow7_calc (j : Fin 8) : A2CachedBox 7 j = A2TableRow7 j := by
  revert j
  decide +kernel
lemma A2TableRow8_calc (j : Fin 8) : A2CachedBox 8 j = A2TableRow8 j := by
  revert j
  decide +kernel
lemma A2TableRow9_calc (j : Fin 8) : A2CachedBox 9 j = A2TableRow9 j := by
  revert j
  decide +kernel
lemma A2TableRow10_calc (j : Fin 8) : A2CachedBox 10 j = A2TableRow10 j := by
  revert j
  decide +kernel
lemma A2TableRow11_calc (j : Fin 8) : A2CachedBox 11 j = A2TableRow11 j := by
  revert j
  decide +kernel
lemma A2TableRow12_calc (j : Fin 8) : A2CachedBox 12 j = A2TableRow12 j := by
  revert j
  decide +kernel
lemma A2TableRow13_calc (j : Fin 8) : A2CachedBox 13 j = A2TableRow13 j := by
  revert j
  decide +kernel
lemma A2TableRow14_calc (j : Fin 8) : A2CachedBox 14 j = A2TableRow14 j := by
  revert j
  decide +kernel
lemma A2TableRow15_calc (j : Fin 8) : A2CachedBox 15 j = A2TableRow15 j := by
  revert j
  decide +kernel
lemma A2TableRow16_calc (j : Fin 8) : A2CachedBox 16 j = A2TableRow16 j := by
  revert j
  decide +kernel
lemma A2TableRow17_calc (j : Fin 8) : A2CachedBox 17 j = A2TableRow17 j := by
  revert j
  decide +kernel
lemma A2TableRow18_calc (j : Fin 8) : A2CachedBox 18 j = A2TableRow18 j := by
  revert j
  decide +kernel
lemma A2TableRow19_calc (j : Fin 8) : A2CachedBox 19 j = A2TableRow19 j := by
  revert j
  decide +kernel
lemma A2TableRow20_calc (j : Fin 8) : A2CachedBox 20 j = A2TableRow20 j := by
  revert j
  decide +kernel
lemma A2TableRow21_calc (j : Fin 8) : A2CachedBox 21 j = A2TableRow21 j := by
  revert j
  decide +kernel
lemma A2TableRow22_calc (j : Fin 8) : A2CachedBox 22 j = A2TableRow22 j := by
  revert j
  decide +kernel
lemma A2Table_calc (i : Fin 23) (j : Fin 8) : A2CachedBox i j = A2Table i j := by
  fin_cases i
  · exact A2TableRow0_calc j
  · exact A2TableRow1_calc j
  · exact A2TableRow2_calc j
  · exact A2TableRow3_calc j
  · exact A2TableRow4_calc j
  · exact A2TableRow5_calc j
  · exact A2TableRow6_calc j
  · exact A2TableRow7_calc j
  · exact A2TableRow8_calc j
  · exact A2TableRow9_calc j
  · exact A2TableRow10_calc j
  · exact A2TableRow11_calc j
  · exact A2TableRow12_calc j
  · exact A2TableRow13_calc j
  · exact A2TableRow14_calc j
  · exact A2TableRow15_calc j
  · exact A2TableRow16_calc j
  · exact A2TableRow17_calc j
  · exact A2TableRow18_calc j
  · exact A2TableRow19_calc j
  · exact A2TableRow20_calc j
  · exact A2TableRow21_calc j
  · exact A2TableRow22_calc j
lemma A2Table_mem (i : Fin 23) (j : Fin 8) : (A2Table i j).Mem ((Acoefficient 1) i j) := by
  rw [← A2Table_calc]
  exact A2CachedBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ATable_mem (side : Fin 2) (i : Fin 23) (r : Fin 8) : (ATable side i r).Mem (Acoefficient side i r) := by
  fin_cases side
  · exact A1Table_mem i r
  · exact A2Table_mem i r

lemma spectrumBox_mem_x_oai (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumBox side q j r).Mem (finiteSpectrum side q j r) := by
  unfold spectrumBox finiteSpectrum
  split_ifs
  · exact CI.mem_mul (atomPolynomial_coeff_mem j) (CI.mem_ofReal (ATable_mem side 22 r))
  · exact CI.mem_sum (fun col => CI.mem_mul (columnTable_mem_x ⟨col.val,by omega⟩ j) (CI.mem_ofReal (ATable_mem side ⟨col.val,by omega⟩ r)))

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_x_oai
