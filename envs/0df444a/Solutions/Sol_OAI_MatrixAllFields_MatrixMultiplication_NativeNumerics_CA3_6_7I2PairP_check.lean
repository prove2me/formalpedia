-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:33:06.273861+00:00
-- url     : https://prove2.me/submissions/75c09030-02ac-4cde-8751-01c6681b4a13

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_6_7I2PairP_check_0_0

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I2Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA3_6_7I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,1),(k,l))) (CA3_6_7I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,2),(k,l))) (CA3_6_7I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,3),(k,l))) (CA3_6_7I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,4),(k,l))) (CA3_6_7I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,5),(k,l))) (CA3_6_7I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,0),(k,l))) (CA3_6_7I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,1),(k,l))) (CA3_6_7I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,2),(k,l))) (CA3_6_7I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,3),(k,l))) (CA3_6_7I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,4),(k,l))) (CA3_6_7I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((1,5),(k,l))) (CA3_6_7I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,0),(k,l))) (CA3_6_7I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,1),(k,l))) (CA3_6_7I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,2),(k,l))) (CA3_6_7I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,3),(k,l))) (CA3_6_7I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,4),(k,l))) (CA3_6_7I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((2,5),(k,l))) (CA3_6_7I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,0),(k,l))) (CA3_6_7I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,1),(k,l))) (CA3_6_7I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,2),(k,l))) (CA3_6_7I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,3),(k,l))) (CA3_6_7I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,4),(k,l))) (CA3_6_7I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((3,5),(k,l))) (CA3_6_7I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,0),(k,l))) (CA3_6_7I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,1),(k,l))) (CA3_6_7I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,2),(k,l))) (CA3_6_7I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,3),(k,l))) (CA3_6_7I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,4),(k,l))) (CA3_6_7I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((4,5),(k,l))) (CA3_6_7I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,0),(k,l))) (CA3_6_7I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,1),(k,l))) (CA3_6_7I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,2),(k,l))) (CA3_6_7I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,3),(k,l))) (CA3_6_7I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,4),(k,l))) (CA3_6_7I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((5,5),(k,l))) (CA3_6_7I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA3_6_7I2PairP_check_oai (a : PairSlot × PairSlot) : contains (CA3_6_7I2PairRaw a) (CA3_6_7I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA3_6_7I2PairP_check_0_0 k l) (CA3_6_7I2PairP_check_0_1 k l) (CA3_6_7I2PairP_check_0_2 k l) (CA3_6_7I2PairP_check_0_3 k l) (CA3_6_7I2PairP_check_0_4 k l) (CA3_6_7I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA3_6_7I2PairP_check_1_0 k l) (CA3_6_7I2PairP_check_1_1 k l) (CA3_6_7I2PairP_check_1_2 k l) (CA3_6_7I2PairP_check_1_3 k l) (CA3_6_7I2PairP_check_1_4 k l) (CA3_6_7I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA3_6_7I2PairP_check_2_0 k l) (CA3_6_7I2PairP_check_2_1 k l) (CA3_6_7I2PairP_check_2_2 k l) (CA3_6_7I2PairP_check_2_3 k l) (CA3_6_7I2PairP_check_2_4 k l) (CA3_6_7I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA3_6_7I2PairP_check_3_0 k l) (CA3_6_7I2PairP_check_3_1 k l) (CA3_6_7I2PairP_check_3_2 k l) (CA3_6_7I2PairP_check_3_3 k l) (CA3_6_7I2PairP_check_3_4 k l) (CA3_6_7I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA3_6_7I2PairP_check_4_0 k l) (CA3_6_7I2PairP_check_4_1 k l) (CA3_6_7I2PairP_check_4_2 k l) (CA3_6_7I2PairP_check_4_3 k l) (CA3_6_7I2PairP_check_4_4 k l) (CA3_6_7I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA3_6_7I2PairP_check_5_0 k l) (CA3_6_7I2PairP_check_5_1 k l) (CA3_6_7I2PairP_check_5_2 k l) (CA3_6_7I2PairP_check_5_3 k l) (CA3_6_7I2PairP_check_5_4 k l) (CA3_6_7I2PairP_check_5_5 k l)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check_oai
