-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.finiteApprox_norm_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:25:37.463202+00:00
-- url     : https://prove2.me/submissions/8b6d6da9-685c-4da0-97dd-cfa496ac09eb

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UminusTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UplusCachedBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

lemma RI.mem_min {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imin b).Mem (min x y) := by
  constructor
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.1 hy.1
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.2 hy.2

end
end AtomicTriangular.Interval

end
end

end OAI
end

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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma box_linear_lower {B x c : ℝ} (_hB : 0 ≤ B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    B * min 0 c ≤ c*x := by
  by_cases hc : 0 ≤ c
  · rw [min_eq_left hc]
    simpa using mul_nonneg hc hx
  · rw [min_eq_right (le_of_not_ge hc)]
    nlinarith

lemma triangle_linear_lower {B Z u a v c : ℝ} (_hB : 0 ≤ B) (hu : 0 ≤ u)
    (huB : u ≤ B) (ha : 0 ≤ a) (haZ : a ≤ Z*u) :
    B * min 0 (min v (v+Z*c)) ≤ v*u+c*a := by
  let q := min 0 (min v (v+Z*c))
  have hq0 : q ≤ 0 := min_le_left _ _
  have hqv : q ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hqc : q ≤ v+Z*c := (min_le_right _ _).trans (min_le_right _ _)
  have hqu : B*q ≤ u*q := mul_le_mul_of_nonpos_right huB hq0
  change B*q ≤ _
  by_cases hc : 0 ≤ c
  · have h1 := mul_le_mul_of_nonneg_right hqv hu
    have h2 := mul_nonneg hc ha
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hqc hu
    have h2 := mul_le_mul_of_nonpos_left haZ (le_of_not_ge hc)
    nlinarith

lemma rowLower_le (row e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    rowLower row ≤ ∑ j : Fin 8, row j*e j := by
  rcases he with ⟨z,w,d,u,a,r,p,hz,hzB,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,rfl⟩
  have h1 := box_linear_lower (by norm_num [Z] : 0 ≤ Z) hz hzB (c := row 0)
  have h2 := box_linear_lower (by norm_num [DeltaStar] : 0 ≤ DeltaStar) hd hdB (c := -row 2)
  have h3 := box_linear_lower (by norm_num [Wstar] : 0 ≤ Wstar) hw hwB (c := row 3+Z*row 2)
  have h4 := triangle_linear_lower (by norm_num [Ustar] : 0 ≤ Ustar) hu huB ha haB (v := row 5) (c := row 4)
  have h5 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hr hrB (c := row 6)
  have h6 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hp hpB (c := row 7)
  norm_num [Fin.sum_univ_succ, Fin.succ]
  change rowLower row ≤ row 0*z + (row 1 + (row 2*(Z*w-d) + (row 3*w + (row 4*a + (row 5*u + (row 6*r + row 7*p))))))
  unfold rowLower
  nlinarith [h1,h2,h3,h4,h5,h6]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
lemma WstarBox_mem : WstarBox.Mem Wstar := RI.mem_divNat (RI.mem_point 61) (by norm_num)
lemma DeltaStarBox_mem : DeltaStarBox.Mem DeltaStar := RI.mem_divNat (RI.mem_point 18) (by norm_num)
lemma UstarBox_mem : UstarBox.Mem Ustar := RI.mem_divNat (RI.mem_point 48) (by norm_num)
lemma PstarBox_mem : PstarBox.Mem Pstar := RI.mem_divNat (RI.mem_point 3) (by norm_num)
lemma rowLowerBox_mem {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ i, (a i).Mem (v i)) : (rowLowerBox a).Mem (rowLower v) := by
  have hz : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
  unfold rowLowerBox rowLower
  apply RI.mem_add
  · apply RI.mem_add
    · apply RI.mem_add
      · apply RI.mem_add
        · exact RI.mem_add (hv 1) (RI.mem_mul ZBox_mem (RI.mem_min hz (hv 0)))
        · exact RI.mem_mul DeltaStarBox_mem (RI.mem_min hz (RI.mem_neg (hv 2)))
      · exact RI.mem_mul WstarBox_mem (RI.mem_min hz (RI.mem_add (hv 3) (RI.mem_mul ZBox_mem (hv 2))))
    · exact RI.mem_mul UstarBox_mem (RI.mem_min hz (RI.mem_min (hv 5) (RI.mem_add (hv 5) (RI.mem_mul ZBox_mem (hv 4)))))
  · exact RI.mem_mul PstarBox_mem (RI.mem_add (RI.mem_min hz (hv 6)) (RI.mem_min hz (hv 7)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNormBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma rowAbs_bound {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ j, (a j).Mem (v j)) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    |∑ j : Fin 8, v j*e j| ≤ (rowAbsNumerator a : ℝ)/scale := by
  have h1 := (rowLowerBox_mem hv).1
  have h2 := (rowLowerBox_mem (fun j => RI.mem_neg (hv j))).1
  have h3 := rowLower_le v e he
  have h4 := rowLower_le (fun j => -v j) e he
  have heq : (∑ j : Fin 8, -v j*e j) = -(∑ j : Fin 8, v j*e j) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [heq] at h4
  have hb1 : (-(rowLowerBox a).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_left (-(rowLowerBox a).lo) _)
  have hb2 : (-(rowLowerBox (fun j => (a j).neg)).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_right (-(rowLowerBox a).lo) _)
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h3 scale_pos.le
    nlinarith
  · apply (le_div_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h4 scale_pos.le
    nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma A1AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A1Table i) = A1AbsNumerators i := by
  revert i
  decide +kernel
lemma A1_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j|) < (258/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j| ≤ (A1AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A1AbsNumerators_calc]
    exact rowAbs_bound (A1Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A1AbsNumerators i) < 258*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A1AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (258/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ) < 258*(scale:ℝ) := by exact_mod_cast hc
      linarith
lemma A2AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A2Table i) = A2AbsNumerators i := by
  revert i
  decide +kernel
lemma A2_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j|) < (280/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j| ≤ (A2AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A2AbsNumerators_calc]
    exact rowAbs_bound (A2Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A2AbsNumerators i) < 280*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A2AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (280/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ) < 280*(scale:ℝ) := by exact_mod_cast hc
      linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma finiteApprox_norm_x_oai (side : Fin 2) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    ‖finiteApprox side e‖ < 3 := by
  rw [l1_norm,tsum_fintype]
  have hb : (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) ≤
      ∑ i : Fin 23, |∑ j : Fin 8, Acoefficient side i j*e j| := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  change (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) < 3
  refine hb.trans_lt ?_
  fin_cases side
  · exact (A1_norm_bound e he).trans (by norm_num)
  · exact (A2_norm_bound e he).trans (by norm_num)

end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.finiteApprox_norm_x_oai := @OAI.AtomicTriangular.Construction.finiteApprox_norm_x_oai
