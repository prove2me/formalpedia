-- Prove2me | solution 1 for OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:56:57.225416+00:00
-- url     : https://prove2.me/submissions/7ce8142a-b43d-4fed-89b7-170dc607923e

import Mathlib
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021
import Theorems.Thm_OAI_Laughlin_Spin_threeBody_haar_diagonal_block_s50
import Theorems.Thm_OAI_Laughlin_Spin_threeBody_haar_offdiagonal_block_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_norm (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ i : PairOrbitalIndex Q, (coupledHighest Q z hQ hz i)^2) = 1 := by
  simp only [pow_two]
  unfold coupledHighest
  rw [sum_extendWeightSlice]
  simp_rw [extendWeightSlice_at,← pow_two]
  have hs := highestUnit_norm (2*Q-2) Q z (by omega) hz
  simpa only [← Fin.sum_univ_eq_sum_range] using hs

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_weight (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalWeight (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz =
      (coupledWeight Q z : ℝ) • coupledHighest Q z hQ hz := by
  rw [totalWeight_diagonal]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change ((2*Q-2 : ℕ)+ (Q : ℝ)-2*((i.1.val : ℝ)+i.2.val))*coupledHighest Q z hQ hz i =
    (coupledWeight Q z : ℝ)*coupledHighest Q z hQ hz i
  by_cases hi : i.1.val+i.2.val=z
  · have hc : (i.1.val : ℝ)+i.2.val=z := by exact_mod_cast hi
    rw [hc]
    congr 1
    unfold coupledWeight
    rw [Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),Nat.cast_sub (by omega : 2 ≤ 3*Q),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  · have he : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [he]; ring

theorem coupledHighest_raising_zero (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalRaise (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz = 0 := by
  apply extendWeightSlice_highest
  intro p
  exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt

theorem coupledDescendant_norm_pos (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : 0 < vectorNormSq (coupledDescendant Q z hQ hz n) := by
  apply descendant_norm_pos (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledWeight Q z) n
  · exact total_raise_lower_commutator _ _
  · exact total_weight_lower_commutator _ _
  · exact Matrix.transpose_transpose _
  · exact coupledHighest_weight Q z hQ hz
  · exact coupledHighest_raising_zero Q z hQ hz
  · change 0 < ∑ i, (coupledHighest Q z hQ hz i)^2
    rw [coupledHighest_norm Q z hQ hz]; norm_num
  · exact hn

theorem normalizedCoupledDescendant_norm (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : vectorNormSq (normalizedCoupledDescendant Q z hQ hz n) = 1 := by
  have hp := coupledDescendant_norm_pos Q z n hQ hz hn
  unfold normalizedCoupledDescendant vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  change (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ ^ 2 *
    vectorNormSq (coupledDescendant Q z hQ hz n) = 1
  rw [inv_pow,Real.sq_sqrt (le_of_lt hp),inv_mul_cancel₀ (ne_of_gt hp)]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Orthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_orthogonal (Q z w : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hzw : z ≠ w) :
    (∑ i, coupledHighest Q z hQ hz i*coupledHighest Q w hQ hw i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i.1.val+i.2.val=z
  · have hh : i.1.val+i.2.val ≠ w := by omega
    have hv : coupledHighest Q w hQ hw i = 0 :=
      extendWeightSlice_off (2*Q-2) Q w (by omega) hw _ i hh
    rw [hv,mul_zero]
  · have hv : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i he
    rw [hv,zero_mul]

theorem coupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) = 0 := by
  apply descendants_orthogonal (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledHighest Q w hQ hw)
    (coupledWeight Q w) (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (coupledHighest_weight Q w hQ hw)
    (coupledHighest_raising_zero Q z hQ hz) (coupledHighest_raising_zero Q w hQ hw) n m
  rcases hne with h | h
  · exact Or.inl (coupledHighest_orthogonal Q z w hQ hz hw h)
  · exact Or.inr h

theorem normalizedCoupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, normalizedCoupledDescendant Q z hQ hz n i *
      normalizedCoupledDescendant Q w hQ hw m i) = 0 := by
  unfold normalizedCoupledDescendant
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ *
      (Real.sqrt (vectorNormSq (coupledDescendant Q w hQ hw m)))⁻¹ *
      (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [coupledDescendant_orthogonal Q z w n m hQ hz hw hne,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledIndex_card (Q : ℕ) (hQ : 2 ≤ Q) :
    Fintype.card (CoupledIndex Q) = Fintype.card (PairOrbitalIndex Q) := by
  have hr : (Fintype.card (CoupledIndex Q) : ℝ) = (Fintype.card (PairOrbitalIndex Q) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (Q+1)) : ((coupledWeight Q z.val+1 : ℕ) : ℝ) = 3*(Q : ℝ)-1-2*z.val := by
      unfold coupledWeight
      rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub (by omega : 2*z.val ≤ 3*Q-2),
        Nat.cast_sub (by omega : 2 ≤ 3*Q)]
      push_cast; ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  exact_mod_cast hr

theorem coupledBasis_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (coupledBasisMatrix Q hQ)ᵀ * coupledBasisMatrix Q hQ = 1 := by
  ext s t
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply,coupledBasisMatrix,Matrix.one_apply]
  by_cases hst : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      normalizedCoupledDescendant_norm Q s.1.val s.2.val hQ (by omega) (by omega)
  · rw [ite_eq_right hst]
    apply normalizedCoupledDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      apply hst
      have he : n=m := Fin.ext hnm
      rw [he]
    · left
      intro h
      exact hzw (Fin.ext h)

theorem coupledBasis_complete (Q : ℕ) (hQ : 2 ≤ Q) :
    coupledBasisMatrix Q hQ * (coupledBasisMatrix Q hQ)ᵀ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq (m := CoupledIndex Q) (n := PairOrbitalIndex Q)
    (R := ℝ) (coupledIndex_card Q hQ)).mp (coupledBasis_isometry Q hQ)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledSelector_sum (Q : ℕ) : (∑ z : Fin (Q+1), coupledSelector Q z) = 1 := by
  ext s t
  by_cases h : s=t
  · subst t
    simp [coupledSelector,Matrix.sum_apply]
  · simp [coupledSelector,Matrix.sum_apply,h]

theorem threeSpinProjector_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), threeSpinProjector Q hQ z) = 1 := by
  unfold threeSpinProjector
  rw [← Matrix.sum_mul,← Matrix.mul_sum,coupledSelector_sum,Matrix.mul_one,coupledBasis_complete Q hQ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem threeSpinProjector_complex_factor (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeSpinProjector Q hQ z).map Complex.ofReal =
      threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ := by
  funext i j
  change (↑(∑ s, (coupledBasisMatrix Q hQ * coupledSelector Q z) i s *
    coupledBasisMatrix Q hQ j s) : ℂ) = _
  simp only [coupledSelector,Matrix.mul_diagonal]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,threeCoupledInclusion,
    Complex.star_def,Complex.conj_ofReal]
  rw [Fintype.sum_sigma]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Complex.ofReal_sum,
    Complex.ofReal_mul,coupledBasisMatrix]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HaarNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix
open Rotation

theorem threeSpinProjector_complex_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), (threeSpinProjector Q hQ z).map Complex.ofReal) = 1 := by
  funext i j
  have h := congrArg Complex.ofReal (congrFun (congrFun (threeSpinProjector_sum Q hQ) i) j)
  simpa only [Matrix.sum_apply,Matrix.map_apply,Complex.ofReal_sum,Matrix.one_apply,
    apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h

theorem physical_threeBody_haar_normalization_s50_oai (Q : ℕ) (hQ : 2 ≤ Q)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M) =
      ∑ z : Fin (Q+1),
        (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/
          (coupledWeight Q z.val+1 : ℕ)) • (threeSpinProjector Q hQ z).map Complex.ofReal := by
  let H := matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M)
  let R := fun z => (threeSpinProjector Q hQ z).map Complex.ofReal
  have hblock (z w : Fin (Q+1)) : R z*H*R w =
      if z=w then (Matrix.trace (R z*M)/(coupledWeight Q z.val+1 : ℕ)) • R z else 0 := by
    change (threeSpinProjector Q hQ z).map Complex.ofReal*H*
      (threeSpinProjector Q hQ w).map Complex.ofReal = _
    rw [threeSpinProjector_complex_factor,threeSpinProjector_complex_factor]
    have he : threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ*H*
        (threeCoupledInclusion Q hQ w*(threeCoupledInclusion Q hQ w)ᴴ) =
        threeCoupledInclusion Q hQ z*
          ((threeCoupledInclusion Q hQ z)ᴴ*H*threeCoupledInclusion Q hQ w)*
          (threeCoupledInclusion Q hQ w)ᴴ := by simp only [Matrix.mul_assoc]
    rw [he]
    by_cases hzw : z=w
    · subst w
      rw [ite_eq_left rfl]
      change _ = (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/_) • _
      rw [threeBody_haar_diagonal_block_s50,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
        ← threeSpinProjector_complex_factor]
    · rw [ite_eq_right hzw,threeBody_haar_offdiagonal_block_s50 Q hQ z w hzw,Matrix.mul_zero,Matrix.zero_mul]
  calc
    _ = (∑ z, R z)*H*(∑ w, R w) := by
      change H = _
      rw [show (∑ z, R z)=1 from threeSpinProjector_complex_sum Q hQ,Matrix.one_mul,Matrix.mul_one]
    _ = ∑ z, ∑ w, R z*H*R w := by rw [Matrix.sum_mul,Matrix.sum_mul]; simp only [Matrix.mul_sum]
    _ = _ := by simp only [hblock,Finset.sum_ite_eq,Finset.mem_univ,ite_true,R]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50_oai := @OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50_oai
