-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourCoupledBasis_complex_complete_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:54:19.829684+00:00
-- url     : https://prove2.me/submissions/64c87966-f666-4c56-9064-b30d324e3588

import Mathlib
import Definitions.Def_OAIQ050L022

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledInclusion_isometry (Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q r hr = 1 := by
  ext n m
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairCoupledInclusion,Matrix.one_apply]
  by_cases h : n=m
  · subst m
    rw [ite_eq_left rfl]
    simpa only [pow_two,vectorNormSq] using pairCoupledWedge_norm Q r n.val hr ho (by omega)
  · rw [ite_eq_right h]
    exact pairCoupledWedge_orthogonal Q r r n.val m.val hr hr ho ho
      (Or.inr (fun he => h (Fin.ext he)))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tensorPairInclusion_isometry (A Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q r hr = 1 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,pairCoupledInclusion_isometry Q r hr ho,
    Matrix.one_kronecker_one]

theorem isometry_vectorNormSq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix I J ℝ) (hW : Wᵀ*W=1) (f : J → ℝ) :
    vectorNormSq (W *ᵥ f) = vectorNormSq f := by
  unfold vectorNormSq
  simp only [pow_two]
  have hp (v : J → ℝ) (w : I → ℝ) :
      (∑ i, (W *ᵥ v) i*w i) = ∑ i, v i*(Wᵀ *ᵥ w) i := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj; ring
  rw [hp,Matrix.mulVec_mulVec,hW,Matrix.one_mulVec]

theorem phased_generic_norm (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    vectorNormSq ((-1 : ℝ)^z • genericUnitDescendant A B z hA hB n) = 1 := by
  unfold vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  have h : ((-1 : ℝ)^z)^2 = 1 := by rw [← pow_mul,mul_comm z 2,pow_mul]; norm_num
  rw [h,one_mul]
  exact genericUnitDescendant_norm A B z n hA hB hn

theorem fourBodyCopy_norm (Q r D n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hn : n ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)) :
    vectorNormSq (fourBodyCopy Q r D hr hA hB n) = 1 := by
  rw [fourBodyCopy,isometry_vectorNormSq _ (tensorPairInclusion_isometry _ Q r hr ho)]
  exact phased_generic_norm _ _ _ _ hA hB hn

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericCoupledIndex_card (A B : ℕ) :
    Fintype.card (GenericCoupledIndex A B) = Fintype.card (SpinIndex A B) := by
  have hr : (Fintype.card (GenericCoupledIndex A B) : ℝ) =
      (Fintype.card (SpinIndex A B) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (min A B+1)) :
        ((genericCoupledWeight A B z.val+1 : ℕ) : ℝ) = A+B+1-2*(z.val : ℝ) := by
      have hz := z.isLt
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z.val ≤ A+B)]
      push_cast
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rcases le_total A B with h | h
    · rw [Nat.min_eq_left h]; ring
    · rw [Nat.min_eq_right h]; ring
  exact_mod_cast hr

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem pairCoupledInclusion_cross (Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q s hs = 0 := by
  ext n m
  exact pairCoupledWedge_orthogonal Q r s n.val m.val hr hs hor hos (Or.inl hne)

theorem tensorPairInclusion_cross (A Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q s hs = 0 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,pairCoupledInclusion_cross Q r s hr hs hor hos hne]
  simp

theorem fourBodyCopy_orthogonal_pair (Q r s D E n m : ℕ)
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s) (hne : r ≠ s)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-s ≤ 2*Q-2) (hD : E-s ≤ genericCoupledWeight Q Q s) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q s E hs hC hD m i) = 0 := by
  have hp {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
      (A : Matrix I J ℝ) (B : Matrix I K ℝ) (v : J → ℝ) (w : K → ℝ) :
      (∑ i, (A *ᵥ v) i * (B *ᵥ w) i) = ∑ j, v j * ((Aᵀ*B) *ᵥ w) j := by
    change (A *ᵥ v) ⬝ᵥ (B *ᵥ w) = v ⬝ᵥ ((Aᵀ*B) *ᵥ w)
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp,tensorPairInclusion_cross _ Q r s hr hs hor hos hne]
  simp

theorem fourBodyCopy_orthogonal_outer (Q r D E n m : ℕ)
    (hr : r ≤ Q) (hor : Odd r) (hrD : r ≤ D) (hrE : r ≤ E)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-r ≤ 2*Q-2) (hD : E-r ≤ genericCoupledWeight Q Q r)
    (hne : D ≠ E ∨ n ≠ m) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q r E hr hC hD m i) = 0 := by
  have hp {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
      (A : Matrix I J ℝ) (h : Aᵀ*A=1) (v w : J → ℝ) :
      (∑ i, (A *ᵥ v) i * (A *ᵥ w) i) = ∑ j, v j*w j := by
    change (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w
    rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp _ (tensorPairInclusion_isometry _ Q r hr hor)]
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((-1 : ℝ)^(D-r) * (-1 : ℝ)^(E-r)) *
      (∑ i, genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB n i *
        genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (E-r) hC hD m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by
      rw [genericUnitDescendant_orthogonal _ _ _ _ _ _ hA hB hC hD (by
        rcases hne with h | h
        · left; omega
        · exact Or.inr h),mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem fourCoupledIndex_card (Q : ℕ) :
    Fintype.card (FourCoupledIndex Q) = Fintype.card (Fin (2*Q-2+1) × WedgePairIndex Q) := by
  rw [Fintype.card_sigma]
  simp_rw [genericCoupledIndex_card,Fintype.card_prod,Fintype.card_fin]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Fintype.card_sigma,Fintype.card_fin] using pairCoupledIndex_card Q

theorem fourCoupledBasis_isometry (Q : ℕ) :
    (fourCoupledBasis Q)ᵀ * fourCoupledBasis Q = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,fourCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      fourBodyCopy_norm Q (oddPairDeficit s.1) (oddPairDeficit s.1+s.2.1.val)
        s.2.2.val (oddPairDeficit_le s.1) (oddPairDeficit_odd s.1) _ _
        (by have := s.2.2.isLt; simpa only [Nat.add_sub_cancel_left] using Nat.le_of_lt_succ this)
  · rw [ite_eq_right h]
    rcases s with ⟨r,⟨z,n⟩⟩
    rcases t with ⟨s,⟨w,m⟩⟩
    dsimp only at *
    by_cases hrs : r=s
    · subst s
      apply fourBodyCopy_orthogonal_outer _ _ _ _ _ _ _ (oddPairDeficit_odd r)
        (by omega) (by omega)
      by_cases hzw : z=w
      · subst w
        right
        intro he
        exact h (by have hn : n=m := Fin.ext he; subst m; rfl)
      · left
        intro he
        exact hzw (Fin.ext (by omega))
    · apply fourBodyCopy_orthogonal_pair _ _ _ _ _ _ _ _ _
        (oddPairDeficit_odd r) (oddPairDeficit_odd s)
      intro he
      exact hrs (Fin.ext (by dsimp [oddPairDeficit] at he; omega))

theorem fourCoupledBasis_complete (Q : ℕ) :
    fourCoupledBasis Q * (fourCoupledBasis Q)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := FourCoupledIndex Q)
    (n := Fin (2*Q-2+1) × WedgePairIndex Q) (R := ℝ)
    (fourCoupledIndex_card Q)).mp (fourCoupledBasis_isometry Q)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem fourCoupledBasis_complex_complete_s50_oai (Q : ℕ) :
    (fourCoupledBasis Q).map Complex.ofReal * ((fourCoupledBasis Q).map Complex.ofReal)ᴴ = 1 := by
  rw [real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (fourCoupledBasis_complete Q)

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.fourCoupledBasis_complex_complete_s50_oai := @OAI.Laughlin.Spin.fourCoupledBasis_complex_complete_s50_oai
