-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourPairEmbedding_resolution_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:55:04.162081+00:00
-- url     : https://prove2.me/submissions/930ba6a5-c11c-4db7-84ab-6c4c5a99c50f

import Mathlib
import Definitions.Def_OAIQ050L022

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourBodyCopy_coordinate (Q r D n : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q) :
    fourBodyCopy Q r D hr hA hB n (p,i) =
      ∑ b : Fin (genericCoupledWeight Q Q r+1), pairCoupledWedge Q r hr b.val i *
        ((-1 : ℝ)^(D-r) * genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
          (D-r) hA hB n (p,b)) := by
  simp only [fourBodyCopy,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensorPairInclusion,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,ite_mul,
    one_mul,zero_mul,pairCoupledInclusion,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

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

theorem genericCoupledBasis_isometry (A B : ℕ) :
    (genericCoupledBasis A B)ᵀ * genericCoupledBasis A B = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,genericCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      genericUnitDescendant_norm A B s.1.val s.2.val _ _ (by have := s.2.isLt; omega)
  · rw [ite_eq_right h]
    apply genericUnitDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      exact h (by have he : n=m := Fin.ext hnm; subst m; rfl)
    · left
      intro he
      exact hzw (Fin.ext he)

theorem genericCoupledBasis_complete (A B : ℕ) :
    genericCoupledBasis A B * (genericCoupledBasis A B)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := GenericCoupledIndex A B) (n := SpinIndex A B) (R := ℝ) (genericCoupledIndex_card A B)).mp
    (genericCoupledBasis_isometry A B)

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

theorem fourWedgeInclusion_factor (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    fourWedgeInclusion Q r D hr hA hB =
      ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
        (pairCoupledInclusion Q r hr).map Complex.ofReal) *
        physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB := by
  ext i n
  rw [fourWedgeInclusion,fourBodyCopy_coordinate]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_one,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,ite_mul,one_mul,zero_mul,physicalCoupledInclusion,
    Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,genericCoupledInclusion,pairCoupledInclusion]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_GenericPhysicalResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCoupledInclusion_complete (A B : ℕ) :
    (∑ z : Fin (min A B+1),
      physicalCoupledInclusion A B z.val (by omega) (by omega) *
        (physicalCoupledInclusion A B z.val (by omega) (by omega))ᴴ) = 1 := by
  have hc : (genericCoupledBasis A B).map Complex.ofReal *
      ((genericCoupledBasis A B).map Complex.ofReal)ᴴ = 1 := by
    ext i j
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledBasis_complete A B) i) j)
    simpa only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
      Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul,Matrix.one_apply,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h
  rw [← hc]
  ext i j
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply,
    Fintype.sum_sigma,physicalCoupledInclusion,Matrix.smul_apply,smul_eq_mul,
    genericCoupledInclusion,genericCoupledBasis]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro n hn
  have hp : ((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)=1 := by
    simp only [star_pow,star_neg,star_one,← mul_pow]
    norm_num
  simp only [star_mul]
  calc
    _ = (((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)) *
      ((genericUnitDescendant A B z.val (by omega) (by omega) n.val i : ℂ)*
        star (genericUnitDescendant A B z.val (by omega) (by omega) n.val j : ℂ)) := by ring
    _ = _ := by rw [hp,one_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TargetResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourPairEmbedding_resolution_s50_oai (Q r : ℕ) (hr : r ≤ Q) :
    fourPairEmbedding Q r hr*(fourPairEmbedding Q r hr)ᴴ =
      ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
        fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega) *
          (fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega))ᴴ := by
  let F : Matrix (FourWedgeIndex Q) (SpinIndex (2*Q-2) (genericCoupledWeight Q Q r)) ℂ :=
    fourPairEmbedding Q r hr
  have hA (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ 2*Q-2 :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_left _ _)
  have hB (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ genericCoupledWeight Q Q r :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_right _ _)
  have hp (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) :
      fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z) *
        (fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z))ᴴ =
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
    rw [fourWedgeInclusion_factor]
    let v : {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r} →
        Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := fun k =>
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2)ᴴ
    exact congrArg v (show (⟨r+z.val-r,by constructor <;> omega⟩ :
      {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r}) = ⟨z.val,by constructor <;> omega⟩
      from Subtype.ext (Nat.add_sub_cancel_left r z.val))
  change F*Fᴴ = _
  calc
    _ = F*(∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z) *
        (physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ)*Fᴴ := by
      rw [physicalCoupledInclusion_complete,Matrix.mul_one]
    _ = ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := Finset.sum_congr rfl (fun z hz => (hp z).symm)

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.fourPairEmbedding_resolution_s50_oai := @OAI.Laughlin.Spin.fourPairEmbedding_resolution_s50_oai
