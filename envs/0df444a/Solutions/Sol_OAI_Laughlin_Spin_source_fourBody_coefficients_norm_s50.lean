-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:59:30.421959+00:00
-- url     : https://prove2.me/submissions/99c7b599-b840-4d65-aac7-45b20f260e6d

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledWedge_off (Q r n : ℕ) (hr : r ≤ Q) (i : WedgePairIndex Q)
    (hi : i.val.1.val+i.val.2.val ≠ r+n) :
    pairCoupledWedge Q r hr n i = 0 := by
  simp only [pairCoupledWedge,tensorToWedgePair,pairCoupledTensor,Pi.smul_apply,smul_eq_mul,
    genericUnitDescendant_off Q Q r n hr hr i.val hi,mul_zero]

theorem genericUnitDescendant_transport_right (A B B' z n : ℕ) (he : B=B')
    (hA : z ≤ A) (hB : z ≤ B) (hB' : z ≤ B') (i : SpinIndex A B) :
    genericUnitDescendant A B z hA hB n i =
      genericUnitDescendant A B' z hA hB' n (i.1,Fin.cast (congrArg (fun k => k+1) he) i.2) := by
  subst B'; rfl

theorem fourBodyCopy_source_coefficient (Q r D T : ℕ) (hrD : r ≤ D) (hDT : D ≤ T)
    (hQT : T+2 ≤ Q) (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hT : p.val+i.val.1.val+i.val.2.val=T) :
    fourBodyCopy Q r D (by omega) (by omega) (by unfold genericCoupledWeight; omega)
      (T-D) (p,i) = fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val := by
  have hcw : genericCoupledWeight Q Q r = 2*Q-2*r := by unfold genericCoupledWeight; omega
  rw [fourBodyCopy_coordinate]
  by_cases hri : r ≤ i.val.1.val+i.val.2.val
  · let b : Fin (genericCoupledWeight Q Q r+1) := ⟨i.val.1.val+i.val.2.val-r,by
      rw [hcw]; omega⟩
    rw [Finset.sum_eq_single b]
    · unfold fourBodyCoefficient
      rw [ite_eq_left hri]
      have hI : r ≤ i.val.1.val+i.val.2.val ∧ i.val.1.val ≤ i.val.1.val+i.val.2.val ∧
          i.val.1.val+i.val.2.val ≤ Q ∧ i.val.1.val+i.val.2.val ≤ Q := by omega
      have hO : D-r ≤ T-r ∧ p.val ≤ T-r ∧ T-r ≤ 2*Q-2 ∧ T-r ≤ 2*Q-2*r := by omega
      rw [physicalCouplingCoefficient,dite_eq_left hI,physicalCouplingCoefficient,dite_eq_left hO]
      simp only [pairCoupledWedge,tensorToWedgePair,pairCoupledTensor,Pi.smul_apply,smul_eq_mul]
      have hi2 : i.val.1.val+i.val.2.val-i.val.1.val=i.val.2.val := by omega
      have hb : T-r-p.val=b.val := by dsimp [b]; omega
      have hn : T-r-(D-r)=T-D := by omega
      try simp only [hi2,hn]
      have hbfin : (⟨T-r-p.val,by omega⟩ : Fin (2*Q-2*r+1)) =
          ⟨b.val,by rw [← hcw]; exact b.isLt⟩ := by apply Fin.ext; exact hb
      rw [hbfin]
      have hout := genericUnitDescendant_transport_right (2*Q-2) (genericCoupledWeight Q Q r)
        (2*Q-2*r) (D-r) (T-D) hcw (by omega) (by unfold genericCoupledWeight; omega)
        (by omega) (p,b)
      rw [hout]
      rfl
    · intro c hc hcb
      rw [pairCoupledWedge_off Q r c.val (by omega) i (by
        intro he; apply hcb; apply Fin.ext; dsimp [b]; omega),zero_mul]
    · simp
  · rw [fourBodyCoefficient,ite_eq_right hri]
    apply Finset.sum_eq_zero
    intro c hc
    rw [pairCoupledWedge_off Q r c.val (by omega) i (by omega),zero_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourBodyCopy_off (Q r D n : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hi : p.val+i.val.1.val+i.val.2.val ≠ D+n) :
    fourBodyCopy Q r D hr hA hB n (p,i) = 0 := by
  rw [fourBodyCopy_coordinate]
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hi' : i.val.1.val+i.val.2.val=r+b.val
  · rw [genericUnitDescendant_off _ _ _ _ hA hB (p,b) (by dsimp; omega),mul_zero,mul_zero]
  · rw [pairCoupledWedge_off Q r b.val hr i hi',zero_mul]

theorem source_fourBody_coefficients_norm_s50_oai (Q r D T : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQT : T+2 ≤ Q) :
    (∑ p : Fin ((2*Q-2)+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=T then
        (fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val)^2 else 0) = 1 := by
  have hn : T-D ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r) := by
    unfold genericCoupledWeight; omega
  have hnorm := fourBodyCopy_norm Q r D (T-D) (by omega) ho (by omega)
    (by unfold genericCoupledWeight; omega) hn
  rw [vectorNormSq,Fintype.sum_prod_type] at hnorm
  rw [← hnorm]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro i hi
  by_cases he : p.val+i.val.1.val+i.val.2.val=T
  · rw [ite_eq_left he,fourBodyCopy_source_coefficient Q r D T hrD hDT hQT p i he]
  · rw [ite_eq_right he,fourBodyCopy_off Q r D (T-D) (by omega) hrD (by omega)
      (by unfold genericCoupledWeight; omega) p i (by omega),zero_pow (by omega)]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50_oai := @OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50_oai
