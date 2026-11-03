-- Prove2me | solution 1 for OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:57:41.544559+00:00
-- url     : https://prove2.me/submissions/58f44e1d-3561-4bbc-848a-9f679dc31531

import Mathlib
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021

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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SignedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCouplingCoefficient_pair_swap (Q r j k : ℕ) (hr : r ≤ Q)
    (hor : Odd r) (hjk : j+k ≤ Q) :
    physicalCouplingCoefficient Q Q r (j+k) k = -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k
  · rw [physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩,
      physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩]
    have hp := pairCoupledTensor_antisymmetric Q r (j+k-r) hr hor ⟨j,by omega⟩ ⟨k,by omega⟩
    simpa only [pairCoupledTensor,Pi.smul_apply,smul_eq_mul,Nat.add_sub_cancel,Nat.add_sub_cancel_left] using hp
  · simp [physicalCouplingCoefficient,h]

theorem fourBodyCoefficient_swap (Q r D T p j k : ℕ) (hr : r ≤ Q) (hor : Odd r)
    (hjk : j+k ≤ Q) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  split_ifs
  · rw [physicalCouplingCoefficient_pair_swap Q r j k hr hor hjk]
    ring
  · simp

theorem fourWedgeUnit_dot (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (hjk : j < k) (v : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ) :
    dotProduct v (fourWedgeUnit Q p j k) = v (⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
  classical
  simp only [dotProduct,fourWedgeUnit,mul_ite,mul_one,mul_zero]
  have he (i : Fin (2*Q-2+1) × WedgePairIndex Q) :
      (i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k) ↔
        i=(⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h3)))
    · intro h; subst i; exact ⟨rfl,rfl,rfl⟩
  simp_rw [he]
  simp

theorem fourWedgeUnit_zero (Q p j k : ℕ) (hkj : k ≤ j) : fourWedgeUnit Q p j k=0 := by
  funext i
  have h := i.2.property
  simp only [fourWedgeUnit,Pi.zero_apply]
  rw [ite_eq_right (by rintro ⟨_,hj,hk⟩; change i.2.val.1.val < i.2.val.2.val at h; omega)]

theorem fourBodyCopy_signed_at_level (Q r D T p j k : ℕ) (hor : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQ : T+2 ≤ Q) (hT : p+j+k=T) :
    dotProduct (fourBodyCopy Q r D (by omega) (by omega)
      (by unfold genericCoupledWeight; omega) (T-D)) (fourSignedUnit Q p j k) =
      fourBodyCoefficient Q r D T p j k := by
  rw [fourSignedUnit,dotProduct_sub]
  rcases lt_trichotomy j k with h | h | h
  · rw [fourWedgeUnit_dot Q p j k (by omega) (by omega) (by omega) h,
      fourWedgeUnit_zero Q p k j (by omega),dotProduct_zero,sub_zero]
    exact fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ hT
  · subst k
    rw [sub_self]
    have he := fourBodyCoefficient_swap Q r D T p j j (by omega) hor (by omega)
    linarith
  · rw [fourWedgeUnit_zero Q p j k (by omega),dotProduct_zero,zero_sub,
      fourWedgeUnit_dot Q p k j (by omega) (by omega) (by omega) h,
      fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ (by dsimp; omega),
      fourBodyCoefficient_swap Q r D T p j k (by omega) hor (by omega),neg_neg]

theorem fourBodyCopy_signed_off (Q r D n p j k : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hT : p+j+k ≠ D+n) :
    dotProduct (fourBodyCopy Q r D hr hA hB n) (fourSignedUnit Q p j k) = 0 := by
  have hz (j k : ℕ) (hT : p+j+k ≠ D+n) :
      dotProduct (fourBodyCopy Q r D hr hA hB n) (fourWedgeUnit Q p j k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [fourWedgeUnit]
    split_ifs with he
    · rw [fourBodyCopy_off Q r D n hr hrD hA hB i.1 i.2 (by omega),zero_mul]
    · exact mul_zero _
  rw [fourSignedUnit,dotProduct_sub,hz j k hT,hz k j (by omega),sub_self]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem trace_cross_outer {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (u v : I → ℝ) :
    Matrix.trace (Vᵀ * realOuter u v * W) =
      ∑ n, dotProduct (fun i => V i n) u * dotProduct (fun i => W i n) v := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,realOuter,
    dotProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourReal_outer_trace_s50_oai (Q D T p j k q l i : ℕ) (hQ : D+2 ≤ Q)
    (hTQ : T+2 ≤ Q) (r s : OddPairLabel D) (hp : p+j+k=T) (hq : q+l+i=T) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ *
      realOuter (fourSignedUnit Q p j k) (fourSignedUnit Q q l i) * retainedFourReal Q D hQ s) =
      if D ≤ T then fourBodyCoefficient Q (oddPairDeficit r) D T p j k *
        fourBodyCoefficient Q (oddPairDeficit s) D T q l i else 0 := by
  rw [trace_cross_outer]
  by_cases hDT : D ≤ T
  · rw [ite_eq_left hDT]
    let n : Fin (fourSpinWeight Q D+1) := ⟨T-D,by unfold fourSpinWeight; omega⟩
    rw [Finset.sum_eq_single n]
    · change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ (T-D)) (fourSignedUnit Q p j k) *
        dotProduct (fourBodyCopy Q (oddPairDeficit s) D _ _ _ (T-D)) (fourSignedUnit Q q l i) = _
      rw [fourBodyCopy_signed_at_level Q (oddPairDeficit r) D T p j k
        (oddPairDeficit_odd r) (oddPairDeficit_le r) hDT hTQ hp,
        fourBodyCopy_signed_at_level Q (oddPairDeficit s) D T q l i
        (oddPairDeficit_odd s) (oddPairDeficit_le s) hDT hTQ hq]
    · intro m hm hmn
      change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ m.val) (fourSignedUnit Q p j k) * _ = 0
      rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D m.val p j k _ (oddPairDeficit_le r) _ _ (by
        intro he; apply hmn; apply Fin.ext; dsimp [n]; omega),zero_mul]
    · simp
  · rw [ite_eq_right hDT]
    apply Finset.sum_eq_zero
    intro n hn
    change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ n.val) (fourSignedUnit Q p j k) * _ = 0
    rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D n.val p j k _ (oddPairDeficit_le r) _ _ (by omega),zero_mul]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50_oai := @OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50_oai
