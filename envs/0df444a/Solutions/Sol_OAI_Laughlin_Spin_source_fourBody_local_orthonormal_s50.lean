-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:00:35.889638+00:00
-- url     : https://prove2.me/submissions/02c1269a-caa6-45ee-bb63-8809059a747e

import Mathlib
import Definitions.Def_OAIQ050L022
import Theorems.Thm_OAI_Laughlin_Spin_fourWeightSlice_sum_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_local_normalization_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_BesselAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_local_orthonormal_s50_oai (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    (∑ b : LocalFourIndex D,
      fourBodyCoefficient Q (oddPairDeficit r) D D b.val.1.val b.val.2.1.val b.val.2.2.val *
      fourBodyCoefficient Q (oddPairDeficit s) D D b.val.1.val b.val.2.1.val b.val.2.2.val) =
      if r = s then 1 else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp only [ite_true]
    simpa only [pow_two] using source_fourBody_local_normalization_s50 Q (oddPairDeficit r) D
      (oddPairDeficit_le r) (oddPairDeficit_odd r) hQ
  · rw [ite_eq_right hrs]
    have hr : oddPairDeficit r ≤ Q := le_trans (oddPairDeficit_le r) (by omega)
    have hs : oddPairDeficit s ≤ Q := le_trans (oddPairDeficit_le s) (by omega)
    have hA : D-oddPairDeficit r ≤ 2*Q-2 := by have := oddPairDeficit_le r; omega
    have hB : D-oddPairDeficit r ≤ genericCoupledWeight Q Q (oddPairDeficit r) := by
      have := oddPairDeficit_le r; unfold genericCoupledWeight; omega
    have hC : D-oddPairDeficit s ≤ 2*Q-2 := by have := oddPairDeficit_le s; omega
    have hE : D-oddPairDeficit s ≤ genericCoupledWeight Q Q (oddPairDeficit s) := by
      have := oddPairDeficit_le s; unfold genericCoupledWeight; omega
    have hne : oddPairDeficit r ≠ oddPairDeficit s := by
      intro he
      exact hrs (Fin.ext (by unfold oddPairDeficit at he; omega))
    have ho := fourBodyCopy_orthogonal_pair Q (oddPairDeficit r) (oddPairDeficit s) D D 0 0
      hr hs (oddPairDeficit_odd r) (oddPairDeficit_odd s) hne hA hB hC hE
    rw [Fintype.sum_prod_type] at ho
    rw [← fourWeightSlice_sum_s50 Q D hQ (fun p j k =>
      fourBodyCoefficient Q (oddPairDeficit r) D D p j.val k.val *
        fourBodyCoefficient Q (oddPairDeficit s) D D p j.val k.val)]
    convert ho using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : p.val+i.val.1.val+i.val.2.val=D
    · rw [ite_eq_left he]
      have h1 := fourBodyCopy_source_coefficient Q (oddPairDeficit r) D D
        (oddPairDeficit_le r) (le_refl D) hQ p i he
      have h2 := fourBodyCopy_source_coefficient Q (oddPairDeficit s) D D
        (oddPairDeficit_le s) (le_refl D) hQ p i he
      simpa only [Nat.sub_self] using congrArg₂ (fun a b : ℝ => a*b) h1.symm h2.symm
    · rw [ite_eq_right he, fourBodyCopy_off Q (oddPairDeficit r) D 0 hr
        (oddPairDeficit_le r) hA hB p i (by simpa only [add_zero] using he),zero_mul]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50_oai := @OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50_oai
