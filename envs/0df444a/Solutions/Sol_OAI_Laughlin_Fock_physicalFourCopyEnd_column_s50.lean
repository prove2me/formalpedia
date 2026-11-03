-- Prove2me | solution 1 for OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:20:30.178923+00:00
-- url     : https://prove2.me/submissions/a40277bf-2f87-4978-85eb-81cd9c0da3b1

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L021
import Theorems.Thm_OAI_Laughlin_Spin_fourWeightSlice_sum_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem retainedFourInclusion_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    retainedFourInclusion Q D hQ r i n =
      (fourBodyCopy Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i : ℂ) := rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourCopyEnd_column_s50_oai (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) (x : Space Q) :
    (∑ i, star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x) =
      physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) x := by
  have hc (i : FourWedgeIndex Q) :
      star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x =
        if i.1.val+i.2.val.1.val+i.2.val.2.val=D then
          (fourBodyCoefficient Q (oddPairDeficit r) D D i.1.val i.2.val.1.val i.2.val.2.val : ℂ) •
            sourceFourEnd Q i.1.val i.2.val.1 i.2.val.2 x else 0 := by
    rw [retainedFourInclusion_column]
    simp only [Fin.val_zero,Complex.star_def,Complex.conj_ofReal]
    by_cases h : i.1.val+i.2.val.1.val+i.2.val.2.val=D
    · have he := fourBodyCopy_source_coefficient Q (oddPairDeficit r) D D
        (oddPairDeficit_le r) (le_refl D) hQ i.1 i.2 h
      simp only [Nat.sub_self] at he
      rw [ite_eq_left h,he]
      rfl
    · rw [ite_eq_right h,fourBodyCopy_off Q (oddPairDeficit r) D 0 _ (oddPairDeficit_le r)
        _ _ i.1 i.2 (by simpa using h)]
      simp
  simp_rw [hc]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [fourWeightSlice_sum_s50 Q D hQ (fun p j k =>
    (fourBodyCoefficient Q (oddPairDeficit r) D D p j.val k.val : ℂ) • sourceFourEnd Q p j k x)]
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50_oai := @OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50_oai
