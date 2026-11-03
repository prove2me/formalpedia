-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourColumn_occupation_coefficient_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:48:11.011176+00:00
-- url     : https://prove2.me/submissions/24f094fc-adf9-4b4f-82a0-2d7e30dae2dd

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_physical_L_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem create_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) : create i (occupationBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q+1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint
    (Pi.basisFun ℂ (Fin (Q+1)))
    (⟨{i},Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q+1)) 1)
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) hd
  change occupationBasis Q {i} * occupationBasis Q A = 0 at h
  rw [occupation_singleton] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem create_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    create i (occupationBasis Q A) = insertionSign Q i A • occupationBasis Q (insert i A) := by
  simpa [insertionSign,hi] using (create_unoccupied_sign Q i A hi).choose_spec.2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem create_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (create i x) A =
      if i ∈ A then insertionSign Q i (A.erase i) * (occupationBasis Q).repr x (A.erase i) else 0 := by
  let e : ℂ := if i ∈ A then insertionSign Q i (A.erase i) else 0
  have h : ((occupationBasis Q).coord A).comp (create i) =
      e • (occupationBasis Q).coord (A.erase i) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (create i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (A.erase i)
    by_cases hiB : i ∈ B
    · rw [create_occupied Q i B hiB]
      have hBA : B ≠ A.erase i := by intro h; rw [h] at hiB; exact Finset.notMem_erase i A hiB
      simp [e,Module.Basis.repr_self,hBA]
    · rw [create_unoccupied Q i B hiB,map_smul,Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · by_cases hBA : B = A.erase i
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have hins : insert i B ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.erase_insert hiB]
          simp [e,hiA,Module.Basis.repr_self,hBA,hins]
      · have hins : insert i B ≠ A := by intro h; rw [← h] at hiA; simp at hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hins]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Bidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_empty (Q : ℕ) : occupationBasis Q ∅ = (1 : Space Q) := by
  let A : Set.powersetCard (Fin (Q+1)) 0 := ⟨∅,rfl⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_zero_apply]

theorem vacuum_bidegree (Q : ℕ) : OccupationBidegree Q 0 0 (1 : Space Q) := by
  intro A hA
  have hn : (∅ : Finset (Fin (Q+1))) ≠ A := by intro he; subst A; simp at hA
  rw [← occupation_empty]
  simp [Module.Basis.repr_self,hn]

theorem create_bidegree (Q n w : ℕ) (x : Space Q) (hx : OccupationBidegree Q n w x)
    (i : Fin (Q+1)) : OccupationBidegree Q (n+1) (w+i.val) (create i x) := by
  intro A hA
  rw [create_coordinate]
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi]
    have hc := Finset.card_erase_of_mem hi
    have hw := Finset.sum_erase_add A (fun j : Fin (Q+1) => j.val) hi
    have hlow : (A.erase i).card ≠ n ∨ (∑ j ∈ A.erase i, j.val) ≠ w := by
      rcases hA with hA | hA
      · left; have hp := Finset.card_pos.mpr ⟨i,hi⟩; omega
      · right; omega
    rw [hx (A.erase i) hlow,mul_zero]
  · rw [ite_eq_right hi]

theorem four_create_bidegree (Q : ℕ) (a b c d : Fin (Q+1)) :
    OccupationBidegree Q 4 (a.val+b.val+c.val+d.val)
      (create a (create b (create c (create d (1 : Space Q))))) := by
  have h := create_bidegree Q _ _ _
    (create_bidegree Q _ _ _ (create_bidegree Q _ _ _
      (create_bidegree Q 0 0 _ (vacuum_bidegree Q) d) c) b) a
  convert h using 1; omega

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_FourLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationBasis_four (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    occupationBasis Q A =
      create (occupationFourLabels Q A hA 0) (create (occupationFourLabels Q A hA 1)
        (create (occupationFourLabels Q A hA 2) (create (occupationFourLabels Q A hA 3) (1 : Space Q)))) := by
  let B : Set.powersetCard (Fin (Q+1)) 4 := ⟨A,hA⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra B.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply,occupationFourLabels,B,create,Pi.basisFun_apply,mode,Matrix.vecTail,Function.comp_def]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourColumn_bidegree (Q r D : ℕ) : OccupationBidegree Q 4 (D+1) (limitFourColumn Q r D) := by
  intro A hA
  simp only [limitFourColumn,map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero; intro p hp
  apply Finset.sum_eq_zero; intro j hj
  apply Finset.sum_eq_zero; intro k hk
  apply Finset.sum_eq_zero; intro x hx
  apply Finset.sum_eq_zero; intro y hy
  by_cases hS : p+j.val+k.val=D
  · by_cases hP : x.val+y.val=p+1
    · have hv := four_create_bidegree Q x y j k A (by
        rcases hA with hA | hA
        · exact Or.inl hA
        · exact Or.inr (by omega))
      rw [hv,mul_zero]
    · simp [pairLimitCoefficient,hP]
  · simp [limitSliceCoefficient,hS]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_OccupationCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_basis_right (Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    occupationInner Q x (occupationBasis Q A) = star ((occupationBasis Q).repr x A) := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem limitFourColumn_occupation_coefficient_s50_oai (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (limitFourColumn Q r D) A = (fourOccupationCoefficient Q r D A : ℂ) := by
  by_cases hA : A.card=4
  · by_cases hw : (∑ i ∈ A, i.val)=D+1
    · let l := occupationFourLabels Q A hA
      have h := limitFourColumn_physical_L_s50 Q r D hr hor (l 0) (l 1) (l 2) (l 3)
        (l.strictMono (by decide)) (l.strictMono (by decide)) (l.strictMono (by decide))
        (by rw [← occupationFourLabels_sum Q A hA]; exact hw)
      rw [← occupationBasis_four Q A hA,occupationInner_basis_right] at h
      have hs := congrArg star h
      simpa [fourOccupationCoefficient,hA,hw,l] using hs
    · rw [limitFourColumn_bidegree Q r D A (Or.inr hw)]
      simp [fourOccupationCoefficient,hA,hw]
  · rw [limitFourColumn_bidegree Q r D A (Or.inl hA)]
    simp [fourOccupationCoefficient,hA]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourColumn_occupation_coefficient_s50_oai := @OAI.Laughlin.Fock.limitFourColumn_occupation_coefficient_s50_oai
