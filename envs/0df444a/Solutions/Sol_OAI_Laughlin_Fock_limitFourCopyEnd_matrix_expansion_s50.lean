-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:50:04.850691+00:00
-- url     : https://prove2.me/submissions/a0048750-5c34-4ec9-b611-386b8adde13a

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_fourOccupation_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_expansion_s50
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_mul_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_occupation_coefficient_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ColumnExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem fourOccupationCreate_mul (Q D : ℕ) (A : FourOccupation Q D) (x : Space Q) :
    fourOccupationCreate Q D A x = occupationBasis Q A.val * x := by
  rw [occupationBasis_four Q A.val A.property.1]
  simp [fourOccupationCreate,create,mul_assoc]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_EndExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_left_ext (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q x z = occupationInner Q y z) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  have hA := h (occupationBasis Q A)
  rw [occupationInner_basis_right,occupationInner_basis_right] at hA
  exact star_injective hA

theorem limitFourCopyEnd_expansion (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • fourOccupationEnd Q D A x := by
  apply occupationInner_left_ext
  intro y
  rw [← limitFourColumn_mul_adjoint_s50,limitFourColumn_expansion_s50 Q r D hr hor]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_right,occupationInner_sum_left,
    occupationInner_smul_right,occupationInner_smul_left,Complex.star_def,Complex.conj_ofReal,
    ← fourOccupationCreate_mul,fourOccupation_adjoint_s50]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_LimitPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem limitFourCopyEnd_matrix_expansion_s50_oai (Q D : ℕ) (i : Fin ((D+1)/2)) (x : Space Q) :
    limitFourCopyEnd Q (Certificate.copyLabel i) D x =
      ∑ A : FourOccupation Q D, star (physicalFourOccupationColumns Q D A i) • fourOccupationEnd Q D A x := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  rw [limitFourCopyEnd_expansion Q _ D hi hoi]
  simp only [physicalFourOccupationColumns,physicalWedgeColumns,
    limitFourColumn_occupation_coefficient_s50 Q _ D hi hoi,Complex.star_def,Complex.conj_ofReal]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50_oai := @OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50_oai
