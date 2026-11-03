-- Prove2me | solution 1 for OAI.Laughlin.Fock.row_normal_square_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:54:11.126602+00:00
-- url     : https://prove2.me/submissions/1afed931-5c4e-46df-ab31-2f758dbd607f

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_coordinate_s50
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_create_inner_s50
import Theorems.Thm_OAI_Laughlin_Fock_create_create_inner_s50

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

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_ContractionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Adjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem insertionSign_star (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    star (insertionSign Q i A) = insertionSign Q i A := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_annihilate_adjoint (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q (create i x) y = occupationInner Q x (annihilate i y) := by
  let f : Finset (Fin (Q+1)) → ℂ := fun A =>
    insertionSign Q i (A.erase i) *
      (star ((occupationBasis Q).repr x (A.erase i)) * (occupationBasis Q).repr y A)
  have hl : occupationInner Q (create i x) y =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
    rw [Finset.sum_filter]
    unfold occupationInner
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hi : i ∈ A <;>
      simp only [f, create_coordinate, hi, ite_true, ite_false, star_mul,
        insertionSign_star, star_zero, zero_mul, mul_comm, mul_left_comm]
  rw [hl, ← sum_unoccupied_insert i f, Finset.sum_filter]
  unfold occupationInner
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hi : i ∈ A <;>
    simp only [f, hi, annihilate_coordinate_s50, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, Finset.erase_insert, zero_mul, mul_assoc, mul_comm]

end Laughlin.Fock

end OAI
end

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

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_left (Q : ℕ) (x y z : Space Q) :
    occupationInner Q (x+y) z = occupationInner Q x z+occupationInner Q y z := by
  simp [occupationInner,add_mul,Finset.sum_add_distrib]

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_RowNormalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem row_normal_square_s50_oai {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (m : I → Fin (Q+1)) (hm : Function.Injective m)
    (ell : ℝ) (u : Space Q) (v : I → Space Q) :
    (occupationNormSq Q ((ell : ℂ) • u + ∑ i, create (m i) (v i)) : ℂ) =
      (ell : ℂ)^2 * (occupationNormSq Q u : ℂ) +
      (∑ i, (ell : ℂ) * (occupationInner Q (annihilate (m i) u) (v i) +
        occupationInner Q (v i) (annihilate (m i) u))) +
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
  rw [← occupationInner_self]
  simp only [occupationInner_add_left,occupationInner_add_right,occupationInner_smul_left,
    occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal,
    occupationInner_sum_left,occupationInner_sum_right]
  have hd (i j : I) : delta (m i) (m j) = if i=j then (1 : ℂ) else 0 := by
    simp only [delta,hm.eq_iff]
  have he : (∑ i, ∑ j, occupationInner Q (create (m i) (v i)) (create (m j) (v j))) =
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
    simp_rw [create_create_inner_s50,hd]
    simp [Finset.sum_sub_distrib,occupationInner_self]
  rw [Finset.sum_comm] at he
  simp only [Finset.sum_add_distrib]
  rw [he]
  simp only [create_annihilate_adjoint,annihilate_create_inner_s50,occupationInner_self,
    Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Fock.row_normal_square_s50_oai.{u_1} := @OAI.Laughlin.Fock.row_normal_square_s50_oai.{u_1}
