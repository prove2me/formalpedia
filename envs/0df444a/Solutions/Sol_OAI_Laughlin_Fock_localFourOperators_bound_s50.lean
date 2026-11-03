-- Prove2me | solution 1 for OAI.Laughlin.Fock.localFourOperators_bound_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:51:12.969378+00:00
-- url     : https://prove2.me/submissions/c18e65a6-c909-4e0f-8387-701478646e98

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_coordinate_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

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

theorem insertionSign_norm (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    ‖insertionSign Q i A‖ = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

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

theorem annihilate_normSq (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) =
      ∑ A : Finset (Fin (Q+1)), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0 := by
  have h (A : Finset (Fin (Q+1))) :
      ‖(occupationBasis Q).repr (annihilate i x) A‖^2 =
        if i ∉ A then ‖(occupationBasis Q).repr x (insert i A)‖^2 else 0 := by
    by_cases hi : i ∈ A <;> simp [annihilate_coordinate_s50,hi,insertionSign_norm]
  unfold occupationNormSq
  simp_rw [h]
  simpa only [Finset.sum_filter] using
    sum_unoccupied_insert (R := ℝ) i (fun A => ‖(occupationBasis Q).repr x A‖^2)

theorem annihilate_normSq_le (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) ≤ occupationNormSq Q x := by
  rw [annihilate_normSq]
  unfold occupationNormSq
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · positivity

theorem two_annihilate_normSq_le (Q : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate k (annihilate j x)) ≤ occupationNormSq Q x :=
  (annihilate_normSq_le Q k _).trans (annihilate_normSq_le Q j x)

theorem limitFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (limitFourEnd Q p j k x) ≤
      occupationNormSq Q (limitPairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (limitPairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CollectionAnnihilatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem collection_limit_annihilator_bound {I : Type*} [Fintype I] (Q : ℕ)
    (p : I → ℕ) (j k : I → Fin (Q+1)) (hp : ∀ i, p i ≤ 23) (x : Space Q) :
    (∑ i, occupationNormSq Q (limitFourEnd Q (p i) (j i) (k i) x)) ≤
      (Fintype.card I : ℝ) * limitPairWindow Q x := by
  calc
    _ ≤ ∑ i : I, limitPairWindow Q x := by
      apply Finset.sum_le_sum
      intro i hi
      apply (limitFour_normSq_le_pair Q (p i) (j i) (k i) x).trans
      change occupationNormSq Q (limitPairEnd Q (p i) x) ≤
        ∑ r ∈ Finset.range 24, occupationNormSq Q (limitPairEnd Q r x)
      exact Finset.single_le_sum
        (f := fun r => occupationNormSq Q (limitPairEnd Q r x))
        (fun r hr => occupationNormSq_nonneg Q _) (Finset.mem_range.mpr (by have h := hp i; omega))
    _ = _ := by simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_TruncatedFourCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem localFourOperators_bound_s50_oai (Q D : ℕ) (hDQ : D ≤ Q) (hD : D ≤ 23) (x : Space Q) :
    (∑ b : LocalFourIndex D, occupationNormSq Q (localFourOperators Q D hDQ b x)) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * limitPairWindow Q x := by
  exact collection_limit_annihilator_bound Q (fun b : LocalFourIndex D => b.val.1.val)
    (fun b => ⟨b.val.2.1.val,by omega⟩) (fun b => ⟨b.val.2.2.val,by omega⟩)
    (fun b => by have := b.val.1.isLt; omega) x

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.localFourOperators_bound_s50_oai := @OAI.Laughlin.Fock.localFourOperators_bound_s50_oai
