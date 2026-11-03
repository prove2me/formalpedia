-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:50:01.607205+00:00
-- url     : https://prove2.me/submissions/38c4476c-39f4-44e1-9ff6-aacc17f8308f

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Definitions.Def_OAIQ050L014
import Theorems.Thm_OAI_Laughlin_Spin_limitSliceCoefficient_antisymmetric_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j) x) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hDQ : D ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let P := fun b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) =>
    b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2
  have he : (∑ b : Fin (D+1) × Fin (Q+1) × Fin (Q+1),
      if P b then f b.1.val b.2.1 b.2.2 else 0) =
      ∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
        if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0 := by
    simp only [Fintype.sum_prod_type,P]
  rw [← he,← Finset.sum_filter,Finset.sum_subtype (p := P) _ (by simp)]
  exact (localFourIndexEquiv Q D hDQ).sum_comp
    (fun b => f b.val.1.val b.val.2.1 b.val.2.2) |>.symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_SymmetricPairSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

private theorem symmetric_pair_sum {I M : Type*} [Fintype I] [LinearOrder I]
    [AddCommGroup M] (F : I → I → M) (hF : ∀ i j, F j i=F i j) (h0 : ∀ i, F i i=0) :
    (∑ i, ∑ j, F i j) = (∑ i, ∑ j, if i < j then F i j else 0) +
      (∑ i, ∑ j, if i < j then F i j else 0) := by
  have he (i j : I) : F i j = (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [h0]
    · simp [h,not_lt_of_gt h,hF]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : I => if j < i then F j i else 0)]

theorem limitFourEnd_swap (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    limitFourEnd Q p k j x = -limitFourEnd Q p j k x := by
  have h := LinearMap.congr_fun (annihilate_anticommute j k) (limitPairEnd Q p x)
  simpa only [limitFourEnd,Module.End.mul_apply,LinearMap.add_apply,LinearMap.zero_apply,
    add_eq_zero_iff_eq_neg] using h

theorem weightedFourEnd_ordered (Q p : ℕ) (S : ℕ → ℕ → ℝ)
    (hS : ∀ j k, S k j = -S j k) (x : Space Q) :
    weightedFourEnd Q p (fun j k => S j.val k.val) x = ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if j<k then (S j.val k.val : ℂ) • limitFourEnd Q p j k x else 0 := by
  let F := fun j k : Fin (Q+1) => ((S j.val k.val / 2 : ℝ) : ℂ) • limitFourEnd Q p j k x
  have hf : ∀ j k, F k j=F j k := by
    intro j k
    simp [F,hS j.val k.val,limitFourEnd_swap Q p j k x,neg_div]
  have h0 : ∀ j, F j j=0 := by
    intro j
    have hs := hS j.val j.val
    have hz : S j.val j.val=0 := by linarith
    simp [F,hz]
  have h := symmetric_pair_sum F hf h0
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ j, ∑ k, F j k) = _
  rw [h,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  split_ifs
  · simp only [F,← add_smul]
    congr 1
    push_cast
    ring
  · simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_LimitFourLocalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_local_sum_s50_oai (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
      (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_ordered Q _ _ (fun j k => limitSliceCoefficient_antisymmetric_s50 r D _ j k hr hor)]
  have he (p : ℕ) (j k : Fin (Q+1)) :
      (if j<k then (limitSliceCoefficient r D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) =
      (if p+j.val+k.val=D ∧ j<k then
        (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) := by
    by_cases hjk : j<k <;> by_cases ht : p+j.val+k.val=D <;> simp [limitSliceCoefficient,hjk,ht]
  simp_rw [he]
  rw [← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D hDQ
    (fun p j k => (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x)

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50_oai := @OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50_oai
