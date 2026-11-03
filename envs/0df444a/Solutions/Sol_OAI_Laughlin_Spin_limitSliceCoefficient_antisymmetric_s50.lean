-- Prove2me | solution 1 for OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:40:01.971427+00:00
-- url     : https://prove2.me/submissions/b602071c-7e0d-433c-b266-ae1a1587a8f8

import Mathlib
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_coefficient_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalPairCoupling_antisymmetric (Q r j k : ℕ) (ho : Odd r) :
    physicalCouplingCoefficient Q Q r (j+k) k =
      -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k ∧ j+k ≤ Q
  · have h1 : r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    have h2 : r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q := by omega
    rw [physicalCouplingCoefficient,dite_eq_left h1,physicalCouplingCoefficient,dite_eq_left h2]
    have hj : j+k-k=j := by omega
    have hk : j+k-j=k := by omega
    simp only [hj,hk]
    exact pairCoupledTensor_antisymmetric Q r (j+k-r) (by omega) ho
      ⟨j,by omega⟩ ⟨k,by omega⟩
  · have h1 : ¬(r ≤ j+k ∧ k ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    have h2 : ¬(r ≤ j+k ∧ j ≤ j+k ∧ j+k ≤ Q ∧ j+k ≤ Q) := by omega
    simp only [physicalCouplingCoefficient,dite_eq_right h1,dite_eq_right h2,neg_zero]

theorem fourBodyCoefficient_antisymmetric (Q r D T p j k : ℕ) (ho : Odd r) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  by_cases hr : r ≤ j+k
  · rw [ite_eq_left hr,ite_eq_left hr,physicalPairCoupling_antisymmetric Q r j k ho]
    ring
  · rw [ite_eq_right hr,ite_eq_right hr,neg_zero]

theorem fourBodyLimitCoefficient_antisymmetric (r D T p j k : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p k j = -fourBodyLimitCoefficient r D T p j k := by
  apply tendsto_nhds_unique (source_fourBody_coefficient_tendsto_s50 r D T p k j hrD hDT (by omega))
  have h := (source_fourBody_coefficient_tendsto_s50 r D T p j k hrD hDT hT).neg
  apply h.congr
  intro Q
  exact (fourBodyCoefficient_antisymmetric Q r D T p j k ho).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SliceCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem limitSliceCoefficient_antisymmetric_s50_oai (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
    limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k := by
  unfold limitSliceCoefficient
  by_cases h : p+j+k=D
  · rw [ite_eq_left (by omega : p+k+j=D),ite_eq_left h,
      fourBodyLimitCoefficient_antisymmetric r D D p j k ho hr (le_refl _) h]
  · rw [ite_eq_right (by omega : p+k+j ≠ D),ite_eq_right h,neg_zero]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50_oai := @OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50_oai
