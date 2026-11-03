-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourColumn_expansion_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:45:57.4564+00:00
-- url     : https://prove2.me/submissions/20d34cd5-604d-4b45-bae7-624b7e218d0f

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_occupation_coefficient_s50

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

theorem limitFourColumn_expansion_s50_oai (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) :
    limitFourColumn Q r D = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • occupationBasis Q A.val := by
  classical
  conv_lhs => rw [← (occupationBasis Q).sum_repr (limitFourColumn Q r D)]
  simp_rw [limitFourColumn_occupation_coefficient_s50 Q r D hr hor]
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  rw [← Finset.sum_subset (Finset.filter_subset P Finset.univ) (f := fun A =>
    (fourOccupationCoefficient Q r D A : ℂ) • occupationBasis Q A)]
  · exact Finset.sum_subtype _ (by simp [P]) _
  · intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [fourOccupationCoefficient,hc,hw]
    · simp [fourOccupationCoefficient,hc]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourColumn_expansion_s50_oai := @OAI.Laughlin.Fock.limitFourColumn_expansion_s50_oai
