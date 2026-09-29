-- Prove2me | solution 1 for ModularCurve.qExpand_mem_xHFunctionField_of_mem_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/12c064d3-e76a-547c-b841-250544a11aad

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_exists_conj_mem_GammaH_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div

set_option autoImplicit false

open AlgebraicCurve IntermediateField ModularCurve HahnSeries
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (M / p) (infSubgroup p M H hpM)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    qExpand ℚ p y ∈ xHFunctionField M H := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) _)
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) (Γ' := CohCarrier.GammaH M H)
    (translation_mem_GammaH (M / p) _) p (fun γ hγ => ModularCurve.exists_conj_mem_GammaH_div p M H hpM γ hγ)
  change y ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) at hy
  change qExpand ℚ p y ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)
  rw [qExpFunctionFieldC] at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))).map
      (qExpandAlgHomC ℚ p) ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

#print axioms solution

end S_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
end P2MW
export P2MW.S_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div (solution)
