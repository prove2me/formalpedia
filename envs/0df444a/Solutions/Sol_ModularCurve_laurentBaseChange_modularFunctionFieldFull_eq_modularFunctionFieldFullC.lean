-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/518f664c-57b5-5b2f-acdd-99d89c02829d

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC

set_option autoImplicit false

namespace P2MSeam
open ModularCurve

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_jq : coeffEmb K jq = jqModC K := by
  rw [← jqModC_rat, ← map_jqModC (algebraMap ℚ K)]
  rfl

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap K (LaurentSeries K) (algebraMap ℚ K c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

theorem laurentBaseChange_adjoin (S : Set (LaurentSeries ℚ)) :
    laurentBaseChange K (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin K (⇑(coeffEmb K) '' S) := by
  apply le_antisymm
  ·
    change IntermediateField.adjoin K _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩

    have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ S) := hx
    have key : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ S)
        ≤ (IntermediateField.adjoin K (⇑(coeffEmb K) '' S)).toSubfield.comap (coeffEmb K) := by
      rw [Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | hy)
      · show coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) c) ∈ IntermediateField.adjoin K (⇑(coeffEmb K) '' S)
        rw [coeffEmb_algebraMap]
        exact IntermediateField.algebraMap_mem _ _
      · show coeffEmb K y ∈ IntermediateField.adjoin K (⇑(coeffEmb K) '' S)
        exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    exact key hx'
  ·
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange K (IntermediateField.subset_adjoin ℚ S hx)

variable (N : ℕ) [NeZero N]

theorem image_coeffEmb_divisorExpansions :
    ⇑(coeffEmb K) '' divisorExpansions N = divisorExpansionsC K N := by
  ext y
  constructor
  · rintro ⟨x, ⟨d, hd0, hd, rfl⟩, rfl⟩
    refine ⟨d, hd0, hd, ?_⟩
    rw [coeffEmb, coeffMap_qExpand, ← coeffEmb, coeffEmb_jq]
  · rintro ⟨d, hd0, hd, rfl⟩
    refine ⟨qExpand ℚ d jq, ⟨d, hd0, hd, rfl⟩, ?_⟩
    rw [coeffEmb, coeffMap_qExpand, ← coeffEmb, coeffEmb_jq]

end P2MSeam

open ModularCurve in

theorem solution (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    laurentBaseChange K (modularFunctionFieldFull N) = modularFunctionFieldFullC K N := by
  show laurentBaseChange K (IntermediateField.adjoin ℚ (divisorExpansions N))
    = IntermediateField.adjoin K (divisorExpansionsC K N)
  rw [P2MSeam.laurentBaseChange_adjoin, P2MSeam.image_coeffEmb_divisorExpansions]

end S_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC (solution)
