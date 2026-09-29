-- Prove2me | solution 1 for NumberField.PlaceDecomp.decompositionSubgroup_fixedPoints_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4b568341-624c-5e92-8a48-a6f08adce297

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp Pointwise
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    (w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨σ, rfl⟩ := FixedPoints.toAlgAut_surjective (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) f
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  show (MulSemiringAction.toAlgAut (NumberField.PlaceDecomp.decomp E K w)
      (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) (w.adicCompletion K) σ⁻¹) x ∈
    w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K
  rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
  exact NumberField.PlaceDecomp.smul_mem_adicCompletionIntegers_iff σ⁻¹ x

end S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top
end P2MW
export P2MW.S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top (solution)
