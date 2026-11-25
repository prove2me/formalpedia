-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NormSign.exists_valuativeRel_of_normed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:26.888517+00:00
-- url     : https://prove2.me/submissions/1311dc38-a08d-4c75-80c2-e9206664f564

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NormSign
namespace GlobalTheory.JR.WeilQuad.NormSign
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance
end GlobalTheory.JR.WeilQuad.NormSign
