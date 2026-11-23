-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.rowMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:09.372308+00:00
-- url     : https://prove2.me/submissions/7a53b2cd-7b29-4e98-a8ab-eae776a53806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.JR.WeilMix
theorem _root_.solution (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring
end GlobalTheory.JR.WeilMix
