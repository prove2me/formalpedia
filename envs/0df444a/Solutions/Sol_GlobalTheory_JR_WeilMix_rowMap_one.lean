-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.rowMap_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:15.176447+00:00
-- url     : https://prove2.me/submissions/c930f370-011e-4641-a7d2-7c76a9bddae5

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
theorem _root_.solution (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]
end GlobalTheory.JR.WeilMix
