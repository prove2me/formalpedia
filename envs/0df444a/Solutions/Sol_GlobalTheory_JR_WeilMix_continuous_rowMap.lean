-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.continuous_rowMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:08.379804+00:00
-- url     : https://prove2.me/submissions/a9723892-4301-4531-8aa5-d30dc3fdf707

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
theorem _root_.solution (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop
end GlobalTheory.JR.WeilMix
