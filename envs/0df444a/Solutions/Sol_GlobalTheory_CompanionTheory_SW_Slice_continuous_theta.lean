-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.continuous_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:44.117936+00:00
-- url     : https://prove2.me/submissions/ea0c5ef3-c373-41bb-87ae-7f6dba6131db

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution (g : V → X) (b₀ : X) : Continuous (theta (Q := Q) g b₀) :=
  continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
end GlobalTheory.CompanionTheory.SW.Slice
