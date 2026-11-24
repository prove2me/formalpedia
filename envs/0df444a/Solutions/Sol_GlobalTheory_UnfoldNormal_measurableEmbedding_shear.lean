-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.measurableEmbedding_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:16.812723+00:00
-- url     : https://prove2.me/submissions/6107e21b-4f72-42cf-b632-6e6cb6cdcc54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Theorems.Thm_GlobalTheory_UnfoldNormal_shear_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnfoldNormal
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution {N : Subgroup H} (hN : IsClosed (N : Set H)) :
    MeasurableEmbedding (shear N) := by
  rw [shear_eq]
  exact shearEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hN.measurableSet).prodMap MeasurableEmbedding.id)
end GlobalTheory.UnfoldNormal
