-- Prove2me | solution 1 for GlobalTheory.ChartRing.map_algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:12.230573+00:00
-- url     : https://prove2.me/submissions/e068e6a2-f683-4b6b-914e-33fcef05b272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsDomain O] (K : Type*) [Field K] [Algebra O K]
  [IsFractionRing O K]
omit [IsDomain O]
namespace GlobalTheory.ChartRing
theorem _root_.solution :
    Function.Injective (PowerSeries.map (algebraMap O K) : O⟦X⟧ →+* K⟦X⟧) :=
  PowerSeries.map_injective _ (IsFractionRing.injective O K)
end GlobalTheory.ChartRing
