-- Prove2me | solution 1 for GlobalTheory.ChartRing.order_map_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:17.889018+00:00
-- url     : https://prove2.me/submissions/94358795-e7ec-4a4c-9612-ef18f24f2752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Theorems.Thm_GlobalTheory_ChartRing_order_map_of_injective

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
theorem _root_.solution (f : O⟦X⟧) : (f.map (algebraMap O K)).order = f.order :=
  order_map_of_injective (IsFractionRing.injective O K) f
end GlobalTheory.ChartRing
