-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.ne_zero_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:42.461012+00:00
-- url     : https://prove2.me/submissions/a2212bed-6675-40d6-ad61-3c55216e3310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  intro h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
end GlobalTheory.Reg.Transfer
