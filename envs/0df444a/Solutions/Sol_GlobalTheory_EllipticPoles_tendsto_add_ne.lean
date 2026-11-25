-- Prove2me | solution 1 for GlobalTheory.EllipticPoles.tendsto_add_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:09.303815+00:00
-- url     : https://prove2.me/submissions/8e55ed2e-3042-4bda-b417-1e44f3825e40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.EllipticPoles
variable (L : PeriodPair)
namespace GlobalTheory.EllipticPoles
theorem _root_.solution (a l : ℂ) : Tendsto (fun z : ℂ ↦ z + l) (𝓝[≠] a) (𝓝[≠] (a + l)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)
end GlobalTheory.EllipticPoles
