-- Prove2me | solution 1 for GlobalTheory.EllipticPoles.tendsto_two_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:23.830613+00:00
-- url     : https://prove2.me/submissions/6333d239-308e-4756-805f-c4fc7c00a883

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
theorem _root_.solution (a : ℂ) : Tendsto (fun z : ℂ ↦ z + z) (𝓝[≠] a) (𝓝[≠] (a + a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((by fun_prop : Continuous fun z : ℂ ↦ z + z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz h
      apply hz
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h / 2)
end GlobalTheory.EllipticPoles
