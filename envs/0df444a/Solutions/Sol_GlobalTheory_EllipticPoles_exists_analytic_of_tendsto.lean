-- Prove2me | solution 1 for GlobalTheory.EllipticPoles.exists_analytic_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:14.096747+00:00
-- url     : https://prove2.me/submissions/8a19e8e7-20b8-4c01-aaea-0040abb78709

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.EllipticPoles
variable (L : PeriodPair)
namespace GlobalTheory.EllipticPoles
theorem _root_.solution {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a)
    (h : Tendsto f (𝓝[≠] a) (𝓝 c)) : ∃ g, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g :=
  hf.meromorphicOrderAt_nonneg_iff.1 ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨c, h⟩)
end GlobalTheory.EllipticPoles
