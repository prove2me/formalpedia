-- Prove2me | solution 1 for GlobalTheory.Jets.C_eps_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:46.599454+00:00
-- url     : https://prove2.me/submissions/f2f66f3e-06fb-4ee0-b93b-3b40ebb9db04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
end GlobalTheory.Jets
