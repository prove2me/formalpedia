-- Prove2me | solution 1 for GlobalTheory.ThetaSpan.ofIntVec_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:13.694057+00:00
-- url     : https://prove2.me/submissions/e4468c04-07cf-4258-b0c3-9f9f87de541b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaSpan
namespace GlobalTheory.ThetaSpan
theorem _root_.solution {g : ℕ} (j : Fin g) :
    ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
  funext i
  by_cases h : i = j
  · subst h; simp [ofIntVec]
  · simp [ofIntVec, Pi.single_eq_of_ne h]
end GlobalTheory.ThetaSpan
