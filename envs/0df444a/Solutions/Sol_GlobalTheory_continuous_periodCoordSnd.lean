-- Prove2me | solution 1 for GlobalTheory.continuous_periodCoordSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:43.996051+00:00
-- url     : https://prove2.me/submissions/aa1d220d-2916-4406-b493-93e2836cb065

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_continuous_periodCoordFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (τ : Matrix ι ι ℂ) : Continuous (periodCoordSnd τ) := by
  unfold periodCoordSnd
  exact Continuous.sub (by fun_prop)
    (continuous_const.matrix_mulVec (continuous_periodCoordFst τ))
end GlobalTheory
