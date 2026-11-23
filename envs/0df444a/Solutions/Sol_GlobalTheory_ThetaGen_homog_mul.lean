-- Prove2me | solution 1 for GlobalTheory.ThetaGen.homog_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:30.108307+00:00
-- url     : https://prove2.me/submissions/fff6b947-6102-4995-8404-d4915dfc0369

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
namespace GlobalTheory.ThetaGen
theorem _root_.solution (a b : ℕ) (f h : X → ℂ) :
    homog a f * homog b h = homog (a + b) (f * h) := by
  funext p; simp only [homog, Pi.mul_apply]; ring
end GlobalTheory.ThetaGen
