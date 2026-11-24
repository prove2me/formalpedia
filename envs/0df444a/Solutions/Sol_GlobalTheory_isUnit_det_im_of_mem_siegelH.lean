-- Prove2me | solution 1 for GlobalTheory.isUnit_det_im_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:30.001362+00:00
-- url     : https://prove2.me/submissions/5e894784-3949-4890-8a2d-ecfcd095daf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice

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
theorem _root_.solution {τ : Matrix ι ι ℂ} (hτ : τ ∈ SiegelH ι) :
    IsUnit (τ.map Complex.im).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 hτ.2.isUnit
end GlobalTheory
