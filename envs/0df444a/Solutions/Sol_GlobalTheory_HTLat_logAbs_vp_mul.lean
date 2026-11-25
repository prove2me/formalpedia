-- Prove2me | solution 1 for GlobalTheory.HTLat.logAbs_vp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:48:28.116805+00:00
-- url     : https://prove2.me/submissions/40971e1f-5d1f-4073-8c53-0dbf5171279e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

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
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
theorem _root_.solution (p : ℕ) (v : Valuation C ℝ≥0) {r s : ℝ≥0} (hr : r ≠ 0) (hs : s ≠ 0) :
    logAbs_vp p v (r * s) = logAbs_vp p v r + logAbs_vp p v s := by
  rw [logAbs_vp, logAbs_vp, logAbs_vp, NNReal.coe_mul,
    Real.log_mul (NNReal.coe_ne_zero.2 hr) (NNReal.coe_ne_zero.2 hs)]
  ring
end GlobalTheory.HTLat
