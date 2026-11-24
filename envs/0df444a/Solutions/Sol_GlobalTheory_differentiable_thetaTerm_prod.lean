-- Prove2me | solution 1 for GlobalTheory.differentiable_thetaTerm_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:35.308014+00:00
-- url     : https://prove2.me/submissions/15cd7469-798f-4ceb-ae8f-3efc1dea0584

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by
  unfold thetaTerm eC
  simp only [dotProduct, Matrix.mulVec, shiftVec, ofRealVec, Pi.add_apply, Matrix.of_apply]
  fun_prop
end GlobalTheory
