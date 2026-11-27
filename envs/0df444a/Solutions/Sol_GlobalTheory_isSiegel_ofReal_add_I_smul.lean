-- Prove2me | solution 1 for GlobalTheory.isSiegel_ofReal_add_I_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:06.364232+00:00
-- url     : https://prove2.me/submissions/39bb7949-a9cc-418d-88e2-5bc48ef36ec4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
namespace GlobalTheory
theorem _root_.solution {X Y : Matrix ι ι ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    IsSiegel (X.map ofReal + I • Y.map ofReal) := by
  have hY' : Y.IsSymm := by
    ext i j
    simpa using hY.isHermitian.apply i j
  refine ⟨?_, ?_⟩
  · ext i j
    simp [hX.apply, hY'.apply]
  · convert hY
    ext i j
    simp
end GlobalTheory
