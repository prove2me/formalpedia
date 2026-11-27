-- Prove2me | solution 1 for GlobalTheory.TorusAtAssembly.im_Hf_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:58.509586+00:00
-- url     : https://prove2.me/submissions/946b67b3-81c7-4a69-b47b-82e7e63c0d5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.TorusAtAssembly
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.TorusAtAssembly
theorem _root_.solution (x z : EuclideanSpace ℂ ι) :
    (Hf (-x) z).im = -(Hf x z).im := by
  simp [Hf, Finset.sum_neg_distrib]
end GlobalTheory.TorusAtAssembly
