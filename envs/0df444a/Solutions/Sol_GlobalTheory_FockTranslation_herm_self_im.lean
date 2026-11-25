-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:08.347796+00:00
-- url     : https://prove2.me/submissions/48b00eb9-e1a1-44a9-af0b-f94ce2f74986

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Theorems.Thm_GlobalTheory_FockTranslation_herm_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory.FockTranslation
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.FockTranslation
theorem _root_.solution (x : EuclideanSpace ℂ ι) : (Hf x x).im = 0 := by
  rw [herm_self, Complex.ofReal_im]
end GlobalTheory.FockTranslation
