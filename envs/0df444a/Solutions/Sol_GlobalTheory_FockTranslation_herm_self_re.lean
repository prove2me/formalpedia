-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:05.592092+00:00
-- url     : https://prove2.me/submissions/f3e7dc2e-8e14-4eae-a744-26663529b080

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
theorem _root_.solution (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [herm_self, Complex.ofReal_re]
end GlobalTheory.FockTranslation
