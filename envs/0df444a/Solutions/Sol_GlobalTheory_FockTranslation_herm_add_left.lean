-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:19.040801+00:00
-- url     : https://prove2.me/submissions/7f60aa35-f1a5-4e2f-9b52-a49db1f6a25a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws

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
theorem _root_.solution (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]
end GlobalTheory.FockTranslation
