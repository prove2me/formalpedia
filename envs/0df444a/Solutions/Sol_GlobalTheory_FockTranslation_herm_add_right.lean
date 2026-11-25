-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:33.278568+00:00
-- url     : https://prove2.me/submissions/477c4834-cdd2-4384-88f5-262c32e7acb7

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
theorem _root_.solution (u v w : EuclideanSpace ℂ ι) : Hf u (v + w) = Hf u v + Hf u w := by
  simp [Hf, mul_add, Finset.sum_add_distrib]
end GlobalTheory.FockTranslation
