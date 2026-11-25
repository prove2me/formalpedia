-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:21.048915+00:00
-- url     : https://prove2.me/submissions/71bd61ef-f1e0-4a25-a7a8-7af10c315b03

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
theorem _root_.solution (u w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf u w) = Hf w u := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.FockTranslation
