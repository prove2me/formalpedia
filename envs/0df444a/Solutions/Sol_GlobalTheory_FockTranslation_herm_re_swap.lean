-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_re_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:41.896438+00:00
-- url     : https://prove2.me/submissions/bab2d566-0e9f-4994-b292-a39351acc3f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Theorems.Thm_GlobalTheory_FockTranslation_herm_conj

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
theorem _root_.solution (u w : EuclideanSpace ℂ ι) : (Hf w u).re = (Hf u w).re := by
  rw [← herm_conj u w, Complex.conj_re]
end GlobalTheory.FockTranslation
