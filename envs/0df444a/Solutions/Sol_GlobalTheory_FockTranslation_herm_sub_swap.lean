-- Prove2me | solution 1 for GlobalTheory.FockTranslation.herm_sub_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:42.38426+00:00
-- url     : https://prove2.me/submissions/1006c9dd-20f0-4493-ab40-c9624d298bb8

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
theorem _root_.solution (u w : EuclideanSpace ℂ ι) :
    Hf w u = Hf u w - 2 * I * ((Hf u w).im : ℂ) := by
  have h := Complex.sub_conj (Hf u w)
  rw [herm_conj] at h
  push_cast at h
  linear_combination -h
end GlobalTheory.FockTranslation
