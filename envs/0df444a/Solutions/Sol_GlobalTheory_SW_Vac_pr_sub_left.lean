-- Prove2me | solution 1 for GlobalTheory.SW.Vac.pr_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:08.737605+00:00
-- url     : https://prove2.me/submissions/7d95eeb2-aa99-49eb-9139-93902e8ff04d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_neg_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (x y a : Matrix κ ι ℚ) : pr (x - y) a = pr x a - pr y a := by
  rw [sub_eq_add_neg, pr_add_left, pr_neg_left, sub_eq_add_neg]
end GlobalTheory.SW.Vac
