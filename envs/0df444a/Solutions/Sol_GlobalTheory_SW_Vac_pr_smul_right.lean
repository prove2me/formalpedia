-- Prove2me | solution 1 for GlobalTheory.SW.Vac.pr_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:07.214628+00:00
-- url     : https://prove2.me/submissions/7507ec91-7dce-4953-8ee1-a0b45424d63b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_comm
import Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_left

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
theorem _root_.solution (c : ℚ) (x a : Matrix κ ι ℚ) : pr a (c • x) = c * pr a x := by
  rw [pr_comm, pr_smul_left, pr_comm x]
end GlobalTheory.SW.Vac
