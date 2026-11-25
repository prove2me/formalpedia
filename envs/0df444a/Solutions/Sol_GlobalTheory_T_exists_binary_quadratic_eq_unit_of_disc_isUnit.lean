-- Prove2me | solution 1 for GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:02.383806+00:00
-- url     : https://prove2.me/submissions/6814b3d4-ccb7-448b-93dc-de62814347d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegersStatement
import Theorems.Thm_GlobalTheory_BinaryUnitForm_exists_eq_adicCompletionIntegers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
end _root_.GlobalTheory.T
