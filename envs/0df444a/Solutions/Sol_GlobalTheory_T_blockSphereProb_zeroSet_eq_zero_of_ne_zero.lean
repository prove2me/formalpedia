-- Prove2me | solution 1 for GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:28:25.415703+00:00
-- url     : https://prove2.me/submissions/f36b8c6a-ad75-49b0-8c91-acf021ef2cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Theorems.Thm_GlobalTheory_SphereMeanNull_blockSphereProb_zeroSet_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B n : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g → blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  first | exact @GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | exact GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | (intros; apply GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero <;> assumption)
end _root_.GlobalTheory.T
