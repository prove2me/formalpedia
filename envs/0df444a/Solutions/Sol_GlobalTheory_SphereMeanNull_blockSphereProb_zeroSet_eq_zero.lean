-- Prove2me | solution 1 for GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:18:54.303846+00:00
-- url     : https://prove2.me/submissions/c048c204-4c8c-4845-959d-fcb39827b956

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZero
import Theorems.Thm_GlobalTheory_SphereMeanNull_exists_blockSphere_eval_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLogIntegrable
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphere_logMean_bound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_null_of_logBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanNull
namespace GlobalTheory.SphereMeanNull
theorem _root_.solution : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu
end GlobalTheory.SphereMeanNull
