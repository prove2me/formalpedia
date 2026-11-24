-- Prove2me | solution 1 for GlobalTheory.PMonE.additiveSystemFrobeniusPowerSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:24.962801+00:00
-- url     : https://prove2.me/submissions/ca8f0123-1ba9-4b0f-9c49-f69553951f11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (hq : 0 < q)
    (U : ℕ → Matrix m m F) : gsum q D U (fun _ => 0) = 0 := by
  unfold gsum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  have : (fun _ : m => (0 : F) ^ q ^ n) = 0 := by
    funext i; simp [zero_pow (pow_pos hq n).ne']
  rw [this, Matrix.mulVec_zero]
end GlobalTheory.PMonE
