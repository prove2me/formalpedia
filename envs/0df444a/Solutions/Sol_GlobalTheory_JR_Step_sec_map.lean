-- Prove2me | solution 1 for GlobalTheory.JR.Step.sec_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:47.289637+00:00
-- url     : https://prove2.me/submissions/e47054c2-f31b-4aea-91a0-619d94a3afa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')
namespace GlobalTheory.JR.Step
theorem _root_.solution (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [sec, glMap]
    split_ifs <;> simp
  · rfl
  · rfl
end GlobalTheory.JR.Step
