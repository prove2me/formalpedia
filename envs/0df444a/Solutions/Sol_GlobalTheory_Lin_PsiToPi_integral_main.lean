-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.integral_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:01.100255+00:00
-- url     : https://prove2.me/submissions/d55e15aa-085d-4d7f-9b00-ac5d0ba3ddd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_hasDerivAt_diff
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (θ : ℤ) {β Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X) :
    ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * mainPsi θ β t =
      (Emain θ β X - mainPsi θ β X / Real.log X) - (Emain θ β Y - mainPsi θ β Y / Real.log Y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u)
  · intro t ht
    rw [Set.uIcc_of_le hYX] at ht
    exact (hasDerivAt_diff θ hβ (lt_of_lt_of_le hY ht.1)).congr_deriv (by ring)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hYX]; exact contOn_main θ β hY
end GlobalTheory.Lin.PsiToPi
