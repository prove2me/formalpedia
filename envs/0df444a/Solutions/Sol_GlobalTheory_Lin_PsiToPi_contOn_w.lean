-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.contOn_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:46.846202+00:00
-- url     : https://prove2.me/submissions/9b2d2a01-e647-4302-a471-f7c05c62a511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError

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
theorem _root_.solution {Y X : ℝ} (hY : 1 < Y) : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.Icc Y X) := by
  intro t ht
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  have hl := Real.log_pos h1
  exact (continuousAt_const.div (continuousAt_id.mul ((Real.continuousAt_log (by linarith)).pow 2))
    (mul_ne_zero (by show t ≠ 0; linarith) (pow_ne_zero 2 hl.ne'))).continuousWithinAt
end GlobalTheory.Lin.PsiToPi
