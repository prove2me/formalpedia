-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.contOn_inv_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.921817+00:00
-- url     : https://prove2.me/submissions/cf54f752-10a9-4777-8e12-da1567307a73

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
theorem _root_.solution : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := fun t ht =>
  (continuousAt_const.div (Real.continuousAt_log (by have : 1 < t := ht; linarith))
    (Real.log_pos ht).ne').continuousWithinAt
end GlobalTheory.Lin.PsiToPi
