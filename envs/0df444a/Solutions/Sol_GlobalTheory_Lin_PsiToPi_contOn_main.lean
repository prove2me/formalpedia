-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.contOn_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.998461+00:00
-- url     : https://prove2.me/submissions/b53b2e74-04af-4ea7-b453-284465b3aa1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_w

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
theorem _root_.solution (θ : ℤ) (β : ℝ) {Y X : ℝ} (hY : 1 < Y) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) (Set.Icc Y X) := by
  refine (contOn_w hY).mul fun t ht => ?_
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  exact (continuousAt_id.sub (continuousAt_const.mul
    ((Real.continuousAt_rpow_const t β (Or.inl (by linarith))).div_const β))).continuousWithinAt
end GlobalTheory.Lin.PsiToPi
