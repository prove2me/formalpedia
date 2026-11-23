-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.intInt_inv_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:52.653375+00:00
-- url     : https://prove2.me/submissions/0413a4e6-1034-48b2-a743-47102f6350af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_inv_log

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
theorem _root_.solution {x : ℝ} (hx : 1 < x) : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  refine contOn_inv_log.mono fun t ht => ?_
  have := ht.1
  have h2 : (1 : ℝ) < min 2 x := lt_min (by norm_num) hx
  exact lt_of_lt_of_le h2 this
end GlobalTheory.Lin.PsiToPi
