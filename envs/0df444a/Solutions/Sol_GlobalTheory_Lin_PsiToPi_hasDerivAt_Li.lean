-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.hasDerivAt_Li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:56.043191+00:00
-- url     : https://prove2.me/submissions/9c299d3b-f168-4c6d-875a-a641e5741524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_inv_log
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_intInt_inv_log

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
theorem _root_.solution {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x :=
  intervalIntegral.integral_hasDerivAt_right (intInt_inv_log hx)
    (contOn_inv_log.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (contOn_inv_log.continuousAt (Ioi_mem_nhds hx))
end GlobalTheory.Lin.PsiToPi
