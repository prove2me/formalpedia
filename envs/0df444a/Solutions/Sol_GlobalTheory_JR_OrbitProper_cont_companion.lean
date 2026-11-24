-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.cont_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:41.442744+00:00
-- url     : https://prove2.me/submissions/76f33c30-3e90-48c6-80ba-fa302c058b8e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.JR.OrbitProper
theorem _root_.solution : Continuous (fun p : Fin r → F => companion p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [companion, of_apply]
  split_ifs
  · exact ((continuous_apply i)).neg
  all_goals exact continuous_const
end GlobalTheory.JR.OrbitProper
