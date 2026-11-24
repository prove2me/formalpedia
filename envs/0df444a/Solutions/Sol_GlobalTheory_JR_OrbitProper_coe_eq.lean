-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:11.01227+00:00
-- url     : https://prove2.me/submissions/6031beea-502a-4abe-8f85-607152a9f138

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_Bm_sec
import Theorems.Thm_GlobalTheory_JR_OrbitProper_Bm_act

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
theorem _root_.solution (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by
  rw [Bm_act, Bm_sec, mul_one]
end GlobalTheory.JR.OrbitProper
