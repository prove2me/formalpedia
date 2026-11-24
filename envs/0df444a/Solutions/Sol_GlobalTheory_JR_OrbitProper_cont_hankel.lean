-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.cont_hankel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:12.215735+00:00
-- url     : https://prove2.me/submissions/63f3f00c-df30-4160-87dc-bb163fd7e5b7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_sec
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_mom

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
theorem _root_.solution : Continuous (fun a : Inv r F => hankel a) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Inv r F => mom (sec a) ((i : ℕ) + (j : ℕ))
    exact (cont_mom _).comp cont_sec
end GlobalTheory.JR.OrbitProper
