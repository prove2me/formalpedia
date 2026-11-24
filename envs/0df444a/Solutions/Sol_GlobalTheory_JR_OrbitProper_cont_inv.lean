-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.cont_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:44.993025+00:00
-- url     : https://prove2.me/submissions/bdad53cf-b5f0-44d9-be3c-bf93469f1f81

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_charpoly_coeff
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
theorem _root_.solution : Continuous (fun Y : Gl r F => inv Y) := by
  unfold inv
  exact (continuous_pi fun i : Fin r => (cont_charpoly_coeff (r := r) (F := F) (i : ℕ)).comp continuous_fst).prodMk
    ((continuous_pi fun i : Fin r => cont_mom (r := r) (F := F) (i : ℕ)).prodMk
      (show Continuous fun Y : Gl r F => Y.2.2.2 from continuous_snd.comp (continuous_snd.comp continuous_snd)))
end GlobalTheory.JR.OrbitProper
