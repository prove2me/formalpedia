-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.cont_Cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:39.965599+00:00
-- url     : https://prove2.me/submissions/4ffdf10f-ad8e-4469-8aea-3fb4227cdb96

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
theorem _root_.solution : Continuous (fun Y : Gl r F => Cm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j
    exact (continuous_apply j).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).matrix_vecMul
        ((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _))
end GlobalTheory.JR.OrbitProper
