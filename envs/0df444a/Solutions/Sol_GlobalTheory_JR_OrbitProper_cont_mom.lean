-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.cont_mom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:54.250885+00:00
-- url     : https://prove2.me/submissions/ff5a1ee5-e17b-44d7-8247-5c0f05ba9309

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
theorem _root_.solution (n : ℕ) : Continuous (fun Y : Gl r F => mom Y n) := by
  unfold mom
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).dotProduct
    (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow n).matrix_mulVec (continuous_fst.comp continuous_snd))
end GlobalTheory.JR.OrbitProper
