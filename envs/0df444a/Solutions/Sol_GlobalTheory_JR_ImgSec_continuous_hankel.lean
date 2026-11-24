-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.continuous_hankel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:40.702878+00:00
-- url     : https://prove2.me/submissions/6f909148-19af-4c56-83ee-222e96f20709

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_mom_sec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution : Continuous (fun a : Inv r k => hankel a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _
end GlobalTheory.JR.ImgSec
