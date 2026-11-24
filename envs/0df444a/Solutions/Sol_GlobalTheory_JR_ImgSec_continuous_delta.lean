-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.continuous_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:20.200921+00:00
-- url     : https://prove2.me/submissions/9ce40d00-c2ec-47dc-b568-ff392547570d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_hankel

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
theorem _root_.solution : Continuous (fun a : Inv r k => Delta a) :=
  continuous_hankel.matrix_det
end GlobalTheory.JR.ImgSec
