-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.continuous_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:53.635721+00:00
-- url     : https://prove2.me/submissions/79c896f5-3db5-447d-8aa9-b52d7765b76c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector

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
theorem _root_.solution : Continuous (fun p : Fin r → k => companion p) :=
  continuous_matrix fun i j => by
    simp only [companion, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const
end GlobalTheory.JR.ImgSec
