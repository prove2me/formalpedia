-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.hankel_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:10.519843+00:00
-- url     : https://prove2.me/submissions/69f1bbe5-c374-42a2-be92-d392908d80d1

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
variable {k : Type} [CommRing k] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (a : Inv r k) : (hankel a).IsSymm := by
  ext i j; simp [hankel, add_comm]
end GlobalTheory.JR.ImgSec
