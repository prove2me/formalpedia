-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.companion_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:40.629552+00:00
-- url     : https://prove2.me/submissions/d843f122-be00-44be-8438-e074ca1b5d13

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
theorem _root_.solution {k' : Type} [CommRing k'] (φ : k →+* k') (p : Fin r → k) :
    (companion p).map φ = companion (fun i => φ (p i)) := by
  ext i j; simp only [companion, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
end GlobalTheory.JR.ImgSec
