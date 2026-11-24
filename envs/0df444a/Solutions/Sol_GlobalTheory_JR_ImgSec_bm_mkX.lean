-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.bm_mkX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:17.374783+00:00
-- url     : https://prove2.me/submissions/3a1e868f-bcce-43de-b43a-980390f73b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_mkX_snd_fst
import Theorems.Thm_GlobalTheory_JR_ImgSec_pow_mulVec_mkX

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by
  ext i j
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.mulVec_single_one]; rfl
end GlobalTheory.JR.ImgSec
