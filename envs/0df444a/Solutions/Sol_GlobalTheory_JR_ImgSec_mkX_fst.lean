-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.mkX_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:53.875738+00:00
-- url     : https://prove2.me/submissions/c913ee0a-eb72-4628-86a8-7ccb535c3543

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_hankel_mul_companion

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
    (mkX a h).1.1 = h * (companion a.1).map (algebraMap F E) * h⁻¹ := by
  have hd' : IsUnit hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  simp only [mkX]
  rw [← hankel_mul_companion, Matrix.map_mul, ← hh, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]
end GlobalTheory.JR.ImgSec
