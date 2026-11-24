-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.pow_mulVec_mkX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:05.561303+00:00
-- url     : https://prove2.me/submissions/4662a70e-a4ac-4d35-abf2-4417fcdfb191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_companionMatrixOfCoeffs_pow_mulVec_firstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_companion_map
import Theorems.Thm_GlobalTheory_JR_ImgSec_mkX_fst

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
theorem _root_.solution (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    ((mkX a h).1.1 ^ (j : ℕ)) *ᵥ (h *ᵥ e1) = h *ᵥ Pi.single j 1 := by
  rw [mkX_fst hh hd]
  have key : ∀ n : ℕ, (h * (companion a.1).map (algebraMap F E) * h⁻¹) ^ n =
      h * ((companion a.1).map (algebraMap F E)) ^ n * h⁻¹ := by
    intro n; induction n with
    | zero => simp [Matrix.mul_nonsing_inv _ hd]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [key, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    companion_map, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector _ j j.2]
end GlobalTheory.JR.ImgSec
