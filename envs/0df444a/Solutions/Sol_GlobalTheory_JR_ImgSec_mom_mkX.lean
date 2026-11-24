-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.mom_mkX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:21.171803+00:00
-- url     : https://prove2.me/submissions/75c3215b-4558-45e9-8ced-b360eb184ea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c
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
theorem _root_.solution (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    mom (mkX a h).toGl j = algebraMap F E (a.2.1 j) := by
  have h0 : 0 < r := j.pos
  simp only [mom, Hn.toGl]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh]
  have he : star (e1 : Fin r → E) = Pi.single (⟨0, h0⟩ : Fin r) 1 := by
    ext i; by_cases hi : (i : ℕ) = 0 <;> simp [e1, hi, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one, single_one_dotProduct]
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hankel_apply']
  simp
end GlobalTheory.JR.ImgSec
