-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.hankel_mul_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:11.413802+00:00
-- url     : https://prove2.me/submissions/3844b814-d3cf-4f0f-b6e1-0dda5f3315f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_mom_sec_add
import Theorems.Thm_P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c

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
theorem _root_.solution (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by
  ext i j
  have h2 : hankelShift a i j = mom (sec a) (((i : ℕ) + 1) + j) := by simp [hankelShift]; ring_nf
  rw [h2, mom_sec_add, Matrix.mul_apply, pow_succ, ← Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul, dotProduct, hankel_apply']
end GlobalTheory.JR.ImgSec
