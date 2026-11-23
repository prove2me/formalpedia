-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.mom_sec_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:49.685804+00:00
-- url     : https://prove2.me/submissions/b3318d3b-ce74-4cf2-b80d-a33e5815c1cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_companionMatrixOfCoeffs_pow_mulVec_firstBasisVector

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
theorem _root_.solution (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by
  have h1 : mom (sec a) (n + j) = a.2.1 ⬝ᵥ ((companion a.1 ^ n) *ᵥ ((companion a.1 ^ (j : ℕ)) *ᵥ e1)) := by
    simp only [mom, sec, pow_add, ← mulVec_mulVec]; rfl
  rw [h1, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector a.1 j j.2, dotProduct_mulVec, dotProduct_single_one]
end GlobalTheory.JR.ImgSec
