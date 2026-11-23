-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.companionMatrixOfCoeffs_pow_mulVec_firstBasisVector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:10.17895+00:00
-- url     : https://prove2.me/submissions/641aa7f2-b7b4-4ae6-b2cc-15eb4dac79fd

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
theorem _root_.solution (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  | 0, hj => by
    ext i; simp [e1, Pi.single_apply, Fin.ext_iff]
  | j + 1, hj => by
    rw [pow_succ', ← mulVec_mulVec, solution p j (by omega), Matrix.mulVec_single_one]
    ext i
    have : j + 1 ≠ r := by omega
    simp [companion, Pi.single_apply, Fin.ext_iff, this]
end GlobalTheory.JR.ImgSec
