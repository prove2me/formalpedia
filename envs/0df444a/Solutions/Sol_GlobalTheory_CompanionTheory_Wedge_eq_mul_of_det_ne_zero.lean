-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.eq_mul_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:12:34.932838+00:00
-- url     : https://prove2.me/submissions/86db6d80-147a-4541-92df-e055a4cb526f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_updateRow_submatrix_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution {K ι κ : Type} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (hd : (U.submatrix s id).det ≠ 0) :
    U = (Matrix.of fun i k => (U.submatrix s id).det⁻¹ *
      (U.submatrix (Function.update s k i) id).det) * U.submatrix s id := by
  ext i l
  rw [Matrix.mul_apply]
  have key : ∀ k, (U.submatrix (Function.update s k i) id).det
      = Matrix.cramer (U.submatrix s id).transpose (U i) k := by
    intro k
    rw [← updateRow_submatrix_eq, Matrix.cramer_apply, Matrix.updateCol_transpose,
      Matrix.det_transpose]
  have hv := Matrix.mulVec_cramer (U.submatrix s id).transpose (U i)
  rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hv
  have hl := congrFun hv l
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hl
  simp only [Matrix.of_apply, key, mul_assoc]
  rw [← Finset.mul_sum, hl, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
end GlobalTheory.CompanionTheory.Wedge
