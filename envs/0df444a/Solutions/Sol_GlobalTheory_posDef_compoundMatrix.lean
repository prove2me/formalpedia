-- Prove2me | solution 1 for GlobalTheory.posDef_compoundMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:26.45222+00:00
-- url     : https://prove2.me/submissions/9fbfc0e9-1ea5-4c85-802d-6b8565c9c8f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_compoundMatrix_mul
import Theorems.Thm_GlobalTheory_compoundMatrix_conjTranspose
import Theorems.Thm_GlobalTheory_compoundMatrix_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]
variable [Fintype n]
namespace GlobalTheory
theorem _root_.solution (k : ℕ) {G : Matrix n n ℂ} (hG : G.PosDef) :
    (compoundMatrix k G).PosDef := by
  let _ := hG.isUnit.invertible
  have hu : IsUnit (compoundMatrix k G) := IsUnit.of_mul_eq_one (compoundMatrix k G⁻¹) (by
    rw [← compoundMatrix_mul, mul_inv_of_invertible, compoundMatrix_one])
  refine (PosSemidef.posDef_iff_isUnit ?_).2 hu
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  rw [hC, compoundMatrix_mul, star_eq_conjTranspose, compoundMatrix_conjTranspose]
  exact posSemidef_conjTranspose_mul_self _
end GlobalTheory
