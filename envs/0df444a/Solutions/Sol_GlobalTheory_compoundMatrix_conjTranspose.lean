-- Prove2me | solution 1 for GlobalTheory.compoundMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:51.656132+00:00
-- url     : https://prove2.me/submissions/ee80aa2d-2d66-4e23-9f8a-2fc7d5a81b16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

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
namespace GlobalTheory
theorem _root_.solution (k : ℕ) (A : Matrix l n ℂ) :
    compoundMatrix k Aᴴ = (compoundMatrix k A)ᴴ := by
  ext I J
  simp only [compoundMatrix, of_apply, conjTranspose_apply, ← det_conjTranspose,
    conjTranspose_submatrix]
end GlobalTheory
