-- Prove2me | solution 1 for GlobalTheory.GaussHerm.det_toEuclideanLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:54.14294+00:00
-- url     : https://prove2.me/submissions/ef5b6e53-7562-45ce-9a2d-2294bccd9671

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm
namespace GlobalTheory.GaussHerm
theorem _root_.solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by
  have : Matrix.toEuclideanLin C = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis C := by
    ext v i : 2
    simp [Matrix.toLin_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.single_apply, Pi.single_apply]
  rw [this, LinearMap.det_toLin]
end GlobalTheory.GaussHerm
