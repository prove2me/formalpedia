-- Prove2me | solution 1 for GlobalTheory.TruncGauss.qf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:31.691865+00:00
-- url     : https://prove2.me/submissions/845636e7-5977-45c8-a67e-c6472e49fa53

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef

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
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (c • A) w = c * qf A w := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end GlobalTheory.TruncGauss
