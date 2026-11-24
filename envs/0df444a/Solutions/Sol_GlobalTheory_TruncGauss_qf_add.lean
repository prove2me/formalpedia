-- Prove2me | solution 1 for GlobalTheory.TruncGauss.qf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:02.609252+00:00
-- url     : https://prove2.me/submissions/7bf977f6-8a3e-4762-9a4a-a7a3b46c61f9

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
theorem _root_.solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (A + B) w = qf A w + qf B w := by
  simp only [qf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
end GlobalTheory.TruncGauss
