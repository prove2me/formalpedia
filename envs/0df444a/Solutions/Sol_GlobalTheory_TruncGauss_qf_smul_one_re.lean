-- Prove2me | solution 1 for GlobalTheory.TruncGauss.qf_smul_one_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:05.414744+00:00
-- url     : https://prove2.me/submissions/d79c3c48-75c2-4a08-8acb-9bcc18eb562f

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_qf_smul
import Theorems.Thm_GlobalTheory_TruncGauss_qf_one

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
theorem _root_.solution {n : ℕ} (c : ℝ) (w : V n) :
    (qf ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) w).re = c * ‖w‖ ^ 2 := by
  rw [qf_smul, qf_one, ← Complex.ofReal_mul, Complex.ofReal_re]
end GlobalTheory.TruncGauss
