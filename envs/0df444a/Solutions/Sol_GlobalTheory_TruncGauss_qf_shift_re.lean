-- Prove2me | solution 1 for GlobalTheory.TruncGauss.qf_shift_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:48.705807+00:00
-- url     : https://prove2.me/submissions/8e5ac2ff-cfdc-4aa0-b58c-a00c1dbaea93

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_qf_add
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
theorem _root_.solution {n : ℕ} (m η : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    (qf ((m : ℂ) • (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) w).re =
      m * ((qf H w).re + η * ‖w‖ ^ 2) := by
  rw [qf_smul, qf_add, qf_smul, qf_one, Complex.re_ofReal_mul, Complex.add_re,
    ← Complex.ofReal_mul, Complex.ofReal_re]
end GlobalTheory.TruncGauss
