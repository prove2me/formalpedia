-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:55.80492+00:00
-- url     : https://prove2.me/submissions/2a58466c-141f-4117-a2ca-187bc766cf22

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (hH : H.PosDef) (hK : K.PosSemidef) (c : ℂ) (T : Matrix n m ℂ) :
    opNorm H K (c • T) ≤ ‖c‖ * opNorm H K T :=
  opNorm_le_of_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _ _ _)) fun v => by
    rw [smul_mulVec, gnorm_smul hK, mul_assoc]
    exact mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK T v) (norm_nonneg _)
end GlobalTheory.HermFrame
