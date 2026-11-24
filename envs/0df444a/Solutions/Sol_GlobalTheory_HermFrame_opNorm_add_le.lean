-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:48.187309+00:00
-- url     : https://prove2.me/submissions/b7a49446-0f7e-407e-9363-53712814b9fc

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_add_le

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
theorem _root_.solution (hH : H.PosDef) (hK : K.PosSemidef) (S T : Matrix n m ℂ) :
    opNorm H K (S + T) ≤ opNorm H K S + opNorm H K T :=
  opNorm_le_of_bound (add_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by
    rw [add_mulVec, add_mul]
    exact (gnorm_add_le hK _ _).trans
      (add_le_add (gnorm_mulVec_le hH hK S v) (gnorm_mulVec_le hH hK T v))
end GlobalTheory.HermFrame
