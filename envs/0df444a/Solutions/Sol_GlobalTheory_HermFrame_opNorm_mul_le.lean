-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:28.101414+00:00
-- url     : https://prove2.me/submissions/741fefa0-d8bf-4e66-b745-84911feff38c

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
theorem _root_.solution (hH : H.PosDef) (hK : K.PosDef) (hL : L.PosSemidef) (S : Matrix l n ℂ)
    (T : Matrix n m ℂ) : opNorm H L (S * T) ≤ opNorm K L S * opNorm H K T :=
  opNorm_le_of_bound (mul_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _)) fun v => by
    rw [← mulVec_mulVec, mul_assoc]
    exact (gnorm_mulVec_le hK hL S _).trans
      (mul_le_mul_of_nonneg_left (gnorm_mulVec_le hH hK.posSemidef T v) (opNorm_nonneg _ _ _))
end GlobalTheory.HermFrame
