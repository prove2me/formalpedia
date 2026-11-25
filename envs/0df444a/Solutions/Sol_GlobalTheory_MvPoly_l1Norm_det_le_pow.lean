-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_det_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:12.260086+00:00
-- url     : https://prove2.me/submissions/394882e3-affa-44bb-a096-cfea5a8b3e22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_det_le
import Theorems.Thm_GlobalTheory_MvPoly_factorial_mul_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι * R) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · simp
  · exact (l1Norm_det_le M h).trans (factorial_mul_pow_le _ ((l1Norm_nonneg _).trans (h a a)))
end GlobalTheory.MvPoly
