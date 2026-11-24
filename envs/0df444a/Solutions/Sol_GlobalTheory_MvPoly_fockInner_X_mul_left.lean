-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockInner_X_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:53.977517+00:00
-- url     : https://prove2.me/submissions/e4ae06b0-965b-44de-bb00-98c15670b822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_multiFactorial_add_single
import Theorems.Thm_GlobalTheory_MvPoly_fockInner_monomial_left

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
variable [NormedCommRing K] [NormedCommRing L]
variable {𝕜 : Type*} [RCLike 𝕜]
namespace GlobalTheory.MvPoly
theorem _root_.solution (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (X i * P) Q = fockInner P (pderiv i Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, one_mul, fockInner_monomial_left, fockInner_monomial_left, coeff_pderiv,
      add_comm _ α, multiFactorial_add_single]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_natCast, map_one]
    ring
  | add P P' h h' => rw [mul_add, fockInner_add_left, fockInner_add_left, h, h']
end GlobalTheory.MvPoly
