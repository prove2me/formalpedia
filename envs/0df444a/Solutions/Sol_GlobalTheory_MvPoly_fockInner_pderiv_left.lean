-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockInner_pderiv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:59.14751+00:00
-- url     : https://prove2.me/submissions/61fd174f-ec2b-44f6-b579-5651f8c52564

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_fockInner_conj_symm
import Theorems.Thm_GlobalTheory_MvPoly_fockInner_X_mul_left

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
    fockInner (pderiv i P) Q = fockInner P (X i * Q) := by
  rw [← fockInner_conj_symm, ← fockInner_X_mul_left, fockInner_conj_symm]
end GlobalTheory.MvPoly
