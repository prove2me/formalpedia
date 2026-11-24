-- Prove2me | solution 1 for GlobalTheory.EisNonConst.qTerm_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:02.007849+00:00
-- url     : https://prove2.me/submissions/9892336d-9a88-466c-8096-0a3a3ef57dcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
namespace GlobalTheory.EisNonConst
theorem _root_.solution {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    ((‖qTerm 𝔞 k z p‖ : ℝ) : ℂ) = qTerm 𝔞 k (fun τ => Complex.I * ((z τ).im : ℂ)) p := by
  have hr : (0 : ℝ) ≤ (|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    apply pow_nonneg; apply div_nonneg (abs_nonneg _)
    unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  unfold qTerm qPow
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr]
  push_cast
  congr 1
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]
end GlobalTheory.EisNonConst
