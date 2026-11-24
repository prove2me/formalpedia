-- Prove2me | solution 1 for GlobalTheory.ColLie.hasDerivAt_coeff_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:44.874254+00:00
-- url     : https://prove2.me/submissions/714309ab-15cf-4c75-91aa-f27c1f4ac7e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
namespace GlobalTheory.ColLie
theorem _root_.solution {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => coeff m (A h)) (coeff m B) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => coeff m (A h * X w)) (coeff m (B * X w)) 0 := by
  classical
  simp only [coeff_mul_X']
  split_ifs
  · exact hA _
  · exact hasDerivAt_const _ _
end GlobalTheory.ColLie
