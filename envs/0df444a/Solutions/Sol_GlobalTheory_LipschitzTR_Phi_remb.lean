-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.Phi_remb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:10.77649+00:00
-- url     : https://prove2.me/submissions/85f045a4-032f-4f33-a044-cf4d31673003

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzFormulaTotallyRealPoisson
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) :
    Phi k z (remb F ν) =
      if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 := by
  unfold Phi
  by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
  · rw [if_pos hc, Finset.prod_congr rfl fun τ _ => by rw [remb_apply, phi1, if_pos (hc τ)],
      Finset.prod_mul_distrib, ← Complex.exp_sum, rhsTerm, Finset.abs_prod, ← Finset.prod_pow, Complex.ofReal_prod]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨τ, hτ⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [remb_apply, phi1, if_neg (not_lt.2 hτ)])
end GlobalTheory.LipschitzTR
