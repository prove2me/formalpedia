-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.fourier_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:17.423376+00:00
-- url     : https://prove2.me/submissions/d7652e2f-2294-41d3-aef8-95869e66f38e

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
import Theorems.Thm_GlobalTheory_LipschitzTR_fourier_lipschitzOneVariableKernel
import Theorems.Thm_GlobalTheory_LipschitzTR_fourier_prod_coord
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) (he : Even k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0)
    (a : F) : 𝓕 (Phi k z) (remb F a) =
      (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ) *
        lhsTerm k z (-a) := by
  rw [show Phi k z = fun ξ : RSp F => ∏ τ, phi1 k (z τ) (ξ τ) from rfl, fourier_prod_coord]
  simp only [remb_apply]
  have h := fun τ : F →+* ℝ => fourier_lipschitzOneVariableKernel k hk he (z τ) (hz τ) (τ a)
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, lhsTerm, Finset.prod_zpow]
  simp [map_neg, sub_eq_add_neg]
end GlobalTheory.LipschitzTR
