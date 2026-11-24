-- Prove2me | solution 1 for GlobalTheory.HeckeTwoPoisson.fourier_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:46.076156+00:00
-- url     : https://prove2.me/submissions/abcbf5a1-78ff-4971-9262-d83672b54363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdeal
import Theorems.Thm_GlobalTheory_HeckeTwoPoisson_hTrans_decay
import Theorems.Thm_GlobalTheory_HeckeTwoPoisson_phi_line
import Theorems.Thm_GlobalTheory_HeckeTwoPoisson_hTrans_eq_fourier
import Theorems.Thm_GlobalTheory_HeckeTwoPoisson_continuous_hTrans
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hTrans_eq_fourier
import Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_phi_line
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
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoPoisson
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR
namespace GlobalTheory.HeckeTwoPoisson
theorem _root_.solution (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (c s : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      phi σ (((c - s : ℝ) : ℂ) + (y : ℂ) * I) := by
  set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf
  obtain ⟨hfc, hfi⟩ := phi_line σ hσ y hy
  have hH := hTrans_eq_fourier σ y
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, hC⟩ := hTrans_decay σ hσ y hy 2
    have h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine (h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · rw [← hH]; exact (continuous_hTrans σ hσ y hy).aestronglyMeasurable
    · have := hC t
      rw [← hH]
      simpa [Real.norm_eq_abs] using this
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi
  have hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      𝓕 (𝓕 f) (s - c) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmod]
  have h3 := congrFun hinv (-(s - c))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h3
  rw [h3, hf]
  congr 2
  push_cast
  ring
end GlobalTheory.HeckeTwoPoisson
