-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.fourier_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:14.221793+00:00
-- url     : https://prove2.me/submissions/fa6bddf6-c328-4354-94dc-1311e9a71cde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeThetaKernelPoissonSummation
import Theorems.Thm_GlobalTheory_HeckePoisson_integrable_hmon_gauss
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_fourier_harmonicMonomial_mul_gaussian_complex
import Theorems.Thm_GlobalTheory_T_fourier_prod_single_coordinate_functions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckePoisson
theorem _root_.solution (n : I → ℤ) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) l = kappa n * gauss n (fun i => l i / 2) := by
  have h := GlobalTheory.T.fourier_prod_single_coordinate_functions I (fun i z => hmon (n i) z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ))
    (fun i => integrable_hmon_gauss (n i)) l
  have e : (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) =
      fun w => ∏ i, (hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)) := rfl
  rw [e, h]
  simp only [GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex]
  unfold kappa gauss
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
  simp [one_div, inv_pow]
end GlobalTheory.HeckePoisson
