-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.norm_half_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:07.247304+00:00
-- url     : https://prove2.me/submissions/b279ea79-baa5-4897-8b4a-1910eab52d0d

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
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
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
theorem _root_.solution (l : EuclideanSpace ℂ I) :
    ‖l‖ ^ 2 ≤ 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖l i‖ ^ 2 ≤ ∑ _i : I, 4 * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_le_pi_norm (fun i => l i / 2 : I → ℂ) i
        have h2 : ‖l i‖ = 2 * ‖(fun i => l i / 2 : I → ℂ) i‖ := by
          simp only [norm_div, Complex.norm_ofNat]; ring
        rw [h2]
        nlinarith [norm_nonneg ((fun i => l i / 2 : I → ℂ) i)]
    _ = 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end GlobalTheory.HeckePoisson
