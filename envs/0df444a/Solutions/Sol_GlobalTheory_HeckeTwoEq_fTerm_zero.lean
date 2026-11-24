-- Prove2me | solution 1 for GlobalTheory.HeckeTwoEq.fTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:36.360165+00:00
-- url     : https://prove2.me/submissions/8cbcd28c-3d3a-4aa4-9046-711bcaaa9eb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinLatticeClassWeightTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZetaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationEqLatticeSeries
import Theorems.Thm_GlobalTheory_HeckeTwoEq_ofReal_prod_cpow
import Theorems.Thm_GlobalTheory_HeckeTwoEq_prod_abs_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoEq
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoEq
theorem _root_.solution [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring
end GlobalTheory.HeckeTwoEq
