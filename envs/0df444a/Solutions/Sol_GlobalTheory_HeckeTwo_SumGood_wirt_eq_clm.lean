-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.wirt_eq_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:40.976209+00:00
-- url     : https://prove2.me/submissions/0ef28cef-a5bb-4bb4-859e-395e0fa7136d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {Φ : Type} [Fintype Φ] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution (τ : Φ) (b : Bool) :
    ∃ Λ : ((Φ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ, ∀ (h : (Φ → ℂ) → ℂ) (z : Φ → ℂ),
      wirt τ b h z = Λ (fderiv ℝ h z) := by
  classical
  refine ⟨(1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ 1) +
    (ContinuousLinearMap.mul ℝ ℂ (if b then I else -I)).comp
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ I))), fun h z => ?_⟩
  simp only [wirt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  push_cast
  ring
end GlobalTheory.HeckeTwo.SumGood
