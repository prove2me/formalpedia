-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.hasDerivAt_invpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:53.217805+00:00
-- url     : https://prove2.me/submissions/65284931-6467-4843-aa6f-8c867465fedb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY

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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {f : ℝ → ℂ} {c : ℂ} {y : ℝ} (hf : HasDerivAt f c y) (hne : f y ≠ 0) (n : ℕ) :
    HasDerivAt (fun y' => (f y')⁻¹ ^ n) (-(n : ℂ) * c * (f y)⁻¹ ^ (n + 1)) y := by
  have hz := (hasDerivAt_zpow (-(n : ℤ)) (f y) (Or.inl hne)).comp y hf
  have hfun : (fun y' => (f y')⁻¹ ^ n) = (fun x : ℂ => x ^ (-(n : ℤ))) ∘ f := by
    funext y'; simp [Function.comp, zpow_neg, inv_pow]
  rw [hfun]
  refine hz.congr_deriv ?_
  have : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast, inv_pow]; push_cast; ring
end GlobalTheory.HeckeTwoDY
