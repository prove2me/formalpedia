-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_expo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:48.809871+00:00
-- url     : https://prove2.me/submissions/821d13dc-7184-40e9-944c-73893f110546

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_hasFDerivAt_logIm

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]
namespace GlobalTheory.HeckeTwo.ProdImWirt
theorem _root_.solution (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this
end GlobalTheory.HeckeTwo.ProdImWirt
