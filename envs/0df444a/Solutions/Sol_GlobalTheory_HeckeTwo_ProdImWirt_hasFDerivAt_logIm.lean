-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_logIm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:21:48.284348+00:00
-- url     : https://prove2.me/submissions/dae69dae-2533-443e-a24f-ba28a2168fc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn

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
theorem _root_.solution (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2
end GlobalTheory.HeckeTwo.ProdImWirt
