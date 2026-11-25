-- Prove2me | solution 1 for GlobalTheory.RealWeil.Superpos.hasFDerivAt_itg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:40.100706+00:00
-- url     : https://prove2.me/submissions/e97967b8-6d99-4848-ad37-2e54c268a2ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
open GlobalTheory.RealWeil.Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}
namespace GlobalTheory.RealWeil.Superpos
theorem _root_.solution {g : V → B} (hg : Differentiable ℝ g) (h : Y → ℂ) (v : V) (y : Y) :
    HasFDerivAt (fun w => itg om ρ ι h g w y) (dI om ρ ι h g v y) v := by
  have b1 : HasFDerivAt (fun w : V => ((om w (ι y) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om.flip (ι y))) v :=
    (Complex.ofRealCLM.comp (om.flip (ι y))).hasFDerivAt
  have b2 := ((b1.const_mul (2 * π * I : ℂ)).cexp).const_mul (h y)
  have b3 : HasFDerivAt (fun w => ρ (ι y) (g w)) (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) v :=
    ((ρ (ι y)).restrictScalars ℝ).hasFDerivAt.comp v (hg v).hasFDerivAt
  exact b2.smul b3
end GlobalTheory.RealWeil.Superpos
