-- Prove2me | solution 1 for GlobalTheory.T.hasGaussIntegralCompactOpen_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:10.902991+00:00
-- url     : https://prove2.me/submissions/3279dfe9-459d-4188-be40-3d6c910def4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompactOpenPi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompactOpenPiStatement
import Theorems.Thm_GlobalTheory_KSp_hasGauss_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  first | exact @GlobalTheory.KSp.hasGauss_pi | exact GlobalTheory.KSp.hasGauss_pi | (intros; apply GlobalTheory.KSp.hasGauss_pi <;> assumption)
end _root_.GlobalTheory.T
