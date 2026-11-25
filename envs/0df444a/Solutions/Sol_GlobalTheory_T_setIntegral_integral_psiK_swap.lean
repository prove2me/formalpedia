-- Prove2me | solution 1 for GlobalTheory.T.setIntegral_integral_psiK_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:12.184831+00:00
-- url     : https://prove2.me/submissions/33f4c53b-b809-4eb1-95cf-4835164800df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwapStatement
import Theorems.Thm_GlobalTheory_JR_Et_whittaker_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  first | exact @GlobalTheory.JR.Et.whittaker_swap | exact GlobalTheory.JR.Et.whittaker_swap | (intros; apply GlobalTheory.JR.Et.whittaker_swap <;> assumption)
end _root_.GlobalTheory.T
