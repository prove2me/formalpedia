-- Prove2me | solution 1 for GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:11.074802+00:00
-- url     : https://prove2.me/submissions/b1e991e4-cc56-4d01-bbf8-334865aa99b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNormStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussTrans_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  first | exact @GlobalTheory.JR.WeilQuad.GaussTrans.main | exact GlobalTheory.JR.WeilQuad.GaussTrans.main | (intros; apply GlobalTheory.JR.WeilQuad.GaussTrans.main <;> assumption)
end _root_.GlobalTheory.T
