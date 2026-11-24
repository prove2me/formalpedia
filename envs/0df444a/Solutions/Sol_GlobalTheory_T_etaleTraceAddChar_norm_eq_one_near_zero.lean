-- Prove2me | solution 1 for GlobalTheory.T.etaleTraceAddChar_norm_eq_one_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:28.476182+00:00
-- url     : https://prove2.me/submissions/c51f83a6-d9cf-41c1-b290-718e26a36656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZeroStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_psiK_norm_eq_one_near_zero


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  first | exact @GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | exact GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | (intros; apply GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero <;> assumption)
end _root_.GlobalTheory.T
