-- Prove2me | solution 1 for GlobalTheory.T.quadraticWeilTorus_mul_unipotent_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:19.176186+00:00
-- url     : https://prove2.me/submissions/b8f035df-911a-4b09-a6da-2cfac182636e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommute
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommuteStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_mOp_nOp


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ), mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.mOp_nOp | exact GlobalTheory.JR.WeilQuad.mOp_nOp | (intros; apply GlobalTheory.JR.WeilQuad.mOp_nOp <;> assumption)
end _root_.GlobalTheory.T
