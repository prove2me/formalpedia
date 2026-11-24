-- Prove2me | solution 1 for GlobalTheory.T.quadraticWeil_fOp_nOp_fOp_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:19.868006+00:00
-- url     : https://prove2.me/submissions/86cafbc4-d1bb-432d-8e98-b768ce9ebdaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGaussStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_fOp_nOp_fOp


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G : ℂ), IsStableGauss A ψ x μ u G → ∀ φ : A.L → ℂ, IsTest φ → ∀ z, fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) * fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | exact GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | (intros; apply GlobalTheory.JR.WeilQuad.fOp_nOp_fOp <;> assumption)
end _root_.GlobalTheory.T
