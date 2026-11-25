-- Prove2me | solution 1 for GlobalTheory.T.normGroupSign_mul_and_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:07.304885+00:00
-- url     : https://prove2.me/submissions/7b82ed07-59c0-4d45-a052-10b8f0c51c20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOneStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_omega_mul_neg_one


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one | exact GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one <;> assumption)
end _root_.GlobalTheory.T
