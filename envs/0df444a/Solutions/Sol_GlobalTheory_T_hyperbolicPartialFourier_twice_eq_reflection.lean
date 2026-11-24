-- Prove2me | solution 1 for GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:08.921854+00:00
-- url     : https://prove2.me/submissions/fb27b536-8842-4e19-a6c5-2f19b2fb5ff5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflectionStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_pt_pt_eq_reflect


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  first | exact @GlobalTheory.JR.Hyp.pt_pt_eq_reflect | exact GlobalTheory.JR.Hyp.pt_pt_eq_reflect | (intros; apply GlobalTheory.JR.Hyp.pt_pt_eq_reflect <;> assumption)
end _root_.GlobalTheory.T
