-- Prove2me | solution 1 for GlobalTheory.T.kirillov_vanishing_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:19.27256+00:00
-- url     : https://prove2.me/submissions/87b8587f-58e4-4ed5-a9c7-0d6e8f88cf52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimitStatement
import Theorems.Thm_GlobalTheory_JR_kirillov_vanishing_l2


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.kirillov_vanishing_l2 | exact GlobalTheory.JR.kirillov_vanishing_l2 | (intros; apply GlobalTheory.JR.kirillov_vanishing_l2 <;> assumption)
end _root_.GlobalTheory.T
