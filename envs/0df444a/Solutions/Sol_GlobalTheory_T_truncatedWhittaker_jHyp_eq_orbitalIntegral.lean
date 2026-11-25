-- Prove2me | solution 1 for GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:59.481044+00:00
-- url     : https://prove2.me/submissions/691c9e4f-9d8e-4d86-9693-e06fa7be0048

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Theorems.Thm_GlobalTheory_whittaker_jHyp_eq_orbK


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  first | exact @GlobalTheory.whittaker_jHyp_eq_orbK | exact GlobalTheory.whittaker_jHyp_eq_orbK | (intros; apply GlobalTheory.whittaker_jHyp_eq_orbK <;> assumption)
end _root_.GlobalTheory.T
