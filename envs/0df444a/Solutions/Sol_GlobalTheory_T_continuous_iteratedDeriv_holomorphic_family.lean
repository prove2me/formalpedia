-- Prove2me | solution 1 for GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:24.588265+00:00
-- url     : https://prove2.me/submissions/b8465788-f14b-4743-90b6-69f59fe9ac1d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousIteratedDerivHolomorphicFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousIteratedDerivHolomorphicFamilyStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuous_iteratedDeriv_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | exact GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | (intros; apply GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family <;> assumption)
end _root_.GlobalTheory.T
