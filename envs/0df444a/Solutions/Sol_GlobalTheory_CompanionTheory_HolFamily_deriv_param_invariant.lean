-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.deriv_param_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:32.714161+00:00
-- url     : https://prove2.me/submissions/d9e82099-89ad-4cfd-ae03-2cfe6d4a84ba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) :
    ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, deriv (E · (γ * g)) z = deriv (E · g) z := by
  intro z hz γ hγ g
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw using hinv w hw γ hγ g
end GlobalTheory.CompanionTheory.HolFamily
