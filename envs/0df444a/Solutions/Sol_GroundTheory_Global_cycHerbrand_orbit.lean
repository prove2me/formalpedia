-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:21.047998+00:00
-- url     : https://prove2.me/submissions/7f33edb8-f5dc-4062-bf8d-24147d974c87

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]
variable [MulAction.IsPretransitive G X]
namespace GroundTheory.Global
theorem _root_.solution [Fintype G] (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand ρ σ = cycHerbrand ρ₀ τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv]
end GroundTheory.Global
