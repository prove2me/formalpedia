-- Prove2me | solution 1 for GroundTheory.Global.cycTateZeroOrbitEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:29.330578+00:00
-- url     : https://prove2.me/submissions/83b081f7-044b-4a9c-b7c3-9f2c3175b024

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk

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
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycSubOne ρ σ).ker) :
    cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ :=
  rfl
end GroundTheory.Global
