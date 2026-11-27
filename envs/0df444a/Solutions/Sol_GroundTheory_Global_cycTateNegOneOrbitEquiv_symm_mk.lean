-- Prove2me | solution 1 for GroundTheory.Global.cycTateNegOneOrbitEquiv_symm_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:26.011355+00:00
-- url     : https://prove2.me/submissions/c52f8a83-55ce-4755-88eb-3adad264d3fe

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Theorems.Thm_GroundTheory_Global_apply_sub_self_mem_range_cycSubOne
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff


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
theorem _root_.solution [Fintype G] [DecidableEq X]
    (ρ : Representation k G (∀ x, M x))
    (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D]
    (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (b : (cycNorm ρ₀).ker) :
    (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).symm (QuotientAddGroup.mk b) =
      QuotientAddGroup.mk ⟨Pi.single x₀ (b : M x₀), single_mem_ker_cycNorm hρ hD hρ₀ b.2⟩ := by
  rw [AddEquiv.symm_apply_eq, eq_comm]
  let _ : Finite X := finite_of_isPretransitive G x₀
  let _ : Fintype X := Fintype.ofFinite X
  show orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ _ = _
  rw [orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]
  show orbitCores ρ x₀ (Pi.single x₀ (b : M x₀)) - (b : M x₀) ∈ (cycSubOne ρ₀ τ).range
  rw [orbitCores_single hρ hD hρ₀]
  exact apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _
end GroundTheory.Global
