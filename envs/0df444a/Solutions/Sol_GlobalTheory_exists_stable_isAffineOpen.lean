-- Prove2me | solution 1 for GlobalTheory.exists_stable_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:02.068085+00:00
-- url     : https://prove2.me/submissions/6e78e47f-919c-4f68-8e79-e18283d4c0bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_aut_map_mul_apply
import Theorems.Thm_GlobalTheory_aut_map_one_apply
import Theorems.Thm_GlobalTheory_exists_isInvariantSection_mem_basicOpen_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
variable {ρ : G →* Aut X}
variable [Finite G]
variable (ρ)
namespace GlobalTheory
theorem _root_.solution [OrbitsInAffineOpens ρ] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (∀ g, V ≤ (ρ g).hom ⁻¹ᵁ V) ∧ x ∈ V := by
  obtain ⟨U, hU, hxU⟩ := OrbitsInAffineOpens.exists_isAffineOpen (ρ := ρ) x
  let W : X.Opens := ⨅ g, (ρ g).hom ⁻¹ᵁ U
  have hmemW : ∀ y, y ∈ W ↔ ∀ g, (ρ g).hom y ∈ U := fun y ↦ by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact Iff.rfl
  have hWU : W ≤ U := fun y hy ↦ by
    have := (hmemW y).1 hy 1
    rwa [aut_map_one_apply] at this
  have hWst : ∀ k, W ≤ (ρ k).hom ⁻¹ᵁ W := fun k y hy ↦ by
    show (ρ k).hom y ∈ W
    rw [hmemW]
    intro g
    rw [← aut_map_mul_apply]
    exact (hmemW y).1 hy _
  have hxW : x ∈ W := (hmemW x).2 hxU
  obtain ⟨f, hsf, hfW⟩ := exists_basicOpen_le_of_finite hU W
    (Set.finite_range fun g ↦ (ρ g).hom x)
    (by rintro _ ⟨g, rfl⟩; exact hxU g) (by rintro _ ⟨g, rfl⟩; exact hWst g hxW)
  have hf' : X.basicOpen (X.presheaf.map (homOfLE hWU).op f) = X.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfW
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hWst
    (X.presheaf.map (homOfLE hWU).op f)
  have htf : X.basicOpen t ≤ X.basicOpen f := fun y hy ↦ by
    have := (hmem y).1 hy 1
    rwa [aut_map_one_apply, hf'] at this
  refine ⟨X.basicOpen t, ?_, fun k y hy ↦ ?_, ?_⟩
  · have hA := (hU.basicOpen f).basicOpen (X.presheaf.map (homOfLE hfW).op t)
    rwa [Scheme.basicOpen_res, inf_eq_right.2 htf] at hA
  · show (ρ k).hom y ∈ X.basicOpen t
    rw [hmem]
    intro g
    rw [← aut_map_mul_apply]
    exact (hmem y).1 hy _
  · rw [hmem]
    intro g
    rw [hf']
    exact hsf ⟨g, rfl⟩
end GlobalTheory
