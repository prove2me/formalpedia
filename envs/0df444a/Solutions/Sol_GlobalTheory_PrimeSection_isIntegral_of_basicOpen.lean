-- Prove2me | solution 1 for GlobalTheory.PrimeSection.isIntegral_of_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:11.2399+00:00
-- url     : https://prove2.me/submissions/1a5e698b-db9d-4d6e-8252-c1b775eb36ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_bijective
import Theorems.Thm_GlobalTheory_PrimeSection_eq_preimage_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X Y : Scheme.{u}} {t : Γ(X, ⊤)}
    (ht : ∀ U : X.Opens, IsAffineOpen U →
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ nonZeroDivisors Γ(X, U))
    (j : Y ⟶ X) [IsOpenImmersion j] [IsIntegral Y] (hj : j.opensRange = X.basicOpen t) :
    IsIntegral X := by
  have hinj : ∀ U : X.Opens, IsAffineOpen U →
      Function.Injective (j.appLE U (j ⁻¹ᵁ U) le_rfl) := fun U hU s s' h ↦ by
    have := hU.isLocalization_basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    refine IsLocalization.injective
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
      ((Submonoid.powers_le).2 (ht U hU)) ?_
    have he : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
      U ⊓ X.basicOpen t := X.basicOpen_res _ _
    refine (appLE_bijective j (W := j ⁻¹ᵁ U) (he.le.trans (inf_le_right.trans hj.ge))
      (he ▸ eq_preimage_inf hj rfl)).1 ?_
    exact (appLE_res j _ _ s).trans (h.trans (appLE_res j _ _ s').symm)
  have : IsReduced X := ⟨fun W ↦ ⟨fun s hs ↦ X.IsSheaf.section_ext fun x hx ↦ by
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨U, hUW, hxU, hinj U hU ?_⟩
    rw [map_zero, map_zero]
    exact ((hs.map _).map _).eq_zero⟩⟩
  have hdense : Dense (Set.range j) := by
    refine dense_iff_inter_open.2 fun W hW ⟨x, hx⟩ ↦ ?_
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨W, hW⟩) hx
    by_contra hne
    have hbot : j ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun y hy ↦ hne ⟨j y, hUW hy, y, rfl⟩
    have : Subsingleton Γ(Y, j ⁻¹ᵁ U) := by rw [hbot]; infer_instance
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    exact not_subsingleton Γ(X, U) (hinj U hU).subsingleton
  have : IrreducibleSpace X := by
    have h := (IrreducibleSpace.isIrreducible_univ Y).image j j.continuous.continuousOn
    rw [Set.image_univ] at h
    have h' := h.closure
    rw [hdense.closure_eq] at h'
    exact (irreducibleSpace_def X).2 h'
  exact isIntegral_of_irreducibleSpace_of_isReduced X
end GlobalTheory.PrimeSection
