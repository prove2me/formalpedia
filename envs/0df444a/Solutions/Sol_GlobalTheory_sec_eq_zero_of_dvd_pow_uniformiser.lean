-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_of_dvd_pow_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:44.321378+00:00
-- url     : https://prove2.me/submissions/0107c4ad-9605-4b7a-a88b-7c09788d723c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroOfDvdPowUniformiser
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_chart
import Theorems.Thm_GlobalTheory_eq_zero_of_mem_pow_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
end GlobalTheory
