-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.exists_section_of_isLocallyFraction_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:03.937146+00:00
-- url     : https://prove2.me/submissions/cb4c8653-7fc0-4106-84c0-bf45f1346edc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
set_option backward.isDefEq.respectTransparency.types false
open ProjectiveSpectrum
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : ∀ x : U, Loc 𝒜 x.1) (ht : (isLocallyFraction 𝒜 0).pred t) :
    ∃ t' : (Proj.structureSheaf 𝒜).obj.obj (op U), ∀ x, (t'.1 x).val = t x := by
  have key : ∀ x : U, ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (_ : x.1 ∈ V) (iV : V ⟶ U)
      (j : ℕ) (r s : 𝒜 j) (s_nin : ∀ y : V, s.1 ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, t (iV y : U) = Localization.mk r.1 ⟨s.1, s_nin y⟩ := by
    intro x
    obtain ⟨V, hxV, iV, i, j, hij, r, s, hr, hs, hsn, w⟩ := ht x
    have e : i = j := by omega
    subst e
    exact ⟨V, hxV, iV, i, ⟨r, hr⟩, ⟨s, hs⟩, hsn, w⟩
  have pt : ∀ x : U, ∃ y : HomogeneousLocalization.AtPrime 𝒜
      x.1.asHomogeneousIdeal.toIdeal, y.val = t x := by
    intro x
    obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
    exact ⟨HomogeneousLocalization.mk ⟨j, r, s,
      (show s.1 ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl from hsn ⟨x.1, hxV⟩)⟩,
      by rw [HomogeneousLocalization.val_mk]; exact (w ⟨x.1, hxV⟩).symm⟩
  choose g hg using pt
  refine ⟨(⟨g, fun x => ?_⟩ : (StructureSheaf.structureSheafInType 𝒜).obj.obj (op U)), hg⟩
  obtain ⟨V, hxV, iV, j, r, s, hsn, w⟩ := key x
  refine ⟨V, hxV, iV, j, r, s, hsn, fun y => HomogeneousLocalization.val_injective _ ?_⟩
  rw [HomogeneousLocalization.val_mk]
  exact (hg _).trans (w y)
end GroundTheory.Arith.SchemeCoh.ProjTwist
