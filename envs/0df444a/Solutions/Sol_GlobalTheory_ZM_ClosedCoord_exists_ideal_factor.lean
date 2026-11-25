-- Prove2me | solution 1 for GlobalTheory.ZM.ClosedCoord.exists_ideal_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:51:30.54144+00:00
-- url     : https://prove2.me/submissions/7d943356-cc0c-4ae5-bc95-69d653087d4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial
namespace GlobalTheory.ZM.ClosedCoord
theorem _root_.solution {Y Z : Scheme.{0}} (i : Y ⟶ Z) [IsClosedImmersion i] {S : Type} [CommRing S]
    (x : Sp S ⟶ Z) : ∃ J : Ideal S, ∀ (R' : Type) [CommRing R'] (φ : S →+* R'),
      (∃ y : Sp R' ⟶ Y, y ≫ i = spMap φ ≫ x) ↔ ∀ f ∈ J, φ f = 0 := by
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.1 (inferInstance : IsClosedImmersion (pullback.snd i x))
  refine ⟨J, fun R' _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩ f hf
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (spMap φ) hy ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ ψ) = spMap φ := by
      rw [Spec.map_comp, hψ, Category.assoc, ← he, pullback.lift_snd]
    have h2 := Spec.map_injective h1
    have h3 : ψ.hom (Ideal.Quotient.mk J f) = φ f := congrArg (fun t => t.hom f) h2
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · intro h
    refine ⟨spMap (Ideal.Quotient.lift J φ h) ≫ e.inv ≫ pullback.fst i x, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
end GlobalTheory.ZM.ClosedCoord
