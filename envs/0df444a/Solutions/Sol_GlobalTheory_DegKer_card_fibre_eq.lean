-- Prove2me | solution 1 for GlobalTheory.DegKer.card_fibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:05:59.617676+00:00
-- url     : https://prove2.me/submissions/989ee2b2-9c8f-4907-873f-bb33349c14fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel

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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) (Ω : Type) [CommRing Ω] [Algebra Γ(Y, U) Ω] :
    letI := (f.app U).hom.toAlgebra
    Nat.card (Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Ω) = Nat.card {y : Spec (CommRingCat.of Ω) ⟶ X //
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Ω)) ≫ hU.fromSpec} := by
  letI := (f.app U).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have w : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl, Scheme.Hom.app_eq_appLE]
  have H := IsOpenImmersion.isPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f w (by simp)
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ hV.fromSpec, ?_⟩) ⟨?_, ?_⟩)
  · rw [Category.assoc, w, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact σ.commutes x
  · intro σ τ h
    have h1 := Spec.map_injective ((cancel_mono _).mp (congrArg Subtype.val h))
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)
  · rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := Spec.map_surjective (H.lift _ _ hy.symm)
    have h1 : f.app U ≫ g = CommRingCat.ofHom (algebraMap Γ(Y, U) Ω) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, H.lift_fst]
    refine ⟨{ g.hom with commutes' := fun x => ?_ }, Subtype.ext ?_⟩
    · exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) x
    · change Spec.map g ≫ _ = y
      rw [hg, H.lift_snd]
end GlobalTheory.DegKer
