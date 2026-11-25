-- Prove2me | solution 1 for GlobalTheory.section_eq_zero_of_forall_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:45.226265+00:00
-- url     : https://prove2.me/submissions/9c17e0e2-786a-4621-8db6-d043048896b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Theorems.Thm_GlobalTheory_FlatPoints_affine_case
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (H Y : Over (Spec (CommRingCat.of O))), IsFinite H.hom → Flat H.hom → IsReduced (specO O F ⊗ H).left → Flat Y.hom → ∀ (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W)), (∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) → f = 0 := by
  intro O F _ _ _ _ hinj H Y hfin hflat hred hY W f h
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  letI : Algebra O Γ(H.left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ(H.left, ⊤) ≅ H := Over.isoMk H.left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have h2 : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ(H.left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have : Module.Flat O Γ(H.left, ⊤) := (Flat.SpecMap_iff (f := ψ)).mp h2
  have h0 : IsIso (specO O F ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.hom)))
  have h3 : IsReduced (specO O F ⊗ specO O Γ(H.left, ⊤)).left :=
    isReduced_of_isOpenImmersion (specO O F ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ(H.left, ⊤)))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ(H.left, ⊤)).inv _ h3
  have : _root_.IsReduced (TensorProduct O F Γ(H.left, ⊤)) := (affine_isReduced_iff _).mp h4
  exact FlatPoints.affine_case O F hinj Γ(H.left, ⊤) H Y e W f h
end GlobalTheory
