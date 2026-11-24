-- Prove2me | solution 1 for GlobalTheory.point_from_fg_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:14.376737+00:00
-- url     : https://prove2.me/submissions/dfb3ad7f-8f1c-46b4-9743-11f56cac1e7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModuliPointFromFgSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFinitePresentation s] (S : Type) [CommRing S] [Algebra F S] (x : Sp S ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap F S).comp φ)) :
    ∃ S₀ : Subalgebra F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ X, x₀ ≫ s = spMap ((algebraMap F S₀).comp φ) ∧
      spMap S₀.val.toRingHom ≫ x₀ = x := by
  classical
  let P : Finset S ⥤ CommRingCat.{0} :=
    { obj t := .of (Algebra.adjoin F (t : Set S))
      map {t t'} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cP : Cocone P :=
    { pt := .of S
      «ι» := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcP : IsColimit cP := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : S := x
        exact ⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset S)ᵒᵖ ⥤ Scheme.{0} := P.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cP.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcP.op
  let κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K :=
    spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)
  have hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t) := inferInstanceAs (IsAffine (Spec _))
  have hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f) := inferInstance
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x
    (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))
  exact ⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩
end GlobalTheory
