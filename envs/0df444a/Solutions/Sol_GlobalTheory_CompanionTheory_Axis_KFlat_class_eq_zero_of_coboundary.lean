-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:19.75638+00:00
-- url     : https://prove2.me/submissions/d14f5cb9-e4b4-4854-a64c-dd9f2fc416a1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_KFlat_pi_rTensor_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_KFlat_pi_rTensor_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis GlobalTheory.CompanionTheory.Axis.KFlat
namespace GlobalTheory.CompanionTheory.Axis.KFlat
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N)
    (g : ∀ T : C, F.obj T ⊗[R] N)
    (h : ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) :
    (H1.mk F).rTensor N t = 0 := by
  classical
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun T T' ↦ by
    haveI : Subsingleton (T ⟶ T') := inferInstance
    exact Finite.of_subsingleton
  let κ : Z1 F →ₗ[R] ∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1 :=
    LinearMap.pi fun x ↦ evZ F x.2.2
  have hκ : Function.Injective κ := fun a b hab ↦ Subtype.ext (by
    funext T T' φ
    exact congrFun hab ⟨T, T', φ⟩)
  let δ : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  obtain ⟨u, hu⟩ := pi_rTensor_exists (R := R) (M := fun T : C ↦ F.obj T) (N := N) g
  have hδ : ∀ {T T' : C} (φ : T ⟶ T'), evZ F φ ∘ₗ δ =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := fun φ ↦ by
    refine LinearMap.ext fun c ↦ ?_
    rfl
  have key : t = δ.rTensor N u := by
    apply Module.Flat.rTensor_preserves_injective_linearMap κ hκ
    rw [← sub_eq_zero, ← map_sub]
    apply pi_rTensor_eq_zero
    rintro ⟨T, T', φ⟩
    rw [← LinearMap.rTensor_comp_apply]
    have e : (LinearMap.proj (⟨T, T', φ⟩ : Σ T : C, Σ T' : C, (T ⟶ T')) :
        (∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1) →ₗ[R] F.obj T') ∘ₗ κ = evZ F φ := rfl
    rw [e, map_sub, h, ← LinearMap.rTensor_comp_apply, hδ, LinearMap.rTensor_sub, LinearMap.sub_apply,
      LinearMap.rTensor_comp_apply, hu, hu, sub_self]
  have hz : H1.mk F ∘ₗ δ = 0 := by
    refine LinearMap.ext fun c ↦ ?_
    exact (H1.mk_eq_zero (F := F) (f := δ c)).2 ⟨c, rfl⟩
  rw [key, ← LinearMap.rTensor_comp_apply, hz, LinearMap.rTensor_zero, LinearMap.zero_apply]
end GlobalTheory.CompanionTheory.Axis.KFlat
