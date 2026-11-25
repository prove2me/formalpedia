-- Prove2me | solution 1 for GlobalTheory.UU.RingPoint.exists_ringPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:48.590198+00:00
-- url     : https://prove2.me/submissions/cbdcfb73-03c3-46d9-b612-a6e708c64f43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Theorems.Thm_GlobalTheory_UU_RingPoint_toSpec_appTop
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RingPoint
namespace GlobalTheory.UU.RingPoint
theorem _root_.solution {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by
  let p : Spec (CommRingCat.of D) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv
  have hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b := fun b => by
    have h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    exact congrArg (fun q => q.hom b) h
  refine ⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv,
    inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩
  have h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left := by
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop]
    exact (toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))
  refine ⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))
end GlobalTheory.UU.RingPoint
