-- Prove2me | solution 1 for GlobalTheory.CubeLift.ev_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:07.590896+00:00
-- url     : https://prove2.me/submissions/a3cdedaa-2e5c-4a86-8a52-58d0fdf0b25b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Theorems.Thm_GlobalTheory_SplitTorus_charUnit_val
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_ev_chi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
section Expand
variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}
private theorem app_global_comp_apply {U V W' : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ W') (u : Γ(W', ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) := by
  rfl
end Expand
section Points
variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}
end Points
section Affine
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
variable {J : Ideal A}
end Affine
end GlobalTheory.CubeLift
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}
namespace GlobalTheory.CubeLift
theorem _root_.solution (f : S' ⟶ S) (t : Spec R ⟶ S') (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((bcMap f X).appTop.hom u) = ev (t ≫ f) u := by
  have e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · simp [SplitTorus.bcMap_hom]
    · have h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) =
          (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ) := by
        rw [← SplitTorus.pull_chi, ← SplitTorus.pull_chi]
        exact (SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm
      have h1 := congrArg (Scheme.ΓSpecIso _).inv.hom h0
      simp only [Iso.hom_inv_id_apply] at h1
      rw [SplitTorus.val_eq, SplitTorus.val_eq] at h1
      rw [app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
      exact h1
  change pull (univPt X t) _ = pull (univPt X (t ≫ f)) u
  simp only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]
end GlobalTheory.CubeLift
