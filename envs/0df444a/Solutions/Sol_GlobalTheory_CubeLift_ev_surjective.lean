-- Prove2me | solution 1 for GlobalTheory.CubeLift.ev_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:49.606569+00:00
-- url     : https://prove2.me/submissions/e0620928-af5b-4ce3-a1ec-2b8482e262a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
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
private theorem ev_base_apply (r : R) :
    ev (X := X) (𝟙 (Spec R)) ((splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      AddMonoidAlgebra.single 0 r := by
  change pull (univPt X _) _ = _
  have hw := Over.w (univPt X (𝟙 (Spec R)))
  simp only [SplitTorus.pull, RingHom.comp_apply]
  rw [← app_global_comp_apply, hw]
  erw [Category.comp_id]
  erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]
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
theorem _root_.solution : Function.Surjective (ev (X := X) (𝟙 (Spec R))) := by
  intro w
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    refine ⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩
    rw [map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]
end GlobalTheory.CubeLift
