-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.cocycle_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:31.359809+00:00
-- url     : https://prove2.me/submissions/c25d0018-a689-4e13-bc2a-25c1693d0a50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_cocycle
import Theorems.Thm_GlobalTheory_SmallExtLift_app_eq_zero_of_mul

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
variable [IsLocalRing R] {ε : R} {p : X ⟶ Spec (CommRingCat.of R)} {i : Y ⟶ X}
  {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
variable {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
namespace GlobalTheory.SmallExtLift
namespace Rel
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0) [Flat p]
    [X.IsSeparated] (hM : M.IsLB) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (a b d : I) (y : Y)
    (ha : (𝟙 Y ≫ i) y ∈ V a) (hb : (𝟙 Y ≫ i) y ∈ V b) (hd : (𝟙 Y ≫ i) y ∈ V d) :
    gr (𝟙 Y ≫ i) y (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr (𝟙 Y ≫ i) y (V b ⊓ V d) ⟨hb, hd⟩ (α b d) =
      gr (𝟙 Y ≫ i) y (V a ⊓ V d) ⟨ha, hd⟩ (α a d) := by
  have h := app_eq_zero_of_mul h0 w (((hA a).inf (hA b)).inf (hA d))
    ((X.presheaf.map (homOfLE inf_le_left).op).hom (α a b) +
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op).hom
        (α b d) -
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom
        (α a d)) (gr_ext fun x hx => by
      rw [map_mul, map_sub, map_add, gr_res, gr_res, gr_res, gr_cst, map_zero]
      exact H.cocycle hε hM hu a b d _ x hx.1.1 hx.1.2 hx.2)
  have h' := congrArg (gr (𝟙 Y) y (i ⁻¹ᵁ (V a ⊓ V b ⊓ V d)) ⟨⟨ha, hb⟩, hd⟩) h
  rw [gr_app, map_sub, map_add, gr_res, gr_res, gr_res, map_zero] at h'
  exact sub_eq_zero.1 h'
end Rel
end GlobalTheory.SmallExtLift
