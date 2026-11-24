-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.isUnit_of_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:46.065653+00:00
-- url     : https://prove2.me/submissions/b2589a42-0db3-4401-bec0-4570c63fa350

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_app_surj
import Theorems.Thm_GlobalTheory_SmallExtLift_isUnit_one_add
import Theorems.Thm_GlobalTheory_SmallExtLift_exists_eq_mul

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
variable {ε : R} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (hε : ε * ε = 0)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : IsUnit ((π.app V).hom a)) :
    IsUnit a := by
  obtain ⟨v', hv'⟩ := ha.exists_right_inv
  obtain ⟨v, rfl⟩ := app_surj Ideal.Quotient.mk_surjective H hV v'
  obtain ⟨b, hb⟩ := exists_eq_mul H hV (a * v - 1) (by rw [map_sub, map_mul, hv', map_one, sub_self])
  have := isUnit_one_add (e := cst p V ε) (by rw [← map_mul, hε, map_zero]) b
  rw [← hb, add_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left this
end GlobalTheory.SmallExtLift
