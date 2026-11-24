-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.mul_eq_zero_of_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:14.59415+00:00
-- url     : https://prove2.me/submissions/f53abdea-f5d6-4424-aecd-98fe3ec95e71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
import Theorems.Thm_GlobalTheory_SmallExtLift_mul_eq_zero_of_mem

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
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    (P : IsPullback i f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : (i.app V).hom a = 0) :
    cst p V ε * a = 0 := by
  have h := mem_of_app_eq_zero IsLocalRing.residue_surjective P hV a ha
  rw [IsLocalRing.ker_residue] at h
  exact mul_eq_zero_of_mem _ hm h
end GlobalTheory.SmallExtLift
