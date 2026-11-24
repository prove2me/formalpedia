-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.app_eq_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:08.081617+00:00
-- url     : https://prove2.me/submissions/32512a7b-3a4a-4b54-b1b1-dbf1b2d12321

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_app_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_flat
import Theorems.Thm_GlobalTheory_SmallExtLift_cst_flat

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
theorem _root_.solution (hε : ε ≠ 0) [Flat p]
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : cst p V ε * a = 0) :
    (i.app V).hom a = 0 := by
  have h := mem_of_flat hε _ (cst_flat p hV) a ha
  refine (show _ ≤ RingHom.ker (i.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
  rw [Ideal.mem_comap, RingHom.mem_ker, app_cst w, (IsLocalRing.residue_eq_zero_iff r).2 hr,
    map_zero]
end GlobalTheory.SmallExtLift
