-- Prove2me | solution 1 for GlobalTheory.TorsionReduced.eq_const_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:11.005869+00:00
-- url     : https://prove2.me/submissions/63aced49-a818-4028-8ba6-3f1f8f4aa453

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Theorems.Thm_GlobalTheory_TorsionReduced_scale_comp_scale
import Theorems.Thm_GlobalTheory_TangentPow_pow_eq_scale_comp
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_TangentPow_scale_one
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_TangentPow_ptMap_id__b9bbf1f25ce6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TorsionReduced
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
namespace GlobalTheory.TorsionReduced
theorem _root_.solution {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hN : IsUnit (N : R)) (y : specO O (DualNumber R) ⟶ G) (hy : y ^ N = 1) :
    y = ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y := by
  set c := ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y with hc
  have h0 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (TrivSqZeroExt.inlAlgHom O R R) = 𝟙 _ := by
    rw [TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_id']
    congr 1
  have h1 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ (y * c⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hc, ← Category.assoc, h0, Category.id_comp, mul_inv_cancel]
  have h2 : c ^ N = 1 := by
    rw [hc, ← MonObj.comp_pow, ← MonObj.comp_pow, hy, comp_one, comp_one]
  have h3 : (y * c⁻¹) ^ N = 1 := by
    rw [mul_pow, inv_pow, hy, h2, inv_one, _root_.mul_one]
  rw [TangentPow.pow_eq_scale_comp h1] at h3
  obtain ⟨a, ha⟩ := hN.exists_left_inv
  have h4 := congrArg (TangentPow.scale O a ≫ ·) h3
  simp only [← Category.assoc, scale_comp_scale, ha, TangentPow.scale_one, Category.id_comp,
    comp_one] at h4
  exact mul_inv_eq_one.mp h4
end GlobalTheory.TorsionReduced
