-- Prove2me | solution 1 for GlobalTheory.ThetaPow.prod_fam_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:46.057881+00:00
-- url     : https://prove2.me/submissions/e3ae9e4c-4cf7-4a54-8199-0c68c60b09af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPow
namespace GlobalTheory.ThetaPow
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
  have hmul : ∀ {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ D.P.A), padd D.P.A a b = a * b := by
    intro T a b
    unfold padd
    rfl
  have hc0 : D.c 0 = 1 := by
    have h2 := D.c_add 0 0
    rw [add_zero, hmul] at h2
    exact mul_eq_left.mp h2.symm
  have h1 : toUnit (DegPre.BF D F) ≫ D.c 0 = toUnit (DegPre.BF D F) ≫ η[D.P.A] := by
    rw [hc0]
    rfl
  have h3 : padd D.P.A (DegPre.prB D F) (toUnit (DegPre.BF D F) ≫ η[D.P.A]) = DegPre.prB D F := by
    rw [hmul]
    exact mul_one _
  have hφ : DegPre.famφ D F 0 = ![(DegPre.prB D F).left, (DegPre.prB D F).left,
      (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left, (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left] := by
    unfold DegPre.famφ
    rw [h1, h3]
  have hε : DegPre.famε k = ![(k : ℤ) - 1, 1, -1, 1] := rfl
  rw [Fin.prod_univ_four, hφ, hε]
  show h (DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (DegPre.prB D F).left ^ (1 : ℤ) *
      h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (-1 : ℤ) * h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (1 : ℤ) =
      h (DegPre.prB D F).left ^ k
  simp only [zpow_neg, zpow_one]
  rw [_root_.inv_mul_cancel_right, ← zpow_add_one, sub_add_cancel, zpow_natCast]
end GlobalTheory.ThetaPow
