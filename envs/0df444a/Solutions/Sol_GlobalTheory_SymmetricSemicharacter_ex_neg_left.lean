-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.ex_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:13.737207+00:00
-- url     : https://prove2.me/submissions/eecaf6c2-0e23-42d0-ae64-2a0d8aa6c79d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution (z : Fin g → ℂ) :
    (u.ex z).left ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-z)).left := by
  have h : u.ex (-z) = (u.ex z)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel, ex_zero]
  rw [h, Hom.inv_def, Over.comp_left]
end GlobalTheory.SymmetricSemicharacter
