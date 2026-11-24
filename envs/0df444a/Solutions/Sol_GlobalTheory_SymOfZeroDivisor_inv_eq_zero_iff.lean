-- Prove2me | solution 1 for GlobalTheory.SymOfZeroDivisor.inv_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:34.048739+00:00
-- url     : https://prove2.me/submissions/ad0ff232-2c75-4b0a-8045-fe1c47271280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymOfZeroDivisor
namespace GlobalTheory.SymOfZeroDivisor
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left = (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A ↔
      t = t ≫ A.hom ≫ eSec A := by
  have h1 : (GrpObj.inv : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  have h2 : eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have h3 : (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A =
      (t ≫ A.hom ≫ eSec A) ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [Category.assoc, reassoc_of% h1]
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ A.hom ≫ u) h2.symm
  rw [h3]
  exact cancel_mono _
end GlobalTheory.SymOfZeroDivisor
