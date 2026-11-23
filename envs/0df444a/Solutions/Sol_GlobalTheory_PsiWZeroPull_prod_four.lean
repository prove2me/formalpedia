-- Prove2me | solution 1 for GlobalTheory.PsiWZeroPull.prod_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:49.753025+00:00
-- url     : https://prove2.me/submissions/fcf14cc8-1748-4e3c-81c5-7e8ae99e5b18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TraceFormTwistIsoOfPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiWZeroPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull
namespace GlobalTheory.PsiWZeroPull
theorem _root_.solution {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (f : A ⟶ A) (x : T ⟶ A) {U : Type}
    [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) i) ^
      (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      k (x * (x ≫ f)).left * (k x.left ^ 2)⁻¹ * (k (x ≫ f).left)⁻¹ * k (1 : T ⟶ A).left ^ 2 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ (𝟙 A * f)).left ^ (1 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) * k (x ≫ f).left ^ (-1 : ℤ) *
    k (x ≫ 1).left ^ (2 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg_one, zpow_neg, zpow_ofNat, zpow_ofNat]
end GlobalTheory.PsiWZeroPull
