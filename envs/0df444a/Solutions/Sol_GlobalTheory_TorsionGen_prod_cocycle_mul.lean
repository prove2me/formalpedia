-- Prove2me | solution 1 for GlobalTheory.TorsionGen.prod_cocycle_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:51.815109+00:00
-- url     : https://prove2.me/submissions/2468d98d-7e4d-4bb3-b887-8a556c937735

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdCocycleMul
import Theorems.Thm_GlobalTheory_TorsionGen_cocycle_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionGen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U]
namespace GlobalTheory.TorsionGen
theorem _root_.solution (t : A → A → U) (coc : ∀ y y' y'', t (y * y') y'' * t y y' = t y (y' * y'') * t y' y'')
    (sym : ∀ y y', t y y' = t y' y) (a y : A) (n : ℕ) :
    (∏ k ∈ Finset.range n, t ((a * y) ^ k) (a * y)) * t a y ^ n * t 1 1 =
      (∏ k ∈ Finset.range n, t (a ^ k) a) * (∏ k ∈ Finset.range n, t (y ^ k) y) * t (a ^ n) (y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have c := cocycle_four t coc sym (a ^ n) (y ^ n) a y
    rw [← mul_pow] at c
    simp only [Finset.prod_range_succ]
    rw [pow_succ a, pow_succ y, pow_succ (t a y)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'
end GlobalTheory.TorsionGen
