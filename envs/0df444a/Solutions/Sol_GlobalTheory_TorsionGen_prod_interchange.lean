-- Prove2me | solution 1 for GlobalTheory.TorsionGen.prod_interchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:00:38.196661+00:00
-- url     : https://prove2.me/submissions/44af1d17-12c9-4253-8c4f-294bb67ab216

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
theorem _root_.solution (t₁ t₂ : A → A → A → U)
    (ic : ∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')
    (x a y : A) (n : ℕ) :
    (∏ k ∈ Finset.range n, t₁ (x ^ k) x (a * y)) * t₂ x a y ^ n * t₂ 1 a y =
      t₂ (x ^ n) a y * (∏ k ∈ Finset.range n, t₁ (x ^ k) x a) * (∏ k ∈ Finset.range n, t₁ (x ^ k) x y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have c := ic (x ^ n) x a y
    simp only [Finset.prod_range_succ]
    rw [pow_succ x, pow_succ (t₂ x a y)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'
end GlobalTheory.TorsionGen
