-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.unit_eq_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:32.110075+00:00
-- url     : https://prove2.me/submissions/e429fe3b-8c56-4818-9b0b-d363de11dccb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroScheme

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
open GlobalTheory GlobalTheory.SameZeroScheme
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by
  apply Units.ext
  apply (mul_cancel_right_mem_nonZeroDivisors ha).1
  rw [← h, hb, h', zpow_one, zpow_neg_one, haa]
  have := g₁.inv_mul
  push_cast
  linear_combination (-(g₀ * c' * a' : R)) * this
end GlobalTheory.SameZeroScheme
