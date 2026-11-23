-- Prove2me | solution 1 for GlobalTheory.CubeBalance.cubN_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:17.485508+00:00
-- url     : https://prove2.me/submissions/03536c52-155b-4881-ac32-f2bd7754782b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CubeBalance
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.CubeBalance
theorem _root_.solution (θ : A → A → A → U) (k : ℕ) (x y : A) :
    cubN θ (k + 1) 1 x y = cubN θ k 1 x y * θ (x ^ k) x y := by
  simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
end GlobalTheory.CubeBalance
