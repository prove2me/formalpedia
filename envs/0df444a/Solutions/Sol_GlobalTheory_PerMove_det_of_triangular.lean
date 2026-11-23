-- Prove2me | solution 1 for GlobalTheory.PerMove.det_of_triangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:35.398822+00:00
-- url     : https://prove2.me/submissions/e5ffbacb-b54b-4c7f-9663-392f1a48de1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] (f : n → α)
    (hf : Function.Injective f) (M : Matrix n n ℂ) (hM : ∀ k l, f l < f k → M k l = 0) :
    M.det = ∏ k, M k k := by
  letI : LinearOrder n := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular fun k l h => hM k l h
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
