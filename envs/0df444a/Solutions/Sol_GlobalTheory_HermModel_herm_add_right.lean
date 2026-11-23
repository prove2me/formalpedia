-- Prove2me | solution 1 for GlobalTheory.HermModel.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:25.894333+00:00
-- url     : https://prove2.me/submissions/7a2b51f1-4906-4b23-9271-3abddd7f92ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan

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
open GlobalTheory GlobalTheory.HermModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermModel
namespace _root_.GlobalTheory.HermModel
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (y + y') = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y + _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y' := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
