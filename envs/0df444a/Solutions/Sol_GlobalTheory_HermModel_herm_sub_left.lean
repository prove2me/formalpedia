-- Prove2me | solution 1 for GlobalTheory.HermModel.herm_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:18.065592+00:00
-- url     : https://prove2.me/submissions/04703c90-a1b1-4b0f-a2a6-fca408c0f4ff

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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (x - x') y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y - _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x' y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
