-- Prove2me | solution 1 for GlobalTheory.HermModel.eq_zero_of_herm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:14.694916+00:00
-- url     : https://prove2.me/submissions/da2c255b-b6a6-4c57-ac29-33c83a0947ea

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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E}
    (hG : G.det ≠ 0) {w : Fin r → E} (hw : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G w u = 0) : w = 0 := by
  refine Matrix.eq_zero_of_vecMul_eq_zero hG (funext fun b => ?_)
  have h := hw (Pi.single b 1)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa [Matrix.vecMul, dotProduct] using h
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
