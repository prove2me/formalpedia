-- Prove2me | solution 1 for GlobalTheory.HermModel.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:07.785799+00:00
-- url     : https://prove2.me/submissions/dea55963-413e-4210-add6-5c5199f0a48d

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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end _root_.GlobalTheory.HermModel
end GlobalTheory.HermModel
