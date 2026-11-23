-- Prove2me | solution 1 for GlobalTheory.DualFamily.herm_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.138169+00:00
-- url     : https://prove2.me/submissions/c5d5e812-18a6-4087-917a-b2046847eb55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.DualFamily
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DualFamily
namespace _root_.GlobalTheory.DualFamily
theorem _root_.solution {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp [Matrix.one_apply]
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
