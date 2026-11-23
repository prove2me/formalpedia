-- Prove2me | solution 1 for GlobalTheory.DualFamily.herm_one_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:33.891123+00:00
-- url     : https://prove2.me/submissions/a5018b82-30ed-4e9c-8fab-ac5612e36e02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq

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
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x) := by
  rw [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.DualFamily.herm_one_eq]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
