-- Prove2me | solution 1 for GlobalTheory.DualFamily.exists_herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:33.753738+00:00
-- url     : https://prove2.me/submissions/821c82ad-5efa-4b90-90cd-c184c0f5b7ef

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
theorem _root_.solution {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u w := by
  refine ⟨fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, _root_.GlobalTheory.DualFamily.herm_one_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  rw [IsCMField.complexConj_apply_apply, smul_eq_mul]
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
