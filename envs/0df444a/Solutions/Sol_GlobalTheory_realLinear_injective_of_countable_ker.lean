-- Prove2me | solution 1 for GlobalTheory.realLinear_injective_of_countable_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:40.550112+00:00
-- url     : https://prove2.me/submissions/119e1555-c412-4d5c-9cf7-9d5eb30e7821

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_subsingleton_of_countable_realModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
namespace GlobalTheory
theorem _root_.solution (L : M →ₗ[ℝ] N) (h : {x | L x = 0}.Countable) :
    Function.Injective L := by
  have : Countable (LinearMap.ker L) := h
  have := subsingleton_of_countable_realModule (LinearMap.ker L)
  exact LinearMap.ker_eq_bot.1 (Submodule.eq_bot_of_subsingleton)
end GlobalTheory
