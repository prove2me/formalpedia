-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tateNegOne_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:04.971645+00:00
-- url     : https://prove2.me/submissions/c016cafc-9060-4122-bd0a-a75d381fc26d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_exists_smul_div_eq_of_tateNorm_eq_one
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hσ hx
  exact Subgroup.subset_closure ⟨σ, y, hy⟩
end GroundTheory.LocalField
