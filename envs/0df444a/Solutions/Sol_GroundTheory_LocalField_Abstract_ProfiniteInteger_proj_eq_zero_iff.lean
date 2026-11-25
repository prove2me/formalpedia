-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.proj_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:22.006892+00:00
-- url     : https://prove2.me/submissions/99b183af-8321-443c-bd4f-5e90964549b5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_exists_eq_nsmul_of_proj_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {n : ℕ+} {x : ℤ̂} : proj n x = 0 ↔ x ∈ multiples n := by
  rw [mem_multiples]
  refine ⟨exists_eq_nsmul_of_proj_eq_zero, ?_⟩
  rintro ⟨y, rfl⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
end GroundTheory.LocalField.Abstract.ProfiniteInteger
