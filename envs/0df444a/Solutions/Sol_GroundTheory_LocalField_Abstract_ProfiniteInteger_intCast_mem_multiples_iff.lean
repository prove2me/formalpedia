-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.intCast_mem_multiples_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:56.799797+00:00
-- url     : https://prove2.me/submissions/ceff5b9a-3972-479d-a1e5-65a048b3b438

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_dvd_of_intCast_eq_nsmul


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
theorem _root_.solution {n : ℕ} (hn : 0 < n) {k : ℤ} :
    (k : ℤ̂) ∈ multiples n ↔ (n : ℤ) ∣ k := by
  rw [mem_multiples]
  refine ⟨fun ⟨w, hw⟩ => dvd_of_intCast_eq_nsmul hn hw, ?_⟩
  rintro ⟨c, rfl⟩
  exact ⟨(c : ℤ̂), by push_cast; rw [nsmul_eq_mul]⟩
end GroundTheory.LocalField.Abstract.ProfiniteInteger
