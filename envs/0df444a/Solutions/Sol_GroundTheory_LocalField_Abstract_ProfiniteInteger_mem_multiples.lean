-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.mem_multiples
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:19.915714+00:00
-- url     : https://prove2.me/submissions/4a87b138-6c93-49a9-a294-7d74221db507

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero

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
theorem _root_.solution {n : ℕ} {x : ℤ̂} : x ∈ multiples n ↔ ∃ y : ℤ̂, x = n • y := by
  simp only [multiples, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
end GroundTheory.LocalField.Abstract.ProfiniteInteger
