-- Prove2me | solution 1 for GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:02.502657+00:00
-- url     : https://prove2.me/submissions/67a14fd4-4adb-4d9c-9694-23d30603ce21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddLeFinrankRangeAddOfComapLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddLeFinrankRangeAddOfComapLeStatement
import Theorems.Thm_GlobalTheory_finrank_add_le_finrank_range_add_of_comap_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  first | exact @GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | exact GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | (intros; apply GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le <;> assumption)
end _root_.GlobalTheory.T
