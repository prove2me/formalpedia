-- Prove2me | solution 1 for GlobalTheory.T.matrix_near_identity_in_congruence_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:24.000873+00:00
-- url     : https://prove2.me/submissions/7dedc6d5-1128-4391-9768-63204c578b44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixNearIdentityInCongruenceSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixNearIdentityInCongruenceSubgroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_exists_mem_congK_of_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | exact GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries <;> assumption)
end _root_.GlobalTheory.T
