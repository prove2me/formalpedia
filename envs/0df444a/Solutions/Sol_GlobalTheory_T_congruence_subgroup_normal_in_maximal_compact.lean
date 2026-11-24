-- Prove2me | solution 1 for GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:36.553108+00:00
-- url     : https://prove2.me/submissions/faf33f4c-8351-4360-8d4f-f9d79be84e26

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Normal_conj_mem_congK


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L), c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl → x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 → c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | exact GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK <;> assumption)
end _root_.GlobalTheory.T
