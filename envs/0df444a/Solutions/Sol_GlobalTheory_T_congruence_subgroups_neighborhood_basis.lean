-- Prove2me | solution 1 for GlobalTheory.T.congruence_subgroups_neighborhood_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:37.520218+00:00
-- url     : https://prove2.me/submissions/048e492d-9bc1-4a17-a99c-3262d4f9294f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupsNeighborhoodBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupsNeighborhoodBasisStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_congK_cofinal


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (U : Set (GL (Fin n) L)), IsOpen U → (1 : GL (Fin n) L) ∈ U → ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε → (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.congK_cofinal | exact GlobalTheory.CompanionTheory.CartGL.congK_cofinal | (intros; apply GlobalTheory.CompanionTheory.CartGL.congK_cofinal <;> assumption)
end _root_.GlobalTheory.T
