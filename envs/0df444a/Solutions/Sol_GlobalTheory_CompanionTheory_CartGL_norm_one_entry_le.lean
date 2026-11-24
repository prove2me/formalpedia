-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.norm_one_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:37.139281+00:00
-- url     : https://prove2.me/submissions/ae003f81-0ed2-41af-bcba-a69f52ab3e53

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaE
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixNearIdentityInCongruenceSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one
end GlobalTheory.CompanionTheory.CartGL
