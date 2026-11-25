-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCount.addSet_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:02.815801+00:00
-- url     : https://prove2.me/submissions/44ae6c4b-8952-4f3d-b39f-7fdf12167cb3

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCount
namespace GlobalTheory.CompanionTheory.ZuckCount
theorem _root_.solution {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) (hs : s ∉ J) :
    addSet μ J + Pi.single s 1 = addSet μ (insert s J) := by
  funext a
  by_cases ha : a = s
  · subst ha
    simp [addSet, hs]
  · simp [addSet, ha]
end GlobalTheory.CompanionTheory.ZuckCount
