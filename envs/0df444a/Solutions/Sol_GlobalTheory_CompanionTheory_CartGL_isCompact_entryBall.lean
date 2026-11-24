-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.isCompact_entryBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:34.910606+00:00
-- url     : https://prove2.me/submissions/340131e8-3065-4f84-a78c-d54822a59a22

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by
  have h : IsCompact (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have e : {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} =
      (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
        Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) := by
    ext M
    constructor
    · intro hM i _ j _
      have := hM i j
      rw [Matrix.sub_apply] at this
      exact mem_closedBall_iff_norm.2 this
    · intro hM i j
      have := mem_closedBall_iff_norm.1 (hM i (Set.mem_univ _) j (Set.mem_univ _))
      rw [Matrix.sub_apply]
      exact this
  rw [e]
  exact h
end GlobalTheory.CompanionTheory.CartGL
