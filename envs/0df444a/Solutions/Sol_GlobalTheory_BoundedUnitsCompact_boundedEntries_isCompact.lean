-- Prove2me | solution 1 for GlobalTheory.BoundedUnitsCompact.boundedEntries_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:29.716964+00:00
-- url     : https://prove2.me/submissions/cd7283ea-1dce-4d9d-b5e0-4282fbc4d600

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedEntriesIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedUnitsCompact
namespace GlobalTheory.BoundedUnitsCompact
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
end GlobalTheory.BoundedUnitsCompact
