-- Prove2me | solution 1 for HSDoublingWork.entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:43.620851+00:00
-- url     : https://prove2.me/submissions/b0fe1e35-39fa-4078-a9fb-a49df4b60ae1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open HSDoublingWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ)
namespace HSDoublingWork
theorem _root_.solution (x : Fin N × Fin N) : ‖cBpp ε z x.1 x.2‖ ^ 2 = U ε z x + U ε z x.swap := by
  obtain ⟨a, b⟩ := x
  dsimp only [cBpp, U, Prod.swap]
  by_cases h1 : a < b ∧ ε a ≠ ε b
  · have h2 : ¬ (b < a ∧ ε b ≠ ε a) := fun h => absurd h1.1 (not_lt.2 h.1.le)
    simp only [dif_pos h1, dif_neg h2, add_zero]
  · by_cases h3 : b < a ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h3, zero_add, norm_star]
    · simp only [dif_neg h1, dif_neg h3, norm_zero]
      norm_num
end HSDoublingWork
