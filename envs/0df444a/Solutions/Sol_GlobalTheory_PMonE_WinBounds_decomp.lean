-- Prove2me | solution 1 for GlobalTheory.PMonE.WinBounds.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:50.953897+00:00
-- url     : https://prove2.me/submissions/5eb2a9b9-f44c-48ec-8fc1-dbe399a12605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.WinBounds
open GlobalTheory.PMonE
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE.WinBounds
theorem _root_.solution (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith
end GlobalTheory.PMonE.WinBounds
