-- Prove2me | solution 1 for GlobalTheory.PMonE.WinBounds.rW_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:53.152203+00:00
-- url     : https://prove2.me/submissions/4508b4bf-5c23-4fa8-9d2b-65721e529aec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBound
import Theorems.Thm_GlobalTheory_PMonE_WinBounds_idx_spec

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
theorem _root_.solution (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]
end GlobalTheory.PMonE.WinBounds
