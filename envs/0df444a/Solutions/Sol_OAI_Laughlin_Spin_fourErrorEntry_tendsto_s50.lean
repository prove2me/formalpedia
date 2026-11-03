-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:03:05.466206+00:00
-- url     : https://prove2.me/submissions/53f6eec6-225c-417b-90c1-3d0fda1049cb

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_coefficient_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem fourErrorEntry_tendsto_s50_oai (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    Tendsto (fun Q => fourErrorEntry Q D r s t e f) atTop (𝓝 (fourErrorLimitEntry D r s t e f)) := by
  unfold fourErrorEntry fourErrorLimitEntry
  dsimp only
  by_cases hD : D ≤ e.1+e.2.1+(f.1+f.2.1-t)
  · simp only [ite_eq_left hD]
    exact (tendsto_const_nhds.mul
      (source_fourBody_coefficient_tendsto_s50 r D _ e.1 e.2.1 _ hr hD rfl)).mul
      (source_fourBody_coefficient_tendsto_s50 s D _ f.1 f.2.1 _ hs hD (by omega))
  · simp only [ite_eq_right hD]; exact tendsto_const_nhds

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50_oai := @OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50_oai
