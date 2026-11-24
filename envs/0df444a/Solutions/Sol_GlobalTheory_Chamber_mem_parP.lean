-- Prove2me | solution 1 for GlobalTheory.Chamber.mem_parP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:33.711796+00:00
-- url     : https://prove2.me/submissions/c42e0e13-ebbb-4978-a542-5e12e4ea8ba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
theorem _root_.solution {𝔞 : Submodule ℝ (A0 k)} {R P : Finset (SV k)} : P ∈ parP 𝔞 R ↔ IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P := by
  simp [parP]
end GlobalTheory.Chamber
