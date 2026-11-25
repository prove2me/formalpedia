-- Prove2me | solution 1 for GlobalTheory.Chamber.IsPar.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:29.667627+00:00
-- url     : https://prove2.me/submissions/283696e6-5721-4a36-9810-7de18717ebcb

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
namespace IsPar
theorem _root_.solution {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) : IsPar Q :=
  ⟨fun h0 => h.1 (e h0), fun u hu u' hu' => h.2 u (e hu) u' (e hu')⟩
end IsPar
end GlobalTheory.Chamber
