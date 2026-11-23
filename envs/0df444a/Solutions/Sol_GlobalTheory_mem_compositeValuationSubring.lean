-- Prove2me | solution 1 for GlobalTheory.mem_compositeValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:37.930504+00:00
-- url     : https://prove2.me/submissions/48abfbae-33c6-4341-9e94-d7fcf969d597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) (x : L) :
    x ∈ compositeValuationSubring W V ↔ ∃ h : x ∈ W, residue W ⟨x, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, h⟩, hV, rfl⟩
end GlobalTheory
