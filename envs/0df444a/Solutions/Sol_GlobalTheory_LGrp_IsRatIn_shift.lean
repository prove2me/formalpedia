-- Prove2me | solution 1 for GlobalTheory.LGrp.IsRatIn.shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:42.98347+00:00
-- url     : https://prove2.me/submissions/e43a3000-1e41-4285-bf6c-008b12e3744b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open Polynomial
namespace GlobalTheory.LGrp
namespace IsRatIn
theorem _root_.solution {q : ℕ} (hq : q ≠ 0) {F : ℂ → ℂ} {R : RatFunc ℂ} (h : IsRatIn q F R) (s : ℂ) :
    IsRatIn q (fun z => F (z + s)) (scaleRat (negPowUnit q hq s) R) := by
  obtain ⟨r, h⟩ := h
  exact ⟨r - s.re, fun z hz => (h (z + s) (by simpa using sub_lt_iff_lt_add.1 hz)).scaleRat hq⟩
end IsRatIn
end GlobalTheory.LGrp
