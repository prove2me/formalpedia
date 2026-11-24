-- Prove2me | solution 1 for GlobalTheory.LGrp.HasValueAt.zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:33.822802+00:00
-- url     : https://prove2.me/submissions/1759eda6-1611-4518-93bb-35689a8a220d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv


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
namespace HasValueAt
theorem _root_.solution {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) (hv : v ≠ 0) (m : ℤ) :
    HasValueAt (R ^ m) x (v ^ m) := by
  cases m with
  | ofNat m => simpa using h.pow m
  | negSucc m => simpa using (h.pow (m + 1)).inv (pow_ne_zero _ hv)
end HasValueAt
end GlobalTheory.LGrp
