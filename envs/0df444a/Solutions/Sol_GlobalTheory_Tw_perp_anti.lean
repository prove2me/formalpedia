-- Prove2me | solution 1 for GlobalTheory.Tw.perp_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:29.619094+00:00
-- url     : https://prove2.me/submissions/5b41e3eb-9eac-4382-85a9-a4d3decacb5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
namespace GlobalTheory.Tw
theorem _root_.solution {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp V' ≤ perp V := fun _ hw v hv => hw v (h hv)
end GlobalTheory.Tw
